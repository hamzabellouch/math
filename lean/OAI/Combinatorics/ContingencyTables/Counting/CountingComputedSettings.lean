import OAI.Combinatorics.ContingencyTables.Counting.CountingPhaseParametersProgram
import OAI.Combinatorics.ContingencyTables.Counting.CountingTerminalProgram
import OAI.Combinatorics.ContingencyTables.Counting.CountingLabelCountProgram
import OAI.Combinatorics.ContingencyTables.Rooted.ComputedRootedInput

namespace OAI

/-! # Computing every scalar control from the original bounded table -/

namespace ContingencyTables.CountingComputedSettings
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram
open CountingPhaseScalarProgram

abbrev Input := CountingBaseProgram.Input
abbrev Parameters := CountingPhaseParametersProgram.Input

def catalog (z : Input) : RootedForestCatalog.Data :=
  ComputedRootedInput.catalogData (z.1,CountingTerminalProgram.cutoff z)
def catalogRealizer : Realizer catalog :=
  composition (f := fun z : Input => (z.1,CountingTerminalProgram.cutoff z))
    (g := ComputedRootedInput.catalogData) (pair first CountingTerminalProgram.cutoffRealizer)
    ComputedRootedInput.catalogDataRealizer
lemma polynomial_catalog : PolynomialTime catalogRealizer :=
  polynomial_composition (polynomial_pair polynomial_first CountingTerminalProgram.polynomial_cutoff)
    ComputedRootedInput.polynomial_catalogData

def labelCount (z : Input) : ℕ := CountingLabelCountProgram.count (catalog z)
def labelCountRealizer : Realizer labelCount :=
  composition (f := catalog) (g := CountingLabelCountProgram.count)
    catalogRealizer CountingLabelCountProgram.countRealizer
lemma polynomial_labelCount : PolynomialTime labelCountRealizer :=
  polynomial_composition polynomial_catalog CountingLabelCountProgram.polynomial_count

def preliminary (z : Input) : List ℕ :=
  [labelCount z,CountingTerminalProgram.cutoff z,CountingTerminalProgram.phases z,0,0,0,
    CountingBaseProgram.capacityBits z.1]
private def consR {f : Input → ℕ} {g : Input → List ℕ}
    (F : Realizer f) (G : Realizer g) : Realizer (fun z => f z::g z) :=
  composition (f := fun z : Input => (f z,g z)) (g := fun p : ℕ×List ℕ => p.1::p.2)
    (pair F G) listCons
private lemma poly_consR {f : Input → ℕ} {g : Input → List ℕ}
    (F : Realizer f) (G : Realizer g) (hF : PolynomialTime F) (hG : PolynomialTime G) :
    PolynomialTime (consR F G) := polynomial_composition (polynomial_pair hF hG) polynomial_listCons

def preliminaryRealizer : Realizer preliminary :=
  consR labelCountRealizer (consR CountingTerminalProgram.cutoffRealizer
    (consR CountingTerminalProgram.phasesRealizer (consR (constant 0) (consR (constant 0)
      (consR (constant 0) (consR (composition (f := fun z : Input => z.1)
        (g := CountingBaseProgram.capacityBits) first CountingBaseProgram.capacityBitsRealizer)
        (constant [])))))))
lemma polynomial_preliminary : PolynomialTime preliminaryRealizer := by
  unfold preliminaryRealizer
  apply poly_consR _ _ polynomial_labelCount
  apply poly_consR _ _ CountingTerminalProgram.polynomial_cutoff
  apply poly_consR _ _ CountingTerminalProgram.polynomial_phases
  apply poly_consR _ _ (polynomial_constant 0)
  apply poly_consR _ _ (polynomial_constant 0)
  apply poly_consR _ _ (polynomial_constant 0)
  exact poly_consR _ _ (polynomial_composition polynomial_first CountingBaseProgram.polynomial_capacityBits)
    (polynomial_constant [])

def fullReturnCap : Expr := 65536*(h+1)^2*(restartTime+1)*(p^2+1)
def controlExpressions : List Expr := [p,w,h,restartTime,0,fullReturnCap,capacityBits]

def basic (z : Input) : Parameters :=
  (vector controlExpressions (preliminary z),CountingBaseProgram.half z.2)
def basicRealizer : Realizer basic :=
  pair (composition (f := preliminary) (g := vector controlExpressions)
    preliminaryRealizer (vectorRealizer controlExpressions))
    (composition second CountingBaseProgram.halfRealizer)
lemma polynomial_basic : PolynomialTime basicRealizer :=
  polynomial_pair (polynomial_composition polynomial_preliminary (polynomial_vector controlExpressions))
    (polynomial_composition polynomial_second CountingBaseProgram.polynomial_half)

def fillObservations (z : Parameters) : Parameters :=
  (z.1.take 4++(CountingPhaseParametersProgram.observations z::z.1.drop 5),z.2)
def fillObservationsRealizer : Realizer fillObservations := by
  let frontR : Realizer (fun z : Parameters => z.1.take 4) :=
    composition (f := fun z : Parameters => (z.1,4))
      (g := fun p : List ℕ×ℕ => p.1.take p.2) (pair first (constant 4)) takeFast
  let suffix : Realizer (fun z : Parameters => z.1.drop 5) :=
    composition (f := fun z : Parameters => (z.1,5))
      (g := fun p : List ℕ×ℕ => p.1.drop p.2) (pair first (constant 5)) dropFast
  let tailR : Realizer (fun z : Parameters => CountingPhaseParametersProgram.observations z::z.1.drop 5) :=
    composition (pair CountingPhaseParametersProgram.observationsRealizer suffix) listCons
  exact pair (composition (pair frontR tailR) append) second
lemma polynomial_fillObservations : PolynomialTime fillObservationsRealizer := by
  unfold fillObservationsRealizer
  exact polynomial_pair (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first (polynomial_constant 4)) polynomial_takeFast)
    (polynomial_composition (polynomial_pair CountingPhaseParametersProgram.polynomial_observations
      (polynomial_composition (polynomial_pair polynomial_first (polynomial_constant 5)) polynomial_dropFast))
        polynomial_listCons)) polynomial_append) polynomial_second

def parameters (z : Input) : Parameters := fillObservations (basic z)
def parametersRealizer : Realizer parameters :=
  composition (f := basic) (g := fillObservations) basicRealizer fillObservationsRealizer
lemma polynomial_parameters : PolynomialTime parametersRealizer :=
  polynomial_composition polynomial_basic polynomial_fillObservations

open CompanionFactorialApplication
open scoped Classical
variable {m n : ℕ}

lemma catalog_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    catalog (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      RootedForestCatalog.data (ComputedCountingParameters.data hEK r c b hne epsilon he) := by
  unfold catalog
  rw [CountingTerminalProgram.cutoff_data r c b epsilon he]
  exact ComputedRootedInput.catalogData_instance hEK r c b hne _ _

lemma labelCount_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    labelCount (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) := by
  rw [labelCount,catalog_data hEK r c b hne epsilon he,CountingLabelCountProgram.count_data]

lemma basic_values (P W H L : ℕ) :
    vector controlExpressions [P,W,H,0,0,0,L]=
      [P,W,H,4*CountingPhaseSchedule.observable P W*(H+P+L+5),0,
        CountingPhaseSchedule.returnCap P H (4*CountingPhaseSchedule.observable P W*(H+P+L+5)),L] := by
  simp [vector,controlExpressions,CountingPhaseScalarProgram.p,CountingPhaseScalarProgram.w,
    CountingPhaseScalarProgram.h,capacityBits,restartTime,observable,fullReturnCap,Expr.eval,
    CountingPhaseSchedule.observable,CountingPhaseSchedule.returnCap]

lemma fillObservations_values (P W H T N R L : ℕ) (e : CountingOracleScheduleProgram.Fraction) :
    fillObservations ([P,W,H,T,N,R,L],e)=
      ([P,W,H,T,CountingPhaseSchedule.observations P W H
        (CountingPhaseSchedule.tolerance H (TreeFraction.val e)),R,L],e) := by
  simp [fillObservations,CountingPhaseParametersProgram.observations_val]

end ContingencyTables.CountingComputedSettings

end OAI
