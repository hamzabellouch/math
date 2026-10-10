import OAI.Combinatorics.ContingencyTables.Transport.ComputedCompanionInstance
import OAI.Combinatorics.ContingencyTables.Rooted.RootedCountingAmplification
import OAI.Combinatorics.ContingencyTables.Counting.CountingTerminalSchedule

namespace OAI

/-! # Counting schedules computed from the original bounded margins

The capacity-bit sum is formed after the executed endpoint translation.
All remaining dimensions, precisions, cutoffs and phase counts use the
proved rational/natural formulas. No numeric schedule hypothesis is
left to an external caller.
-/

namespace ContingencyTables.ComputedCountingParameters

open CompanionFactorialApplication CompanionOracleDensity RootedPhaseHistory GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def dimensionAllowance : ℕ := 1+m*n

def capacityBits (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) : ℕ :=
  ∑ a : Fin m×Fin n,(ComputedTableTightening.newBounds r c b a.1 a.2+1).size

def coefficient (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) : ℕ :=
  CountingTerminalSchedule.coefficient (capacityBits r c b) (dimensionAllowance (m:=m) (n:=n))
    (epsilon/2)

def binCount (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) : ℕ :=
  16*coefficient r c b epsilon*(dimensionAllowance (m:=m) (n:=n))^2

def cutoff (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) : ℕ :=
  100*dimensionAllowance (m:=m) (n:=n)*binCount r c b epsilon

def phases (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) : ℕ :=
  10*coefficient r c b epsilon*(dimensionAllowance (m:=m) (n:=n))^2*(cutoff r c b epsilon+1)

lemma coefficient_pos (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0<epsilon) : 0<coefficient r c b epsilon :=
  CountingTerminalSchedule.coefficient_pos _ _ (by unfold dimensionAllowance; omega)
    (epsilon/2) (by positivity)

lemma binCount_pos (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0<epsilon) : 0<binCount r c b epsilon := by
  have hC:=coefficient_pos r c b epsilon he
  have hd : 0<dimensionAllowance (m:=m) (n:=n) := by unfold dimensionAllowance; omega
  unfold binCount
  positivity

lemma cutoff_two (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0<epsilon) : 2≤cutoff r c b epsilon := by
  have hK:=binCount_pos r c b epsilon he
  have hd : 1≤dimensionAllowance (m:=m) (n:=n) := by unfold dimensionAllowance; omega
  unfold cutoff
  nlinarith

def data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    Instance (Fin m) (Fin n) :=
  ComputedCompanionInstance.instanceData hEK r c b hne (cutoff r c b epsilon)
    (cutoff_two r c b epsilon he)

lemma data_dimension (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    (data hEK r c b hne epsilon he).d=dimensionAllowance (m:=m) (n:=n) := rfl

lemma data_capacityBits (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    CountingTerminalSchedule.capacityBits (data hEK r c b hne epsilon he)=capacityBits r c b := rfl

lemma binCount_cast (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    (binCount r c b epsilon:ℝ)=binWidth (data hEK r c b hne epsilon he)
      (coefficient r c b epsilon) := by
  simp only [binCount,binWidth,data_dimension,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]

lemma cutoff_eq (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    (data hEK r c b hne epsilon he).W=
      100*(data hEK r c b hne epsilon he).d*binCount r c b epsilon := rfl

lemma phases_final (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    phases r c b epsilon=CompanionTerminalApplication.finalPhase
      (data hEK r c b hne epsilon he) (capacityBits r c b) ((epsilon/2:ℚ):ℝ) := by
  rw [CountingTerminalSchedule.finalPhase_eq _ _ (epsilon/2) (by positivity)]
  rfl

lemma phases_height (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    phases r c b epsilon=rationalHeight (data hEK r c b hne epsilon he)
      (coefficient r c b epsilon) := rfl

/-- The canonical zero grid point is valid even when there are no free
coordinates; its construction does not search the geometric state space. -/
def start (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    Grid (I:=Fin (dimension (data hEK r c b hne epsilon he))) (binCount r c b epsilon) :=
  fun _=>⟨0,le_refl _,by have h:=binCount_pos r c b epsilon he; omega⟩

def settings (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    Settings (data hEK r c b hne epsilon he) :=
  RootedCountingSchedule.settings (data hEK r c b hne epsilon he)
    (coefficient r c b epsilon) (binCount r c b epsilon) (phases r c b epsilon)
    (capacityBits r c b) (binCount_pos r c b epsilon he) (cutoff_eq hEK r c b hne epsilon he).ge
    (epsilon/2) (start hEK r c b hne epsilon he)

end
end ContingencyTables.ComputedCountingParameters

end OAI
