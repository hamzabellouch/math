import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedTwoStage
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedYYReduction
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedThirdXZ

namespace OAI

/-! One literal rational six-local to two-local X/Z family.  The intermediate
types retain the original term index and the bounded gadget-word index. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedXZ
open scoped Classical

abbrev ThreeTerm (κ : Type) := (κ × Fin 4) × Fin 4
abbrev ThreeQubit (ι κ : Type) := (ι ⊕ κ) ⊕ (κ × Fin 4)
abbrev TwoTerm (κ : Type) := ThreeTerm κ × Fin 7
abbrev TwoQubit (ι κ : Type) := ThreeQubit ι κ ⊕ ThreeTerm κ
abbrev XZThreeTerm (κ : Type) := TwoTerm κ × Fin 4
abbrev XZThreeQubit (ι κ : Type) := TwoQubit ι κ ⊕ TwoTerm κ
abbrev OutputTerm (κ : Type) := XZThreeTerm κ × Fin 7
abbrev OutputQubit (ι κ : Type) := XZThreeQubit ι κ ⊕ XZThreeTerm κ

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def threeWord (xs : κ → List ι) (w : κ → ι → Fin 4) :
    ThreeTerm κ → ThreeQubit ι κ → Fin 4 := QuantumOrderedTwoStage.word xs w

def threeSites (xs : κ → List ι) : ThreeTerm κ → List (ThreeQubit ι κ) :=
  QuantumOrderedTwoStage.sites xs

def threeCoefficient (J : κ → ℚ) (N : ℕ) : ThreeTerm κ → ℚ :=
  QuantumOrderedTwoStage.coefficient J N

def twoWord (xs : κ → List ι) (w : κ → ι → Fin 4) :
    TwoTerm κ → TwoQubit ι κ → Fin 4 :=
  QuantumOrderedThird.outputWord (threeSites xs) (threeWord xs w)

def twoSites (xs : κ → List ι) (w : κ → ι → Fin 4) :
    TwoTerm κ → List (TwoQubit ι κ) :=
  QuantumOrderedThird.outputSites (threeSites xs) (threeWord xs w)

def twoCoefficient (J : κ → ℚ) (N : ℕ) : TwoTerm κ → ℚ :=
  QuantumOrderedThird.outputCoefficient (threeCoefficient J N) N

def xzThreeWord (xs : κ → List ι) (w : κ → ι → Fin 4) :
    XZThreeTerm κ → XZThreeQubit ι κ → Fin 4 :=
  QuantumOrderedYY.outputWord (twoSites xs w) (twoWord xs w)

def xzThreeSites (xs : κ → List ι) (w : κ → ι → Fin 4) :
    XZThreeTerm κ → List (XZThreeQubit ι κ) :=
  QuantumOrderedYY.outputSites (twoSites xs w)

def xzThreeCoefficient (J : κ → ℚ) (N : ℕ) : XZThreeTerm κ → ℚ :=
  QuantumOrderedYY.outputCoefficient (twoCoefficient J N) N

def word (xs : κ → List ι) (w : κ → ι → Fin 4) :
    OutputTerm κ → OutputQubit ι κ → Fin 4 :=
  QuantumOrderedThird.outputWord (xzThreeSites xs w) (xzThreeWord xs w)

def sites (xs : κ → List ι) (w : κ → ι → Fin 4) :
    OutputTerm κ → List (OutputQubit ι κ) :=
  QuantumOrderedThird.outputSites (xzThreeSites xs w) (xzThreeWord xs w)

def coefficient (J : κ → ℚ) (N : ℕ) : OutputTerm κ → ℚ :=
  QuantumOrderedThird.outputCoefficient (xzThreeCoefficient J N) N

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem threeSites_nodup (xs : κ → List ι) (hx : ∀ e, (xs e).Nodup) :
    ∀ p, (threeSites xs p).Nodup := QuantumOrderedTwoStage.sites_nodup xs hx

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem threeSites_length (xs : κ → List ι) (hlen : ∀ e, (xs e).length ≤ 6) :
    ∀ p, (threeSites xs p).length ≤ 3 := QuantumOrderedTwoStage.sites_length xs hlen

theorem threeSites_cover (xs : κ → List ι) (w : κ → ι → Fin 4) :
    ∀ p, qmaPauliSupport (threeWord xs w p) ⊆ (threeSites xs p).toFinset :=
  QuantumOrderedTwoStage.support_cover xs w

theorem three_even (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) :
    ∀ p, Even (qmaPauliYCount (threeWord xs w p)) :=
  QuantumOrderedTwoStage.even xs w hx hcover he

theorem twoSites_nodup (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup) :
    ∀ p, (twoSites xs w p).Nodup :=
  QuantumOrderedThird.outputSites_nodup _ _
    (threeSites_length xs hlen) (threeSites_nodup xs hx)

theorem twoSites_length (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) : ∀ p, (twoSites xs w p).length ≤ 2 :=
  QuantumOrderedThird.outputSites_length _ _ (threeSites_length xs hlen)

theorem twoSites_cover (xs : κ → List ι) (w : κ → ι → Fin 4) :
    ∀ p, qmaPauliSupport (twoWord xs w p) ⊆ (twoSites xs w p).toFinset :=
  QuantumOrderedThird.outputSites_cover _ _

theorem two_even (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) :
    ∀ p, Even (qmaPauliYCount (twoWord xs w p)) :=
  QuantumOrderedThird.output_even _ _ (threeSites_length xs hlen)
    (threeSites_nodup xs hx) (threeSites_cover xs w) (three_even xs w hx hcover he)

theorem xzThreeSites_nodup (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup) :
    ∀ p, (xzThreeSites xs w p).Nodup :=
  QuantumOrderedYY.outputSites_nodup _ (twoSites_nodup xs w hlen hx)

theorem xzThreeSites_length (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) : ∀ p, (xzThreeSites xs w p).length ≤ 3 :=
  QuantumOrderedYY.outputSites_length _ (twoSites_length xs w hlen)

theorem xzThreeSites_cover (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) :
    ∀ p, qmaPauliSupport (xzThreeWord xs w p) ⊆ (xzThreeSites xs w p).toFinset :=
  QuantumOrderedYY.outputSites_cover _ _ (twoSites_length xs w hlen)
    (twoSites_nodup xs w hlen hx) (twoSites_cover xs w) (two_even xs w hlen hx hcover he)

theorem xzThree_noY (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) : ∀ p i, xzThreeWord xs w p i ≠ 2 :=
  QuantumOrderedYY.output_noY _ _ (twoSites_length xs w hlen)
    (twoSites_nodup xs w hlen hx) (twoSites_cover xs w) (two_even xs w hlen hx hcover he)

theorem sites_nodup (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup) :
    ∀ p, (sites xs w p).Nodup :=
  QuantumOrderedThird.outputSites_nodup _ _ (xzThreeSites_length xs w hlen)
    (xzThreeSites_nodup xs w hlen hx)

theorem sites_length (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) : ∀ p, (sites xs w p).length ≤ 2 :=
  QuantumOrderedThird.outputSites_length _ _ (xzThreeSites_length xs w hlen)

theorem sites_cover (xs : κ → List ι) (w : κ → ι → Fin 4) :
    ∀ p, qmaPauliSupport (word xs w p) ⊆ (sites xs w p).toFinset := by
  intro p i hi
  have h := QuantumOrderedThird.outputSites_cover (xzThreeSites xs w) (xzThreeWord xs w) p hi
  have hm : i ∈ sites xs w p := by simpa only [sites, List.mem_toFinset] using h
  exact List.mem_toFinset.mpr hm

theorem noY (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) : ∀ p i, word xs w p i ≠ 2 :=
  QuantumOrderedThird.output_noY _ _ (xzThree_noY xs w hlen hx hcover he)

theorem support (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (p : OutputTerm κ) :
    (qmaPauliSupport (word xs w p)).card ≤ 2 :=
  (Finset.card_le_card (sites_cover xs w p)).trans
    ((List.toFinset_card_le _).trans (sites_length xs w hlen p))

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem term_count : Fintype.card (OutputTerm κ) = 3136*Fintype.card κ := by
  simp only [OutputTerm,XZThreeTerm,TwoTerm,ThreeTerm,Fintype.card_prod,Fintype.card_fin]
  omega

omit [DecidableEq ι] [DecidableEq κ] in
theorem qubit_count : Fintype.card (OutputQubit ι κ) =
    Fintype.card ι+581*Fintype.card κ := by
  simp only [OutputQubit,XZThreeQubit,TwoQubit,ThreeQubit,XZThreeTerm,TwoTerm,ThreeTerm,
    Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega

end ContinuumCoulomb.QuantumOrderedXZ

end

end OAI
