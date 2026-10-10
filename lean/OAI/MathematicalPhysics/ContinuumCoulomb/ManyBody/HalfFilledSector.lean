import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.SpinEmbedding
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HubbardExcitation
import Mathlib.Logic.Equiv.Set

namespace OAI

/-! The actual half-filled occupation basis splits into spins and charge defects. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

theorem spinOccupationSet_mem (m : ℕ) (s : SourceSpinBasis (m + 1))
    (i : Fin (m + 1)) (σ : Fin 2) :
    siteMode m i σ ∈ spinOccupationSet m s ↔ σ = s i := by
  change siteMode m i σ ∈
    (Set.powersetCard.ofFinEmbEquiv (spinModeOrderEmbedding m s) :
      Finset (Fin ((2 * m + 1) + 1))) ↔ _
  rw [Set.powersetCard.mem_coe_iff,
    Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]
  constructor
  · rintro ⟨j, hj⟩
    have h := (siteMode_eq_iff m j i (s j) σ).mp hj
    simpa only [h.1] using h.2.symm
  · intro h
    exact ⟨i, congrArg (siteMode m i) h.symm⟩

theorem spinOccupationSet_card (m : ℕ) (s : SourceSpinBasis (m + 1)) :
    (spinOccupationSet m s).card = m + 1 :=
  (Set.powersetCard.ofFinEmbEquiv (spinModeOrderEmbedding m s)).property

theorem occupationAt_spinOccupationSet (m : ℕ) (s : SourceSpinBasis (m + 1))
    (i : Fin (m + 1)) : occupationAt m (spinOccupationSet m s) i = 1 := by
  apply Fin.ext
  simp only [occupationAt, spinOccupationSet_mem]
  generalize s i = σ
  fin_cases σ <;> norm_num

/-- The sum of actual local particle counts is the cardinality of the
occupied-mode set, including doubly occupied sites. -/
theorem occupationAt_sum (m : ℕ) (A : Finset (Fin ((2 * m + 1) + 1))) :
    (∑ i, (occupationAt m A i : ℕ)) = A.card := by
  have hlocal (i : Fin (m + 1)) :
      (occupationAt m A i : ℕ) = ∑ σ : Fin 2,
        if siteMode m i σ ∈ A then 1 else 0 := by
    rw [Fin.sum_univ_two]
    rfl
  simp_rw [hlocal]
  rw [← Fintype.sum_prod_type (fun p : Fin (m + 1) × Fin 2 =>
    if siteMode m p.1 p.2 ∈ A then (1 : ℕ) else 0)]
  have h := (siteModes m).sum_comp
    (fun k => if k ∈ A then (1 : ℕ) else 0)
  change (∑ p : Fin (m + 1) × Fin 2,
      if siteModes m p ∈ A then 1 else 0) = A.card
  rw [h]
  simp

def occupationSpin (m : ℕ) (A : Finset (Fin ((2 * m + 1) + 1))) :
    SourceSpinBasis (m + 1) :=
  fun i => if siteMode m i 0 ∈ A then 0 else 1

theorem onePerSite_mem_iff (m : ℕ) (A : Finset (Fin ((2 * m + 1) + 1)))
    (hA : ∀ i, occupationAt m A i = 1) (i : Fin (m + 1)) (σ : Fin 2) :
    siteMode m i σ ∈ A ↔ σ = occupationSpin m A i := by
  have hi := congrArg Fin.val (hA i)
  change (if siteMode m i 0 ∈ A then 1 else 0) +
    (if siteMode m i 1 ∈ A then 1 else 0) = 1 at hi
  fin_cases σ <;> dsimp [occupationSpin] <;> split_ifs at * <;> simp_all

/-- Every one-electron-per-site occupation is a unique canonical spin
occupation; there are no missing states in the low sector. -/
theorem onePerSite_eq_spinOccupationSet (m : ℕ)
    (A : Finset (Fin ((2 * m + 1) + 1))) (hA : ∀ i, occupationAt m A i = 1) :
    A = spinOccupationSet m (occupationSpin m A) := by
  ext k
  obtain ⟨⟨i, σ⟩, rfl⟩ := (siteModes m).surjective k
  exact (onePerSite_mem_iff m A hA i σ).trans (spinOccupationSet_mem m _ i σ).symm

abbrev HalfFilledBasis (m : ℕ) :=
  {A : Finset (Fin ((2 * m + 1) + 1)) // A.card = m + 1}

abbrev HalfFilledLowBasis (m : ℕ) :=
  {A : HalfFilledBasis m // ∀ i, occupationAt m A.val i = 1}

abbrev HalfFilledHighBasis (m : ℕ) :=
  {A : HalfFilledBasis m // ¬ ∀ i, occupationAt m A.val i = 1}

def spinLowEquiv (m : ℕ) : SourceSpinBasis (m + 1) ≃ HalfFilledLowBasis m where
  toFun s := ⟨⟨spinOccupationSet m s, spinOccupationSet_card m s⟩,
    occupationAt_spinOccupationSet m s⟩
  invFun A := occupationSpin m A.val.val
  left_inv s := by
    funext i
    simp only [occupationSpin, spinOccupationSet_mem]
    generalize s i = σ
    fin_cases σ <;> norm_num
  right_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    exact (onePerSite_eq_spinOccupationSet m A.val.val A.property).symm

/-- An exact partition of the full fixed-particle basis, including all
spin spectators in the charge-defect complement. -/
def halfFilledPartition (m : ℕ) :
    SourceSpinBasis (m + 1) ⊕ HalfFilledHighBasis m ≃ HalfFilledBasis m :=
  (Equiv.sumCongr (spinLowEquiv m) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl {A : HalfFilledBasis m | ∀ i, occupationAt m A.val i = 1})

theorem halfFilled_occupation_sum (m : ℕ) (A : HalfFilledBasis m) :
    (∑ i, (occupationAt m A.val i : ℕ)) = m + 1 :=
  (occupationAt_sum m A.val).trans A.property

end ContinuumCoulomb.HubbardGlobal

end

end OAI
