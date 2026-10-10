import OAI.Probability.SignedSweeps.BaseCases

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma groupAverage_apply_action {G E : Type*} [Group G] [Fintype G]
    [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (g : G) (x : E) :
    groupAverage ρ (ρ g x) = groupAverage ρ x := by
  classical
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    ← Module.End.mul_apply, ← map_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

lemma groupAverage_anti_fixed {G E : Type*} [Group G] [Fintype G]
    [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (g : G) (x : E)
    (hx : ρ g x = -x) : groupAverage ρ x = 0 := by
  have hh := groupAverage_apply_action ρ g x
  rw [hx, map_neg] at hh
  have hz : (2 : ℂ) • groupAverage ρ x = 0 := by
    rw [two_smul, ← hh]
    exact neg_add_eq_zero.mpr hh.symm
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

lemma regularRepresentation_single {n : ℕ} (g h : SymmetricGroup n) (z : ℂ) :
    regularRepresentation n g (EuclideanSpace.single h z) =
      EuclideanSpace.single (g * h) z := by
  classical
  ext k
  simp only [regularRepresentation_apply, PiLp.single_apply, inv_mul_eq_iff_eq_mul]

lemma complexSign_mul_self {n : ℕ} (g : SymmetricGroup n) :
    complexSign n g * complexSign n g = 1 := by
  change (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ) * (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ) = 1
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

lemma polytabloid_column_action {n : ℕ} (lam : Partition n) (g : colSubgroup lam) :
    regularRepresentation n g.1 (polytabloid lam) = complexSign n g.1 • polytabloid lam := by
  classical
  change regularRepresentation n g.1 (∑ c : colSubgroup lam, ∑ a : rowSubgroup lam,
    complexSign n c.1 • EuclideanSpace.single (c.1 * a.1) 1) = complexSign n g.1 •
    (∑ c : colSubgroup lam, ∑ a : rowSubgroup lam,
      complexSign n c.1 • EuclideanSpace.single (c.1 * a.1) 1)
  simp only [map_sum, map_smul, regularRepresentation_single, Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.mulLeft g)
  intro c
  apply Finset.sum_congr rfl
  intro a _
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, smul_smul, ← mul_assoc,
    complexSign_mul_self, one_mul]

lemma long_column_coordinate_pair {d : ℕ} (lam : Partition (2 ^ d))
    (hl : 2 ^ d / 2 < lam.1.colLen 0) (i : Fin d) (g : SymmetricGroup (2 ^ d)) :
    ∃ a b : Fin (2 ^ d), a ≠ b ∧ lam.colOf a = lam.colOf b ∧
      Equiv.swap (g a) (g b) ∈ coordinateSubgroup d i := by
  classical
  let B := {j : Fin d // j ≠ i} → Fin 2
  have hcard : 2 ^ d = 2 * Fintype.card B := by
    simpa [B, Fintype.card_fun] using Fintype.card_congr (Equiv.funSplitAt i (Fin 2))
  let a : Fin (lam.1.colLen 0) → Fin (2 ^ d) := fun c =>
    lam.tableau ⟨(c.1, 0), YoungDiagram.mem_iff_lt_colLen.mpr c.2⟩
  have hai : Function.Injective a := by
    intro c e hce
    have ht := lam.tableau.injective hce
    exact Fin.ext (congrArg (fun c : {c // c ∈ lam.1.cells} => c.1.1) ht)
  let f : Fin (lam.1.colLen 0) → B :=
    fun c j => (positionsEquiv d).symm (g (a c)) j.1
  obtain ⟨c, e, hce, hfe⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by
    simp only [Fintype.card_fin]
    omega)
  refine ⟨a c, a e, fun he => hce (hai he), ?_, ?_⟩
  · simp [Partition.colOf, a]
  · apply swap_mem_fiberSubgroup
    exact hfe

lemma regular_layer_annihilates_generator {d : ℕ} (lam : Partition (2 ^ d))
    (hl : 2 ^ d / 2 < lam.1.colLen 0) (i : Fin d) (g : SymmetricGroup (2 ^ d)) :
    groupAverage ((regularRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype)
      (regularRepresentation (2 ^ d) g (polytabloid lam)) = 0 := by
  classical
  obtain ⟨a, b, hab, hc, hm⟩ := long_column_coordinate_pair lam hl i g
  apply groupAverage_anti_fixed _ ⟨Equiv.swap (g a) (g b), hm⟩
  change regularRepresentation _ (Equiv.swap (g a) (g b))
    (regularRepresentation _ g (polytabloid lam)) = _
  rw [← Module.End.mul_apply, ← map_mul, Equiv.swap_mul_eq_mul_swap]
  simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
  rw [map_mul, Module.End.mul_apply]
  have ha := polytabloid_column_action lam ⟨Equiv.swap a b, swap_mem_fiberSubgroup _ hc⟩
  have hs : complexSign _ (Equiv.swap a b) = -1 := by
    simp [complexSign, Equiv.Perm.sign_swap hab]
  rw [ha, hs, neg_one_smul, map_neg]

lemma layerOperator_eq_zero_of_long_column {d : ℕ} (lam : Partition (2 ^ d))
    (hl : 2 ^ d / 2 < lam.1.colLen 0) (i : Fin d) : layerOperator lam i = 0 := by
  classical
  let A := groupAverage ((regularRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype)
  have ha : (spechtSubrepresentation lam).toSubmodule ≤ A.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact regular_layer_annihilates_generator lam hl i g
  ext x
  have hx := ha x.property
  apply (show Function.Injective (spechtInclusion lam) from Subtype.val_injective)
  rw [LinearMap.zero_apply, map_zero]
  change A (spechtInclusion lam x) = 0 at hx
  simp only [layerOperator, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have he (g : coordinateSubgroup d i) : spechtInclusion lam (spechtRepresentation lam g.1 x) =
      regularRepresentation _ g.1 (spechtInclusion lam x) := rfl
  simp only [he]
  simpa only [A, groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, MonoidHom.comp_apply, Subgroup.subtype_apply] using hx

lemma sweepOperator_eq_zero_of_long_column {d : ℕ} (hd : 1 ≤ d) (lam : Partition (2 ^ d))
    (hl : 2 ^ d / 2 < lam.1.colLen 0) : sweepOperator lam = 0 := by
  apply List.prod_eq_zero
  have hi := layerOperator_eq_zero_of_long_column lam hl ⟨0, hd⟩
  rw [← hi]
  simp

lemma weightedMoment_eq_zero_of_long_column {d : ℕ} (hd : 1 ≤ d) (lam : Partition (2 ^ d))
    (hl : 2 ^ d / 2 < lam.1.colLen 0) {r : ℕ} (hr : 1 ≤ r) :
    weightedMoment lam r = 0 := by
  simp [weightedMoment, sweepSquare, positiveSquare,
    sweepOperator_eq_zero_of_long_column hd lam hl, zero_pow (by omega : r ≠ 0)]

end SignedSweeps
end

end OAI
