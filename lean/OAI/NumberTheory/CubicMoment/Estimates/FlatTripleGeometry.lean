import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleFlatCount
import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleRoughScales
import OAI.NumberTheory.CubicMoment.Estimates.FixedScalePowers
import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleWeightLengths
import OAI.NumberTheory.CubicMoment.Estimates.OverlapScale

namespace OAI

/-! The largest coordinate of a flat triple gives a genuine transition
range. All lower bounds come from the original nonzero box. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largeTuple_singleton_product {i j : ℕ} (z : largeTupleBoxIndex i j)
    (a : Fin i ⊕ Fin j) :
    largeTupleGroupLength (Finset.univ\{a}) z*largeTupleNormScale z.1.2 a =
      ∏ b, largeTupleNormScale z.1.2 b := by
  have hh := Finset.prod_mul_prod_compl ({a} : Finset (Fin i ⊕ Fin j))
    (largeTupleNormScale z.1.2)
  simpa only [Finset.prod_singleton,mul_comm,largeTupleGroupLength,Finset.compl_eq_univ_sdiff] using hh

lemma largeTuple_other_le_square {i j : ℕ} (hij : i+j = 3)
    (z : largeTupleBoxIndex i j) (a : Fin i ⊕ Fin j)
    (hmax : ∀ b, largeTupleNormScale z.1.2 b ≤ largeTupleNormScale z.1.2 a) :
    largeTupleGroupLength (Finset.univ\{a}) z ≤ (largeTupleNormScale z.1.2 a)^2 := by
  unfold largeTupleGroupLength
  calc
    _ ≤ ∏ _b ∈ (Finset.univ\{a} : Finset (Fin i ⊕ Fin j)), largeTupleNormScale z.1.2 a :=
      Finset.prod_le_prod₀ (fun b _ => (largeTupleNormScale_pos _ b).le) (fun b _ => hmax b)
    _ = _ := by simp [Finset.card_sdiff_of_subset (Finset.subset_univ _),hij]

lemma largeTuple_product_le_cube {i j : ℕ} (hij : i+j = 3)
    (z : largeTupleBoxIndex i j) (a : Fin i ⊕ Fin j)
    (hmax : ∀ b, largeTupleNormScale z.1.2 b ≤ largeTupleNormScale z.1.2 a) :
    (∏ b, largeTupleNormScale z.1.2 b) ≤ (largeTupleNormScale z.1.2 a)^3 := by
  calc
    _ ≤ ∏ _b : Fin i ⊕ Fin j, largeTupleNormScale z.1.2 a :=
      Finset.prod_le_prod₀ (fun b _ => (largeTupleNormScale_pos _ b).le) (fun b _ => hmax b)
    _ = _ := by simp [hij]

lemma eventually_maximum_triple_scale :
    ∀ᶠ X : ℝ in atTop, ∀ B P : ℝ, 0 ≤ B → X/16 ≤ P → P ≤ B^3 →
      X^(1/4:ℝ) ≤ B := by
  filter_upwards [eventually_gt_atTop (0:ℝ),
    eventually_const_mul_rpow_le (by norm_num : (3/4:ℝ) < 1) 16] with X hX hpow
  intro B P hB hlo hhi
  rw [Real.rpow_one] at hpow
  apply le_of_pow_le_pow_left₀ (by norm_num : (3:ℕ) ≠ 0) hB
  have he : (X^(1/4:ℝ))^3 = X^(3/4:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hX.le]
    norm_num
  rw [he]
  exact (le_div_iff₀ (by norm_num : (0:ℝ) < 16)).mpr (by simpa only [mul_comm] using hpow) |>.trans (hlo.trans hhi)

lemma flatTriple_transition_lower {A B Z : ℝ} (hB : 0 < B) (hZ : 0 ≤ Z)
    (G : ℕ) (hflat : B^3 ≤ (A*B)*Z^G) (hlog : Z^G ≤ B) : B ≤ A := by
  have hA : 0 ≤ A := by
    by_contra hn
    have hneg : A*B < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hn) hB
    have hnz : (A*B)*Z^G ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le (pow_nonneg hZ _)
    have hp : 0 < B^3 := pow_pos hB _
    linarith
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hB)).mp
  calc
    B*B^2 = B^3 := by ring
    _ ≤ (A*B)*Z^G := hflat
    _ ≤ (A*B)*B := mul_le_mul_of_nonneg_left hlog (mul_nonneg hA hB.le)
    _ = A*B^2 := by ring

theorem eventually_flatTriple_transition_geometry {i j : ℕ} (hij : i+j = 3) (G : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (z : largeTupleBoxIndex i j) (a : Fin i ⊕ Fin j),
      let B := largeTupleNormScale z.1.2 a
      let A := largeTupleGroupLength (Finset.univ\{a}) z
      (∀ b, largeTupleNormScale z.1.2 b ≤ B) →
      X/16 ≤ (∏ b, largeTupleNormScale z.1.2 b) →
      B^3 ≤ (∏ b, largeTupleNormScale z.1.2 b)*(1+Real.log X)^G →
      X^(1/4:ℝ) ≤ B ∧ B ≤ A ∧ A ≤ B^2 := by
  filter_upwards [eventually_maximum_triple_scale,eventually_gt_atTop (0:ℝ),
    eventually_ge_atTop (1:ℝ),overlap_power_log_saving (by norm_num : (0:ℝ) < 1/4) G 0]
    with X hquarter hX hX1 hlog
  intro z a
  dsimp only
  intro hmax hlo hflat
  have hB : 0 < largeTupleNormScale z.1.2 a := largeTupleNormScale_pos _ _
  have hQB := hquarter _ _ hB.le hlo (largeTuple_product_le_cube hij z a hmax)
  have hlog' : (1+Real.log X)^G ≤ largeTupleNormScale z.1.2 a := by
    apply le_trans _ hQB
    apply (div_le_one (Real.rpow_pos_of_pos hX _)).mp
    simpa only [Nat.mul_zero,pow_zero,div_one] using hlog
  refine ⟨hQB,?_,largeTuple_other_le_square hij z a hmax⟩
  apply flatTriple_transition_lower hB (by linarith [Real.log_nonneg hX1]) G _ hlog'
  simpa only [largeTuple_singleton_product] using hflat

end CubicFirstMoment

end

end OAI
