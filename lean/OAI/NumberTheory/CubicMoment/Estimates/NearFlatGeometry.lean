import OAI.NumberTheory.CubicMoment.Estimates.FlatTripleGeometry

namespace OAI

/-! The complement of the explicitly counted flat boxes supplies the
logarithmic length gap required by the ordinary bilinear estimate. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma nonflat_singleton_length_gap {i j : ℕ} (z : largeTupleBoxIndex i j)
    (a : Fin i ⊕ Fin j) {Z : ℝ} (hZ : 0 < Z) (G : ℕ)
    (hmax : ∀ b, largeTupleNormScale z.1.2 b ≤ largeTupleNormScale z.1.2 a)
    (hn : ¬∃ B : ℝ, (∀ b, largeTupleNormScale z.1.2 b ≤ B) ∧
      B^3 ≤ (∏ b, largeTupleNormScale z.1.2 b)*Z^G) :
    largeTupleGroupLength (Finset.univ\{a}) z ≤ (largeTupleNormScale z.1.2 a)^2/Z^G := by
  have hB := largeTupleNormScale_pos z.1.2 a
  have hh : (∏ b, largeTupleNormScale z.1.2 b)*Z^G < (largeTupleNormScale z.1.2 a)^3 :=
    lt_of_not_ge (fun h => hn ⟨_,hmax,h⟩)
  rw [← largeTuple_singleton_product z a] at hh
  apply (le_div_iff₀ (pow_pos hZ G)).mpr
  apply le_of_lt
  apply (mul_lt_mul_iff_right₀ hB).mp
  calc
    _ = (largeTupleGroupLength (Finset.univ\{a}) z*largeTupleNormScale z.1.2 a)*Z^G := by ring
    _ < (largeTupleNormScale z.1.2 a)^3 := hh
    _ = _ := by ring

lemma nearFlat_log_denominator {X B : ℝ} (hX : 1 ≤ X) (hB : 1 ≤ B)
    (hBX : B ≤ 3*X) {g G : ℕ} (hg : g+1 ≤ G)
    (hlarge : max 2 ((2:ℝ)^g) ≤ 1+Real.log X) :
    (1+Real.log B)^g ≤ (1+Real.log X)^G := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hlog := Real.log_le_log (zero_lt_one.trans_le hB) hBX
  rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hXp.ne'] at hlog
  have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
  have hZX : 1 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hZB : 0 ≤ 1+Real.log B := by linarith [Real.log_nonneg hB]
  calc
    _ ≤ (2*(1+Real.log X))^g := pow_le_pow_left₀ hZB (by linarith [le_max_left 2 ((2:ℝ)^g)]) g
    _ = (2:ℝ)^g*(1+Real.log X)^g := mul_pow _ _ _
    _ ≤ (1+Real.log X)*(1+Real.log X)^g :=
      mul_le_mul_of_nonneg_right ((le_max_right 2 ((2:ℝ)^g)).trans hlarge) (by positivity)
    _ = (1+Real.log X)^(g+1) := by rw [pow_succ]; ring
    _ ≤ _ := pow_le_pow_right₀ hZX hg

end CubicFirstMoment

end

end OAI
