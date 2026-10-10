import OAI.NumberTheory.CubicMoment.Estimates.FlatTripleGeometry

namespace OAI

/-! A surviving tuple in the specified exceptional neighborhood is
balanced enough that the product of the other two scales exceeds each
single scale. This supplies the lower transition range also off the
flat locus. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma exceptionalTriple_coordinate_exponent {i j : ℕ} {δ : ℝ}
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : largePrimeTupleExceptional δ q) (a : Fin i ⊕ Fin j) :
    |largePrimeTupleExponent q a-1/3| < δ := by
  exact (Finset.single_le_sum (fun b _ => abs_nonneg (largePrimeTupleExponent q b-1/3))
    (Finset.mem_univ a)).trans_lt hq.2

lemma exceptionalTriple_coordinate_norm {i j : ℕ} {δ X : ℝ}
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hδ : δ ≤ 1/12) (hq : q ∈ largePrimeTupleBox i j X)
    (hex : largePrimeTupleExceptional δ q)
    (hln : 0 < Real.log (norm (largePrimeTupleProduct q))) (a : Fin i ⊕ Fin j) :
    largePrimeTupleNorm q a ≤ norm (largePrimeTupleProduct q)^(5/12:ℝ) := by
  have hn : 0 < norm (largePrimeTupleProduct q) := by
    rw [← largePrimeTupleNorm_prod]
    exact Finset.prod_pos (fun b _ => zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq b).1)
  have hp : 0 < largePrimeTupleNorm q a := zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq a).1
  have hb := exceptionalTriple_coordinate_exponent hex a
  have he : largePrimeTupleExponent q a ≤ 5/12 := by
    linarith [le_abs_self (largePrimeTupleExponent q a-1/3)]
  apply (Real.log_le_log_iff hp (Real.rpow_pos_of_pos hn _)).mp
  rw [Real.log_rpow hn]
  exact (div_le_iff₀ hln).mp he

theorem exceptionalTriple_scale_square (i j : ℕ) {δ : ℝ} (hδ : δ ≤ 1/12) :
    ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H : ℝ) {N : ℕ}
      (k : (Fin i ⊕ Fin j) → Fin N),
      ∀ q ∈ largePrimeTupleBox i j X,
      largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0 →
      largePrimeTupleExceptional δ q → ∀ a,
      (largeTupleNormScale (fun a => (k a).val) a)^2 ≤
        ∏ b, largeTupleNormScale (fun a => (k a).val) b := by
  filter_upwards [eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 200,
    eventually_const_mul_rpow_le (by norm_num : (5/6:ℝ) < 1) (16*3^(5/6:ℝ))]
    with X hX hlog hgap
  intro ℓ ξ Ct H N k q hq hne hex a
  have hXp : 0 < X := zero_lt_one.trans_le hX
  obtain ⟨hn,hln⟩ := largePrimeTuplePiece_log_pos hX hlog k hne
  have hupper := exceptionalTriple_coordinate_norm hδ hq hex hln a
  have hcoord := (largePrimeTuplePiece_coordinate_range k (mul_ne_zero_iff.mp hne).2 a).1
  have hpow := pow_le_pow_left₀ (largeTupleNormScale_pos _ _).le (hcoord.trans hupper) 2
  have he : (norm (largePrimeTupleProduct q)^(5/12:ℝ))^2 =
      norm (largePrimeTupleProduct q)^(5/6:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hn.le]
    norm_num
  rw [he] at hpow
  have hprod := largePrimeTuplePiece_scale_product hXp k hne
  rw [hex.1] at hprod
  have hP : X/16 ≤ (∏ b, largeTupleNormScale (fun a => (k a).val) b) := by
    simpa only [largeTupleSubsetScale,show (2:ℝ)*2^3=16 by norm_num] using hprod.1
  have hu := (largePrimeTupleTerm_product_range hXp (mul_ne_zero_iff.mp hne).1).2
  change norm (largePrimeTupleProduct q) ≤ 3*X at hu
  calc
    _ ≤ norm (largePrimeTupleProduct q)^(5/6:ℝ) := hpow
    _ ≤ (3*X)^(5/6:ℝ) := Real.rpow_le_rpow hn.le hu (by norm_num)
    _ ≤ X/16 := by
      rw [Real.mul_rpow (by norm_num) hXp.le]
      rw [Real.rpow_one] at hgap
      apply (le_div_iff₀ (by norm_num : (0:ℝ) < 16)).mpr
      nlinarith
    _ ≤ _ := hP

end CubicFirstMoment

end

end OAI
