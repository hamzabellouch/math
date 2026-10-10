import OAI.NumberTheory.TotientAsymptotic.HeadSquareCase
import OAI.NumberTheory.TotientAsymptotic.SquareLayerSum

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def headSquareFamily (x : ℝ) (H : ℕ) (t : ℝ) : Finset (RemainderDatum (L x H) × ℕ) := by
  letI : DecidableEq (RemainderDatum (L x H) × ℕ) := Classical.decEq _
  exact (squareLayerPrimes x 0).biUnion (fun q =>
    (Finset.Icc 0 (L x H)).biUnion (fun j =>
      (Finset.Icc 0 (L x H)).biUnion (fun k => headSquareCase x H t q j k)))

lemma discard_square_log_with_head {x : ℝ} (hx : 1 < x) (hB : 2 ≤ B x) :
    2*(1+Real.log (discardPrimeBound (B x) : ℝ))^2*Real.log x ≤
      (8*Real.exp 2)*Real.exp (6*B x) := by
  have ha := mul_le_mul_of_nonneg_right (discard_square_log_mass hB) (Real.log_pos hx).le
  have he : Real.log x=Real.exp (B x) := (Real.exp_log (Real.log_pos hx)).symm
  rw [he] at ha ⊢
  apply ha.trans
  rw [mul_assoc,← Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)

lemma head_square_family_count (hmertens : MertensProductInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t ≤ x,
      ((headSquareFamily x H t).card : ℝ) ≤
      (x/Real.log x)*(∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*rho^(m x) := by
  obtain ⟨D,hD,hcase⟩ := head_square_case_count hmertens
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp (square_head_discard_geometric
    (C := 8*Real.exp 2) (D := D) (by positivity) (lt_of_lt_of_le zero_lt_one hD))
  filter_upwards [hcase,ford_band_polynomial_lower 44,eventually_collision_indices,eventually_ge_atTop H₀,
    eventually_ge_atTop 2,P_tendsto.eventually (eventually_ge_atTop 1)]
    with H hc hpoly hind hH0 hH hP
  filter_upwards [hc,hpoly,ford_band_log_upper,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_ge_atTop (2 : ℝ)),eventually_gt_atTop (1 : ℝ)]
    with x hcases hp hlog hHm hB hx
  intro t ht
  let W := ∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹
  let A := 1+Real.log (discardPrimeBound (B x) : ℝ)
  let E := D*(2*B x+2)
  let I := Finset.Icc 0 (L x H)
  let Q := squareLayerPrimes x 0
  let z := collisionSmoothCutoff x 0
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hA : 0 ≤ A := by
    have hN : (1 : ℝ) ≤ discardPrimeBound (B x) := by exact_mod_cast (show 1 ≤ discardPrimeBound (B x) by have := (discardPrimeBound_bounds hB).1; omega)
    dsimp [A]
    linarith [Real.log_nonneg hN]
  have hI : (I.card : ℝ) ≤ m x := by
    have hcn : I.card ≤ m x := by dsimp [I]; simp only [Nat.card_Icc]; unfold L; omega
    exact_mod_cast hcn
  have hz1 : 1 ≤ z := by dsimp [z,collisionSmoothCutoff]; exact Real.one_le_exp (Real.exp_pos _).le
  have hs := finite_square_case_sum Q I (headSquareCase x H t) (fun _ => (1 : ℝ))
    (fun _ => by norm_num) (mul_nonneg (zero_lt_one.trans hx).le hW) (sq_nonneg A)
    (pow_nonneg hE (m x)) hI hz1 (fun q hq => (Finset.mem_filter.mp hq).2) (by
      intro q hq j hj k hk
      have hqp := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1).2
      simpa only [W,A,E,Finset.sum_const,smul_eq_mul,nsmul_eq_mul,mul_one,mul_assoc]
        using hcases t ht j k q (Finset.mem_Icc.mp hj).2 (Finset.mem_Icc.mp hk).2 hqp)
  have hs' : ((headSquareFamily x H t).card : ℝ) ≤ x*W*((m x : ℝ)^2*A^2*E^(m x))*(2/z) := by
    simpa only [headSquareFamily,Q,I,Finset.sum_const,smul_eq_mul,nsmul_eq_mul,mul_one] using hs
  have hm0 : 0 < m x := by omega
  have hb44 : (m x : ℝ)^44 ≤ B x := by simpa [fordBandScale] using hp 0 hm0 hHm
  have hlog0 : Real.log (6*B x) ≤ 26*m x := by simpa [fordBandScale] using hlog 0 hm0
  have hcut : B x/(8*(m x : ℝ)^20) ≤ (7/10)*fordBandScale x (collisionLastIndex x 0) := by
    simpa [fordBandScale] using collision_cutoff_exponent_lower (by linarith : 1 < B x) hm0 (hind x hHm 0 (Nat.zero_le _)).2.1
  have hsmall := hH₀ (m x) (hH0.trans hHm) (B x) ((7/10)*fordBandScale x (collisionLastIndex x 0)) hb44 hlog0 hcut
  have hlogx := Real.log_pos hx
  have hcoef : 0 ≤ (x/Real.log x)*W := mul_nonneg (div_nonneg (zero_lt_one.trans hx).le hlogx.le) hW
  calc
    _ ≤ x*W*((m x : ℝ)^2*A^2*E^(m x))*(2/z) := hs'
    _ = ((x/Real.log x)*W)*((m x : ℝ)^2*(2*A^2*Real.log x)*E^(m x)/z) := by field_simp
    _ ≤ ((x/Real.log x)*W)*((m x : ℝ)^2*((8*Real.exp 2)*Real.exp (6*B x))*E^(m x)/z) := by
      have ht := mul_le_mul_of_nonneg_left (discard_square_log_with_head hx hB)
        (show 0 ≤ (m x : ℝ)^2 by positivity)
      have ht' := mul_le_mul_of_nonneg_right ht (pow_nonneg hE (m x))
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right ht' (by dsimp [z,collisionSmoothCutoff]; positivity)) hcoef
    _ ≤ _ := mul_le_mul_of_nonneg_left hsmall hcoef

end TotientAsymptotic

end

end OAI
