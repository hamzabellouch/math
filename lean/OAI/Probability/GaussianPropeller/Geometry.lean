import OAI.Probability.GaussianPropeller.CapReduction

namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Geometry

open scoped RealInnerProductSpace

lemma pair_factor_le_eight {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : a + b + c ≤ 1) :
    (1 + c)^2 * ((1 + a)^2 + (1 + b)^2) ≤ 8 := by
  have hc1 : c ≤ 1 := by linarith
  have hab : a + b ≤ 1 - c := by linarith
  have hab2 := (sq_le_sq₀ (by linarith : 0 ≤ a+b) (by linarith : 0 ≤ 1-c)).mpr hab
  have hu : (1+a)^2 + (1+b)^2 ≤ (2-c)^2 + 1 := by
    nlinarith only [hab, hab2, mul_nonneg ha hb]
  have hmul := mul_le_mul_of_nonneg_left hu (sq_nonneg (1+c))
  have hc2 := (sq_le_sq₀ hc (by norm_num : (0:ℝ) ≤ 1)).mpr hc1
  have hpos : 0 ≤ (1-c)^2 * (3-c^2) := mul_nonneg (sq_nonneg _) (by nlinarith)
  have hid : 8 - (1+c)^2 * ((2-c)^2+1) = (1-c)^2*(3-c^2) := by ring
  linarith only [hmul, hpos, hid]

lemma triple_factor_le_ten {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : a + b + c ≤ 1) :
    (1+a)^2*(1+b)^2 + (1+a)^2*(1+c)^2 + (1+b)^2*(1+c)^2 ≤ 10 := by
  let s := a+b+c
  let p := a*b+a*c+b*c
  let q := a*b*c
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := hs
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hs2 : s^2 ≤ 1 := by nlinarith only [hs0, hs1, mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  have hps : 3*p ≤ s^2 := by
    dsimp [p,s]
    nlinarith only [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (b-c)]
  have hp1 : p ≤ 1/3 := by linarith only [hps,hs2]
  have hsp : s*p ≤ 1/3 := (mul_le_mul_of_nonneg_right hs1 hp0).trans (by simpa using hp1)
  have hp2 : p^2 ≤ 1/9 := by
    have hh := (sq_le_sq₀ hp0 (by norm_num : (0:ℝ) ≤ 1/3)).mpr hp1
    norm_num at hh ⊢
    exact hh
  have hq : 0 ≤ (6+2*s)*q := mul_nonneg (by positivity) hq0
  have hid : (1+a)^2*(1+b)^2 + (1+a)^2*(1+c)^2 + (1+b)^2*(1+c)^2 =
      3+4*s+2*s^2+2*s*p+p^2-(6+2*s)*q := by dsimp [s,p,q]; ring
  rw [hid]
  linarith only [hs1, hs2, hsp, hp2, hq]

lemma row_two_le {ι : Type uι} {E : Type uE} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (w : ι → E)
    (hw : ∑ i, w i = 0) (hneg : ∀ i j, i ≠ j → ⟪w i, w j⟫ ≤ 0)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    -⟪w i, w j⟫ - ⟪w i, w k⟫ ≤ ‖w i‖^2 := by
  have hr : ∑ l ∈ Finset.univ.erase i, -⟪w i, w l⟫ = ‖w i‖^2 := by
    have hsum : ∑ l, ⟪w i, w l⟫ = 0 := by rw [← inner_sum, hw, inner_zero_right]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hsum
    rw [Finset.sum_neg_distrib, real_inner_self_eq_norm_sq] at *
    linarith only [hsum]
  rw [← hr]
  have hsub : ({j,k} : Finset ι) ⊆ Finset.univ.erase i := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · simp [hij.symm]
    · simp [hik.symm]
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun l hl _ => neg_nonneg.mpr (hneg i l (Finset.mem_erase.mp hl).1.symm))
  simpa only [Finset.sum_pair hjk, sub_eq_add_neg] using h

lemma row_determinants_lower {h₁ h₂ h₃ u v : ℝ}
    (hu : u ≤ 0) (hv : v ≤ 0) (hr : -u-v ≤ h₃) :
    h₃*(h₁+h₂-h₃) ≤ (h₃*h₁-u^2)+(h₃*h₂-v^2) := by
  have hp : 0 ≤ -u-v := by linarith
  have hh : 0 ≤ h₃ := hp.trans hr
  have hs := (sq_le_sq₀ hp hh).mpr hr
  nlinarith only [hs, mul_nonneg (neg_nonneg.mpr hu) (neg_nonneg.mpr hv)]

lemma three_correlations_lower {h₁ h₂ h₃ s ρ₁₂ ρ₁₃ ρ₂₃ : ℝ}
    (hs : 0 ≤ s) (hh₁ : s ≤ h₁) (hh₂ : s ≤ h₂) (hh₃ : s ≤ h₃)
    (h₁₂ : -1 ≤ ρ₁₂ ∧ ρ₁₂ ≤ 0) (h₁₃ : -1 ≤ ρ₁₃ ∧ ρ₁₃ ≤ 0)
    (h₂₃ : -1 ≤ ρ₂₃ ∧ ρ₂₃ ≤ 0) (hvar : 0 ≤ 3+2*(ρ₁₂+ρ₁₃+ρ₂₃)) :
    (3/2:ℝ)*s^2 ≤ h₁*h₂*(1-ρ₁₂^2)+h₁*h₃*(1-ρ₁₃^2)+h₂*h₃*(1-ρ₂₃^2) := by
  have hb {x : ℝ} (hx : -1 ≤ x ∧ x ≤ 0) : x^2 ≤ -x := by
    nlinarith only [mul_nonneg (by linarith only [hx.1] : 0 ≤ 1+x) (neg_nonneg.mpr hx.2)]
  have hv₁₂ : 0 ≤ 1-ρ₁₂^2 := by nlinarith only [hb h₁₂, h₁₂.1]
  have hv₁₃ : 0 ≤ 1-ρ₁₃^2 := by nlinarith only [hb h₁₃, h₁₃.1]
  have hv₂₃ : 0 ≤ 1-ρ₂₃^2 := by nlinarith only [hb h₂₃, h₂₃.1]
  have hsum : 3/2 ≤ (1-ρ₁₂^2)+(1-ρ₁₃^2)+(1-ρ₂₃^2) := by
    linarith only [hb h₁₂, hb h₁₃, hb h₂₃, hvar]
  have hprod {a b : ℝ} (ha : s ≤ a) (hb : s ≤ b) : s^2 ≤ a*b := by
    simpa only [pow_two] using mul_le_mul ha hb hs (hs.trans ha)
  calc
    (3/2:ℝ)*s^2 ≤ ((1-ρ₁₂^2)+(1-ρ₁₃^2)+(1-ρ₂₃^2))*s^2 :=
      mul_le_mul_of_nonneg_right hsum (sq_nonneg s)
    _ = s^2*(1-ρ₁₂^2)+s^2*(1-ρ₁₃^2)+s^2*(1-ρ₂₃^2) := by ring
    _ ≤ _ := add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right (hprod hh₁ hh₂) hv₁₂)
      (mul_le_mul_of_nonneg_right (hprod hh₁ hh₃) hv₁₃))
      (mul_le_mul_of_nonneg_right (hprod hh₂ hh₃) hv₂₃)

section InnerProduct
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def unitVector (w : E) : E := ‖w‖⁻¹ • w

lemma unitVector_norm {w : E} (hw : w ≠ 0) : ‖unitVector w‖ = 1 := by
  simp [unitVector, norm_smul, norm_ne_zero_iff.mpr hw]

lemma unitVector_inner_cancel (u v : E) :
    ‖u‖ * ‖v‖ * ⟪unitVector u, unitVector v⟫ = ⟪u,v⟫ := by
  by_cases hu : u = 0
  · simp [hu, unitVector]
  by_cases hv : v = 0
  · simp [hv, unitVector]
  simp only [unitVector, inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
  field_simp [norm_ne_zero_iff.mpr hu, norm_ne_zero_iff.mpr hv]

lemma unitVector_inner_nonpos {u v : E} (h : ⟪u,v⟫ ≤ 0) :
    ⟪unitVector u, unitVector v⟫ ≤ 0 := by
  simp only [unitVector, inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _))
    (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) h)

lemma unitVector_inner_bounds {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : ⟪u,v⟫ ≤ 0) :
    -1 ≤ ⟪unitVector u, unitVector v⟫ ∧ ⟪unitVector u, unitVector v⟫ ≤ 0 := by
  have hc := norm_inner_le_norm (𝕜 := ℝ) (unitVector u) (unitVector v)
  rw [unitVector_norm hu, unitVector_norm hv, mul_one, Real.norm_eq_abs] at hc
  exact ⟨(abs_le.mp hc).1, unitVector_inner_nonpos h⟩

lemma unitVector_variance (u v w : E) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    0 ≤ 3 + 2 * (⟪unitVector u, unitVector v⟫ + ⟪unitVector u, unitVector w⟫ +
      ⟪unitVector v, unitVector w⟫) := by
  have h := sq_nonneg ‖unitVector u + unitVector v + unitVector w‖
  rw [norm_add_sq_real, norm_add_sq_real, inner_add_left,
    unitVector_norm hu, unitVector_norm hv, unitVector_norm hw] at h
  nlinarith only [h]

lemma gram_det_unitVector (u v : E) :
    ‖u‖^2 * ‖v‖^2 * (1-⟪unitVector u, unitVector v⟫^2) =
      ‖u‖^2 * ‖v‖^2 - ⟪u,v⟫^2 := by
  calc
    _ = ‖u‖^2*‖v‖^2-(‖u‖*‖v‖*⟪unitVector u, unitVector v⟫)^2 := by ring
    _ = _ := by rw [unitVector_inner_cancel]

lemma three_gram_determinants_lower (u v w : E) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : ⟪u,v⟫ ≤ 0) (huw : ⟪u,w⟫ ≤ 0) (hvw : ⟪v,w⟫ ≤ 0)
    {s : ℝ} (hs : 0 ≤ s) (hsu : s ≤ ‖u‖^2) (hsv : s ≤ ‖v‖^2) (hsw : s ≤ ‖w‖^2) :
    (3/2:ℝ)*s^2 ≤ (‖u‖^2*‖v‖^2-⟪u,v⟫^2) + (‖u‖^2*‖w‖^2-⟪u,w⟫^2) +
      (‖v‖^2*‖w‖^2-⟪v,w⟫^2) := by
  have h := three_correlations_lower hs hsu hsv hsw
    (unitVector_inner_bounds hu hv huv) (unitVector_inner_bounds hu hw huw)
    (unitVector_inner_bounds hv hw hvw) (unitVector_variance u v w hu hv hw)
  simpa only [gram_det_unitVector] using h

lemma gram_det_nonneg (u v : E) : 0 ≤ ‖u‖^2*‖v‖^2-⟪u,v⟫^2 := by
  have h := real_inner_mul_inner_self_le u v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith only [h]

lemma first_constraint_of_pair_bounds (u v w : E) {t c L κ a b q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) (hsum : a+b+q ≤ 1)
    (hc : t^2 ≤ c) (hw : c-t^2 ≤ ‖w‖^2)
    (hdiag : L-c-2*t^2 ≤ ‖u‖^2+‖v‖^2-‖w‖^2)
    (hwu : ⟪w,u⟫ ≤ 0) (hwv : ⟪w,v⟫ ≤ 0)
    (hrow : -⟪w,u⟫-⟪w,v⟫ ≤ ‖w‖^2)
    (hpair₁ : ‖w‖^2*‖u‖^2-⟪w,u⟫^2 ≤ κ^2*t^2*(1+q)^2*(1+a)^2)
    (hpair₂ : ‖w‖^2*‖v‖^2-⟪w,v⟫^2 ≤ κ^2*t^2*(1+q)^2*(1+b)^2) :
    (c-t^2)*(L-c-2*t^2) ≤ 8*κ^2*t^2 := by
  have hlower : (c-t^2)*(L-c-2*t^2) ≤
      (‖w‖^2*‖u‖^2-⟪w,u⟫^2)+(‖w‖^2*‖v‖^2-⟪w,v⟫^2) := by
    by_cases hsign : 0 ≤ L-c-2*t^2
    · exact (mul_le_mul hw hdiag hsign (sq_nonneg ‖w‖)).trans
        (row_determinants_lower hwu hwv hrow)
    · exact (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hc) (le_of_not_ge hsign)).trans
        (add_nonneg (gram_det_nonneg w u) (gram_det_nonneg w v))
  have hu := mul_le_mul_of_nonneg_left (pair_factor_le_eight ha hb hq hsum)
    (mul_nonneg (sq_nonneg κ) (sq_nonneg t))
  nlinarith only [hlower, hpair₁, hpair₂, hu]

lemma second_constraint_of_pair_bounds (u v w : E)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) {t c κ a b q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) (hsum : a+b+q ≤ 1)
    (hc : t^2 ≤ c) (hsu : c-t^2 ≤ ‖u‖^2) (hsv : c-t^2 ≤ ‖v‖^2)
    (hsw : c-t^2 ≤ ‖w‖^2) (huv : ⟪u,v⟫ ≤ 0) (huw : ⟪u,w⟫ ≤ 0) (hvw : ⟪v,w⟫ ≤ 0)
    (hpair₁ : ‖u‖^2*‖v‖^2-⟪u,v⟫^2 ≤ κ^2*t^2*(1+a)^2*(1+b)^2)
    (hpair₂ : ‖u‖^2*‖w‖^2-⟪u,w⟫^2 ≤ κ^2*t^2*(1+a)^2*(1+q)^2)
    (hpair₃ : ‖v‖^2*‖w‖^2-⟪v,w⟫^2 ≤ κ^2*t^2*(1+b)^2*(1+q)^2) :
    (3/2:ℝ)*(c-t^2)^2 ≤ 10*κ^2*t^2 := by
  have hlow := three_gram_determinants_lower u v w hu hv hw huv huw hvw
    (sub_nonneg.mpr hc) hsu hsv hsw
  have hup := mul_le_mul_of_nonneg_left (triple_factor_le_ten ha hb hq hsum)
    (mul_nonneg (sq_nonneg κ) (sq_nonneg t))
  nlinarith only [hlow, hpair₁, hpair₂, hpair₃, hup]

end InnerProduct

end GaussianPropeller.Geometry

end OAI
