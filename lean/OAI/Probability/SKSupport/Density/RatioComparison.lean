import Mathlib
import OAI.Probability.SKSupport.Backward.BackwardRescale
import OAI.Probability.SKSupport.Parabolic.ReverseBurgers

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma BackwardShape.zero {r : ℝ → ℝ} (hr : BackwardShape r) : r 0=0 := by
  have hh := hr.odd 0
  simp only [neg_zero] at hh
  linarith

lemma BackwardShape.pos {r : ℝ → ℝ} (hr : BackwardShape r) {x : ℝ} (hx : 0 < x) :
    0 < r x := by
  simpa only [hr.zero] using strictMono_of_deriv_pos hr.derivative_pos hx

theorem ReverseBurgers.ratio_nonneg_interior {r s : ℝ → ℝ → ℝ} {H : ℝ}
    (hr : ReverseBurgers r H) (hs : SmoothForward s)
    (hshape : ∀ t ∈ Icc (0:ℝ) H, BackwardShape (r t))
    (hso : ∀ t, Function.Odd (s t))
    (hsa : ∀ t, 0 ≤ t → ∀ x, 0 ≤ deriv (s t) x)
    (hsw : ∀ t, 0 ≤ t → ∀ x, 0 ≤ x → iteratedDeriv 2 (s t) x ≤ 0)
    (hi : ∀ x, 0 ≤ x → 0 ≤ ratioWronskian r s 0 x)
    {T : ℝ} (hT : 0 ≤ T) (hTH : T < H) :
    ∀ x, 0 ≤ x → 0 ≤ ratioWronskian r s T x := by
  obtain ⟨R,hR⟩ := hr.family.bound
  obtain ⟨V,hV⟩ := hr.family.deriv.bound
  obtain ⟨A,hA⟩ := hs.deriv_family.bound
  obtain ⟨C,hC,hCs⟩ := hs.family.bound
  have hsz (t : ℝ) : s t 0=0 := by
    have hh := hso t 0
    simp only [neg_zero] at hh
    linarith
  have hsp (t : ℝ) (ht : 0 ≤ t) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ s t x := by
    have hm := monotone_of_deriv_nonneg ((hs.family.smooth t).differentiable (by simp)) (hsa t ht)
    simpa only [hsz] using hm hx
  have hlow (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) (x : ℝ) (hx : 0 ≤ x) :
      -((R:ℝ)*A+C*((V:ℝ)+R)) ≤ ratioWronskian r s t x := by
    have hrsh := hshape t ⟨ht.1,ht.2.trans hTH.le⟩
    have hv : 0 ≤ deriv (r t) x := (hrsh.derivative_pos x).le
    have hvb : deriv (r t) x ≤ V := (le_abs_self _).trans (hV t x)
    have htangent := tangent_bound_of_concave_odd (hr.family.regular t).smooth hrsh.zero
      (fun _ hy => hrsh.second_nonpos _ hy.le) hx
    have hrb : r t x ≤ R := (le_abs_self _).trans (hR t x)
    have hsb : s t x ≤ C*(1+x) := by
      simpa only [abs_of_nonneg hx] using (le_abs_self _).trans (hCs t x)
    have hp1 : -((R:ℝ)*A) ≤ r t x*deriv (s t) x := by
      have hh := mul_le_mul (hR t x) (hA t x) (abs_nonneg _) R.coe_nonneg
      rw [← abs_mul] at hh
      exact (neg_le_neg hh).trans (neg_abs_le _)
    have hp2 : s t x*deriv (r t) x ≤ C*((V:ℝ)+R) := by
      have hh := mul_le_mul_of_nonneg_right hsb hv
      have hh₂ := mul_le_mul_of_nonneg_left (show (1+x)*deriv (r t) x ≤ (V:ℝ)+R by nlinarith) hC
      nlinarith
    dsimp [ratioWronskian]
    linarith
  intro x hx
  apply Parabolic.nonnegative_halfLine_bounded
    (u := ratioWronskian r s) (ut := ratioWronskianRate r s)
    (ux := fun t => deriv (ratioWronskian r s t))
    (uxx := fun t => iteratedDeriv 2 (ratioWronskian r s t))
    (β := fun t x => -(deriv (r t) x/r t x))
    (c := fun t x => -(deriv (r t) x+deriv (s t) x)) (C := 0) (K := 0)
    (M := (R:ℝ)*A+C*((V:ℝ)+R)) (by norm_num) (by positivity)
    ((hr.ratio_continuous hs).mono (by intro p hp;exact ⟨⟨hp.1.1,hp.1.2.trans hTH.le⟩,mem_univ _⟩))
    (fun t _ => (((hr.family.regular t).smooth.continuous.mul (hs.deriv_family.regular t).smooth.continuous).sub
      ((hs.family.smooth t).continuous.mul (hr.family.deriv.regular t).smooth.continuous)))
    (fun t ht x _ => (hr.ratio_time hs ht.1 (ht.2.trans_lt hTH) x).hasDerivWithinAt)
    (fun t _ x _ => by
      rw [(ratioWronskian_spatial (hr.family.regular t).smooth (hs.family.smooth t) x).deriv]
      exact ratioWronskian_spatial (hr.family.regular t).smooth (hs.family.smooth t) x)
    (fun t _ x _ => by
      convert ratioWronskian_second (hr.family.regular t).smooth (hs.family.smooth t) x using 1
      rw [iteratedDeriv_succ,iteratedDeriv_one,
        (ratioWronskian_second (hr.family.regular t).smooth (hs.family.smooth t) x).deriv])
    (fun t ht x hx => ?_) (fun t ht x _ => ?_) (fun t ht x hx => ?_)
    hlow hi (fun t ht => ?_) T ⟨hT,le_rfl⟩ x hx
  · have hrsh := hshape t ⟨ht.1.le,ht.2.trans hTH.le⟩
    simpa only [zero_mul] using mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (div_nonneg (hrsh.derivative_pos x).le (hrsh.pos hx).le)) hx.le
  · exact neg_nonpos.mpr (add_nonneg
      (hshape t ⟨ht.1.le,ht.2.trans hTH.le⟩ |>.derivative_pos x |>.le) (hsa t ht.1.le x))
  · have hrsh := hshape t ⟨ht.1.le,ht.2.trans hTH.le⟩
    have he := ratioWronskian_equation hs (hr.family.regular t).smooth x (ne_of_gt (hrsh.pos hx))
    have hk : 0 ≤ backwardWronskian r t x := hrsh.wronskian_nonneg x hx.le
    have hnon : 0 ≤ r t x*s t x*(2*backwardWronskian r t x/(r t x)^2-
        iteratedDeriv 2 (r t) x-iteratedDeriv 2 (s t) x) :=
      mul_nonneg (mul_nonneg (hrsh.pos hx).le (hsp t ht.1.le x hx.le))
        (by have hh := div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hk) (sq_nonneg (r t x))
            linarith [hrsh.second_nonpos x hx.le,hsw t ht.1.le x hx.le])
    convert he ▸ hnon using 1
    ring
  · dsimp [ratioWronskian]
    rw [(hshape t ⟨ht.1,ht.2.trans hTH.le⟩).zero,hsz]
    simp

theorem ReverseBurgers.ratio_nonneg {r s : ℝ → ℝ → ℝ} {H : ℝ}
    (hr : ReverseBurgers r H) (hs : SmoothForward s)
    (hshape : ∀ t ∈ Icc (0:ℝ) H, BackwardShape (r t))
    (hso : ∀ t, Function.Odd (s t))
    (hsa : ∀ t, 0 ≤ t → ∀ x, 0 ≤ deriv (s t) x)
    (hsw : ∀ t, 0 ≤ t → ∀ x, 0 ≤ x → iteratedDeriv 2 (s t) x ≤ 0)
    (hi : ∀ x, 0 ≤ x → 0 ≤ ratioWronskian r s 0 x)
    {T : ℝ} (hT : T ∈ Icc (0:ℝ) H) :
    ∀ x, 0 ≤ x → 0 ≤ ratioWronskian r s T x := by
  intro x hx
  by_cases hTH : T < H
  · exact hr.ratio_nonneg_interior hs hshape hso hsa hsw hi hT.1 hTH x hx
  have he : T=H := le_antisymm hT.2 (le_of_not_gt hTH)
  subst T
  by_cases hH : H=0
  · simpa only [hH] using hi x hx
  have hHp : 0 < H := lt_of_le_of_ne hT.1 (Ne.symm hH)
  have : NeBot (𝓝[Ico (0:ℝ) H] H) := right_nhdsWithin_Ico_neBot hHp
  have hc : ContinuousOn (fun t => ratioWronskian r s t x) (Icc (0:ℝ) H) :=
    (hr.ratio_continuous hs).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ ht => ⟨ht,mem_univ _⟩)
  apply ge_of_tendsto ((hc H ⟨hHp.le,le_rfl⟩).mono Ico_subset_Icc_self)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hr.ratio_nonneg_interior hs hshape hso hsa hsw hi ht.1 ht.2 x hx

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def datumScore (a : ℝ) (L : ℝ → ℝ) (x : ℝ) := x/a-deriv L x

lemma forwardScore_eq_datumScore {a : ℝ} {L : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    forwardScore a L t=datumScore (a+t) (forwardCorrection a L t) := by
  funext x
  simp only [forwardScore,datumScore,forwardTime,max_eq_left ht]

lemma forwardScore_initial {a : ℝ} (ha : a ≠ 0) (L : ℝ → ℝ) :
    forwardScore a L 0=datumScore a L := by
  rw [forwardScore_eq_datumScore le_rfl,add_zero,forwardCorrection_terminal a ha]

lemma datumScore_deriv {L : ℝ → ℝ} (hL : ContDiff ℝ ∞ L) (a x : ℝ) :
    deriv (datumScore a L) x=1/a-iteratedDeriv 2 L x := by
  have hh := ((hasDerivAt_id x).div_const a).sub (hasDerivAt_spatialJet hL 1 x)
  apply HasDerivAt.deriv
  convert hh using 1
  first | rfl | ((try funext y);simp only [datumScore,id_eq,iteratedDeriv_succ,iteratedDeriv_zero,Pi.sub_apply])

lemma datumScore_jump {L φ : ℝ → ℝ} (hL : ContDiff ℝ ∞ L) (hφ : ContDiff ℝ ∞ φ) (a δ : ℝ) :
    datumScore a (fun x => L x-δ*φ x)=fun x => datumScore a L x+δ*deriv φ x := by
  funext x
  have hd : deriv (fun x => L x-δ*φ x) x=deriv L x-δ*deriv φ x := by
    apply HasDerivAt.deriv
    convert (((hL.differentiable (by simp)) x).hasDerivAt.sub
      (((hφ.differentiable (by simp)) x).hasDerivAt.const_mul δ)) using 1
  rw [datumScore,hd]
  dsimp only [datumScore]
  ring

lemma ratioWronskian_jump {L φ : ℝ → ℝ} (hL : ContDiff ℝ ∞ L) (hφ : ContDiff ℝ ∞ φ)
    (a c d x : ℝ) (hc : c ≠ 0) :
    ratioWronskian (fun _ y => d*deriv φ y)
      (fun _ => datumScore a (fun y => L y-(d-c)*φ y)) 0 x =
    d/c*ratioWronskian (fun _ y => c*deriv φ y) (fun _ => datumScore a L) 0 x := by
  have hds : ContDiff ℝ ∞ (datumScore a L) :=
    (contDiff_id.div_const a).sub (contDiff_infty_iff_deriv.mp hL |>.2)
  rw [datumScore_jump hL hφ]
  have hder (k : ℝ) : deriv (fun y => k*deriv φ y) x=k*iteratedDeriv 2 φ x := by
    apply HasDerivAt.deriv
    convert (hasDerivAt_spatialJet hφ 1 x).const_mul k using 1
    first | rfl | simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  have hd : deriv (fun y => datumScore a L y+(d-c)*deriv φ y) x =
      deriv (datumScore a L) x+(d-c)*iteratedDeriv 2 φ x := by
    apply HasDerivAt.deriv
    convert ((hds.differentiable (by simp)) x).hasDerivAt.add
      ((hasDerivAt_spatialJet hφ 1 x).const_mul (d-c)) using 1
    first | rfl | ((try funext y);simp only [iteratedDeriv_succ,iteratedDeriv_zero,Pi.add_apply])
  dsimp only [ratioWronskian]
  rw [hd,hder,hder]
  field_simp [hc]
  ring

lemma ratioWronskian_first_jump {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {a c d C : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : 0 < d)
    (hshape : BackwardShape (fun x => d*deriv φ x)) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ ratioWronskian (fun _ y => d*deriv φ y)
      (fun _ => datumScore a (fun y => C-(d-c)*φ y)) 0 x := by
  rw [ratioWronskian_jump contDiff_const hφ a c d x (ne_of_gt hc)]
  have htan := tangent_bound_of_concave_odd
    (contDiff_const.mul (contDiff_infty_iff_deriv.mp hφ |>.2)) hshape.zero
    (fun y hy => hshape.second_nonpos y hy.le) hx
  have hv : deriv (fun y => d*deriv φ y) x=d*iteratedDeriv 2 φ x := by
    apply HasDerivAt.deriv
    convert (hasDerivAt_spatialJet hφ 1 x).const_mul d using 1
    first | rfl | simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  rw [hv] at htan
  have ht : 0 ≤ deriv φ x-x*iteratedDeriv 2 φ x := by nlinarith
  have he : ratioWronskian (fun _ y => c*deriv φ y)
      (fun _ => datumScore a (fun _ => C)) 0 x = c/a*(deriv φ x-x*iteratedDeriv 2 φ x) := by
    have hs : datumScore a (fun _ => C)=fun y => y/a := by
      funext y
      simp [datumScore]
    rw [hs]
    have hv' : deriv (fun y => c*deriv φ y) x=c*iteratedDeriv 2 φ x := by
      apply HasDerivAt.deriv
      convert (hasDerivAt_spatialJet hφ 1 x).const_mul c using 1
      first | rfl | simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    have hq : deriv (fun y : ℝ => y/a) x=1/a := by
      exact ((hasDerivAt_id x).div_const a).deriv
    dsimp only [ratioWronskian]
    rw [hv',hq]
    ring
  rw [he]
  exact mul_nonneg (div_nonneg hd.le hc.le) (mul_nonneg (div_nonneg hc.le ha.le) ht)

end ZeroTemperatureSK.Heat

end
end

end OAI
