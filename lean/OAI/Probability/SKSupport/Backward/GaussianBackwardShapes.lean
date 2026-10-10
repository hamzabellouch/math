import Mathlib
import OAI.Probability.SKSupport.Regularity.Regularity
import OAI.Probability.SKSupport.Moments.FiniteStrictConvex
import OAI.Probability.SKSupport.Parabolic.ForwardSigns
import OAI.Probability.SKSupport.Backward.BackwardRescale
import OAI.Probability.SKSupport.Diffusion.TerminalShapes

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

theorem gaussianBurgers_shape {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (he : Function.Even f)
    (hcurv : ∀ x, 0 < deriv (deriv f) x) {c : ℝ} (hc : 0 < c)
    (hi : BackwardShape (fun x => c*deriv f x))
    {t : ℝ} (ht : 0 ≤ t) : BackwardShape (gaussianBurgers c f t) := by
  have hr := gaussianBurgers_smooth hf hLip hc.le
  have ho := gaussianBurgers_odd hf hLip he hc.le
  have hz := gaussianBurgers_terminal (f := f) c
  have hiv : BackwardShape (gaussianBurgers c f 0) := by rw [hz]; exact hi
  have hv (s : ℝ) (_hs : 0 ≤ s) (x : ℝ) : 0 < deriv (gaussianBurgers c f s) x := by
    have hj := gaussianBurgers_jet hf hLip hc.le 1 s x
    simp only [iteratedDeriv_one] at hj
    rw [hj]
    exact mul_pos hc (by simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      varianceLogHeat_curvature_pos hf hLip hcurv hc.le s x)
  refine ⟨ho t,hv t ht,?_,?_,?_⟩
  · exact hr.second_nonpos ho hiv.second_nonpos t ht
  · exact hr.rate_nonpos ho hiv.rate_nonpos t ht
  · exact hr.wronskian_nonneg ho hv hiv.second_nonpos hiv.rate_nonpos hiv.wronskian_nonneg t ht

theorem logSemigroup_backward_shape {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (he : Function.Even f)
    (hcurv : ∀ x, 0 < deriv (deriv f) x) {c : ℝ} (hc : 0 < c)
    (hi : BackwardShape (fun x => c*deriv f x)) (h : ℝ≥0) :
    BackwardShape (fun x => c*deriv (logSemigroup c h f) x) := by
  have hh := gaussianBurgers_shape hf hLip he hcurv hc hi h.coe_nonneg
  have heq : varianceLogHeat c h f = logSemigroup c h f :=
    funext (varianceLogHeat_eq_logSemigroup hf.smooth.continuous.measurable c h)
  have heq' : gaussianBurgers c f h = fun x => c*deriv (logSemigroup c h f) x := by
    funext x
    rw [gaussianBurgers,heq]
  rwa [heq'] at hh

lemma softAbs_backward_shape {M c : ℝ} (hc : 0 < c) (hM : c ≤ M) :
    BackwardShape (fun x => c*deriv (softAbs M) x) := by
  have hMp := hc.trans_le hM
  have he : (fun x => c*deriv (softAbs M) x) = tanhDrift c M := by
    funext x
    rw [(hasDerivAt_softAbs (ne_of_gt hMp) x).deriv]
    rfl
  rw [he]
  refine ⟨?_,?_,fun x hx => (tanhDrift_initial_signs hc hM x hx).1,
    fun x hx => (tanhDrift_initial_signs hc hM x hx).2.1,
    fun x hx => (tanhDrift_initial_signs hc hM x hx).2.2⟩
  · intro x
    simp only [tanhDrift,mul_neg,Real.tanh_neg]
  · intro x
    rw [(tanhDrift_derivative c M x).deriv]
    exact mul_pos (mul_pos hc hMp) (tanh_sq_gap_pos (M*x))

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

theorem cascade_backward_shape {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    (h : ℝ≥0) (N i : ℕ) :
    BackwardShape (fun x => (c i:ℝ)*deriv (cascade c h (softAbs M) N i) x) := by
  have hMp : 0 < M := (hc 0).trans_le (hM 0)
  have hf := regularDatum_softAbs (ne_of_gt hMp)
  have hLip := softAbs_lipschitz (ne_of_gt hMp)
  induction N generalizing i with
  | zero => exact softAbs_backward_shape (hc i) (hM i)
  | succ N ih =>
    have hdatum := cascade_regular hf hLip c h N (i+1)
    have hsmooth : ContDiff ℝ ∞ (fun x => (c (i+1):ℝ)*deriv (cascade c h (softAbs M) N (i+1)) x) :=
      contDiff_const.mul hdatum.deriv_bounded.smooth
    have hir := BackwardShape.rescale hsmooth (ih (i+1))
      (div_pos (hc i) (hc (i+1)))
      ((div_le_one (hc (i+1))).mpr (show (c i:ℝ) ≤ c (i+1) from hmono (Nat.le_succ i)))
    have he : (fun x => ((c i:ℝ)/(c (i+1):ℝ))*
        ((c (i+1):ℝ)*deriv (cascade c h (softAbs M) N (i+1)) x)) =
        fun x => (c i:ℝ)*deriv (cascade c h (softAbs M) N (i+1)) x := by
      funext x
      field_simp [ne_of_gt (hc (i+1))]
    rw [he] at hir
    exact logSemigroup_backward_shape hdatum (cascade_lipschitz hLip c h N (i+1))
      (cascade_even hf hLip (softAbs_even M) c h N (i+1))
      (cascade_curvature_pos hf hLip (softAbs_curvature_pos hMp) c h N (i+1))
      (hc i) hir h

theorem finiteHead_backward_shape {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    (h : ℝ≥0) (N i : ℕ) (t : ℝ) (ht : t ≤ h) :
    BackwardShape (fun x => (c i:ℝ)*deriv (finiteValue c h (softAbs M) (N+1) i t) x) := by
  have hMp : 0 < M := (hc 0).trans_le (hM 0)
  have hf := regularDatum_softAbs (ne_of_gt hMp)
  have hLip := softAbs_lipschitz (ne_of_gt hMp)
  have hdatum := cascade_regular hf hLip c h N (i+1)
  have hsmooth : ContDiff ℝ ∞ (fun x => (c (i+1):ℝ)*deriv (cascade c h (softAbs M) N (i+1)) x) :=
    contDiff_const.mul hdatum.deriv_bounded.smooth
  have hir := BackwardShape.rescale hsmooth (cascade_backward_shape c hc hmono hM h N (i+1))
    (div_pos (hc i) (hc (i+1)))
    ((div_le_one (hc (i+1))).mpr (show (c i:ℝ) ≤ c (i+1) from hmono (Nat.le_succ i)))
  have he : (fun x => ((c i:ℝ)/(c (i+1):ℝ))*
      ((c (i+1):ℝ)*deriv (cascade c h (softAbs M) N (i+1)) x)) =
      fun x => (c i:ℝ)*deriv (cascade c h (softAbs M) N (i+1)) x := by
    funext x
    field_simp [ne_of_gt (hc (i+1))]
  rw [he] at hir
  have hh := gaussianBurgers_shape hdatum (cascade_lipschitz hLip c h N (i+1))
    (cascade_even hf hLip (softAbs_even M) c h N (i+1))
    (cascade_curvature_pos hf hLip (softAbs_curvature_pos hMp) c h N (i+1))
    (hc i) hir (sub_nonneg.mpr ht)
  have heq : (fun x => (c i:ℝ)*deriv (finiteValue c h (softAbs M) (N+1) i t) x) =
      gaussianBurgers (c i) (cascade c h (softAbs M) N (i+1)) ((h:ℝ)-t) := by
    rw [finiteValue_head _ c h N i ht]
    rfl
  rwa [heq]

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma RegularDatum.exists_lipschitz {f : ℝ → ℝ} (hf : RegularDatum f) :
    ∃ K : ℝ≥0, LipschitzWith K f := by
  obtain ⟨K,hK⟩ := hf.deriv_bounded.bound
  exact ⟨K,lipschitzWith_of_nnnorm_deriv_le (hf.smooth.differentiable (by simp))
    (fun x => NNReal.coe_le_coe.mp (by simpa only [coe_nnnorm,Real.norm_eq_abs] using hK x))⟩

lemma RegularDatum.sub_mul {f g : ℝ → ℝ} (hf : RegularDatum f) (hg : RegularDatum g) (δ : ℝ) :
    RegularDatum (fun x => f x-δ*g x) := by
  refine ⟨hf.smooth.sub (contDiff_const.mul hg.smooth),?_⟩
  have he : deriv (fun x => f x-δ*g x)=fun x => deriv f x+(-δ)*deriv g x := by
    funext x
    convert (((hf.smooth.differentiable (by simp)) x).hasDerivAt.sub
      (((hg.smooth.differentiable (by simp)) x).hasDerivAt.const_mul δ)).deriv using 1
    first | rfl | ring
  rw [he]
  exact hf.deriv_bounded.add (hg.deriv_bounded.const_mul (-δ))

def backwardBoundary (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N i : ℕ) : ℝ → ℝ :=
  cascade c h f (N-i) i

def forwardBoundary (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N : ℕ) : ℕ → ℝ → ℝ
  | 0 => fun _ => -(c 0:ℝ)*backwardBoundary c h f N 0 0
  | i+1 => fun x => (if i=0 then
      -(1/2:ℝ)*Real.log (2*Real.pi*(h:ℝ))-(c 0:ℝ)*backwardBoundary c h f N 0 0
      else forwardCorrection ((i:ℝ)*h) (forwardBoundary c h f N i) h x)-
      ((c (i+1):ℝ)-(c i:ℝ))*backwardBoundary c h f N (i+1) x

lemma forwardBoundary_regular {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) {h : ℝ≥0} (hh : 0 < (h:ℝ)) (N i : ℕ) :
    RegularDatum (forwardBoundary c h f N i) := by
  induction i with
  | zero => exact RegularDatum.const _
  | succ i ih =>
    have hφ : RegularDatum (backwardBoundary c h f N (i+1)) := cascade_regular hf hLip c h _ _
    rw [forwardBoundary]
    by_cases hi : i=0
    · subst i
      simp only [ite_true]
      exact (RegularDatum.const _).sub_mul hφ _
    · simp only [hi,ite_false]
      obtain ⟨K,hK⟩ := ih.exists_lipschitz
      exact (forwardCorrection_regular (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hi)) hh) ih hK h).sub_mul hφ _

lemma backwardBoundary_shape {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    (h : ℝ≥0) (N i : ℕ) :
    BackwardShape (fun x => (c i:ℝ)*deriv (backwardBoundary c h (softAbs M) N i) x) :=
  cascade_backward_shape c hc hmono hM h _ _

lemma backwardBoundary_third_nonpos {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    (h : ℝ≥0) (N i : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    iteratedDeriv 3 (backwardBoundary c h (softAbs M) N i) x ≤ 0 := by
  have hp := (hc 0).trans_le (hM 0)
  have hf : RegularDatum (backwardBoundary c h (softAbs M) N i) :=
    cascade_regular (regularDatum_softAbs (ne_of_gt hp)) (softAbs_lipschitz (ne_of_gt hp)) c h _ _
  have hh := (backwardBoundary_shape c hc hmono hM h N i).second_nonpos x hx
  rw [iteratedDeriv_const_mul_field,← iteratedDeriv_succ'] at hh
  exact nonpos_of_mul_nonpos_right hh (hc i)

lemma forwardBoundary_shape {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    {h : ℝ≥0} (hh : 0 < (h:ℝ)) (N i : ℕ) :
    ForwardDatumShape (forwardBoundary c h (softAbs M) N i) := by
  have hp := (hc 0).trans_le (hM 0)
  have hf := regularDatum_softAbs (ne_of_gt hp)
  have hLip := softAbs_lipschitz (ne_of_gt hp)
  induction i with
  | zero => exact ForwardDatumShape.const _
  | succ i ih =>
    have hφ : RegularDatum (backwardBoundary c h (softAbs M) N (i+1)) := cascade_regular hf hLip c h _ _
    have heφ := cascade_even hf hLip (softAbs_even M) c h (N-(i+1)) (i+1)
    have hv : ∀ x, 0 ≤ iteratedDeriv 2 (backwardBoundary c h (softAbs M) N (i+1)) x := by
      intro x
      simpa only [backwardBoundary,iteratedDeriv_succ,iteratedDeriv_zero] using
        (cascade_curvature_pos hf hLip (softAbs_curvature_pos hp) c h (N-(i+1)) (i+1) x).le
    have hw := backwardBoundary_third_nonpos c hc hmono hM h N (i+1)
    have hδ : 0 ≤ (c (i+1):ℝ)-(c i:ℝ) := sub_nonneg.mpr (hmono (Nat.le_succ i))
    rw [forwardBoundary]
    by_cases hi : i=0
    · subst i
      simp only [ite_true]
      exact ForwardDatumShape.jump contDiff_const hφ.smooth (ForwardDatumShape.const _) heφ hv hw hδ
    · simp only [hi,ite_false]
      have hr := forwardBoundary_regular hf hLip c hh N i
      obtain ⟨K,hK⟩ := hr.exists_lipschitz
      have ha := mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hi)) hh
      exact ForwardDatumShape.jump (forwardCorrection_smooth hr hK h) hφ.smooth
        (forwardCorrection_shape ha hr hK ih h.coe_nonneg) heφ hv hw hδ

end ZeroTemperatureSK.Heat

end
end

end OAI
