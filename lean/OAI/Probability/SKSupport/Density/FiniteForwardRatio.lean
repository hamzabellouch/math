import Mathlib
import OAI.Probability.SKSupport.Backward.GaussianBackwardShapes
import OAI.Probability.SKSupport.Density.Certificate
import OAI.Probability.SKSupport.Density.RatioComparison

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def backwardSegment (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N i : ℕ) (t x : ℝ) :=
  gaussianBurgers (c i) (backwardBoundary c h f N (i+1)) ((h:ℝ)-t) x

lemma backwardSegment_initial {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) {N i : ℕ} (hi : i < N) :
    backwardSegment c h f N i 0=fun x => (c i:ℝ)*deriv (backwardBoundary c h f N i) x := by
  have hn : N-i=(N-(i+1))+1 := by omega
  have hφ := (cascade_regular hf hLip c h (N-(i+1)) (i+1)).smooth.continuous.measurable
  have he : varianceLogHeat (c i) (h:ℝ) (backwardBoundary c h f N (i+1)) =
      backwardBoundary c h f N i := by
    funext x
    unfold backwardBoundary
    rw [varianceLogHeat_eq_logSemigroup_toNNReal hφ,Real.toNNReal_coe]
    simp only [hn,cascade]
  change (fun x => (c i:ℝ)*deriv (varianceLogHeat (c i) ((h:ℝ)-0) (backwardBoundary c h f N (i+1))) x)=_
  rw [sub_zero,he]

lemma backwardSegment_terminal (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N i : ℕ) :
    backwardSegment c h f N i h=fun x => (c i:ℝ)*deriv (backwardBoundary c h f N (i+1)) x := by
  change (fun x => (c i:ℝ)*deriv (varianceLogHeat (c i) ((h:ℝ)-h) (backwardBoundary c h f N (i+1))) x)=_
  have he : varianceLogHeat (c i) 0 (backwardBoundary c h f N (i+1))=backwardBoundary c h f N (i+1) := by
    funext x
    simpa only [backward,sub_self] using backward_terminal (c i) (h:ℝ) (backwardBoundary c h f N (i+1)) x
  rw [sub_self,he]

lemma backwardSegment_reverse {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) : ReverseBurgers (backwardSegment c h f N i) h :=
  (gaussianBurgers_smooth (cascade_regular hf hLip c h _ _)
    (cascade_lipschitz hLip c h _ _) (c i).coe_nonneg).reverse h.coe_nonneg

lemma backwardSegment_shape {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    (h : ℝ≥0) (N i : ℕ) {t : ℝ} (ht : t ≤ h) :
    BackwardShape (backwardSegment c h (softAbs M) N i t) := by
  have hh := finiteHead_backward_shape c hc hmono hM h (N-(i+1)) i t ht
  rw [finiteValue_head _ c h _ i ht] at hh
  exact hh

def boundaryRatio (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N i : ℕ) (x : ℝ) :=
  ratioWronskian (fun _ y => (c i:ℝ)*deriv (backwardBoundary c h f N i) y)
    (fun _ => datumScore ((i:ℝ)*h) (forwardBoundary c h f N i)) 0 x

lemma forwardSegment_ratio {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    {h : ℝ≥0} (hh : 0 < (h:ℝ)) {N i : ℕ} (hi0 : 0 < i) (hiN : i < N)
    (hi : ∀ x, 0 ≤ x → 0 ≤ boundaryRatio c h (softAbs M) N i x)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) h) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ ratioWronskian (backwardSegment c h (softAbs M) N i)
      (forwardScore ((i:ℝ)*h) (forwardBoundary c h (softAbs M) N i)) t x := by
  have hp := (hc 0).trans_le (hM 0)
  have hf := regularDatum_softAbs (ne_of_gt hp)
  have hLip := softAbs_lipschitz (ne_of_gt hp)
  have hL := forwardBoundary_regular hf hLip c hh N i
  obtain ⟨K,hK⟩ := hL.exists_lipschitz
  have ha := mul_pos (Nat.cast_pos.mpr hi0) hh
  have hshape := forwardBoundary_shape c hc hmono hM hh N i
  have hs := forwardScore_smooth ha hL hK
  apply (backwardSegment_reverse hf hLip c h N i).ratio_nonneg hs
    (fun τ hτ => backwardSegment_shape c hc hmono hM h N i hτ.2)
    (forwardScore_odd hL hK hshape.even) (fun τ hτ y => ?_) (fun τ hτ y hy => ?_)
    (fun y hy => ?_) ht x hx
  · rw [forwardScore_deriv hL hK]
    have h₂ := (forwardCorrection_shape ha hL hK hshape hτ).second y
    have hb := inv_pos.mpr (forwardTime_pos ha τ)
    linarith
  · rw [forwardScore_second hL hK]
    exact neg_nonpos.mpr ((forwardCorrection_shape ha hL hK hshape hτ).third y hy)
  · have hh := hi y hy
    change 0 ≤ (backwardSegment c h (softAbs M) N i 0 y)*
      deriv (forwardScore ((i:ℝ)*h) (forwardBoundary c h (softAbs M) N i) 0) y-
      forwardScore ((i:ℝ)*h) (forwardBoundary c h (softAbs M) N i) 0 y*
      deriv (backwardSegment c h (softAbs M) N i 0) y
    rw [backwardSegment_initial hf hLip c h hiN,forwardScore_initial (ne_of_gt ha)]
    exact hh

theorem boundaryRatio_nonneg {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    {h : ℝ≥0} (hh : 0 < (h:ℝ)) (N i : ℕ) (hi0 : 0 < i) (hiN : i ≤ N) :
    ∀ x, 0 ≤ x → 0 ≤ boundaryRatio c h (softAbs M) N i x := by
  have hp := (hc 0).trans_le (hM 0)
  have hf := regularDatum_softAbs (ne_of_gt hp)
  have hLip := softAbs_lipschitz (ne_of_gt hp)
  induction i with
  | zero => omega
  | succ i ih =>
    intro x hx
    by_cases hi : i=0
    · subst i
      have hφ := (cascade_regular hf hLip c h (N-1) 1).smooth
      have hs := backwardBoundary_shape c hc hmono hM h N 1
      simpa only [boundaryRatio,forwardBoundary,ite_true,Nat.zero_add,Nat.cast_one,one_mul,backwardBoundary] using
        ratioWronskian_first_jump hφ hh (hc 0) (hc 1) (C := -(1/2:ℝ)*Real.log (2*Real.pi*(h:ℝ))-
          (c 0:ℝ)*backwardBoundary c h (softAbs M) N 0 0) hs hx
    · have hi0' : 0 < i := Nat.pos_of_ne_zero hi
      have hiN' : i < N := by omega
      have hprev := forwardSegment_ratio c hc hmono hM hh hi0' hiN'
        (ih hi0' hiN'.le) (t := (h:ℝ)) ⟨h.coe_nonneg,le_rfl⟩ x hx
      have hφ : ContDiff ℝ ∞ (backwardBoundary c h (softAbs M) N (i+1)) :=
        (cascade_regular hf hLip c h (N-(i+1)) (i+1)).smooth
      have hL := forwardBoundary_regular hf hLip c hh N i
      obtain ⟨K,hK⟩ := hL.exists_lipschitz
      have he : ((i+1:ℕ):ℝ)*(h:ℝ)=(i:ℝ)*h+h := by push_cast;ring
      change 0 ≤ ratioWronskian (fun _ => backwardSegment c h (softAbs M) N i h)
        (fun _ => forwardScore ((i:ℝ)*h) (forwardBoundary c h (softAbs M) N i) h) 0 x at hprev
      rw [forwardScore_eq_datumScore h.coe_nonneg,backwardSegment_terminal] at hprev
      dsimp only [boundaryRatio]
      simp only [forwardBoundary,ite_eq_right hi,he]
      rw [ratioWronskian_jump (forwardCorrection_smooth hL hK h) hφ _ _ _ _ (ne_of_gt (hc i))]
      exact mul_nonneg (div_nonneg (hc (i+1)).le (hc i).le) hprev

theorem finite_forward_ratio {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    {h : ℝ≥0} (hh : 0 < (h:ℝ)) {N i : ℕ} (hi0 : 0 < i) (hiN : i < N)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) h) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ ratioWronskian (backwardSegment c h (softAbs M) N i)
      (forwardScore ((i:ℝ)*h) (forwardBoundary c h (softAbs M) N i)) t x :=
  forwardSegment_ratio c hc hmono hM hh hi0 hiN
    (boundaryRatio_nonneg c hc hmono hM hh N i hi0 hiN.le) ht x hx

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def certR (r : ℝ → ℝ) (x : ℝ) := (r x)^2
def certK (r s : ℝ → ℝ) (x : ℝ) := r x*s x
def certV (r : ℝ → ℝ) := deriv r
def certW (r : ℝ → ℝ) := iteratedDeriv 2 r
def certZ (r : ℝ → ℝ) := iteratedDeriv 3 r
def certB (r : ℝ → ℝ) (x : ℝ) := -certW r x/r x
def certJ (r s : ℝ → ℝ) (x : ℝ) := deriv s x-(s x/r x)*certV r x
def certL (r s : ℝ → ℝ) (x : ℝ) := -r x*iteratedDeriv 2 s x

def certFlux (r s ρ : ℝ → ℝ) (x : ℝ) :=
  r x*Certificate.F₂ (certR r x) (certK r s x) (certV r x) (certB r x) (certJ r s x)*ρ x

def certDivergence (r s ρ : ℝ → ℝ) (x : ℝ) :=
  ρ x*Certificate.WF₂ (certR r x) (certK r s x) (certV r x) (certB r x) (certJ r s x)
    (certZ r x) (certL r s x)

lemma cert_flux_derivative {r s ρ : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s)
    {x : ℝ} (hne : r x ≠ 0) (hρ : HasDerivAt ρ ((r x-s x)*ρ x) x) :
    HasDerivAt (certFlux r s ρ) (certDivergence r s ρ x) x := by
  have hr' : HasDerivAt r (certV r x) x := (hr.differentiable (by simp) x).hasDerivAt
  have hv : HasDerivAt (certV r) (certW r x) x := by simpa only [iteratedDeriv_one,certV,certW] using hasDerivAt_spatialJet hr 1 x
  have hw : HasDerivAt (certW r) (certZ r x) x := hasDerivAt_spatialJet hr 2 x
  have hs' : HasDerivAt s (deriv s x) x := (hs.differentiable (by simp) x).hasDerivAt
  have hs'' : HasDerivAt (deriv s) (iteratedDeriv 2 s x) x := by simpa only [iteratedDeriv_one] using hasDerivAt_spatialJet hs 1 x
  apply Certificate.hasDerivAt_flux hr' hρ (hr'.pow 2) (hr'.mul hs') hv
    (hw.neg.div hr' hne) (hs''.sub (((hs'.div hr' hne).mul hv))) rfl rfl
  · simp only [Pi.pow_apply];ring
  · dsimp [certK,certR,certJ]
    field_simp [hne]
    ring
  · dsimp [certR,certB]
    field_simp [hne]
  · dsimp [certB]
    field_simp [hne]
  · dsimp [certJ,certK,certB,certL]
    field_simp [hne]
    ring

lemma cert_halfLine_signs {r s : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s)
    (hshape : BackwardShape r) (hso : Function.Odd s) (hsa : ∀ x, 0 ≤ deriv s x)
    (hsw : ∀ x, 0 ≤ x → iteratedDeriv 2 s x ≤ 0)
    (hQ : ∀ x, 0 ≤ x → 0 ≤ r x*deriv s x-s x*deriv r x)
    {x : ℝ} (hx : 0 < x) :
    0 ≤ certR r x ∧ 0 ≤ certK r s x ∧ 0 ≤ certV r x ∧ 0 ≤ certJ r s x ∧
    0 ≤ certB r x-2*certV r x ∧ 0 ≤ certL r s x ∧
    0 ≤ certZ r x+certB r x*certV r x-2*certR r x*certB r x := by
  have hp := hshape.pos hx
  have hn := ne_of_gt hp
  have hs0 : s 0=0 := by have hh := hso 0;simp only [neg_zero] at hh;linarith
  have hsp : 0 ≤ s x := by
    simpa only [hs0] using (monotone_of_deriv_nonneg (hs.differentiable (by simp)) hsa hx.le)
  refine ⟨sq_nonneg _,mul_nonneg hp.le hsp,(hshape.derivative_pos x).le,?_,?_,?_,?_⟩
  · have he : certJ r s x=(r x*deriv s x-s x*deriv r x)/r x := by
      dsimp [certJ,certV]
      field_simp
    rw [he]
    exact div_nonneg (hQ x hx.le) hp.le
  · have he : certB r x-2*certV r x= -2*burgersRate (fun _ => r) 0 x/r x := by
      dsimp [certB,certW,certV,burgersRate]
      field_simp [hn]
      ring
    rw [he]
    exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by norm_num) (hshape.rate_nonpos x hx.le)) hp.le
  · exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hp.le) (hsw x hx.le)
  · have he : certZ r x+certB r x*certV r x-2*certR r x*certB r x=
        2*backwardWronskian (fun _ => r) 0 x/r x := by
      rw [backwardWronskian,burgersRate_spatial_deriv hr]
      dsimp [certZ,certB,certW,certV,certR,burgersRate]
      field_simp [hn]
      ring
    rw [he]
    exact div_nonneg (mul_nonneg (by norm_num) (hshape.wronskian_nonneg x hx.le)) hp.le

lemma cert_halfLine_coercive {r s : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s)
    (hshape : BackwardShape r) (hso : Function.Odd s) (hsa : ∀ x, 0 ≤ deriv s x)
    (hsw : ∀ x, 0 ≤ x → iteratedDeriv 2 s x ≤ 0)
    (hQ : ∀ x, 0 ≤ x → 0 ≤ r x*deriv s x-s x*deriv r x)
    {x : ℝ} (hx : 0 < x) :
    (1661507/1521000000:ℝ)*(certV r x)^4+
      Certificate.WF₂ (certR r x) (certK r s x) (certV r x) (certB r x) (certJ r s x)
        (certZ r x) (certL r s x) ≤
      (certZ r x)^2-12*certV r x*(certW r x)^2+6*(certV r x)^4 := by
  obtain ⟨hR,hK,hv,hj,hB,hL,hS⟩ := cert_halfLine_signs hr hs hshape hso hsa hsw hQ hx
  have he : certR r x*(certB r x)^2=(certW r x)^2 := by
    dsimp [certR,certB]
    field_simp [ne_of_gt (hshape.pos hx)]
  have hh := Certificate.pointwise_coercivity hR hK hv hj hB hL hS
  rw [show 12*certR r x*certV r x*(certB r x)^2=12*certV r x*(certR r x*(certB r x)^2) by ring,he] at hh
  exact hh

end ZeroTemperatureSK.Heat

end
end

end OAI
