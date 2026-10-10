import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.BoundedDegreeMonomials

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance gaussianDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance gaussianDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance gaussianFormNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance gaussianFormSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

lemma deriv_radial_line (F : E → ℝ) (hF : Differentiable ℝ F) (x : E) (t : ℝ) :
    deriv (fun s : ℝ => F (s • x)) t = fderiv ℝ F (t • x) x := by
  simpa only [Function.comp_def, id_eq, one_smul] using ((hF (t • x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const x)).deriv

lemma second_deriv_radial_line (F : E → ℝ) (hF : ContDiff ℝ 2 F) (x : E) (t : ℝ) :
    deriv (deriv (fun s : ℝ => F (s • x))) t =
      fderiv ℝ (fderiv ℝ F) (t • x) x x := by
  have hd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ F) := (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heq : deriv (fun s : ℝ => F (s • x)) = fun s => fderiv ℝ F (s • x) x :=
    funext (deriv_radial_line F hd x)
  rw [heq]
  exact (((hD (t • x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const x)).clm_apply (hasDerivAt_const t x)).deriv.trans (by simp)

lemma second_order_line_taylor (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) :
    ∃ t ∈ Ioo (0 : ℝ) 1, f 1 = f 0 + deriv f 0 + deriv (deriv f) t / 2 := by
  obtain ⟨t,ht,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1)
    (x₀ := 0) (x := 1) (by norm_num) hf.contDiffOn
  have hu : UniqueDiffOn ℝ (uIcc (0 : ℝ) 1) := uniqueDiffOn_uIcc (by norm_num)
  have hdf := (hf.differentiable (by norm_num) 0).derivWithin
    (hu 0 (by simp))
  have htw : taylorWithinEval f 1 (uIcc (0 : ℝ) 1) 0 1 = f 0 + deriv f 0 := by
    rw [show 1 = 0+1 from rfl, taylorWithinEval_succ]
    simp only [taylor_within_zero_eval, Nat.cast_zero, zero_add, Nat.factorial_zero,
      Nat.cast_one, inv_one, sub_zero, zero_add, pow_one, one_mul, one_smul]
    rw [iteratedDerivWithin_one, hdf]
  refine ⟨t, by simpa using ht, ?_⟩
  rw [htw] at he
  norm_num [iteratedDeriv_succ] at he
  linarith

lemma gaussian_of_hessian (F : E → ℝ) (hF : ContDiff ℝ 2 F)
    {r c δ : ℝ} (h0 : F 0 = 0)
    (h1 : ∀ x, fderiv ℝ F 0 x ≤ δ*‖x‖)
    (h2 : ∀ y ∈ Metric.ball (0 : E) r, ∀ v,
      fderiv ℝ (fderiv ℝ F) y v v ≤ -2*c*‖v‖^2)
    {x : E} (hx : x ∈ Metric.ball (0 : E) r) :
    F x ≤ δ*‖x‖-c*‖x‖^2 := by
  have hline : ContDiff ℝ 2 (fun t : ℝ => F (t • x)) :=
    hF.comp (contDiff_id.smul contDiff_const)
  obtain ⟨t,ht,he⟩ := second_order_line_taylor _ hline
  have htx : t • x ∈ Metric.ball (0 : E) r := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2.le).trans_lt
      (mem_ball_zero_iff.mp hx)
  rw [one_smul, zero_smul, h0, zero_add,
    deriv_radial_line F (hF.differentiable (by norm_num)), zero_smul,
    second_deriv_radial_line F hF] at he
  have hh := h2 (t • x) htx x
  have hl := h1 x
  linarith

omit [NormedSpace ℝ E] in
lemma compact_uniform_value_radius {X B : Type*} [TopologicalSpace X]
    [NormedAddCommGroup B] (H : X × E → B) (hH : Continuous H)
    {P : Set X} (hP : IsCompact P) {c : ℝ} (hc : 0 < c) :
    ∃ r > 0, ∀ p ∈ P, ∀ y ∈ Metric.ball (0 : E) r,
      ‖H (p,y) - H (p,0)‖ < c := by
  have hH0 : Continuous (fun q : X × E => H (q.1,0)) :=
    hH.comp (continuous_fst.prodMk continuous_const)
  have hopen : IsOpen {q : X × E | ‖H q - H (q.1,0)‖ < c} :=
    isOpen_lt (hH.sub hH0).norm continuous_const
  have hsub : P ×ˢ {(0 : E)} ⊆ {q : X × E | ‖H q - H (q.1,0)‖ < c} := by
    rintro ⟨p,y⟩ ⟨hp,hy⟩
    have hy0 : y = 0 := mem_singleton_iff.mp hy
    subst y
    change ‖H (p,0) - H (p,0)‖ < c
    simpa only [sub_self, norm_zero] using hc
  obtain ⟨u,v,hu,hv,hPu,h0v,huv⟩ := generalized_tube_lemma hP
    isCompact_singleton hopen hsub
  obtain ⟨r,hr,hrv⟩ := Metric.isOpen_iff.mp hv 0 (h0v (mem_singleton 0))
  exact ⟨r,hr,fun p hp y hy => huv ⟨hPu hp,hrv hy⟩⟩

lemma compact_uniform_hessian_radius {X : Type*} [TopologicalSpace X]
    (F : X → E → ℝ)
    (hD : Continuous (fun q : X × E => fderiv ℝ (fderiv ℝ (F q.1)) q.2))
    {P : Set X} (hP : IsCompact P) {c : ℝ} (hc : 0 < c) :
    ∃ r > 0, ∀ p ∈ P, ∀ y ∈ Metric.ball (0 : E) r,
      ‖fderiv ℝ (fderiv ℝ (F p)) y - fderiv ℝ (fderiv ℝ (F p)) 0‖ < c := by
  exact compact_uniform_value_radius _ hD hP hc

theorem compact_gaussian_localization {X : Type*} [TopologicalSpace X]
    (F : X → E → ℝ) (hF : ∀ p, ContDiff ℝ 2 (F p))
    (hD : Continuous (fun q : X × E => fderiv ℝ (fderiv ℝ (F q.1)) q.2))
    {P : Set X} (hP : IsCompact P) (δ : X → ℝ) {c : ℝ} (hc : 0 < c)
    (h0 : ∀ p ∈ P, F p 0 = 0)
    (h1 : ∀ p ∈ P, ∀ x, fderiv ℝ (F p) 0 x ≤ δ p*‖x‖)
    (h2 : ∀ p ∈ P, ∀ v, fderiv ℝ (fderiv ℝ (F p)) 0 v v ≤ -4*c*‖v‖^2) :
    ∃ r > 0, ∀ p ∈ P, ∀ x ∈ Metric.ball (0 : E) r,
      F p x ≤ δ p*‖x‖-c*‖x‖^2 := by
  obtain ⟨r,hr,hnear⟩ := compact_uniform_hessian_radius F hD hP hc
  refine ⟨r,hr,fun p hp x hx => gaussian_of_hessian (F p) (hF p) (h0 p hp) (h1 p hp) ?_ hx⟩
  intro y hy v
  have hn := (hnear p hp y hy).le
  have hh := h2 p hp v
  have hb := ((fderiv ℝ (fderiv ℝ (F p)) y - fderiv ℝ (fderiv ℝ (F p)) 0).le_opNorm v)
  have hb' := ((fderiv ℝ (fderiv ℝ (F p)) y - fderiv ℝ (fderiv ℝ (F p)) 0) v).le_opNorm v
  have hdiff : fderiv ℝ (fderiv ℝ (F p)) y v v - fderiv ℝ (fderiv ℝ (F p)) 0 v v ≤ c*‖v‖^2 := by
    calc
      _ ≤ ‖(fderiv ℝ (fderiv ℝ (F p)) y - fderiv ℝ (fderiv ℝ (F p)) 0) v v‖ := by
        simpa only [sub_apply, Real.norm_eq_abs] using le_abs_self
          (fderiv ℝ (fderiv ℝ (F p)) y v v - fderiv ℝ (fderiv ℝ (F p)) 0 v v)
      _ ≤ c*‖v‖^2 := by
        calc
          _ ≤ ‖(fderiv ℝ (fderiv ℝ (F p)) y - fderiv ℝ (fderiv ℝ (F p)) 0) v‖*‖v‖ := hb'
          _ ≤ (‖fderiv ℝ (fderiv ℝ (F p)) y - fderiv ℝ (fderiv ℝ (F p)) 0‖*‖v‖)*‖v‖ := by gcongr
          _ ≤ (c*‖v‖)*‖v‖ := by gcongr
          _ = c*‖v‖^2 := by ring
  nlinarith [sq_nonneg ‖v‖]

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
section SecondJetBridge
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def hessianFromJet : (E [×2]→L[ℝ] F) →L[ℝ] (E →L[ℝ] E →L[ℝ] F) :=
  ((continuousMultilinearCurryFin1 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap.postcomp E).comp
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) F).toContinuousLinearEquiv.toContinuousLinearMap

lemma hessianFromJet_iterated (f : E → F) (x : E) :
    hessianFromJet (iteratedFDeriv ℝ 2 f x) = fderiv ℝ (fderiv ℝ f) x := by
  ext v w
  change (iteratedFDeriv ℝ 2 f x) (Fin.cons v (fun _ => w)) = _
  simpa using iteratedFDeriv_two_apply (𝕜 := ℝ) f x (Fin.cons v (fun _ => w))

lemma continuous_hessian_of_iterated {X : Type*} [TopologicalSpace X]
    (f : X → E → F)
    (hf : Continuous (fun q : X × E => iteratedFDeriv ℝ 2 (f q.1) q.2)) :
    Continuous (fun q : X × E => fderiv ℝ (fderiv ℝ (f q.1)) q.2) := by
  simpa only [Function.comp_def, hessianFromJet_iterated] using hessianFromJet.continuous.comp hf

lemma second_fderiv_eval_const (f : E → F) (hf : ContDiff ℝ 2 f) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  simpa using (hd.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv |> congrArg (fun L => L v)
end SecondJetBridge

section PolynomialSecondJet
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
lemma second_fderiv_realPolyEval (P : MvPolynomial σ ℂ) (x v w : σ → ℝ) :
    fderiv ℝ (fderiv ℝ (realPolyEval P)) x v w =
      ∑ i, ∑ j, (w i : ℂ)*(v j : ℂ)*realPolyEval (pderiv j (pderiv i P)) x := by
  rw [←second_fderiv_eval_const (realPolyEval P)
    ((contDiff_realPolyEval P).of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)))) x v w]
  simp only [fderiv_realPolyEval]
  rw [fderiv_fun_sum (fun i _ =>
    ((contDiff_const.mul (contDiff_realPolyEval (pderiv i P))).differentiable (by simp) x))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_const_mul ((contDiff_realPolyEval (pderiv i P)).differentiable (by simp) x)]
  simp only [smul_apply, smul_eq_mul, fderiv_realPolyEval,
    Finset.mul_sum, mul_assoc]

lemma polynomial_prescribed_two_jet (P : MvPolynomial σ ℂ)
    (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ)
    (hQ : ∀ i j, Q i j = Q j i) (hP : VanishTo (P-wavePhaseSeed c z Q) 3) :
    realPolyEval P 0 = c ∧
    (∀ v, fderiv ℝ (realPolyEval P) 0 v = ∑ i, (v i : ℂ)*z i) ∧
    (∀ v w, fderiv ℝ (fderiv ℝ (realPolyEval P)) 0 v w =
      ∑ i, ∑ j, (w i : ℂ)*(v j : ℂ)*Q j i) := by
  have h0 := hP.constantCoeff_eq_zero (by decide)
  have h1 (i : σ) := (hP.pderiv i).constantCoeff_eq_zero (by decide)
  have h2 (i j : σ) := ((hP.pderiv i).pderiv j).constantCoeff_eq_zero (by decide)
  simp only [map_sub, wavePhaseSeed_constantCoeff] at h0
  simp only [map_sub, wavePhaseSeed_gradient] at h1
  simp only [map_sub, wavePhaseSeed_hessian c z Q hQ] at h2
  refine ⟨by simpa only [realPolyEval_at_zero] using sub_eq_zero.mp h0, ?_, ?_⟩
  · intro v
    simp only [fderiv_realPolyEval, realPolyEval_at_zero, fun i => sub_eq_zero.mp (h1 i)]
  · intro v w
    simp only [second_fderiv_realPolyEval, realPolyEval_at_zero, fun i j => sub_eq_zero.mp (h2 i j)]

end PolynomialSecondJet
section LinearReJet
variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]

lemma continuous_iterated_re_precomp (f : X → F → ℂ)
    (hf : ∀ p, ContDiff ℝ ∞ (f p)) (L : E →L[ℝ] F) (k : ℕ)
    (hj : Continuous (fun q : X × F => iteratedFDeriv ℝ k (f q.1) q.2)) :
    Continuous (fun q : X × E => iteratedFDeriv ℝ k
      (fun x => (f q.1 (L x)).re) q.2) := by
  have hle : (k : ℕ∞ω) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
  have heq (p : X) (x : E) : iteratedFDeriv ℝ k (fun y => (f p (L y)).re) x =
      Complex.reCLM.compContinuousMultilinearMap
        ((iteratedFDeriv ℝ k (f p) (L x)).compContinuousLinearMap (fun _ => L)) := by
    change iteratedFDeriv ℝ k (Complex.reCLM ∘ (f p ∘ L)) x = _
    rw [Complex.reCLM.iteratedFDeriv_comp_left ((hf p).comp L.contDiff).contDiffAt hle,
      L.iteratedFDeriv_comp_right (hf p) x hle]
  simp only [heq]
  exact ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => E) ℂ ℝ)
    Complex.reCLM).continuous.comp
    ((ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := ℂ) (fun _ : Fin k => L)).continuous.comp
      (hj.comp (continuous_fst.prodMk (L.continuous.comp continuous_snd))))

lemma first_fderiv_re_precomp (f : F → ℂ) (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] F) (x v : E) :
    fderiv ℝ (fun y => (f (L y)).re) x v = (fderiv ℝ f (L x) (L v)).re := by
  have hd := Complex.reCLM.hasFDerivAt.comp x
    ((hf.differentiable (by simp) (L x)).hasFDerivAt.comp x L.hasFDerivAt)
  exact congrArg (fun T => T v) hd.fderiv

lemma second_fderiv_re_precomp (f : F → ℂ) (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] F) (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => (f (L y)).re)) x v w =
      (fderiv ℝ (fderiv ℝ f) (L x) (L v) (L w)).re := by
  have hle : (2 : ℕ∞ω) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2))
  have he := Complex.reCLM.iteratedFDeriv_comp_left ((hf.comp L.contDiff).contDiffAt) hle
    (x := x)
  rw [L.iteratedFDeriv_comp_right hf x hle] at he
  have hh := congrArg (fun T => T ![v,w]) he
  change (iteratedFDeriv ℝ 2 (Complex.reCLM ∘ f ∘ L) x) ![v,w] =
    ((iteratedFDeriv ℝ 2 f (L x)) (fun i => L (![v,w] i))).re at hh
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Function.comp_def, Complex.reCLM_apply] using hh

end LinearReJet
variable {E X σ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [Fintype σ] [DecidableEq σ]

lemma second_fderiv_sub (f g : E → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    fderiv ℝ (fderiv ℝ (f-g)) x =
      fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) x := by
  have hh := congrArg (hessianFromJet (E := E) (F := ℝ))
    (iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt (i := 2) (x := x))
  simpa only [map_sub, hessianFromJet_iterated] using hh

theorem compact_polynomial_gaussian (L : E →L[ℝ] (σ → ℝ))
    (P : X → MvPolynomial σ ℂ) (hPc : CoeffContinuous P)
    (N : ℕ) (hN : ∀ p, (P p).totalDegree ≤ N)
    (φ : X → E → ℝ) (hφ : ∀ p, ContDiff ℝ ∞ (φ p))
    (hφ2 : Continuous (fun q : X × E => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (s : X → ℂ) (z : X → σ → ℂ) (Q : X → σ → σ → ℂ)
    (hs0 : ∀ p, (s p).re = φ p 0)
    (hQ : ∀ p i j, Q p i j = Q p j i)
    (hseed : ∀ p, VanishTo (P p-wavePhaseSeed (s p) (z p) (Q p)) 3)
    {K : Set X} (hK : IsCompact K) (δ : X → ℝ) {c : ℝ} (hc : 0 < c)
    (hlinear : ∀ p ∈ K, ∀ v,
      (∑ i, (L v i : ℂ)*z p i).re - fderiv ℝ (φ p) 0 v ≤ δ p*‖v‖)
    (hgap : ∀ p ∈ K, ∀ v,
      (∑ i, ∑ j, (L v i : ℂ)*(L v j : ℂ)*Q p j i).re -
        fderiv ℝ (fderiv ℝ (φ p)) 0 v v ≤ -4*c*‖v‖^2) :
    ∃ r > 0, ∀ p ∈ K, ∀ x ∈ Metric.ball (0 : E) r,
      (realPolyEval (P p) (L x)).re - φ p x ≤ δ p*‖x‖-c*‖x‖^2 := by
  let G := fun p x => (realPolyEval (P p) (L x)).re
  let F := fun p => G p - φ p
  have hle : (2 : ℕ∞ω) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2))
  have hG (p : X) : ContDiff ℝ ∞ (G p) :=
    Complex.reCLM.contDiff.comp ((contDiff_realPolyEval (P p)).comp L.contDiff)
  have hF (p : X) : ContDiff ℝ ∞ (F p) := (hG p).sub (hφ p)
  have hGj := continuous_iterated_re_precomp (fun p => realPolyEval (P p))
    (fun p => contDiff_realPolyEval (P p)) L 2 (continuous_polynomial_jets P hPc N hN 2)
  have hFj : Continuous (fun q : X × E => iteratedFDeriv ℝ 2 (F q.1) q.2) := by
    have heq (p : X) (x : E) : iteratedFDeriv ℝ 2 (F p) x =
        iteratedFDeriv ℝ 2 (G p) x - iteratedFDeriv ℝ 2 (φ p) x :=
      iteratedFDeriv_sub_apply ((hG p).of_le hle).contDiffAt ((hφ p).of_le hle).contDiffAt
    convert (hGj.sub hφ2) using 1
    funext q
    exact heq q.1 q.2
  apply compact_gaussian_localization F (fun p => (hF p).of_le hle)
    (continuous_hessian_of_iterated F hFj) hK δ hc
  · intro p hp
    change (realPolyEval (P p) (L 0)).re - φ p 0 = 0
    rw [map_zero, (polynomial_prescribed_two_jet (P p) (s p) (z p) (Q p) (hQ p) (hseed p)).1,
      hs0 p, sub_self]
  · intro p hp v
    change fderiv ℝ (G p - φ p) 0 v ≤ _
    rw [fderiv_sub ((hG p).differentiable (by simp) 0) ((hφ p).differentiable (by simp) 0)]
    simp only [sub_apply]
    change fderiv ℝ (fun x => (realPolyEval (P p) (L x)).re) 0 v - _ ≤ _
    rw [first_fderiv_re_precomp _ (contDiff_realPolyEval (P p)), map_zero,
      (polynomial_prescribed_two_jet (P p) (s p) (z p) (Q p) (hQ p) (hseed p)).2.1]
    exact hlinear p hp v
  · intro p hp v
    change fderiv ℝ (fderiv ℝ (G p-φ p)) 0 v v ≤ _
    rw [second_fderiv_sub (G p) (φ p) ((hG p).of_le hle) ((hφ p).of_le hle)]
    simp only [sub_apply]
    change fderiv ℝ (fderiv ℝ (fun x => (realPolyEval (P p) (L x)).re)) 0 v v - _ ≤ _
    rw [second_fderiv_re_precomp _ (contDiff_realPolyEval (P p)), map_zero,
      (polynomial_prescribed_two_jet (P p) (s p) (z p) (Q p) (hQ p) (hseed p)).2.2]
    exact hgap p hp v



end YauCounterexamples
end

end OAI
