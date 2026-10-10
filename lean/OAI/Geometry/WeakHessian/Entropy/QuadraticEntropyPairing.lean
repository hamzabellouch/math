import Mathlib
import OAI.Geometry.WeakHessian.Entropy.EntropyPairingLimits
import OAI.Geometry.WeakHessian.LocalBounds.WeightedPairing2
import OAI.Geometry.WeakHessian.LocalBounds.RadialRoots
import OAI.Geometry.WeakHessian.LocalBounds.QuadraticPairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile32
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

lemma tendsto_by_uniform_approximations {a : ℕ → ℝ} {A : ℝ}
    {b : ℕ → ℕ → ℝ} {B e : ℕ → ℝ}
    (hb : ∀ k, Tendsto (b k) atTop (𝓝 (B k))) (he : Tendsto e atTop (𝓝 0))
    (hab : ∀ k n, |a n-b k n| ≤ e k) (hAB : ∀ k, |A-B k| ≤ e k) :
    Tendsto a atTop (𝓝 A) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨k,hk⟩ := ((he.eventually (eventually_lt_nhds (show (0:ℝ) < ε/3 by positivity))).exists)
  filter_upwards [(Metric.tendsto_nhds.mp (hb k)) (ε/3) (by positivity)] with n hn
  rw [Real.dist_eq] at hn ⊢
  have H : |a n-A| ≤ |a n-b k n|+|b k n-B k|+|B k-A| := by
    have heq : a n-A = (a n-b k n)+(b k n-B k)+(B k-A) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  rw [abs_sub_comm (B k) A] at H
  linarith [hab k n,hAB k]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

lemma CurvatureDimension.quadratic_entropy_pairing_fixed {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (hq : QuadraticCheegerEnergy m) (o : X) {T : ℝ≥0} (hTpos : 0 < T)
    {φs : ℕ → X → ℝ} {φ w : X → ℝ}
    (hφs : ∀ n, QuadraticLipschitzBound o T (φs n)) (hφ : QuadraticLipschitzBound o T φ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ n, |φs n o| ≤ B) (hbφ : |φ o| ≤ B)
    (hT : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x)))
    (hw : Sobolev m w) {A : ℝ} (hA : ∀ᵐ x ∂m, |w x| ≤ A)
    (hwW : MemLp (fun x => w x*(dist x o+T)) 2 m) :
    Tendsto (fun n => ∫ x,w x*gamma m w (φs n) x ∂m) atTop
      (𝓝 (∫ x,w x*gamma m w φ x ∂m)) := by
  have hp : (0:ℝ) < T := hTpos
  have hpar := hcd.global_localGradientParallelogram hfin o hq
  let W (x : X) := dist x o+(T:ℝ)
  let v (k : ℕ) (x : X) := w x*radialCutoff o k x
  obtain ⟨D,hD,hUG,hDT⟩ := radial_root_approximation hfin hw o
  let hv (k : ℕ) : Sobolev m (v k) := Sobolev.of_upperGradient hfin (radial_mul_memLp hw.1 o k) (hUG k) (hD k)
  obtain ⟨hs,hsT⟩ := radial_root_strong hcd hfin hq hw o
  obtain ⟨hdW,hdWT⟩ := radial_weighted_root_tendsto hwW o
  have hvW (k : ℕ) : MemLp (fun x => v k x*W x) 2 m := by
    have he : (fun x => v k x*W x) = fun x => w x*W x*radialCutoff o k x := by funext x; dsimp [v]; ring
    rw [he]
    exact radial_mul_memLp hwW o k
  let e (k : ℕ) := ‖(hdW k).toLp (fun x => (v k x-w x)*W x)‖*‖(hD k).toLp (D k)‖+
    ‖hwW.toLp (fun x => w x*W x)‖*‖(hs k).2.2.toLp (weakGradient m (fun x => v k x-w x))‖
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [zero_mul,mul_zero,zero_add,e,v,W] using (hdWT.mul hDT.norm).add (hsT.const_mul ‖hwW.toLp (fun x => w x*W x)‖)
  have hnorm (k : ℕ) : ‖(hv k).2.2.toLp (weakGradient m (v k))‖ ≤ ‖(hD k).toLp (D k)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(hv k).2.2.coeFn_toLp,(hD k).coeFn_toLp,
      (weakGradient_isMinimal (hv k).2.1.2).2 _ (hUG k),weakGradient_nonneg (m := m) (v k)] with x he hd hg hn
    rw [he,hd,Real.norm_eq_abs,abs_of_nonneg hn,Real.norm_eq_abs]
    exact hg.trans (le_abs_self _)
  have bound (k : ℕ) (f : X → ℝ) (hf : QuadraticLipschitzBound o T f) :
      |(∫ x,w x*gamma m w f x ∂m)-(∫ x,v k x*gamma m (v k) f x ∂m)| ≤ e k := by
    rw [abs_sub_comm]
    have H := weighted_gamma_root_difference hfin hpar (hv k) hw (hf.localSobolev hfin hp)
      (ae_of_all _ fun x => by positivity) (hf.gradient_le hfin hp) (hvW k) hwW (hdW k)
    exact H.trans (add_le_add (mul_le_mul_of_nonneg_left (hnorm k) (norm_nonneg _)) le_rfl)
  have hvA (k : ℕ) : ∀ᵐ x ∂m, |v k x| ≤ A := by
    filter_upwards [hA] with x hx
    dsimp [v]
    rw [abs_mul,abs_of_nonneg (radialCutoff_nonneg o k x)]
    exact (mul_le_of_le_one_right (abs_nonneg _) (radialCutoff_le_one o k x)).trans hx
  have fixed (k : ℕ) : Tendsto (fun n => ∫ x,v k x*gamma m (v k) (φs n) x ∂m) atTop
      (𝓝 (∫ x,v k x*gamma m (v k) φ x ∂m)) := by
    have hg := (hv k).square_bounded hfin (hvA k)
    have hgs : ∀ᵐ x ∂m, x ∉ Metric.closedBall o ((k:ℝ)+1) → (v k x)^2 = 0 := by
      apply ae_of_all
      intro x hx
      have hz : radialCutoff o k x = 0 := by
        have hd : (k:ℝ)+1 ≤ dist x o := le_of_lt (lt_of_not_ge hx)
        unfold radialCutoff
        rw [max_eq_left]
        exact sub_nonpos.mpr ((le_div_iff₀ (by positivity : (0:ℝ)<(k:ℝ)+1)).mpr (by simpa using hd))
      simp [v,hz]
    have H := hcd.quadratic_potential_pairing_tendsto hfin hq o ((k:ℝ≥0)+1)
      hTpos hφs hφ hB hb hbφ hT hg hgs
    have eqn (f : X → ℝ) (hf : QuadraticLipschitzBound o T f) :
        (∫ x,gamma m f (fun x => (v k x)^2) x ∂m) = 2*(∫ x,v k x*gamma m (v k) f x ∂m) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [gamma_comm (m := m) f (fun x => (v k x)^2),
        gamma_square_bounded hfin hpar (hv k) (hf.localSobolev hfin hp) (hvA k)] with x hc he
      rw [hc,he]
      ring
    have J := H.div_const 2
    simp only [eqn _ (hφs _),eqn φ hφ,mul_div_cancel_left₀ _ (two_ne_zero : (2:ℝ) ≠ 0)] at J
    exact J
  exact tendsto_by_uniform_approximations fixed he (fun k n => bound k (φs n) (hφs n)) (fun k => bound k φ hφ)

lemma CurvatureDimension.quadratic_entropy_pairing_tendsto {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (hq : QuadraticCheegerEnergy m) (o : X) {T : ℝ≥0} (hTpos : 0 < T)
    {φs : ℕ → X → ℝ} {φ w : X → ℝ}
    (hφs : ∀ n, QuadraticLipschitzBound o T (φs n)) (hφ : QuadraticLipschitzBound o T φ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ n, |φs n o| ≤ B) (hbφ : |φ o| ≤ B)
    (hT : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x)))
    (hw : Sobolev m w) {A : ℝ} (hA : ∀ᵐ x ∂m, |w x| ≤ A)
    (hwW : MemLp (fun x => w x*(dist x o+T)) 2 m)
    {vs : ℕ → X → ℝ} (hvs : ∀ n, Sobolev m (vs n))
    (hvsW : ∀ n, MemLp (fun x => vs n x*(dist x o+T)) 2 m)
    (hdW : ∀ n, MemLp (fun x => (vs n x-w x)*(dist x o+T)) 2 m)
    (hWT : Tendsto (fun n => ‖(hdW n).toLp (fun x => (vs n x-w x)*(dist x o+T))‖) atTop (𝓝 0))
    (hE : Tendsto (fun n => ‖((hvs n).sub hfin hw).2.2.toLp
      (weakGradient m (fun x => vs n x-w x))‖) atTop (𝓝 0))
    {M : ℝ} (hM : ∀ n, ‖(hvs n).2.2.toLp (weakGradient m (vs n))‖ ≤ M) :
    Tendsto (fun n => ∫ x,2*vs n x*gamma m (φs n) (vs n) x ∂m) atTop
      (𝓝 (∫ x,2*w x*gamma m φ w x ∂m)) := by
  have hp : (0:ℝ) < T := hTpos
  have hpar := hcd.global_localGradientParallelogram hfin o hq
  have hbt := (hWT.mul_const M).add (hE.const_mul ‖hwW.toLp (fun x => w x*(dist x o+T))‖)
  simp only [mul_zero,zero_mul,zero_add] at hbt
  have hd : Tendsto (fun n => (∫ x,vs n x*gamma m (vs n) (φs n) x ∂m)-
      (∫ x,w x*gamma m w (φs n) x ∂m)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hbt
    intro n
    rw [Real.norm_eq_abs]
    exact (weighted_gamma_root_difference hfin hpar (hvs n) hw ((hφs n).localSobolev hfin hp)
      (ae_of_all _ fun x => by positivity) ((hφs n).gradient_le hfin hp) (hvsW n) hwW (hdW n)).trans
        (add_le_add (mul_le_mul_of_nonneg_left (hM n) (norm_nonneg _)) le_rfl)
  have hf := hcd.quadratic_entropy_pairing_fixed hfin hq o hTpos hφs hφ hB hb hbφ hT hw hA hwW
  have H := (hd.add hf).const_mul 2
  simp only [zero_add,sub_add_cancel] at H
  simp_rw [entropy_pairing_twice hfin (hvs _).2.1 ((hφs _).localSobolev hfin hp),
    entropy_pairing_twice hfin hw.2.1 (hφ.localSobolev hfin hp)]
  exact H
end WeakHessian

end
end InlinedFile32

end OAI
