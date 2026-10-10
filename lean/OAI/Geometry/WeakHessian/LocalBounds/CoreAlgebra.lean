import Mathlib
import OAI.Geometry.WeakHessian.Calculus.CompactThickenedIndicator
import OAI.Geometry.WeakHessian.LocalBounds.Smul
import OAI.Geometry.WeakHessian.Sobolev.CompContDiff2

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile110
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsLaplacian.unique (hfinite : FiniteOnBoundedSets m) {f L M : X → ℝ}
    (hL : IsLaplacian m f L) (hM : IsLaplacian m f M) : L =ᵐ[m] M := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one,
      hfinite _ Metric.isBounded_ball⟩⟩
  have hzero : (fun x => L x - M x) =ᵐ[m] 0 := by
    apply WeakHessianCalculus.ae_eq_zero_of_integral_lipschitz_compact
      ((hL.2.1.sub hM.2.1).locallyIntegrable (by norm_num))
    intro φ hc hφ
    obtain ⟨C, hC⟩ := hφ
    have hS := sobolev_of_lipschitz_compactSupport hfinite hC hc
    have hI : Integrable (fun x => L x * φ x) m := hL.2.1.integrable_mul hS.1
    have hJ : Integrable (fun x => M x * φ x) m := hM.2.1.integrable_mul hS.1
    change (∫ x, (L x - M x) * φ x ∂m) = 0
    simp_rw [sub_mul]
    rw [integral_sub hI hJ]
    have heq := (hL.2.2 φ hS).symm.trans (hM.2.2 φ hS)
    linarith
  filter_upwards [hzero] with x hx
  exact sub_eq_zero.mp hx

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma laplacian_isLaplacian {f : X → ℝ} (hf : InLaplacianDomain m f) :
    IsLaplacian m f (laplacian m f) := by
  change ∃ L, IsLaplacian m f L at hf
  unfold laplacian
  simpa only [dite_eq_left hf] using Classical.choose_spec hf

lemma IsLaplacian.ae_laplacian (hfinite : FiniteOnBoundedSets m) {f L : X → ℝ}
    (hf : IsLaplacian m f L) : laplacian m f =ᵐ[m] L :=
  (laplacian_isLaplacian ⟨L,hf⟩).unique hfinite hf

lemma laplacian_congr_ae (hfinite : FiniteOnBoundedSets m) {f g : X → ℝ}
    (hf : InLaplacianDomain m f) (hfg : f =ᵐ[m] g) :
    laplacian m f =ᵐ[m] laplacian m g := by
  have hfgL := (laplacian_isLaplacian hf).congr_ae hfg Filter.EventuallyEq.rfl
  exact (hfgL.ae_laplacian hfinite).symm

end WeakHessian

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def integratedBochner (m : Measure X) (g ξ : X → ℝ) : ℝ :=
  -(∫ x, gamma m ξ (fun y => gamma m g g y/2) x ∂m) +
    ∫ x, (ξ x*laplacian m g x+gamma m ξ g x)*laplacian m g x ∂m

def driftBochner (m : Measure X) (V g ξ : X → ℝ) : ℝ :=
  -(∫ x, Real.exp (V x)*gamma m ξ (fun y => gamma m g g y/2) x ∂m) +
    ∫ x, Real.exp (V x)*(ξ x*(laplacian m g x+gamma m V g x)+gamma m ξ g x)*
      (laplacian m g x+gamma m V g x) ∂m

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma driftBochner_eq_sub_hessian (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {V g ξ : X → ℝ}
    (hg : IsTestFunction m g) (hq : Sobolev m (fun y => gamma m g g y/2))
    {L T : ℝ≥0} (hV : LipschitzWith L V) (hξ : LipschitzWith T ξ)
    {B C : ℝ} (hB : ∀ x, |V x| ≤ B) (hC : ∀ x, |ξ x| ≤ C)
    (hξS : Sobolev m ξ) :
    driftBochner m V g ξ =
      integratedBochner m g (fun x => ξ x*Real.exp (V x)) -
      weakHessian m V g (fun x => ξ x*Real.exp (V x)) := by
  have hgS := (laplacian_isLaplacian hg.1).1
  have hA := (laplacian_isLaplacian hg.1).2.1
  have hVS := localSobolev_of_lipschitz hfinite hV
  have hb := memLp_gamma_of_lipschitz hfinite hpar hV hgS
  have hc := memLp_gamma_of_lipschitz hfinite hpar hξ hgS
  have hxb : MemLp (fun x => ξ x*gamma m V g x) 2 m := by
    simpa only [mul_comm] using memLp_mul_bounded hb hξ.continuous.aestronglyMeasurable (ae_of_all m hC)
  have hxA : MemLp (fun x => ξ x*laplacian m g x) 2 m := by
    simpa only [mul_comm] using memLp_mul_bounded hA hξ.continuous.aestronglyMeasurable (ae_of_all m hC)
  have hU : MemLp (fun x => ξ x*(laplacian m g x+gamma m V g x)+gamma m ξ g x) 2 m := by
    convert (hxA.add hxb).add hc using 1
    funext x
    simp only [Pi.add_apply]
    ring
  have hw : AEStronglyMeasurable (fun x => Real.exp (V x)) m :=
    (Real.continuous_exp.comp hV.continuous).aestronglyMeasurable
  have hwB : ∀ᵐ x ∂m, ‖Real.exp (V x)‖ ≤ Real.exp B := ae_of_all m fun x => by
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
      Real.exp_le_exp.mpr ((le_abs_self _).trans (hB x))
  have hB' : ∀ᵐ x ∂m, V x ≤ B := ae_of_all m fun x => (le_abs_self _).trans (hB x)
  have hxp := gamma_mul_exp_left hfinite hpar hξS.2.1 hVS hgS.2.1 hB'
    (weakGradient_le_lipschitz hfinite hV)
  have hxq := gamma_mul_exp_left hfinite hpar hξS.2.1 hVS hq.2.1 hB'
    (weakGradient_le_lipschitz hfinite hV)
  have hi1 : Integrable (fun x => Real.exp (V x)*gamma m ξ (fun y => gamma m g g y/2) x) m :=
    (integrable_gamma hfinite hξS hq).bdd_mul hw hwB
  have hi2 : Integrable (fun x => Real.exp (V x)*(ξ x*gamma m V (fun y => gamma m g g y/2) x)) m :=
    (hξS.1.integrable_mul (memLp_gamma_of_lipschitz hfinite hpar hV hq)).bdd_mul hw hwB
  have hiA : Integrable (fun x => Real.exp (V x)*
      ((ξ x*(laplacian m g x+gamma m V g x)+gamma m ξ g x)*laplacian m g x)) m :=
    (hU.integrable_mul hA).bdd_mul hw hwB
  have hib : Integrable (fun x => Real.exp (V x)*
      ((ξ x*(laplacian m g x+gamma m V g x)+gamma m ξ g x)*gamma m V g x)) m :=
    (hU.integrable_mul hb).bdd_mul hw hwB
  have eq1 : (∫ x, gamma m (fun y => ξ y*Real.exp (V y)) (fun y => gamma m g g y/2) x ∂m) =
      (∫ x, Real.exp (V x)*gamma m ξ (fun y => gamma m g g y/2) x ∂m) +
      ∫ x, Real.exp (V x)*(ξ x*gamma m V (fun y => gamma m g g y/2) x) ∂m := by
    rw [← integral_add hi1 hi2]
    apply integral_congr_ae
    filter_upwards [hxq] with x hx
    rw [hx]
    ring
  have eq2 : (∫ x, ((ξ x*Real.exp (V x))*laplacian m g x+
      gamma m (fun y => ξ y*Real.exp (V y)) g x)*laplacian m g x ∂m) =
      ∫ x, Real.exp (V x)*
        ((ξ x*(laplacian m g x+gamma m V g x)+gamma m ξ g x)*laplacian m g x) ∂m := by
    apply integral_congr_ae
    filter_upwards [hxp] with x hx
    rw [hx]
    ring
  have eq3 : (∫ x, (gamma m (fun y => ξ y*Real.exp (V y)) g x+
      (ξ x*Real.exp (V x))*laplacian m g x)*gamma m V g x ∂m) =
      ∫ x, Real.exp (V x)*
        ((ξ x*(laplacian m g x+gamma m V g x)+gamma m ξ g x)*gamma m V g x) ∂m := by
    apply integral_congr_ae
    filter_upwards [hxp] with x hx
    rw [hx]
    ring
  have eq4 : (∫ x, (ξ x*Real.exp (V x))*gamma m V (fun y => gamma m g g y/2) x ∂m) =
      ∫ x, Real.exp (V x)*(ξ x*gamma m V (fun y => gamma m g g y/2) x) ∂m := by
    congr 1
    funext x
    ring
  have eq5 : (∫ x, Real.exp (V x)*(ξ x*(laplacian m g x+gamma m V g x)+gamma m ξ g x)*
      (laplacian m g x+gamma m V g x) ∂m) =
      (∫ x, Real.exp (V x)*
        ((ξ x*(laplacian m g x+gamma m V g x)+gamma m ξ g x)*laplacian m g x) ∂m) +
      ∫ x, Real.exp (V x)*
        ((ξ x*(laplacian m g x+gamma m V g x)+gamma m ξ g x)*gamma m V g x) ∂m := by
    rw [← integral_add hiA hib]
    congr 1
    funext x
    ring
  unfold driftBochner integratedBochner weakHessian
  rw [eq1,eq2,eq3,eq4,eq5]
  ring
end WeakHessian

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma weakHessian_const_mul (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {F g h : X → ℝ}
    (hF : LocalSobolev m F) (hg : LocalSobolev m g)
    (hq : LocalSobolev m (fun y => gamma m g g y/2)) (c : ℝ) :
    weakHessian m (fun x => c*F x) g h = c*weakHessian m F g h := by
  have hfg := gamma_const_mul_left hfinite hpar hF hg c
  have hfq := gamma_const_mul_left hfinite hpar hF hq c
  unfold weakHessian
  have e1 : (∫ x, (gamma m h g x+h x*laplacian m g x)*gamma m (fun y => c*F y) g x ∂m) =
      c*(∫ x, (gamma m h g x+h x*laplacian m g x)*gamma m F g x ∂m) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]
    ring
  have e2 : (∫ x, h x*gamma m (fun y => c*F y) (fun y => gamma m g g y/2) x ∂m) =
      c*(∫ x, h x*gamma m F (fun y => gamma m g g y/2) x ∂m) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hfq] with x hx
    rw [hx]
    ring
  rw [e1,e2]
  ring
end WeakHessian

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma WeakHessianUpperBound.core_dual (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {F G g ξ : X → ℝ}
    (hHess : WeakHessianUpperBound m F G)
    (hg : IsTestFunction m g) (hgc : HasCompactSupport g)
    (hq : Sobolev m (fun y => gamma m g g y/2))
    {L T : ℝ≥0} (hF : LipschitzWith L F) (hξ : LipschitzWith T ξ)
    {B C : ℝ} (hB : ∀ x, |F x| ≤ B) (hC : ∀ x, |ξ x| ≤ C)
    (hξc : HasCompactSupport ξ) (hξ0 : ∀ x, 0 ≤ ξ x)
    {a K : ℝ} (ha : 0 ≤ a)
    (horig : K*(∫ x, (ξ x*Real.exp (a*F x))*gamma m g g x ∂m) ≤
      integratedBochner m g (fun x => ξ x*Real.exp (a*F x))) :
    K*(∫ x, (ξ x*Real.exp (a*F x))*gamma m g g x ∂m) -
      a*(∫ x, (ξ x*Real.exp (a*F x))*G x*gamma m g g x ∂m) ≤
      driftBochner m (fun x => a*F x) g ξ := by
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x, |a*F x| ≤ |a| * B := fun x => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg a)
  have hw := lipschitz_exp_bounded hV (fun x => (le_abs_self _).trans (hVB x))
  have hwB : ∀ x, |Real.exp (a*F x)| ≤ Real.exp (|a| * B) := fun x => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hVB x))
  have hφ := lipschitz_mul_bounded hξ hw hC hwB
  have hh := hHess g hg hgc (fun x => ξ x*Real.exp (a*F x)) ⟨_,hφ⟩
    hξc.mul_right (fun x => mul_nonneg (hξ0 x) (Real.exp_pos _).le)
  rw [driftBochner_eq_sub_hessian hfinite hpar hg hq hV hξ hVB hC
    (sobolev_of_lipschitz_compactSupport hfinite hξ hξc),
    weakHessian_const_mul hfinite hpar (localSobolev_of_lipschitz hfinite hF)
      (laplacian_isLaplacian hg.1).1.2.1 hq.2.1]
  linarith [mul_le_mul_of_nonneg_left hh ha]

lemma WeakHessianUpperBound.core_integrated (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {F G g ξ : X → ℝ}
    (hHess : WeakHessianUpperBound m F G)
    (hg : IsTestFunction m g) (hgc : HasCompactSupport g)
    (hq : Sobolev m (fun y => gamma m g g y/2))
    {L T : ℝ≥0} (hF : LipschitzWith L F) (hξ : LipschitzWith T ξ)
    {B C D : ℝ} (hB : ∀ x, |F x| ≤ B) (hC : ∀ x, |ξ x| ≤ C)
    (hG : ∀ x, |G x| ≤ D) (hGc : Continuous G)
    (hξc : HasCompactSupport ξ) (hξ0 : ∀ x, 0 ≤ ξ x)
    {a K : ℝ} (ha : 0 ≤ a)
    (horig : K*(∫ x, (ξ x*Real.exp (a*F x))*gamma m g g x ∂m) ≤
      integratedBochner m g (fun x => ξ x*Real.exp (a*F x))) :
    (∫ x, Real.exp (a*F x)*ξ x*(K-a*G x)*gamma m g g x ∂m) ≤
      driftBochner m (fun x => a*F x) g ξ := by
  have hgS := (laplacian_isLaplacian hg.1).1
  have hφB : ∀ᵐ x ∂m, ‖ξ x*Real.exp (a*F x)‖ ≤ |C| * Real.exp (|a| * B) := by
    filter_upwards [] with x
    simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul ((hC x).trans (le_abs_self _)) _ (Real.exp_pos _).le (abs_nonneg _)
    apply Real.exp_le_exp.mpr
    calc a*F x ≤ |a*F x| := le_abs_self _
      _ = |a| * |F x| := abs_mul _ _
      _ ≤ |a| * B := mul_le_mul_of_nonneg_left (hB x) (abs_nonneg _)
  have hφm : AEStronglyMeasurable (fun x => ξ x*Real.exp (a*F x)) m :=
    (hξ.continuous.mul (Real.continuous_exp.comp (continuous_const.mul hF.continuous))).aestronglyMeasurable
  have hi := (integrable_gamma hfinite hgS hgS).bdd_mul hφm hφB
  have hiG : Integrable (fun x => (ξ x*Real.exp (a*F x))*G x*gamma m g g x) m := by
    have ht := hi.bdd_mul hGc.aestronglyMeasurable (ae_of_all m fun x => by
      simpa only [Real.norm_eq_abs] using hG x)
    convert ht using 1
    funext x
    ring
  calc
    (∫ x, Real.exp (a*F x)*ξ x*(K-a*G x)*gamma m g g x ∂m) =
        K*(∫ x, (ξ x*Real.exp (a*F x))*gamma m g g x ∂m) -
        a*(∫ x, (ξ x*Real.exp (a*F x))*G x*gamma m g g x ∂m) := by
      rw [← integral_const_mul,← integral_const_mul,← integral_sub (hi.const_mul K) (hiG.const_mul a)]
      congr 1
      funext x
      ring
    _ ≤ _ := hHess.core_dual hfinite hpar hg hgc hq hF hξ hB hC hξc hξ0 ha horig
end WeakHessian

end
end InlinedFile110

end OAI
