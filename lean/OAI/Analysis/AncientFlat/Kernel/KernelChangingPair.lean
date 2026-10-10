import OAI.Analysis.AncientFlat.Kernel.ClassicalBase
import OAI.Analysis.AncientFlat.Evolution.ChangingPair

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
namespace FlatDuality
open BiharmonicKernel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
def kernelTest (θ γ : ℝ → ℝ) (z : V) (r : ℝ) (x : V) : ℂ :=
  (γ r : ℂ)*kernel (θ r) (x-z)
def kernelTestDeriv (θ γ : ℝ → ℝ) (z : V) (r : ℝ) (x : V) : ℂ :=
  (Complex.ofReal (deriv γ r))*kernel (θ r) (x-z)+
    (γ r : ℂ)*(-bilapKernel (θ r) (x-z)*(Complex.ofReal (deriv θ r)))
lemma hasDerivAt_kernelTest (θ γ : ℝ → ℝ) (z : V) (r : ℝ)
    (hθ : DifferentiableAt ℝ θ r) (hγ : DifferentiableAt ℝ γ r) (hr : 0<θ r) (x : V) :
    HasDerivAt (fun s => kernelTest θ γ z s x) (kernelTestDeriv θ γ z r x) r := by
  simpa only [kernelTest,kernelTestDeriv,Function.comp_def,Complex.real_smul,mul_comm (Complex.ofReal (deriv θ r))] using!
    hγ.hasDerivAt.ofReal_comp.mul ((hasDerivAt_kernel_bilap (θ r) hr (x-z)).scomp r hθ.hasDerivAt)
lemma continuous_kernelTest (θ γ : ℝ → ℝ) (z : V) (r : ℝ) (hr : 0<θ r) :
    Continuous (kernelTest θ γ z r) :=
  continuous_const.mul (continuous_kernel_comp (fun _ : V => θ r) (fun x => x-z)
    continuous_const (continuous_id.sub continuous_const) (fun _ => hr))
lemma continuous_kernelTestDeriv (θ γ : ℝ → ℝ) (z : V) (r : ℝ) (hr : 0<θ r) :
    Continuous (kernelTestDeriv θ γ z r) :=
  (continuous_const.mul (continuous_kernel_comp (fun _ : V => θ r) (fun x => x-z)
    continuous_const (continuous_id.sub continuous_const) (fun _ => hr))).add
    (continuous_const.mul (((continuous_bilapKernel_comp (fun _ : V => θ r) (fun x => x-z)
      continuous_const (continuous_id.sub continuous_const) (fun _ => hr)).neg).mul continuous_const))

lemma hasDerivAt_kernel_pair (θ γ : ℝ → ℝ) (hθ : ContDiff ℝ 1 θ) (hγ : ContDiff ℝ 1 γ)
    (z : V) {u : ℝ → V →ᵇ ℂ} {p : V →ᵇ ℂ} {t : ℝ}
    (hu : HasDerivAt u p t) (ht : 0<θ t) :
    HasDerivAt (fun r => ∫ x, kernelTest θ γ z r x*u r x)
      (∫ x, kernelTestDeriv θ γ z t x*u t x+kernelTest θ γ z t x*p x) t := by
  let a := θ t/2
  let b := 2*θ t
  let G := ‖γ t‖+1
  let D := ‖deriv γ t‖+1
  let Q := ‖deriv θ t‖+1
  have ha : 0<a := by dsimp [a]; positivity
  have hG : 0<G := by dsimp [G]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hθn : ∀ᶠ r in 𝓝 t, θ r ∈ Ioo a b :=
    hθ.continuous.continuousAt.eventually (Ioo_mem_nhds (by dsimp [a]; linarith) (by dsimp [b]; linarith))
  have hγn : ∀ᶠ r in 𝓝 t, ‖γ r‖<G :=
    hγ.continuous.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))
  have hDn : ∀ᶠ r in 𝓝 t, ‖deriv γ r‖<D :=
    hγ.continuous_deriv_one.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))
  have hQn : ∀ᶠ r in 𝓝 t, ‖deriv θ r‖<Q :=
    hθ.continuous_deriv_one.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hθn.and (hγn.and (hDn.and hQn)))
  have hb0 : t ∈ Metric.ball t δ := Metric.mem_ball_self hδ
  obtain ⟨A,hAi,hAn,hAb⟩ := FrozenParametrix.kernel_majorant_nonneg (V := V) a b ha
  obtain ⟨B,hBi,_,hBn,hBb⟩ := bilapKernel_weighted_majorant (V := V) a b ha
  let A₁ : V → ℝ := fun x => G*A (x-z)
  let B₁ : V → ℝ := fun x => D*A (x-z)+(G*Q)*B (x-z)
  have hAbound : ∀ r ∈ Metric.ball t δ, ∀ x, ‖kernelTest θ γ z r x‖≤A₁ x := by
    intro r hr x
    obtain ⟨hq,hg,_,_⟩ := hball hr
    change ‖(γ r : ℂ)*kernel (θ r) (x-z)‖≤G*A (x-z)
    rw [norm_mul,Complex.norm_real]
    exact mul_le_mul hg.le (hAb _ ⟨hq.1.le,hq.2.le⟩ _) (norm_nonneg _) hG.le
  have hBbound : ∀ r ∈ Metric.ball t δ, ∀ x, ‖kernelTestDeriv θ γ z r x‖≤B₁ x := by
    intro r hr x
    obtain ⟨hq,hg,hd,hq'⟩ := hball hr
    unfold kernelTestDeriv
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul,norm_mul,norm_neg,Complex.norm_real,Complex.norm_real,Complex.norm_real]
    calc
      _ ≤ D*A (x-z)+G*(B (x-z)*Q) := add_le_add
        (mul_le_mul hd.le (hAb _ ⟨hq.1.le,hq.2.le⟩ _) (norm_nonneg _) hD.le)
        (mul_le_mul hg.le (mul_le_mul (hBb _ ⟨hq.1.le,hq.2.le⟩ _) hq'.le
          (norm_nonneg _) (hBn _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hG.le)
      _ = B₁ x := by dsimp [B₁]; ring
  refine hasDerivAt_changing_pair hu (kernelTest θ γ z) (kernelTestDeriv θ γ z t)
    (Metric.ball t δ) (Metric.ball_mem_nhds t hδ)
    ?_ ?_ ?_ A₁ B₁ ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    exact (continuous_kernelTest θ γ z r (ha.trans (hball hr).1.1)).aestronglyMeasurable
  · exact (continuous_kernelTestDeriv θ γ z t ht).aestronglyMeasurable
  · exact hasDerivAt_kernelTest θ γ z t ((hθ.differentiable (by norm_num)) t) ((hγ.differentiable (by norm_num)) t) ht
  · exact (hAi.comp_sub_right z).const_mul G
  · exact ((hAi.comp_sub_right z).const_mul D).add ((hBi.comp_sub_right z).const_mul (G*Q))
  · exact fun x => mul_nonneg hG.le (hAn _)
  · exact fun x => add_nonneg (mul_nonneg hD.le (hAn _)) (mul_nonneg (mul_nonneg hG.le hQ.le) (hBn _))
  · exact hAbound
  · intro r hr x
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hasDerivAt_kernelTest θ γ z s ((hθ.differentiable (by norm_num)) s)
        ((hγ.differentiable (by norm_num)) s) (ha.trans (hball hs).1.1) x).hasDerivWithinAt)
      (fun s hs => hBbound s hs x) (convex_ball t δ) hb0 hr
end FlatDuality

end

end OAI
