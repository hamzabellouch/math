import OAI.Combinatorics.SparsestCut.CubeGeometry

namespace OAI

universe u1 u2

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CubeTransfer
open MeasureTheory Set Filter
open scoped BigOperators
noncomputable section
variable {m : ℕ} {A : Type u1} [Fintype A]
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "μ" => CubePoincare.cube (m := m)
lemma continuous_integrable (f : E → ℝ) (hf : Continuous f) : Integrable f μ := by
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0:E) (Real.sqrt m)).exists_bound_of_continuousOn hf.continuousOn
  apply CubeGeometry.bounded_integrable hf.aestronglyMeasurable
  filter_upwards [CubeGeometry.cube_norm (m := m)] with x hx
  simpa only [Real.norm_eq_abs] using hB x (by simpa using hx)
lemma pair_continuous_integrable (f : E × E → ℝ) (hf : Continuous f) : Integrable f ((μ).prod μ) := by
  let K : Set E := Metric.closedBall 0 (Real.sqrt m)
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨B,hB⟩ := (hK.prod hK).exists_bound_of_continuousOn hf.continuousOn
  have hm : ∀ᵐ x : E ∂μ, x∈K := by simpa only [K,Metric.mem_closedBall,dist_zero_right] using CubeGeometry.cube_norm (m := m)
  have hp : ∀ᵐ z : E × E ∂(μ).prod μ, z∈K ×ˢ K := by
    apply (Measure.ae_prod_iff_ae_ae (hK.measurableSet.prod hK.measurableSet)).mpr
    filter_upwards [hm] with x hx
    filter_upwards [hm] with y hy
    exact ⟨hx,hy⟩
  apply (integrable_const B).mono' hf.aestronglyMeasurable
  filter_upwards [hp] with z hz
  exact hB z hz

lemma average_from_gradient (f H : A → E → ℝ) {M B K : ℝ}
    (hf : ∀ a, Measurable (f a)) (hM : ∀ a x, |f a x|≤M)
    (hH : ∀ a, ContDiff ℝ 1 (H a))
    (he : ∀ᵐ x : E ∂μ, ∑ a, |H a x-f a x|≤B)
    (hg : ∀ᵐ x : E ∂μ, ∑ a, ‖fderiv ℝ (H a) x‖≤K) :
    (∫ z : E × E, ∑ a, |f a z.1-f a z.2| ∂(μ).prod μ)≤2*B+(Real.pi/2)*K := by
  classical
  have hfi (a : A) : Integrable (f a) μ :=
    CubeGeometry.bounded_integrable (hf a).aestronglyMeasurable (Eventually.of_forall (hM a))
  have hfdi (a : A) : Integrable (fun z : E × E => |f a z.1-f a z.2|) ((μ).prod μ) :=
    ((hfi a).comp_fst μ |>.sub ((hfi a).comp_snd μ)).abs
  have hHd (a : A) : Integrable (fun z : E × E => |H a z.1-H a z.2|) ((μ).prod μ) :=
    pair_continuous_integrable _ (by have hh := (hH a).continuous; fun_prop)
  have hDi (a : A) : Integrable (fun x : E => ‖fderiv ℝ (H a) x‖) μ :=
    continuous_integrable _ (by exact ((hH a).continuous_fderiv (by norm_num)).norm)
  have hgb : (∫ z : E × E, ∑ a, |H a z.1-H a z.2| ∂(μ).prod μ)≤(Real.pi/2)*K := by
    rw [integral_finsetSum _ (fun a _ => hHd a)]
    calc
      _ ≤ ∑ a, (Real.pi/2)*(∫ x : E, ‖fderiv ℝ (H a) x‖ ∂μ) :=
        Finset.sum_le_sum (fun a _ => CubePoincare.cube_first_moment (H a) (hH a))
      _ = (Real.pi/2)*(∫ x : E, ∑ a, ‖fderiv ℝ (H a) x‖ ∂μ) := by
        rw [integral_finsetSum _ (fun a _ => hDi a),Finset.mul_sum]
      _ ≤ (Real.pi/2)*K := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          _ ≤ ∫ _x : E, K ∂μ := integral_mono_ae (integrable_finsetSum _ (fun a _ => hDi a)) (integrable_const K) hg
          _ = _ := by simp
  have hep : ∀ᵐ z : E × E ∂(μ).prod μ,
      (∑ a, |H a z.1-f a z.1|≤B) ∧ (∑ a, |H a z.2-f a z.2|≤B) := by
    have hem : Measurable (fun x : E => ∑ a, |H a x-f a x|) :=
      Finset.measurable_sum _ (fun a _ => ((hH a).continuous.measurable.sub (hf a)).abs)
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_le (hem.comp measurable_fst) measurable_const).inter
        (measurableSet_le (hem.comp measurable_snd) measurable_const))).mpr
    filter_upwards [he] with x hx
    filter_upwards [he] with y hy
    exact ⟨hx,hy⟩
  have hpoint : ∀ᵐ z : E × E ∂(μ).prod μ, (∑ a, |f a z.1-f a z.2|)≤2*B+∑ a, |H a z.1-H a z.2| := by
    filter_upwards [hep] with z hz
    have hle (a : A) : |f a z.1-f a z.2|≤|H a z.1-f a z.1|+|H a z.1-H a z.2|+|H a z.2-f a z.2| := by
      calc
        _ = |-(H a z.1-f a z.1)+(H a z.1-H a z.2)+(H a z.2-f a z.2)| := by congr 1; ring
        _ ≤ _ := by simpa only [abs_neg] using (abs_add_three (-(H a z.1-f a z.1)) (H a z.1-H a z.2) (H a z.2-f a z.2))
    have hh := Finset.sum_le_sum (fun a (_ : a∈(Finset.univ : Finset A)) => hle a)
    simp only [Finset.sum_add_distrib] at hh
    linarith [hz.1,hz.2]
  have hfinal := integral_mono_ae (integrable_finsetSum _ (fun a _ => hfdi a))
    ((integrable_const (2*B)).add (integrable_finsetSum _ (fun a _ => hHd a))) hpoint
  simp only [Pi.add_apply] at hfinal
  have hadd := integral_add (show Integrable (fun _ : E × E => 2*B) ((μ).prod μ) from integrable_const _)
    (integrable_finsetSum Finset.univ (fun a _ => hHd a))
  rw [hadd] at hfinal
  simpa using hfinal.trans (add_le_add le_rfl hgb)
end
end UniformSparsestCut.CubeTransfer

namespace UniformSparsestCut.ContractionAverage
open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m N S : ℕ} {A : Type u2} [Fintype A]
local notation "E" => EuclideanSpace ℝ (Fin (m+1))
local notation "μ" => CubePoincare.cube (m := m+1)
open ContractionCore

lemma average (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0)
    (hnp : ∀ s i j, i≠j → ∀ t : ℝ, u s i≠t • u s j) (hn : ∀ s i, ‖u s i‖≤2)
    {τ lam δ R J G : ℝ} (hτ : 0<τ) (hlam : 0<lam) (hlam1 : lam<1)
    (hδ : 0≤δ) (hJ : 0≤J) (hG : 0≤G)
    (F : RoundedCharts.Vertex u τ → A → ℝ) {M : ℝ} (hM : 0≤M) (hbound : ∀ v a, |F v a|≤M)
    (hclose : ∀ s t x (hx : x∈RoundedCharts.cube 2)
      (hs : RoundedCharts.regular (u s) τ x) (ht : RoundedCharts.regular (u t) τ x),
      ∑ a, |F (vertex u τ s x hx hs) a-F (vertex u τ t x hx ht) a|≤R)
    (hmacro : ∀ s x y (hx : x∈RoundedCharts.cube 2) (hy : y∈RoundedCharts.cube 2)
      (hs : RoundedCharts.regular (u s) τ x) (ht : RoundedCharts.regular (u s) τ y),
      ∑ a, |F (vertex u τ s x hx hs) a-F (vertex u τ s y hy ht) a|≤G*‖x-y‖+R)
    (hjump : ∀ (vp vm : RoundedCharts.Vertex u τ) (i : Fin N), vp.val.1=vm.val.1 →
      vp.val.2 i=vm.val.2 i+1 → (∀ j, j≠i → vp.val.2 j=vm.val.2 j) → ∑ a, |F vp a-F vm a|≤J)
    (hsmall : ∀ s i, τ/|u s i 0| *KernelGeometry.L lam≤1)
    (hgood : ∀ D : StrongDual ℝ E, ∃ good : Finset (Fin S), (S:ℝ)/2≤good.card ∧
      ∀ s∈good, ∀ i, |D (u s i)|≤δ*‖D‖)
    (s0 : Fin S) :
    (∫ z : E × E, ∑ a, |ConcreteCells.function u hu τ F s0 a z.1-
        ConcreteCells.function u hu τ F s0 a z.2| ∂(μ).prod μ)≤
      2*(G*(lam*Real.sqrt (m+1:ℕ))+R)+Real.pi*(δ*((N:ℝ)*(2*J/τ))+(m+1:ℕ)*R*KernelGeometry.L lam) := by
  let f : A → E → ℝ := ConcreteCells.function u hu τ F s0
  let H : A → E → ℝ := fun a => ConvolutionBounds.smooth (KernelGeometry.κ lam) (f a) volume
  have hc (a : A) : ContDiff ℝ 1 (H a) := by
    exact (KernelGeometry.compact hlam).contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ)
      ((KernelGeometry.smooth lam).of_le (by simp)) (ConcreteCells.function_integrable u hu τ F hM hbound s0 a)
  have he : ∀ᵐ x : E ∂μ, (∑ a, |H a x-f a x|)≤G*(lam*Real.sqrt (m+1:ℕ))+R := by
    have hr := CubeGeometry.cube_ac.ae_le (RoundedCharts.ae_regular (u s0) τ (by
      intro i h; exact hu s0 i (by rw [h]; rfl)))
    filter_upwards [CubeGeometry.cube_mem (m := m+1),hr] with x hx hrx
    exact smoothing_error u hu hτ hlam hlam1 hn hG F hM hbound hmacro s0 x (fun j => (hx j).le) hrx
  have hg : ∀ᵐ x : E ∂μ, (∑ a, ‖fderiv ℝ (H a) x‖)≤
      2*(δ*((N:ℝ)*(2*J/τ))+(m+1:ℕ)*R*KernelGeometry.L lam) := by
    filter_upwards [CubeGeometry.cube_mem (m := m+1)] with x hx
    exact gradient_bound u hu hnp hn hτ hlam hlam1 hδ hJ F hM hbound hclose hjump hsmall hgood s0 x (fun j => (hx j).le)
  have h := CubeTransfer.average_from_gradient f H (fun a => ConcreteCells.function_measurable u hu τ F s0 a)
    (fun a x => ConcreteCells.function_bounded u hu τ F hM hbound s0 a x) hc he hg
  convert h using 1 ; ring
end
end UniformSparsestCut.ContractionAverage

end

end OAI
