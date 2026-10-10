import OAI.Geometry.Perimeter.Regularity.GeometricHolder
import OAI.Geometry.Perimeter.Regularity.EllipticSecantBounds

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack

 theorem GeometricHolderAt.comp_lipschitz {X V W : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace V] [PseudoMetricSpace W] {θ : ℝ} (hθ : 0 ≤ θ)
    {f : X → V} {g : V → W} {p : X} (hf : GeometricHolderAt θ f p)
    (hc : ContinuousAt f p) {s L : ℝ} (hs : 0<s) (hL : 0 ≤ L)
    (hg : ∀ x∈Metric.ball (f p) s, ∀ y∈Metric.ball (f p) s,
      dist (g x) (g y) ≤ L*dist x y) : GeometricHolderAt θ (fun x ↦ g (f x)) p := by
  obtain ⟨r,C,hr,hC,hf⟩ := hf
  obtain ⟨b,hb,hbim⟩ := Metric.continuousAt_iff.mp hc s hs
  refine ⟨min r b,L*C,lt_min hr hb,mul_nonneg hL hC,fun j x hx y hy hxy ↦ ?_⟩
  have him {z : X} (hz : z∈Metric.ball p (min r b)) : f z∈Metric.ball (f p) s :=
    Metric.mem_ball.mpr (hbim ((Metric.mem_ball.mp hz).trans_le (min_le_right _ _)))
  apply (hg _ (him hx) _ (him hy)).trans
  have hh := hf j x (Metric.ball_subset_ball (min_le_left _ _) hx) y
    (Metric.ball_subset_ball (min_le_left _ _) hy)
    (hxy.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (pow_nonneg hθ j)))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hL

 theorem GeometricHolderAt.comp_C1 {X V W : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {θ : ℝ} (hθ : 0 ≤ θ) {f : X → V} {g : V → W} {p : X}
    (hf : GeometricHolderAt θ f p) (hc : ContinuousAt f p) (hg : ContDiff ℝ 1 g) :
    GeometricHolderAt θ (fun x ↦ g (f x)) p := by
  obtain ⟨r,L,hr,hL,h⟩ := contDiff_local_lipschitz hg (f p)
  exact hf.comp_lipschitz hθ hc hr hL (fun x hx y hy ↦ by
    simpa only [dist_eq_norm] using h x hx y hy)

 theorem GeometricHolderAt.pi {ι X V : Type*} [Fintype ι] [PseudoMetricSpace X]
    [NormedAddCommGroup V] {θ : ℝ} (hθ : 0 ≤ θ) {f : X → ι → V} {p : X}
    (h : ∀ i, GeometricHolderAt θ (fun x ↦ f x i) p) :
    GeometricHolderAt θ f p := by
  classical
  have hall (s : Finset ι) : ∃ r C : ℝ, 0<r ∧ 0 ≤ C ∧
      ∀ i∈s, ∀ j x, x∈Metric.ball p r → ∀ y, y∈Metric.ball p r →
        dist x y ≤ θ^j*r → dist (f x i) (f y i) ≤ C*(1/2)^j := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,0,by norm_num,le_rfl,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨r,C,hr,hC,hs⟩ := ih
      obtain ⟨b,D,hb,hD,hi⟩ := h i
      refine ⟨min r b,max C D,lt_min hr hb,hC.trans (le_max_left _ _),?_⟩
      intro k hk j x hx y hy hxy
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact (hi j x (Metric.ball_subset_ball (min_le_right _ _) hx) y
          (Metric.ball_subset_ball (min_le_right _ _) hy)
          (hxy.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (pow_nonneg hθ j)))).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      · exact (hs k hk j x (Metric.ball_subset_ball (min_le_left _ _) hx) y
          (Metric.ball_subset_ball (min_le_left _ _) hy)
          (hxy.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (pow_nonneg hθ j)))).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  obtain ⟨r,C,hr,hC,hh⟩ := hall Finset.univ
  refine ⟨r,C,hr,hC,fun j x hx y hy hxy ↦ ?_⟩
  exact (dist_pi_le_iff (by positivity)).mpr (fun i ↦ hh i (Finset.mem_univ _) j x hx y hy hxy)

 theorem GeometricHolderAt.clm_apply_iff {X V W : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {θ : ℝ} (hθ : 0 ≤ θ)
    {f : X → V →L[ℝ] W} {p : X} (hc : ContinuousAt f p) :
    GeometricHolderAt θ f p ↔ ∀ e, GeometricHolderAt θ (fun x ↦ f x e) p := by
  constructor
  · intro h e
    exact h.comp_C1 hθ hc (ContinuousLinearMap.apply ℝ W e).contDiff
  · intro h
    let d := Module.finrank ℝ V
    have hd : d=Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
    let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
    let e₂ := (e₁.arrowCongr (1 : W ≃L[ℝ] W)).trans (ContinuousLinearEquiv.piRing (Fin d))
    have hpi : GeometricHolderAt θ (fun x ↦ e₂ (f x)) p := GeometricHolderAt.pi hθ (fun i ↦ h _)
    have hh := hpi.comp_C1 hθ (e₂.continuous.continuousAt.comp hc) e₂.symm.contDiff
    simpa only [e₂.symm_apply_apply] using hh

end RPISingularHarnack

end

end OAI
