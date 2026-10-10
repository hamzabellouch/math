import OAI.Geometry.RCD.Sobolev.DifferentiableMeanRemainder

namespace OAI

/-! # Directional derivatives recovered from translated shrinking probability laws -/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem translated_mean_derivative {n : ℕ} {g : Euclidean n → ℝ}
    (hg : Continuous g) {D : Euclidean n →L[ℝ] ℝ} {x : Euclidean n}
    (hd : HasFDerivAt g D x) {A : ℝ} (hA : 0≤A)
    (r : ℕ → ℝ) (hr : ∀ k, 0<r k) (hrlim : Tendsto r atTop (𝓝 0))
    (P : ℕ → ProbabilityMeasure (Euclidean n))
    (hs : ∀ k, ∀ᵐ y ∂(P k : Measure (Euclidean n)), dist y x≤A*r k)
    (v : Euclidean n) :
    Tendsto (fun k => ((∫ y, g y ∂((P k).map (fun y => y+r k • v) : Measure (Euclidean n)))-
      (∫ y, g y ∂(P k : Measure (Euclidean n))))/r k) atTop (𝓝 (D v)) := by
  let Q := fun k => (P k).map (fun y => y+r k • v)
  have hmap (k : ℕ) : Measurable (fun y : Euclidean n => y+r k • v) :=
    measurable_id.add_const _
  have hQs (k : ℕ) : ∀ᵐ y ∂(Q k : Measure (Euclidean n)), dist y x≤(A+‖v‖)*r k := by
    change ∀ᵐ y ∂(P k : Measure (Euclidean n)).map (fun y => y+r k • v), _
    apply (ae_map_iff (hmap k).aemeasurable measurableSet_closedBall).mpr
    filter_upwards [hs k] with y hy
    calc dist (y+r k • v) x ≤ dist (y+r k • v) y+dist y x := dist_triangle _ _ _
      _ ≤ r k*‖v‖+A*r k := by
        have he : dist (y+r k • v) y=r k*‖v‖ := by
          simp [dist_eq_norm,norm_smul,abs_of_pos (hr k)]
        rw [he]
        exact add_le_add_right hy _
      _ = (A+‖v‖)*r k := by ring
  let F := fun y => g y-g x-D (y-x)
  have hF : Continuous F := by dsimp only [F]; fun_prop
  have hP := differentiable_mean_remainder hd hA r hr hrlim P hs
  have hQ := differentiable_mean_remainder hd (add_nonneg hA (norm_nonneg v)) r hr hrlim Q hQs
  have hlim := (hQ.sub hP).add_const (D v)
  simp only [sub_self,zero_add] at hlim
  have hi (k : ℕ) (f : Euclidean n → ℝ) (hf : Continuous f) :
      Integrable f (P k : Measure (Euclidean n)) := by
    have hh := hf.continuousOn.integrableOn_compact
      (μ := (P k : Measure (Euclidean n))) (isCompact_closedBall x (A*r k))
    change Integrable f ((P k : Measure (Euclidean n)).restrict (closedBall x (A*r k))) at hh
    rw [Measure.restrict_eq_self_of_ae_mem (s := closedBall x (A*r k)) (hs k)] at hh
    exact hh
  have hident (k : ℕ) :
      ((∫ y, F y ∂(Q k : Measure (Euclidean n)))/r k-
        (∫ y, F y ∂(P k : Measure (Euclidean n)))/r k)+D v=
      ((∫ y, g y ∂(Q k : Measure (Euclidean n)))-
        (∫ y, g y ∂(P k : Measure (Euclidean n))))/r k := by
    have hc : Continuous (fun y => g (y+r k • v)-g y) := by fun_prop
    have hiF : Integrable (fun y => F (y+r k • v)) (P k : Measure (Euclidean n)) :=
      hi k _ (hF.comp (by fun_prop))
    have hig : Integrable (fun y => g (y+r k • v)) (P k : Measure (Euclidean n)) :=
      hi k _ (hg.comp (by fun_prop))
    have hpoint (y : Euclidean n) : F (y+r k • v)-F y=g (y+r k • v)-g y-r k*D v := by
      dsimp only [F]
      rw [show y+r k • v-x=(y-x)+r k • v by abel,map_add,map_smul]
      simp only [smul_eq_mul]
      ring
    have he : (∫ y, F y ∂(Q k : Measure (Euclidean n)))-
        (∫ y, F y ∂(P k : Measure (Euclidean n)))=
        (∫ y, g y ∂(Q k : Measure (Euclidean n)))-
          (∫ y, g y ∂(P k : Measure (Euclidean n)))-r k*D v := by
      rw [show (Q k : Measure (Euclidean n))=(P k : Measure (Euclidean n)).map
        (fun y => y+r k • v) from rfl,integral_map (hmap k).aemeasurable hF.aestronglyMeasurable]
      rw [← integral_sub hiF (hi k F hF)]
      simp_rw [hpoint]
      rw [integral_sub (hi k _ hc) (integrable_const _),
        integral_sub hig (hi k g hg),
        integral_const,smul_eq_mul]
      rw [integral_map (hmap k).aemeasurable hg.aestronglyMeasurable]
      simp
    rw [← sub_div,he]
    field_simp [(hr k).ne']
    ring
  exact hlim.congr' (Eventually.of_forall hident)

end RegularPointCoordinates

end

end OAI
