import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceC2Difference
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapJetStability
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapKernelCapture

namespace OAI

/-! Replacing an actual nondegenerate crosscap by its quadratic jet on a
smaller neighborhood, while creating no further singularities. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem quadratic_crosscap_preparation {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (b : Bool) (t₀ : ℝ)
    (hzero : surfaceDirection f b (0,t₀) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection f b) (0,t₀)))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (r : ℝ) (g : Base → ProjectionTarget 3), 0 < r ∧ r ≤ ρ ∧
      ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 (0 : Base)] surfaceTaylorTwo f ∧
      (∀ x, r ≤ ‖x‖ → g x = f x) ∧
      tsupport (g-f) ⊆ closedBall (0 : Base) (r/2) ∧
      ∀ x ∈ ball (0 : Base) r, (¬ Function.Injective (fderiv ℝ g x) ↔ x = 0) := by
  obtain ⟨r₀,δ₀,hr₀,hδ₀,hstable⟩ := crosscap_jet_stability hf b (0,t₀) hzero hreg
  have hv := crosscap_transverse_derivative_ne_zero hf b (0,t₀) hreg.1
  obtain ⟨δ₁,hδ₁,hcapture⟩ := kernel_capture_near (fderiv ℝ f 0) b t₀ hzero hv (half_pos hr₀)
  have hc : ContinuousAt (fderiv ℝ f) 0 := (hf.continuous_fderiv (by simp)).continuousAt
  have hevent : ∀ᶠ x in 𝓝 (0 : Base), ‖fderiv ℝ f x-fderiv ℝ f 0‖ < δ₁/2 := by
    simpa only [mem_ball,dist_eq_norm] using hc.eventually (ball_mem_nhds _ (half_pos hδ₁))
  obtain ⟨η,hη,hnear⟩ := Metric.eventually_nhds_iff.mp hevent
  let r := min ρ (min η (r₀/2))
  have hr : 0 < r := lt_min hρ (lt_min hη (half_pos hr₀))
  have hrη : r ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hrr₀ : r ≤ r₀/2 := (min_le_right _ _).trans (min_le_right _ _)
  let ε := min δ₀ (δ₁/4)
  have hε : 0 < ε := lt_min hδ₀ (by positivity)
  obtain ⟨g,hg,hgerm,houtside,hsupport,hC2⟩ := exists_local_quadratic_replacement hf hε hr
  have hfix : fderiv ℝ g 0 = fderiv ℝ f 0 := by
    rw [hgerm.fderiv_eq,surfaceTaylorTwo_fderiv hf]
    simp
  have hest := surface_C2_difference hf hg hC2
  have hnear' : ∀ x ∈ ball (0 : Base) r₀,
      ‖fderiv ℝ g x-fderiv ℝ f x‖ ≤ δ₀ ∧
      ‖fderiv ℝ (fderiv ℝ g) x-fderiv ℝ (fderiv ℝ f) x‖ ≤ δ₀ := by
    intro x _
    exact ⟨(hest x).1.trans (min_le_left _ _),(hest x).2.trans (min_le_left _ _)⟩
  have hisolated := hstable g hg hfix hnear'
  refine ⟨r,g,hr,min_le_left _ _,hg,hgerm,houtside,hsupport,?_⟩
  intro x hx
  constructor
  · intro hbad
    have hxη : dist x 0 < η := (mem_ball.mp hx).trans_le hrη
    have hclose : ‖fderiv ℝ g x-fderiv ℝ f 0‖ < δ₁ := by
      calc
        _ ≤ ‖fderiv ℝ g x-fderiv ℝ f x‖+‖fderiv ℝ f x-fderiv ℝ f 0‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < ε+δ₁/2 := add_lt_add_of_le_of_lt (hest x).1 (hnear hxη)
        _ < δ₁ := by have he := min_le_right δ₀ (δ₁/4); dsimp [ε]; linarith
    obtain ⟨t,ht,hker⟩ := hcapture (fderiv ℝ g x) hclose hbad
    have hball : (x,t) ∈ ball ((0 : Base),t₀) r₀ := by
      rw [mem_ball,dist_eq_norm,Prod.norm_def]
      apply max_lt
      · have hn : ‖x‖ < r₀/2 := by simpa only [dist_zero_right] using (mem_ball.mp hx).trans_le hrr₀
        simp only [Prod.fst_sub,sub_zero]
        linarith
      · change |t-t₀| < r₀
        linarith
    exact congrArg Prod.fst ((hisolated (x,t) hball).mp hker)
  · rintro rfl hI
    have hz : fderiv ℝ g 0 (tangentRay b t₀) = fderiv ℝ g 0 0 := by
      rw [hfix,map_zero]
      exact hzero
    exact tangentRay_ne_zero b t₀ (hI hz)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
