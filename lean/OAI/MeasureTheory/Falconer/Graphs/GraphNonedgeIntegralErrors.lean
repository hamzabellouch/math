import OAI.MeasureTheory.Falconer.Graphs.GraphActualNonedgeGeometry
import OAI.MeasureTheory.Falconer.Graphs.GraphEtaIntegratedNonedge
import OAI.MeasureTheory.Falconer.Graphs.GraphZIntegratedNonedge

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def graphPointIntegral (f : Plane × ℝ → ℂ) (v s : ℝ) (x y : Plane) : ℂ :=
  ∫ z : ℝ, ∫ η : Plane, Complex.exp (Complex.I*Complex.ofReal
    ((2:ℝ)^v*inner ℝ η (graphA z x+s • graphB z y)))*f (η,z)

def GraphNonedge (N : ℕ) (sig p s z₀ : ℝ) (e₀ v₀ w₀ : Plane) : Prop :=
  graphNonedgeThreshold N sig p < ‖graphA z₀ v₀+s • graphB z₀ w₀‖ ∨
    graphNonedgeThreshold N sig p < |inner ℝ e₀ (graphDerivative s v₀ w₀)|

theorem graphPointIntegral_nonedge_of_errors {f : Plane × ℝ → ℂ} {C : ℝ}
    (n N : ℕ) (sig v p s z₀ : ℝ) (x y v₀ w₀ e₀ : Plane)
    (hf : GraphDerivativeBound n f C (graphNonedgeDerivativeScale N sig (v-p)))
    (hs : tsupport f ⊆ graphAmplitudeCompact) (hC : 0 ≤ C)
    (herr : ∀ η z, f (η,z) ≠ 0 →
      ‖(graphA z x+s • graphB z y)-(graphA z₀ v₀+s • graphB z₀ w₀)‖ ≤ graphNonedgeThreshold N sig p/2 ∧
      |inner ℝ (graphNormalizedAxis η) (graphDerivative s x y)-
        inner ℝ e₀ (graphDerivative s v₀ w₀)| ≤ graphNonedgeThreshold N sig p/2)
    (hfail : GraphNonedge N sig p s z₀ e₀ v₀ w₀) :
    ‖graphPointIntegral f v s x y‖ ≤
      8*C*volume.real (Metric.closedBall (0:Plane) 8)*16^n*((2:ℝ)^N)^(-26*sig*(n:ℝ)) := by
  rcases hfail with hvec | hscalar
  · have hg : ∀ z : ℝ, (∃ η, f (η,z) ≠ 0) →
        ((2:ℝ)^v*graphNonedgeThreshold N sig p)/2 ≤ ‖((2:ℝ)^v) • (graphA z x+s • graphB z y)‖ := by
      intro z hz
      obtain ⟨η,hη⟩ := hz
      have he := graph_vector_nonedge_lower ((2:ℝ)^v) s z z₀ x y v₀ w₀ (by positivity)
        (herr η z hη).1 le_rfl hvec
      simpa only [norm_smul,innerSL_apply_norm] using he
    have hi := graph_eta_integrated_nonedge_bound n N sig v p s x y hf hs hC hg
    apply hi.trans
    have hp : (2:ℝ)^n ≤ 16^n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
  · have hg : ∀ η : Plane, (∃ z, f (η,z) ≠ 0) →
        ((2:ℝ)^v*graphNonedgeThreshold N sig p)/16 ≤ |(2:ℝ)^v*inner ℝ η (graphDerivative s x y)| := by
      intro η hη
      obtain ⟨z,hz⟩ := hη
      have hlo : (1:ℝ)/8 ≤ ‖η‖ := (hs (subset_closure hz)).2
      have hn : η ≠ 0 := norm_pos_iff.mp (by linarith)
      have he := graph_scalar_nonedge_lower ((2:ℝ)^v) s x y v₀ w₀ (graphNormalizedAxis η) e₀
        (by positivity) (by dsimp [graphNonedgeThreshold]; positivity) hlo (herr η z hz).2 le_rfl hscalar
      have hid : ‖η‖ • graphNormalizedAxis η = η := by
        rw [graphNormalizedAxis,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hn),one_smul]
      rwa [hid] at he
    have hi := graph_z_integrated_nonedge_bound n N sig v p s x y hf hs hC hg
    exact hi.trans_eq (by ring)

end PlanarFalconer

end OAI
