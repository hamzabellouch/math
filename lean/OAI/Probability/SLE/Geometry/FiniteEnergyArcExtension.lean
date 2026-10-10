import OAI.Probability.SLE.Geometry.ComplexAngularEnergy

namespace OAI

/-! An angular section with finite derivative energy has a continuous
extension to both endpoints. The construction is its actual integral primitive. -/
noncomputable section
open Set Filter Metric Function MeasureTheory
open scoped Topology ENNReal

namespace SLEExactGauge

lemma finite_energy_angular_extension {f : ℝ → ℂ}
    (hf : ∀ θ∈Ioo 0 Real.pi, DifferentiableAt ℝ f θ)
    (hd : MemLp (deriv f) 2 (volume.restrict (Ioo 0 Real.pi))) :
    ∃ F : ℝ → ℂ, Continuous F ∧ EqOn F f (Ioo 0 Real.pi) := by
  let a := Real.pi/2
  have ha : a∈Ioo 0 Real.pi := ⟨half_pos Real.pi_pos,by dsimp [a]; linarith [Real.pi_pos]⟩
  let g := (Ioo 0 Real.pi).indicator (deriv f)
  have hi : Integrable g volume := (integrable_indicator_iff measurableSet_Ioo).mpr
    (hd.integrable (by norm_num))
  refine ⟨fun θ => f a + ∫ s in a..θ, g s,
    continuous_const.add (hi.continuous_primitive a),?_⟩
  intro θ hθ
  have hs : uIcc a θ⊆Ioo 0 Real.pi := ordConnected_Ioo.uIcc_subset ha hθ
  have hi' : IntegrableOn (deriv f) (Ioo 0 Real.pi) := hd.integrable (by norm_num)
  have hid : IntervalIntegrable (deriv f) volume a θ := intervalIntegrable_iff.mpr
    (hi'.mono_set (uIoc_subset_uIcc.trans hs))
  have he : (∫ s in a..θ, g s)=∫ s in a..θ, deriv f s :=
    intervalIntegral.integral_congr (fun s hs' => indicator_of_mem (hs hs') _)
  change f a + (∫ s in a..θ, g s)=f θ
  rw [he,intervalIntegral.integral_deriv_eq_sub (fun s hs' => hf s (hs hs')) hid]
  exact add_sub_cancel _ _

lemma continuous_angular_oscillation_on_endpoints {F : ℝ → ℂ}
    (hF : Continuous F) (ε : ℝ)
    (hsmall : ∀ θ∈Ioo 0 Real.pi, ∀ φ∈Ioo 0 Real.pi, ‖F θ-F φ‖≤ε) :
    ∀ θ∈Icc 0 Real.pi, ∀ φ∈Icc 0 Real.pi, ‖F θ-F φ‖≤ε := by
  have hc : IsClosed {p : ℝ×ℝ | ‖F p.1-F p.2‖≤ε} :=
    isClosed_le ((hF.comp continuous_fst).sub (hF.comp continuous_snd)).norm continuous_const
  have hs : (Ioo (0:ℝ) Real.pi) ×ˢ (Ioo (0:ℝ) Real.pi)⊆
      {p : ℝ×ℝ | ‖F p.1-F p.2‖≤ε} := fun p hp => hsmall p.1 hp.1 p.2 hp.2
  have hcl := hc.closure_subset_iff.mpr hs
  rw [closure_prod_eq,closure_Ioo (ne_of_lt Real.pi_pos)] at hcl
  intro θ hθ φ hφ
  exact hcl (show (θ,φ)∈(Icc 0 Real.pi) ×ˢ (Icc 0 Real.pi) from ⟨hθ,hφ⟩)

end SLEExactGauge

end

end OAI
