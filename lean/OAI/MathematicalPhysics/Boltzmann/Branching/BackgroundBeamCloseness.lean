import OAI.MathematicalPhysics.Boltzmann.Approximation.CapFiniteBackgroundLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.BackgroundCappedLoss
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricMesh

namespace OAI

section

/-! # The selected mesh scale stays close to the center of a small transverse window -/

noncomputable section

namespace BoltzmannNonuniqueness.GeometricBackground

theorem scale_ratio_error {r ρ μ δ h : ℝ} (_hr : 0 < r) (hμ : 0 < μ)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hh : 0 ≤ h)
    (hwindow : |ρ-r| ≤ δ*r) (hlo : μ ≤ ρ) (hhi : ρ ≤ (1+h)*μ) :
    |r/μ-1| ≤ (h+δ)/(1-δ) := by
  have hw := abs_le.mp hwindow
  have hd : 0 < 1-δ := sub_pos.mpr hδ1
  have hp : 0 < 1+δ := by positivity
  have hlow : 1/(1+δ) ≤ r/μ := (div_le_div_iff₀ hp hμ).mpr (by nlinarith)
  have hone : 1-δ ≤ 1/(1+δ) := (le_div_iff₀ hp).mpr (by nlinarith [sq_nonneg δ])
  have hupp : r/μ ≤ (1+h)/(1-δ) := (div_le_div_iff₀ hμ hd).mpr (by nlinarith)
  have he : (1+h)/(1-δ)-1 = (h+δ)/(1-δ) := by field_simp; ring
  have hQ : δ ≤ (h+δ)/(1-δ) := (le_div_iff₀ hd).mpr (by nlinarith [sq_nonneg δ])
  apply abs_le.mpr
  constructor
  · linarith
  · linarith

theorem selected_scale_ratio_error {θ η r δ : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hr : 0 < r) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (y : VelocityWeight.Transverse) (hy : 0 < ‖y‖) (hwindow : |‖y‖-r| ≤ δ*r) :
    |r/scale θ η y-1| ≤ (Real.exp η-1+δ)/(1-δ) := by
  have hb := GeometricMesh.cell_bounds hθ hη hy
  apply scale_ratio_error hr (scale_pos hθ η y) hδ hδ1
    (sub_nonneg.mpr (Real.one_le_exp hη.le)) hwindow hb.1
  simpa only [scale,add_sub_cancel] using hb.2.le

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Bounded background velocity averages on positive-time slabs -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.background_average_slab_bound (E : HotLimitExtraction S)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) {a t B : ℝ} (ha : 0 < a) (ht : a ≤ t)
    {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B) (x : JetPrototype.Space) :
    |∫ v, ψ v ∂E.background t x| ≤ 2*((1/4)*((K*max 1 (α*γ)⁻¹)/a))*B := by
  classical
  have hB : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hψB 0)
  have hp : 0 < E.phase := zero_lt_one.trans_le E.phase_mem.1
  have hc : 0 ≤ K*max 1 (α*γ)⁻¹ := mul_nonneg hK (le_max_of_le_left zero_le_one)
  by_cases hx : GeometricBackground.active E.phase η E.fraction x.1
  · rw [background,GeometricBackground.background,ite_eq_left hx]
    apply (AxialBackground.integral_cell_abs_le hK hα hγ
      (GeometricBackground.scale_pos hp η x.1) (ha.trans_le ht).le x.2 ψ
      (fun v _ => hψB v)).trans
    apply mul_le_mul_of_nonneg_right _ hB
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact div_le_div_of_nonneg_left hc ha
      (ht.trans (le_add_of_nonneg_left (GeometricBackground.scale_pos hp η x.1).le))
  · rw [background,GeometricBackground.background,ite_eq_right hx,integral_zero_measure,abs_zero]
    positivity

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Quantitative closeness of the actual compressed beam density -/

noncomputable section

open Set
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.AxialBackground

theorem axial_weight_close_to_one {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| ≤ δ → 1-S x ≤ ε := by
  have hcont : ContinuousAt S 0 := continuous_S.continuousAt
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hcont ε hε
  refine ⟨δ/2,by positivity,fun x hx => ?_⟩
  have hdist : dist x 0 < δ := by
    simpa only [Real.dist_eq,sub_zero] using hx.trans_lt (half_lt_self hδ)
  have hh := hclose hdist
  have hzero : S 0 = 1 := by simp [S]
  rw [hzero,Real.dist_eq] at hh
  have hlow := (abs_lt.mp hh).1
  linarith

theorem beam_argument_bound {r μ α γ t C σ z : ℝ} (_hr : 0 < r) (hμ : 0 < μ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (hC : 0 ≤ C)
    (htC : t ≤ C*r) (hzC : |z| ≤ C*r) (hR : r/μ ≤ 2) (hσ : |σ| = 1) :
    |γ*AxialFlow.foot σ α γ μ t z/μ| ≤ 6*C*γ ∧ t*α*γ/μ ≤ 2*C*γ := by
  have hrμ : r ≤ 2*μ := (div_le_iff₀ hμ).mp hR
  have hf := foot_abs_bound hα ht σ γ μ z
  rw [hσ] at hf
  have hfoot : |AxialFlow.foot σ α γ μ t z| ≤ 3*C*r := by
    have htα : t*(1+α) ≤ 2*t := by nlinarith
    linarith
  constructor
  · rw [abs_div,abs_mul,abs_of_nonneg hγ,abs_of_pos hμ]
    apply (div_le_iff₀ hμ).mpr
    calc
      γ*|AxialFlow.foot σ α γ μ t z| ≤ γ*(3*C*r) := mul_le_mul_of_nonneg_left hfoot hγ
      _ ≤ γ*(3*C*(2*μ)) := by gcongr
      _ = _ := by ring
  · apply (div_le_iff₀ hμ).mpr
    have hta : t*α ≤ t := mul_le_of_le_one_right ht hα1
    calc
      t*α*γ ≤ t*γ := mul_le_mul_of_nonneg_right hta hγ
      _ ≤ (C*r)*γ := mul_le_mul_of_nonneg_right htC hγ
      _ ≤ (C*(2*μ))*γ := by gcongr
      _ = _ := by ring

theorem relativeWeight_close {r μ α γ t ε : ℝ} (hr : 0 ≤ r) (hμ : 0 < μ)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (_hε : 0 ≤ ε)
    (hR : r/μ ≤ 2) (hmesh : |r/μ-1| ≤ ε/5) (σ z : ℝ)
    (hS : 1-S (γ*AxialFlow.foot σ α γ μ t z/μ) ≤ ε/5)
    (hc : t*α*γ/μ ≤ ε/5) : |relativeWeight r α γ μ t σ z-1| ≤ ε := by
  have hh := relativeWeight_error hr hμ hα hγ ht σ z
  have hs0 : 0 ≤ 1-S (γ*AxialFlow.foot σ α γ μ t z/μ) := sub_nonneg.mpr (S_le_one _)
  have hc0 : 0 ≤ t*α*γ/μ := by positivity
  have hbound : (r/μ)*(1-S (γ*AxialFlow.foot σ α γ μ t z/μ)+t*α*γ/μ) ≤
      2*(ε/5+ε/5) := mul_le_mul hR (add_le_add hS hc) (add_nonneg hs0 hc0) (by norm_num)
  linarith

end BoltzmannNonuniqueness.AxialBackground

end

end

end OAI
