import OAI.Geometry.RCD.Harmonic.FirstOrderTransverseBarrier

namespace OAI

/-! # Positive inner mass of the transverse barrier -/

open Set Filter MeasureTheory Metric
open scoped InnerProductSpace NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem transverse_barrier_pointwise_lower {n : ℕ} (a z : Euclidean n)
    (ha : ‖a‖=1) {δ : ℝ} (hδ : 0<δ) (hz : ‖z‖≤δ/2) :
    δ^2/2≤(if -δ<⟪z,a⟫_ℝ then max (δ^2-(‖z‖^2-⟪z,a⟫_ℝ^2)) 0 else 0) := by
  have hw : |⟪z,a⟫_ℝ|≤δ/2 := by
    exact ((abs_real_inner_le_norm z a).trans_eq (by rw [ha,mul_one])).trans hz
  have hax : -δ<⟪z,a⟫_ℝ := by linarith [(abs_le.mp hw).1]
  rw [ite_eq_left hax]
  apply le_trans _ (le_max_left _ _)
  have hsq := (sq_le_sq₀ (norm_nonneg z) (by positivity : 0≤δ/2)).mpr hz
  nlinarith [sq_nonneg ⟪z,a⟫_ℝ]

theorem transverse_barrier_integral_lower {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {n : ℕ} (a : Euclidean n) (ha : ‖a‖=1) (v : X → Euclidean n)
    {Ω A : Set X} (hA : MeasurableSet A) (hsub : A⊆Ω) {δ : ℝ} (hδ : 0<δ)
    (hfin : μ A≠∞)
    (hI : IntegrableOn (fun x =>
      if -δ<⟪v x,a⟫_ℝ then max (δ^2-(‖v x‖^2-⟪v x,a⟫_ℝ^2)) 0 else 0) Ω μ)
    (hv : ∀ x∈A, ‖v x‖≤δ/2) :
    δ^2/2*μ.real A≤∫ x in Ω,
      (if -δ<⟪v x,a⟫_ℝ then max (δ^2-(‖v x‖^2-⟪v x,a⟫_ℝ^2)) 0 else 0) ∂μ := by
  let I x := if -δ<⟪v x,a⟫_ℝ then max (δ^2-(‖v x‖^2-⟪v x,a⟫_ℝ^2)) 0 else 0
  have hI0 (x : X) : 0≤I x := by dsimp [I]; split_ifs <;> positivity
  have hi : (∫ x in A, (δ^2/2:ℝ) ∂μ)≤∫ x in A, I x ∂μ := by
    have hcI : IntegrableOn (fun _ : X => (δ^2/2:ℝ)) A μ := integrableOn_const hfin
    apply integral_mono_ae hcI (hI.mono_set hsub)
    filter_upwards [ae_restrict_mem hA] with x hx
    exact transverse_barrier_pointwise_lower a (v x) ha hδ (hv x hx)
  have hm : (∫ x in A, I x ∂μ)≤∫ x in Ω, I x ∂μ :=
    setIntegral_mono_set hI (Eventually.of_forall hI0) (Eventually.of_forall hsub)
  have hres := hi.trans hm
  simpa only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_comm] using hres

end RegularPointCoordinates

end

end OAI
