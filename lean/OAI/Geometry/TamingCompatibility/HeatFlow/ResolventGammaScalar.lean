import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeSpectralHeat

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization MeasureTheory Set
open scoped Manifold ContDiff RealInnerProductSpace

def hodgeGammaWeight (s : ℝ) : ℝ := Real.exp (-s) * s^5

lemma hodgeGammaWeight_continuous : Continuous hodgeGammaWeight :=
  continuous_id.neg.rexp.mul (continuous_id.pow 5)

lemma hodgeGammaWeight_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ hodgeGammaWeight s := by
  exact mul_nonneg (Real.exp_pos _).le (pow_nonneg hs _)

lemma hodgeGammaWeight_integrable : IntegrableOn hodgeGammaWeight (Ioi 0) := by
  convert Real.GammaIntegral_convergent (s := 6) (by norm_num) using 1
  funext s
  simp only [hodgeGammaWeight, show (6:ℝ)-1 = 5 by norm_num, Real.rpow_ofNat]

lemma hodgeGammaWeight_laplace (r z : ℝ) (hz : 0 ≤ z) :
    ∫ s : ℝ in Ioi 0, hodgeGammaWeight s * Real.exp (-(r^2*s)*z) =
      120 * (1/(1+r^2*z))^6 := by
  have hp : 0 < 1+r^2*z := by positivity
  have hg : Real.Gamma 6 = 120 := by norm_num
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a:=6) (r:=1+r^2*z) (by norm_num) hp
  have he : (fun s : ℝ => hodgeGammaWeight s * Real.exp (-(r^2*s)*z)) =
      (fun s : ℝ => s^(5:ℕ) * Real.exp (-((1+r^2*z)*s))) := by
    funext s
    unfold hodgeGammaWeight
    rw [mul_comm (Real.exp (-s)) (s^5), mul_assoc, ← Real.exp_add]
    congr 1
    ring_nf
  rw [he]
  norm_num only [show (6:ℝ)-1 = 5 by norm_num, Real.rpow_ofNat, hg] at h
  exact h.trans (mul_comm _ _)

lemma hodgeGammaWeight_integral : ∫ s : ℝ in Ioi 0, hodgeGammaWeight s = 120 := by
  simpa only [mul_zero, Real.exp_zero, mul_one, add_zero, div_one, one_pow] using
    hodgeGammaWeight_laplace 0 0 le_rfl
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma hodgeHeatGamma_integrable (r : ℝ) (f : L2 A J α hs ht true) :
    IntegrableOn (fun s : ℝ => hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f)
      (Ioi 0) := by
  have hc : Continuous (fun s : ℝ => hodgeGammaWeight s •
      hodgeSpectralHeat A J α hs ht D hD (r^2*s) f) := hodgeGammaWeight_continuous.smul
    ((hodgeSpectralHeat_continuous A J α hs ht D hD f).comp
      (continuous_const.mul continuous_id))
  apply (hodgeGammaWeight_integrable.mul_const ‖f‖).mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hsp
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hodgeGammaWeight_nonneg hsp.le)]
  exact mul_le_mul_of_nonneg_left (hodgeSpectralHeat_norm_le A J α hs ht D hD _ f)
    (hodgeGammaWeight_nonneg hsp.le)

def hodgeHeatGammaLinear (r : ℝ) : L2 A J α hs ht true →ₗ[ℝ] L2 A J α hs ht true where
  toFun f := ∫ s : ℝ in Ioi 0, hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f
  map_add' f g := by
    simp only [map_add, smul_add]
    exact integral_add (hodgeHeatGamma_integrable A J α hs ht D hD r f)
      (hodgeHeatGamma_integrable A J α hs ht D hD r g)
  map_smul' c f := by
    simp only [map_smul, RingHom.id_apply, smul_comm (hodgeGammaWeight _) c]
    exact integral_smul c _

lemma hodgeHeatGammaLinear_norm_le (r : ℝ) (f : L2 A J α hs ht true) :
    ‖hodgeHeatGammaLinear A J α hs ht D hD r f‖ ≤ 120 * ‖f‖ := by
  calc
    _ ≤ ∫ s : ℝ in Ioi 0, ‖hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s : ℝ in Ioi 0, hodgeGammaWeight s * ‖f‖ := by
      apply integral_mono_ae (hodgeHeatGamma_integrable A J α hs ht D hD r f).norm
        (hodgeGammaWeight_integrable.mul_const ‖f‖)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hsp
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hodgeGammaWeight_nonneg hsp.le)]
      exact mul_le_mul_of_nonneg_left (hodgeSpectralHeat_norm_le A J α hs ht D hD _ f)
        (hodgeGammaWeight_nonneg hsp.le)
    _ = 120 * ‖f‖ := by rw [integral_mul_const, hodgeGammaWeight_integral]

def hodgeHeatGamma (r : ℝ) : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  (hodgeHeatGammaLinear A J α hs ht D hD r).mkContinuous 120
    (hodgeHeatGammaLinear_norm_le A J α hs ht D hD r)

lemma hodgeHeatGamma_eigenvector (r : ℝ)
    (x : ℝ) (f : L2 A J α hs ht true) (hf : f ≠ 0)
    (hx : hodgeResolvent A J α hs ht 1 f = x • f) :
    hodgeHeatGamma A J α hs ht D hD r f =
      (120 * (x/(r^2+(1-r^2)*x))^6) • f := by
  obtain ⟨hx0,hx1⟩ := hodgeResolvent_eigenvalue_positive_le_one A J α hs ht f hf x hx
  have hxinv : 1 ≤ x⁻¹ := (one_le_inv₀ hx0).mpr hx1
  have hrate : hodgeSpectralRate x = x⁻¹-1 := max_eq_right (sub_nonneg.mpr hxinv)
  have he : (∫ s : ℝ in Ioi 0,
      hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f) =
      (∫ s : ℝ in Ioi 0, hodgeGammaWeight s * Real.exp (-(r^2*s)*hodgeSpectralRate x)) • f := by
    rw [← integral_smul_const]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hsp
    dsimp only
    rw [hodgeSpectralHeat_eigenvector A J α hs ht D hD _ x f hx]
    simp only [hodgeHeatMultiplier, max_eq_left (mul_nonneg (sq_nonneg r) hsp.le), smul_smul]
  change (∫ s : ℝ in Ioi 0, hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f) = _
  rw [he, hodgeGammaWeight_laplace r (hodgeSpectralRate x) (le_max_left 0 (x⁻¹-1))]
  have hd : r^2+(1-r^2)*x ≠ 0 := by
    have hp := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hx1)
    apply ne_of_gt
    nlinarith
  have hz := ne_of_gt (show 0 < 1+r^2*hodgeSpectralRate x by
    have hp := mul_nonneg (sq_nonneg r) (le_max_left 0 (x⁻¹-1)); dsimp [hodgeSpectralRate]; linarith)
  have heq : 1/(1+r^2*hodgeSpectralRate x) = x/(r^2+(1-r^2)*x) := by
    rw [hrate] at hz ⊢
    field_simp [ne_of_gt hx0, hd, hz]
    ring
  rw [heq]

lemma hodgeHeatGamma_eq_sixth_power (r : ℝ) (hr : 0 < r) :
    hodgeHeatGamma A J α hs ht D hD r = (120 : ℝ) • (hodgeRegularization A J α hs ht r ^ 2) := by
  let L := hodgeHeatGamma A J α hs ht D hD r - (120 : ℝ) • (hodgeRegularization A J α hs ht r ^ 2)
  have hi : (⨆ x : ℝ, Module.End.eigenspace
      (hodgeResolvent A J α hs ht 1).toLinearMap x) ≤ L.ker := by
    apply iSup_le
    intro x f hf
    have hx := Module.End.mem_eigenspace_iff.mp hf
    change L f = 0
    by_cases hzero : f = 0
    · subst f; exact map_zero L
    · obtain ⟨hx0,hx1⟩ := hodgeResolvent_eigenvalue_positive_le_one A J α hs ht f hzero x hx
      dsimp [L]
      rw [sub_apply, smul_apply,
        hodgeHeatGamma_eigenvector A J α hs ht D hD r x f hzero hx,
        hodgeRegularization_sq_eigenvector A J α hs ht r hr f x hx0.le hx1 hx,
        smul_smul, sub_self]
  have hcl : (⨆ x : ℝ, Module.End.eigenspace
      (hodgeResolvent A J α hs ht 1).toLinearMap x).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure,
      hodgeResolvent_eigenspaces_total A J α hs ht D hD]
    simp
  have htop : ⊤ ≤ L.ker := by
    rw [← hcl]
    exact Submodule.topologicalClosure_minimal _ hi (ContinuousLinearMap.isClosed_ker L)
  ext f
  have hf : L f = 0 := htop (Submodule.mem_top)
  exact sub_eq_zero.mp hf

lemma hodgeRegularization_sq_eq_heat_integral (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true) :
    (hodgeRegularization A J α hs ht r ^ 2) f = (1/120 : ℝ) •
      (∫ s : ℝ in Ioi 0,
        hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f) := by
  have he := congrArg (fun T : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true => T f)
    (hodgeHeatGamma_eq_sixth_power A J α hs ht D hD r hr)
  change (∫ s : ℝ in Ioi 0,
    hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f) =
      (120 : ℝ) • (hodgeRegularization A J α hs ht r ^ 2) f at he
  rw [he, smul_smul]
  norm_num

end TamingCompatibility.GeometricHilbert

end

end OAI
