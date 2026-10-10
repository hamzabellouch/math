import OAI.Geometry.Kahler.BaseCirclePowerLog

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma phaseAction_patch (k : ℕ) (R : ℝ) (p ξ : Sphere) (z : Circle) :
    phaseAction z ξ ∈ peakPatch k R p ↔ ξ ∈ peakPatch k R p := by
  change (Real.exp (-R/k) < ‖bracket ((z:ℂ) • (ξ:Base)) (p:Base)‖) ↔ _
  rw [circle_bracket_norm]
  rfl

lemma sigma_phase_average_restrict {V : Sphere → ℝ} (hV : Continuous V)
    {s : Set Sphere} (hs : MeasurableSet s)
    (hinv : ∀ (z : Circle) (ξ : Sphere), phaseAction z ξ ∈ s ↔ ξ ∈ s) :
    (∫ ξ in s, V ξ ∂sigma)=∫ ξ in s, ∫ z : Circle, V (phaseAction z ξ) ∂circleMeasure ∂sigma := by
  classical
  have hc : Continuous (fun p : Circle × Sphere => V (phaseAction p.1 p.2)) := hV.comp phaseAction_continuous
  have hi := (compact_continuous_integrable (μ := circleMeasure.prod sigma) hc).indicator (hs.preimage measurable_snd)
  have he : (fun p : Circle × Sphere => (Prod.snd ⁻¹' s).indicator (fun p => V (phaseAction p.1 p.2)) p)=
      fun p : Circle × Sphere => (s.indicator V) (phaseAction p.1 p.2) := by
    funext p
    simp only [indicator_apply,mem_preimage,hinv]
  change Integrable (fun p : Circle × Sphere => (Prod.snd ⁻¹' s).indicator (fun p => V (phaseAction p.1 p.2)) p) (circleMeasure.prod sigma) at hi
  rw [he] at hi
  have hunit : ∀ z : Circle, (∫ ξ, (s.indicator V) (phaseAction z ξ) ∂sigma)=∫ ξ, (s.indicator V) ξ ∂sigma := by
    intro z
    exact sigma_integral_unitary (phaseIsometry z z.norm_coe) (s.indicator V)
  have havg : (∫ ξ, (s.indicator V) ξ ∂sigma)= ∫ ξ, ∫ z : Circle, (s.indicator V) (phaseAction z ξ) ∂circleMeasure ∂sigma := by
    rw [← integral_integral_swap hi]
    simp_rw [hunit]
    simp
  have heinner : ∀ ξ : Sphere, (∫ z : Circle, (s.indicator V) (phaseAction z ξ) ∂circleMeasure)=
      s.indicator (fun ξ => ∫ z : Circle, V (phaseAction z ξ) ∂circleMeasure) ξ := by
    intro ξ
    by_cases hξ : ξ ∈ s
    · simp only [indicator_of_mem hξ]
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => indicator_of_mem ((hinv z ξ).mpr hξ) V)
    · rw [indicator_of_notMem hξ]
      apply integral_eq_zero_of_ae
      exact Eventually.of_forall (fun z => indicator_of_notMem (fun h => hξ ((hinv z ξ).mp h)) V)
  simp_rw [heinner] at havg
  simpa only [integral_indicator hs] using havg

lemma circle_regularized_shifted_moments {q ε : ℝ} (hq : 0 ≤ q) (hε : ε ≠ 0)
    {k : ℕ} (hk : 0 < k) (f : ℝ) (w : Circle) :
    (∫ z : Circle, regularizedLog 1 ε ((q:ℂ)*((z*w:Circle):ℂ)^k)*
      (1+f*(((z*w:Circle):ℂ)^k).re) ∂circleMeasure)=
    Real.log (logFactor q ε)-Real.log (1+ε^2)-f*q/logFactor q ε := by
  rw [integral_mul_right_eq_self (μ := circleMeasure) (fun z : Circle =>
    regularizedLog 1 ε ((q:ℂ)*(z:ℂ)^k)*(1+f*((z:ℂ)^k).re)) w]
  exact circle_regularized_power_moments hq hε hk f

lemma densityCorrection_constant_phase {k : ℕ} {R : ℝ} {f b : ℝ → ℝ} {p ξ : Sphere}
    (hpatch : ξ ∈ peakPatch k R p) (w : Circle)
    (hw : bracket (ξ:Base) (p:Base)=(‖bracket (ξ:Base) (p:Base)‖:ℂ)*(w:ℂ)) (z : Circle) :
    densityCorrection k R f b (fun _ => 1) p (phaseAction z ξ)=
    (‖bracket (ξ:Base) (p:Base)‖^2)⁻¹*f (densityHeight k p ξ)*(((z*w:Circle):ℂ)^k).re := by
  have hn : 0 < ‖bracket (ξ:Base) (p:Base)‖ := peakPatch_norm_pos hpatch
  have hnC : (‖bracket (ξ:Base) (p:Base)‖:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hder : ∀ x : Base, phaseDerivative (fun _ : Base => (1:ℝ)) x=0 := by
    intro x
    simp only [phaseDerivative,(hasFDerivAt_const (1:ℝ) x).fderiv,zero_apply]
  change densityCorrection k R f b (fun _ => 1) p ((z:ℂ) • (ξ:Base))=_
  have hpatch' : Real.exp (-R/k) < ‖bracket (ξ:Base) (p:Base)‖ := hpatch
  rw [densityCorrection,circle_bracket_norm,ite_eq_left hpatch']
  dsimp only [densityCorrectionRaw]
  rw [circle_bracket_norm,densityHeight_phase,hder]
  have hphase : bracket ((z:ℂ) • (ξ:Base)) (p:Base)/(‖bracket (ξ:Base) (p:Base)‖:ℂ)=((z*w:Circle):ℂ) := by
    rw [bracket_smul,Circle.coe_mul]
    nth_rw 1 [hw]
    field_simp
  rw [hphase]
  simp only [mul_one,mul_zero,zero_mul,sub_zero,mul_assoc]

lemma ideal_patch_phase_mean {a ε ρ : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ ρ) (hε : ε ≠ 0)
    {k : ℕ} (hk : 0 < k) {R : ℝ} (f b : ℝ → ℝ) {p ξ : Sphere}
    (hpatch : ξ ∈ peakPatch k R p) :
    (∫ z : Circle, regularizedLog a ε ((ρ:ℂ)*bracket (phaseAction z ξ : Base) (p:Base)^k)*
      (1+densityCorrection k R f b (fun _ => 1) p (phaseAction z ξ)) ∂circleMeasure)=
    Real.log (logFactor (a*ρ*‖bracket (ξ:Base) (p:Base)‖^k) ε)-Real.log (1+ε^2)-
      (‖bracket (ξ:Base) (p:Base)‖^2)⁻¹*f (densityHeight k p ξ)*
      (a*ρ*‖bracket (ξ:Base) (p:Base)‖^k)/logFactor (a*ρ*‖bracket (ξ:Base) (p:Base)‖^k) ε := by
  obtain ⟨w,hw⟩ := exists_circle_norm_factor (bracket (ξ:Base) (p:Base))
  have hw' : bracket (ξ:Base) (p:Base)=(‖bracket (ξ:Base) (p:Base)‖:ℂ)*(w:ℂ) := by rw [mul_comm]; exact hw.symm
  have he : ∀ z : Circle, regularizedLog a ε ((ρ:ℂ)*bracket (phaseAction z ξ : Base) (p:Base)^k)=
      regularizedLog 1 ε ((a*ρ*‖bracket (ξ:Base) (p:Base)‖^k:ℝ)*((z*w:Circle):ℂ)^k) := by
    intro z
    rw [regularizedLog_rescale,phaseAction_coe,bracket_smul,Circle.coe_mul]
    nth_rw 1 [hw']
    congr 1
    push_cast
    simp only [mul_pow]
    ring
  simp_rw [he,densityCorrection_constant_phase hpatch w hw']
  exact circle_regularized_shifted_moments (by positivity) hε hk _ w

end PinchedHartogs.BaseConstruction

end

end OAI
