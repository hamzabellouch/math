import OAI.Geometry.Relativity.CKS.ADMFlux
import OAI.Geometry.Relativity.CKS.ADMAverage

namespace OAI

noncomputable section
namespace CKSADM
noncomputable section
open Set Filter MeasureTheory CKSSphericalHarmonics CKSSphericalChart CKSBending CKSInducedSphere
open scoped Topology ContDiff

def unitVector (x : E) : E := ‖x‖⁻¹ • x

lemma unitVector_norm {x : E} (hx : x ≠ 0) : ‖unitVector x‖ = 1 := by
  simpa only [unitVector,Metric.mem_sphere,dist_zero_right] using normalize_mem_sphere x hx

lemma unitVector_smooth {x : E} (hx : x ≠ 0) : ContDiffAt ℝ ∞ unitVector x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

lemma norm_radius_sphere {r : ℝ} (hr : 0 < r) (n : Sphere) : ‖r • (n:E)‖ = r := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  simp

lemma unitVector_radius {r : ℝ} (hr : 0 < r) (n : Sphere) : unitVector (r • (n:E)) = n := by
  rw [unitVector,norm_radius_sphere hr,smul_smul,inv_mul_cancel₀ hr.ne',one_smul]

def cartMass (f₀ : C(Sphere,ℝ)) (m R : ℝ) (x : E) : ℝ :=
  paddingMass R ‖x‖ + canonicalF f₀ m (heatTime R ‖x‖) (unitVector x)

lemma cartMass_smooth (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0 < R) {x : E} (hx : x ≠ 0) : ContDiffAt ℝ ∞ (cartMass f₀ m R) x := by
  have hn : ContDiffAt ℝ ∞ (fun x : E => ‖x‖) x := contDiffAt_norm ℝ hx
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have ht : ContDiffAt ℝ ∞ (fun y : E => heatTime R ‖y‖) x :=
    ((heatTime_smooth hR).contDiffAt (isOpen_Ioi.mem_nhds hr)).comp x hn
  have hc : ContDiffAt ℝ ∞ (fun y : E => paddingMass R ‖y‖) x :=
    ((paddingMass_smooth hR).contDiffAt (isOpen_Ioi.mem_nhds hr)).comp x hn
  have hu : unitVector x ≠ 0 := by
    intro hh
    have hq := unitVector_norm hx
    rw [hh,norm_zero] at hq
    norm_num at hq
  have hz : (heatTime R ‖x‖,unitVector x) ∈ heatDomain := hu
  have hh : ContDiffAt ℝ ∞ (fun z : ℝ × E => canonicalF f₀ m z.1 z.2)
      (heatTime R ‖x‖,unitVector x) :=
    (canonicalF_joint f₀ hf₀ m).contDiffAt (heatDomain_open.mem_nhds hz)
  have hcomp := hh.comp x (ht.prodMk (unitVector_smooth hx))
  exact hc.add hcomp

lemma cartMass_radius (f₀ : C(Sphere,ℝ)) (m R : ℝ) {r : ℝ} (hr : 0 < r) (n : Sphere) :
    cartMass f₀ m R (r • (n:E)) = tailSphereMass f₀ m R r n := by
  simp only [cartMass,norm_radius_sphere hr,unitVector_radius hr,tailSphereMass]

def cartB (f₀ : C(Sphere,ℝ)) (m R : ℝ) (x : E) : ℝ :=
  (1-2*cartMass f₀ m R x/‖x‖)⁻¹-1

lemma cartB_smooth (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0 < R) {x : E} (hx : x ≠ 0)
    (hd : 1-2*cartMass f₀ m R x/‖x‖ ≠ 0) : ContDiffAt ℝ ∞ (cartB f₀ m R) x := by
  have hh := (contDiffAt_const.sub ((contDiffAt_const.mul (cartMass_smooth f₀ hf₀ m hR hx)).div
    (contDiffAt_norm ℝ hx) (norm_ne_zero_iff.mpr hx))).inv hd
  exact hh.sub contDiffAt_const

def surfaceEnergy (f₀ : C(Sphere,ℝ)) (m R r : ℝ) : ℝ :=
  r^2/(16*Real.pi) * ∫ n : Sphere, energyIntegrand (cartB f₀ m R) (r • (n:E)) ∂surfaceMeasure

lemma surfaceEnergy_eq_reduced (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m R r B : ℝ)
    (hR : 0 < R) (hB : 0 ≤ B) (hF : ∀ n : Sphere, |tailSphereMass f₀ m R r n| ≤ B)
    (hr : 4*B+1 ≤ r) : surfaceEnergy f₀ m R r = reducedEnergy f₀ m R r := by
  have hrp : 0 < r := by linarith
  unfold surfaceEnergy reducedEnergy
  rw [← integral_const_mul,← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro n
  have hx : (r • (n:E)) ≠ 0 := smul_ne_zero hrp.ne' (sphere_ne_zero n)
  have hd : 0 < 1-2*cartMass f₀ m R (r • (n:E))/‖r • (n:E)‖ := by
    rw [cartMass_radius f₀ m R hrp,norm_radius_sphere hrp]
    have hh := denominator_lower hB (hF n) hr
    linarith
  dsimp only
  rw [energyIntegrand_eq ((cartB_smooth f₀ hf₀ m hR hx hd.ne').differentiableAt (by simp)) hx]
  simp only [cartB,cartMass_radius f₀ m R hrp,norm_radius_sphere hrp]
  have hd' : 1-2*tailSphereMass f₀ m R r n/r ≠ 0 := by
    simpa only [cartMass_radius f₀ m R hrp,norm_radius_sphere hrp] using hd.ne'
  have hden : r-tailSphereMass f₀ m R r n*2 ≠ 0 := by
    have hh := (le_abs_self _).trans (hF n)
    linarith
  field_simp [hrp.ne',hd',hden]
  ring_nf
  field_simp [hden]
  ring

theorem constructed_ADM_energy (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 1 ≤ R) :
    Tendsto (surfaceEnergy f₀ m R) atTop (𝓝 (m+paddingCharge R)) ∧
      0 ≤ paddingCharge R ∧ paddingCharge R ≤ 2/Real.sqrt R := by
  refine ⟨?_,paddingCharge_bounds (by linarith : 0 < R)⟩
  apply (reducedEnergy_limit f₀ hf₀ m hR).congr'
  obtain ⟨B,hB,hbound⟩ := tailSphereMass_bound f₀ hf₀ m
  filter_upwards [eventually_ge_atTop (3*R),eventually_ge_atTop (4*B+1)] with r hr hlarge
  exact (surfaceEnergy_eq_reduced f₀ hf₀ m R r B (by linarith) hB.le (hbound R r hR hr) hlarge).symm

end
end CKSADM

end

end OAI
