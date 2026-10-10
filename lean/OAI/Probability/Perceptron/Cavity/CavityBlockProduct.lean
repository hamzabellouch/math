import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityShellLimit

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

def cavityRadialUnit (_n L : ℕ) (p : Ioi (0:ℝ)×Spin L) : Spin L :=
  (Real.sqrt (p.1.val^2+‖p.2‖^2))⁻¹ •p.2

lemma cavityRadialUnit_measurable (n L : ℕ) : Measurable (cavityRadialUnit n L) := by
  unfold cavityRadialUnit
  fun_prop

def cavityUnitEmbed (n L : ℕ) (p : Metric.sphere (0:Spin (n+1)) 1×Spin L) : Spin (n+1)×Spin L :=
  (Real.sqrt (1-‖p.2‖^2) •p.1.val,p.2)

lemma cavityUnitEmbed_measurable (n L : ℕ) : Measurable (cavityUnitEmbed n L) := by
  unfold cavityUnitEmbed
  fun_prop

lemma cavity_radial_rho {r b : ℝ} (hr : 0<r) (_hb : 0≤b) :
    Real.sqrt (1-((Real.sqrt (r^2+b^2))⁻¹*b)^2)=(Real.sqrt (r^2+b^2))⁻¹*r := by
  have hs : 0<Real.sqrt (r^2+b^2) := Real.sqrt_pos.mpr (by positivity)
  have hs2:=Real.sq_sqrt (show 0≤r^2+b^2 by positivity)
  have hsum : ((Real.sqrt (r^2+b^2))⁻¹*r)^2+((Real.sqrt (r^2+b^2))⁻¹*b)^2=1 := by
    field_simp
    nlinarith
  rw [show 1-((Real.sqrt (r^2+b^2))⁻¹*b)^2=((Real.sqrt (r^2+b^2))⁻¹*r)^2 by linarith,
    Real.sqrt_sq (by positivity)]

lemma cavityRadialBlock_unitEmbed (n L : ℕ)
    (p : (Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1)×Spin L) :
    cavityRadialBlock n L p=cavityUnitEmbed n L (p.1.2,cavityRadialUnit n L (p.1.1,p.2)) := by
  have ha : 0≤(Real.sqrt (p.1.1.val^2+‖p.2‖^2))⁻¹ := by positivity
  unfold cavityRadialBlock cavityUnitEmbed cavityRadialUnit
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,cavity_radial_rho p.1.1.prop (norm_nonneg p.2)]

lemma cavityRadial_reorder_preserving (n L : ℕ) :
    MeasurePreserving (fun p : (Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1)×Spin L=>(p.1.2,(p.1.1,p.2)))
      (((gaussianRadiusLaw n).prod (unitSphereLaw (n+1))).prod (stdGaussian (Spin L)))
      ((unitSphereLaw (n+1)).prod ((gaussianRadiusLaw n).prod (stdGaussian (Spin L)))) :=
  by
    let : IsProbabilityMeasure (unitSphereLaw (n+1)) := inferInstance
    have hs : MeasurePreserving (Prod.swap : Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1 →
        Metric.sphere (0:Spin (n+1)) 1×Ioi (0:ℝ))
        ((gaussianRadiusLaw n).prod (unitSphereLaw (n+1)))
        ((unitSphereLaw (n+1)).prod (gaussianRadiusLaw n)) := Measure.measurePreserving_swap
    exact (measurePreserving_prodAssoc (unitSphereLaw (n+1)) (gaussianRadiusLaw n) (stdGaussian (Spin L))).comp
      (hs.prod (MeasurePreserving.id (stdGaussian (Spin L))))

def cavityUnitLaw (n L : ℕ) : ProbabilityMeasure (Spin L) :=
  ⟨((gaussianRadiusLaw n).prod (stdGaussian (Spin L))).map (cavityRadialUnit n L),
    inferInstance⟩

lemma cavityUnitPair_preserving (n L : ℕ) :
    MeasurePreserving (fun p : (Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1)×Spin L=>
      (p.1.2,cavityRadialUnit n L (p.1.1,p.2)))
      (((gaussianRadiusLaw n).prod (unitSphereLaw (n+1))).prod (stdGaussian (Spin L)))
      ((unitSphereLaw (n+1)).prod (cavityUnitLaw n L)) :=
  by
    have h1 := MeasurePreserving.id (unitSphereLaw (n+1))
    have h2 : MeasurePreserving (cavityRadialUnit n L)
        ((gaussianRadiusLaw n).prod (stdGaussian (Spin L))) (cavityUnitLaw n L) :=
      ⟨cavityRadialUnit_measurable n L,rfl⟩
    exact (h1.prod h2).comp (cavityRadial_reorder_preserving n L)

theorem sphereBlock_product_law (n L : ℕ) :
    (unitSphereLaw (n+1+L)).map (fun u=>gaussianBlockSplit (n+1) L u.val)=
      ((unitSphereLaw (n+1)).prod (cavityUnitLaw n L)).map (cavityUnitEmbed n L) := by
  rw [sphereBlock_radial_law,←(cavityUnitPair_preserving n L).map_eq,
    Measure.map_map (cavityUnitEmbed_measurable n L) (cavityUnitPair_preserving n L).measurable]
  congr 1
  funext p
  exact cavityRadialBlock_unitEmbed n L p

lemma cavityUnitLaw_actual (n L : ℕ) :
    (cavityUnitLaw n L : Measure (Spin L))=
      (unitSphereLaw (n+1+L)).map (fun u=>(gaussianBlockSplit (n+1) L u.val).2) := by
  have he:=congrArg (fun μ : Measure (Spin (n+1)×Spin L)=>μ.map Prod.snd) (sphereBlock_product_law n L)
  have hm : Measurable (fun u : Metric.sphere (0:Spin (n+1+L)) 1=>gaussianBlockSplit (n+1) L u.val) :=
    (gaussianBlockSplit_measurable (n+1) L).comp measurable_subtype_coe
  rw [Measure.map_map measurable_snd hm,
    Measure.map_map measurable_snd (cavityUnitEmbed_measurable n L)] at he
  change _=((unitSphereLaw (n+1)).prod (cavityUnitLaw n L : Measure (Spin L))).map Prod.snd at he
  rw [Measure.map_snd_prod,measure_univ,one_smul] at he
  exact he.symm

lemma cavitySphereLaw_unit (n L : ℕ) :
    (cavitySphereLaw n L : Measure (Spin L))=
      (cavityUnitLaw n L : Measure (Spin L)).map (fun z=>Real.sqrt (n+1+L:ℕ) •z) := by
  have hm : Measurable (fun u : Metric.sphere (0:Spin (n+1+L)) 1 =>
      (gaussianBlockSplit (n+1) L u.val).2) :=
    (((gaussianBlockSplit_measurable (n+1) L).comp measurable_subtype_coe).snd)
  rw [cavityUnitLaw_actual,Measure.map_map (by fun_prop) hm]
  rfl

def cavitySphereBlockEmbed (n L : ℕ) (p : Metric.sphere (0:Spin (n+1)) 1×Spin L) : Spin (n+1)×Spin L :=
  cavityUnitEmbed n L (p.1,(Real.sqrt (n+1+L:ℕ))⁻¹ •p.2)

lemma cavitySphereBlockEmbed_measurable (n L : ℕ) : Measurable (cavitySphereBlockEmbed n L) := by
  unfold cavitySphereBlockEmbed
  apply (cavityUnitEmbed_measurable n L).comp
  fun_prop

lemma cavitySphereBlockEmbed_scaled (n L : ℕ) (x : Metric.sphere (0:Spin (n+1)) 1) (z : Spin L) :
    cavitySphereBlockEmbed n L (x,Real.sqrt (n+1+L:ℕ) •z)=cavityUnitEmbed n L (x,z) := by
  have hp : 0<Real.sqrt (n+1+L:ℕ) := Real.sqrt_pos.mpr (by positivity)
  simp only [cavitySphereBlockEmbed,smul_smul,inv_mul_cancel₀ hp.ne',one_smul]

lemma cavitySphereBlockEmbed_formula (n L : ℕ) (p : Metric.sphere (0:Spin (n+1)) 1×Spin L) :
    cavitySphereBlockEmbed n L p=
      (Real.sqrt (1-‖p.2‖^2/(n+1+L:ℕ)) •p.1.val,(Real.sqrt (n+1+L:ℕ))⁻¹ •p.2) := by
  have hp : 0≤((n+1+L:ℕ):ℝ) := by positivity
  simp only [cavitySphereBlockEmbed,cavityUnitEmbed,norm_smul,Real.norm_eq_abs,
    mul_pow,sq_abs,inv_pow,Real.sq_sqrt hp,div_eq_mul_inv,mul_comm]

theorem sphereBlock_scaled_product_law (n L : ℕ) :
    (unitSphereLaw (n+1+L)).map (fun u=>gaussianBlockSplit (n+1) L u.val)=
      ((unitSphereLaw (n+1)).prod (cavitySphereLaw n L)).map (cavitySphereBlockEmbed n L) := by
  have hs : MeasurePreserving (fun z : Spin L=>Real.sqrt (n+1+L:ℕ) •z)
      (cavityUnitLaw n L) (cavitySphereLaw n L) :=
    ⟨by fun_prop,(cavitySphereLaw_unit n L).symm⟩
  let : IsProbabilityMeasure (unitSphereLaw (n+1)) := inferInstance
  have hp : MeasurePreserving (fun p : Metric.sphere (0:Spin (n+1)) 1×Spin L =>
      (p.1,Real.sqrt (n+1+L:ℕ) •p.2))
      ((unitSphereLaw (n+1)).prod (cavityUnitLaw n L : Measure (Spin L)))
      ((unitSphereLaw (n+1)).prod (cavitySphereLaw n L : Measure (Spin L))) :=
    (MeasurePreserving.id (unitSphereLaw (n+1))).prod hs
  rw [sphereBlock_product_law,←hp.map_eq,
    Measure.map_map (cavitySphereBlockEmbed_measurable n L) hp.measurable]
  congr 1
  funext p
  exact (cavitySphereBlockEmbed_scaled n L p.1 p.2).symm

lemma cavityRadialUnit_norm_lt (n L : ℕ) (p : Ioi (0:ℝ)×Spin L) :
    ‖cavityRadialUnit n L p‖^2<1 := by
  have hr : 0<p.1.val := p.1.prop
  have hs : 0<Real.sqrt (p.1.val^2+‖p.2‖^2) := Real.sqrt_pos.mpr (by positivity)
  have he : ((Real.sqrt (p.1.val^2+‖p.2‖^2))⁻¹*p.1.val)^2+
      ((Real.sqrt (p.1.val^2+‖p.2‖^2))⁻¹*‖p.2‖)^2=1 := by
    field_simp
    rw [Real.sq_sqrt (by positivity)]
  have hpos : 0<((Real.sqrt (p.1.val^2+‖p.2‖^2))⁻¹*p.1.val)^2 := by positivity
  simp only [cavityRadialUnit,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
  linarith

lemma cavityUnitLaw_norm_lt (n L : ℕ) : ∀ᵐ z ∂(cavityUnitLaw n L : Measure (Spin L)),‖z‖^2<1 := by
  rw [show (cavityUnitLaw n L : Measure (Spin L))=Measure.map (cavityRadialUnit n L)
    ((gaussianRadiusLaw n).prod (stdGaussian (Spin L))) from rfl]
  exact (ae_map_iff (cavityRadialUnit_measurable n L).aemeasurable (measurableSet_lt (by fun_prop) measurable_const)).mpr
    (ae_of_all _ (cavityRadialUnit_norm_lt n L))

lemma cavitySphereLaw_norm_lt (n L : ℕ) : ∀ᵐ z ∂(cavitySphereLaw n L : Measure (Spin L)),‖z‖^2<(n+1+L:ℕ) := by
  rw [cavitySphereLaw_unit]
  apply (ae_map_iff (by fun_prop) (measurableSet_lt (by fun_prop) measurable_const)).mpr
  filter_upwards [cavityUnitLaw_norm_lt n L] with z hz
  have ht : 0<((n+1+L:ℕ):ℝ) := by positivity
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,Real.sq_sqrt ht.le]
  nlinarith

end SphericalPerceptronFreeEnergy
end

end OAI
