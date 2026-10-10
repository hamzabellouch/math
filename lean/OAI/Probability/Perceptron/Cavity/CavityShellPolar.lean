import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityBlockProduct

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

abbrev PositiveRadius : Type := ↥(Ioi (0:ℝ))

def cavityPolarRadius (n k : ℕ) (p : PositiveRadius×PositiveRadius) : PositiveRadius :=
  ⟨Real.sqrt (n+1+(k+1):ℕ) * (Real.sqrt (p.1.val^2+p.2.val^2))⁻¹*p.2.val,by
    change 0 < Real.sqrt (n+1+(k+1):ℕ) * (Real.sqrt (p.1.val^2+p.2.val^2))⁻¹*p.2.val
    have hr : 0<p.1.val := p.1.prop
    have hq : 0<p.2.val := p.2.prop
    positivity⟩

lemma cavityPolarRadius_measurable (n k : ℕ) : Measurable (cavityPolarRadius n k) := by
  unfold cavityPolarRadius
  fun_prop

def cavityRadiusLaw (n k : ℕ) : ProbabilityMeasure PositiveRadius :=
  ⟨((gaussianRadiusLaw n).prod (gaussianRadiusLaw k)).map (cavityPolarRadius n k),
    inferInstance⟩

lemma cavity_polar_data_preserving (n k : ℕ) :
    MeasurePreserving (fun p : (PositiveRadius×PositiveRadius)×Metric.sphere (0:Spin (k+1)) 1=>
      (p.1.1,p.1.2.val •p.2.val))
      (((gaussianRadiusLaw n).prod (gaussianRadiusLaw k)).prod (unitSphereLaw (k+1)))
      ((gaussianRadiusLaw n).prod (stdGaussian (Spin (k+1)))) := by
  have h : MeasurePreserving (fun p : PositiveRadius×(PositiveRadius×Metric.sphere (0:Spin (k+1)) 1)=>
      (p.1,p.2.1.val •p.2.2.val))
      ((gaussianRadiusLaw n).prod ((gaussianRadiusLaw k).prod (unitSphereLaw (k+1))))
      ((gaussianRadiusLaw n).prod (stdGaussian (Spin (k+1)))) :=
    (MeasurePreserving.id (gaussianRadiusLaw n)).prod (stdGaussian_radial_preserving k)
  exact h.comp (measurePreserving_prodAssoc (gaussianRadiusLaw n) (gaussianRadiusLaw k) (unitSphereLaw (k+1)))

lemma cavity_polar_radius_preserving (n k : ℕ) :
    MeasurePreserving (fun p : (PositiveRadius×PositiveRadius)×Metric.sphere (0:Spin (k+1)) 1=>
      (cavityPolarRadius n k p.1,p.2))
      (((gaussianRadiusLaw n).prod (gaussianRadiusLaw k)).prod (unitSphereLaw (k+1)))
      ((cavityRadiusLaw n k : Measure PositiveRadius).prod (unitSphereLaw (k+1))) := by
  have h : MeasurePreserving (cavityPolarRadius n k)
      ((gaussianRadiusLaw n).prod (gaussianRadiusLaw k)) (cavityRadiusLaw n k) :=
    ⟨cavityPolarRadius_measurable n k,rfl⟩
  exact h.prod (MeasurePreserving.id (unitSphereLaw (k+1)))

theorem cavitySphereLaw_polar (n k : ℕ) :
    (cavitySphereLaw n (k+1) : Measure (Spin (k+1)))=
      ((cavityRadiusLaw n k : Measure PositiveRadius).prod (unitSphereLaw (k+1))).map
        (fun p=>p.1.val •p.2.val) := by
  rw [cavitySphereLaw_unit]
  change (Measure.map (cavityRadialUnit n (k+1))
    ((gaussianRadiusLaw n).prod (stdGaussian (Spin (k+1))))).map _=_
  have hm : Measurable ((fun z : Spin (k+1)=>Real.sqrt (n+1+(k+1):ℕ) •z) ∘
      cavityRadialUnit n (k+1)) :=
    (by fun_prop : Measurable (fun z : Spin (k+1)=>Real.sqrt (n+1+(k+1):ℕ) •z)).comp
      (cavityRadialUnit_measurable n (k+1))
  rw [Measure.map_map (by fun_prop) (cavityRadialUnit_measurable _ _),
    ←(cavity_polar_data_preserving n k).map_eq,
    Measure.map_map hm (cavity_polar_data_preserving n k).measurable,
    ←(cavity_polar_radius_preserving n k).map_eq,
    Measure.map_map (by fun_prop) (cavity_polar_radius_preserving n k).measurable]
  congr 1
  funext p
  have hu : ‖p.2.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.2.prop
  simp only [Function.comp_def,cavityRadialUnit,cavityPolarRadius,norm_smul,Real.norm_eq_abs,
    abs_of_pos (show 0<p.1.2.val from p.1.2.prop),hu,mul_one,smul_smul,mul_assoc]

def cavityRadiusShell (k : ℕ) : Set PositiveRadius :=
  {r | (k+1:ℕ)≤r.val^2 ∧ r.val^2≤(k+1:ℕ)+1}

lemma cavityRadiusShell_measurable (k : ℕ) : MeasurableSet (cavityRadiusShell k) := by
  unfold cavityRadiusShell
  exact (measurableSet_le measurable_const (measurable_subtype_coe.pow_const 2)).inter
    (measurableSet_le (measurable_subtype_coe.pow_const 2) measurable_const)

lemma cavityShell_smul_preimage (k : ℕ) :
    (fun p : PositiveRadius×Metric.sphere (0:Spin (k+1)) 1=>p.1.val •p.2.val) ⁻¹'
      cavityShell (k+1)=cavityRadiusShell k×ˢuniv := by
  ext p
  simp [cavityShell,cavityRadiusShell,norm_smul]

theorem cavitySphereLaw_shell_polar (n k : ℕ) :
    (cavitySphereLaw n (k+1) : Measure (Spin (k+1))).restrict (cavityShell (k+1))=
      (((cavityRadiusLaw n k : Measure PositiveRadius).restrict (cavityRadiusShell k)).prod
        (unitSphereLaw (k+1))).map (fun p=>p.1.val •p.2.val) := by
  rw [cavitySphereLaw_polar,Measure.restrict_map (by fun_prop) (cavityShell_measurable _),
    cavityShell_smul_preimage,←Measure.prod_restrict,Measure.restrict_univ]


lemma cavityRadiusShell_bounds (k : ℕ) {r : PositiveRadius} (hr : r∈cavityRadiusShell k) :
    Real.sqrt (k+1:ℕ)≤r.val ∧ r.val≤(k:ℝ)+3 := by
  have hp : 0<r.val := r.prop
  have h1 : (k+1:ℕ)≤r.val^2 := hr.1
  have h2 : r.val^2≤(k+1:ℕ)+1 := hr.2
  constructor
  · exact (Real.sqrt_le_iff).mpr ⟨hp.le,h1⟩
  · have hk : (0:ℝ)≤k := Nat.cast_nonneg k
    push_cast at h2
    nlinarith [sq_nonneg (r.val-1)]

lemma cavity_shell_angular_integrable (n k : ℕ) (W C : ℝ) (Y : Spin (k+1)) :
    Integrable (fun p : PositiveRadius×Metric.sphere (0:Spin (k+1)) 1=>
      Real.exp (W+p.1.val^2*C/2+p.1.val*inner ℝ Y p.2.val))
      (((cavityRadiusLaw n k : Measure PositiveRadius).restrict (cavityRadiusShell k)).prod
        (unitSphereLaw (k+1))) := by
  let μ:=(cavityRadiusLaw n k : Measure PositiveRadius).restrict (cavityRadiusShell k)
  have hae : ∀ᵐ p : PositiveRadius×Metric.sphere (0:Spin (k+1)) 1
      ∂μ.prod (unitSphereLaw (k+1)),p.1∈cavityRadiusShell k := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_fst (cavityRadiusShell_measurable k))).mpr
    filter_upwards [ae_restrict_mem (cavityRadiusShell_measurable k)] with r hr
    exact ae_of_all _ fun _=>hr
  apply Integrable.of_bound (by fun_prop)
    (Real.exp (|W|+((k+1:ℕ)+1)*|C|/2+((k:ℝ)+3)*‖Y‖))
  filter_upwards [hae] with p hp
  have hr : 0<p.1.val := p.1.prop
  have hu : ‖p.2.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.2.prop
  have hinner : inner ℝ Y p.2.val≤‖Y‖ := by
    simpa only [hu,mul_one] using (le_abs_self _).trans (abs_real_inner_le_norm Y p.2.val)
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  apply add_le_add
  · apply add_le_add (le_abs_self _)
    exact div_le_div_of_nonneg_right
      ((mul_le_mul_of_nonneg_left (le_abs_self C) (sq_nonneg p.1.val)).trans
        (mul_le_mul_of_nonneg_right (show p.1.val^2≤(k+1:ℕ)+1 from hp.2) (abs_nonneg C))) (by norm_num)
  · exact (mul_le_mul_of_nonneg_left hinner hr.le).trans
      (mul_le_mul_of_nonneg_right (cavityRadiusShell_bounds k hp).2 (norm_nonneg Y))

lemma cavitySphereLaw_shell_integral (n k : ℕ) (W C : ℝ) (Y : Spin (k+1)) :
    (∫ z in cavityShell (k+1),Real.exp (W+‖z‖^2*C/2+inner ℝ Y z)
      ∂(cavitySphereLaw n (k+1) : Measure (Spin (k+1))))=
      ∫ r in cavityRadiusShell k,Real.exp (W+r.val^2*C/2)*sphericalExp k Y r.val
        ∂(cavityRadiusLaw n k : Measure PositiveRadius) := by
  rw [cavitySphereLaw_shell_polar,integral_map (by fun_prop) (by fun_prop)]
  have he : (fun p : PositiveRadius×Metric.sphere (0:Spin (k+1)) 1=>
      Real.exp (W+‖p.1.val •p.2.val‖^2*C/2+inner ℝ Y (p.1.val •p.2.val)))=
      (fun p=>Real.exp (W+p.1.val^2*C/2+p.1.val*inner ℝ Y p.2.val)) := by
    funext p
    have hu : ‖p.2.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.2.prop
    simp only [norm_smul,Real.norm_eq_abs,hu,mul_one,sq_abs,real_inner_smul_right]
  rw [he,integral_prod _ (cavity_shell_angular_integrable n k W C Y)]
  apply integral_congr_ae
  filter_upwards [] with r
  simp only [Real.exp_add,integral_const_mul,sphericalExp]

lemma cavitySphereLaw_shell_mass_polar (n k : ℕ) :
    (cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1))=
      (cavityRadiusLaw n k : Measure PositiveRadius).real (cavityRadiusShell k) := by
  have h:=cavitySphereLaw_shell_integral n k 0 0 0
  simpa [sphericalExp] using h

theorem cavitySphereLaw_shell_lower (n k : ℕ) (W C : ℝ) (Y : Spin (k+1))
    {K : ℝ} (hC : |C|≤K) :
    (cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1))*
      (Real.exp (-K/2)*Real.exp (W+(k+1:ℕ)*C/2)*sphericalExp k Y (Real.sqrt (k+1:ℕ)))≤
      ∫ z in cavityShell (k+1),Real.exp (W+‖z‖^2*C/2+inner ℝ Y z)
        ∂(cavitySphereLaw n (k+1) : Measure (Spin (k+1))) := by
  rw [cavitySphereLaw_shell_integral,cavitySphereLaw_shell_mass_polar]
  have hi := (cavity_shell_angular_integrable n k W C Y).integral_prod_left
  have he : (fun r : PositiveRadius=>∫ u : Metric.sphere (0:Spin (k+1)) 1,
      Real.exp (W+r.val^2*C/2+r.val*inner ℝ Y u.val) ∂unitSphereLaw (k+1))=
      (fun r=>Real.exp (W+r.val^2*C/2)*sphericalExp k Y r.val) := by
    funext r
    simp only [Real.exp_add,integral_const_mul,sphericalExp]
  rw [he] at hi
  calc
    _ = ∫ _ in cavityRadiusShell k,
        Real.exp (-K/2)*Real.exp (W+(k+1:ℕ)*C/2)*sphericalExp k Y (Real.sqrt (k+1:ℕ))
          ∂(cavityRadiusLaw n k : Measure PositiveRadius) := by simp [mul_comm]
    _ ≤ _ := by
      apply integral_mono_ae (integrable_const _) hi
      filter_upwards [ae_restrict_mem (cavityRadiusShell_measurable k)] with r hr
      have hD : |(r.val^2-(k+1:ℕ))*C|≤K := by
        rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr hr.1)]
        have hK : 0≤K := (abs_nonneg C).trans hC
        calc
          _≤1*K := mul_le_mul (by linarith [hr.2]) hC (abs_nonneg C) (by norm_num)
          _=K := one_mul K
      have hexp : Real.exp (-K/2)*Real.exp (W+(k+1:ℕ)*C/2)≤Real.exp (W+r.val^2*C/2) := by
        rw [←Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [(abs_le.mp hD).1]
      exact mul_le_mul hexp
        (sphericalExp_mono k Y (Real.sqrt_nonneg _) (cavityRadiusShell_bounds k hr).1)
        ((by norm_num : (0:ℝ)≤1).trans (one_le_sphericalExp _ _ _)) (Real.exp_pos _).le

end SphericalPerceptronFreeEnergy
end

end OAI
