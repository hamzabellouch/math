import OAI.MathematicalPhysics.Boltzmann.Branching.CompressedAxialDecay
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialAtomicSheet
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialFlow
import OAI.MathematicalPhysics.Boltzmann.Jets.FreeCoreGainKernel
import OAI.MathematicalPhysics.Boltzmann.Jets.JetBarrierKinetic
import OAI.MathematicalPhysics.Boltzmann.Jets.JetSupersolutions

namespace OAI

section

/-! # The actual compact thermal parameters preserve axial decay -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetCoreMap

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem sourceFoot_abs_lower {α d t T Z : ℝ}
    (hα : 0 ≤ α) (hd : 0 ≤ d) (hdmax : d ≤ 1) (ht : 0 ≤ t) (htT : t ≤ T)
    (γ μ : ℝ) (a : Bool) (z w : ℝ) (hw : |w| ≤ 1)
    (hz : Z+T*(α+2) ≤ |z|) : Z ≤ |sourceFoot (JetPrototype.sign a) α γ μ d t z w| := by
  have hp := JetAxialLaw.axialMap_abs_le hα hd (JetPrototype.sign a) γ μ t z w
  have hsign : |JetPrototype.sign a| = 1 := by cases a <;> norm_num [JetPrototype.sign]
  rw [hsign] at hp
  have hp' : |axialMap (JetPrototype.sign a) α γ μ d t z w| ≤ α+2 := by
    have h := mul_le_mul_of_nonneg_left hw hd
    linarith
  have htp : |t*axialMap (JetPrototype.sign a) α γ μ d t z w| ≤ T*(α+2) := by
    rw [abs_mul,abs_of_nonneg ht]
    exact mul_le_mul htT hp' (abs_nonneg _) (by linarith)
  rw [sourceFoot_eq]
  linarith [abs_sub_abs_le_abs_sub z (t*axialMap (JetPrototype.sign a) α γ μ d t z w)]

theorem weight_axial_decay {K α γ μ d t T M Z : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 < γ) (hμ : 0 < μ)
    (hd : 0 ≤ d) (hdmax : d ≤ 1) (ht : 0 ≤ t) (htT : t ≤ T)
    (hM : μ ≤ M) (hZ : 0 < Z) (η : ℝ) (a : Bool) (x : JetPrototype.Space)
    (hx : Z+T*(α+2) ≤ |x.2|) (w : Transverse × ℝ) :
    weight η K α γ μ d t a x w ≤
      (4*K*M/(γ^2*Z^2))*JetThermalKernel.J (SheetMeasures.join w) := by
  have hA : 0 ≤ 4*K*M/(γ^2*Z^2) := by
    have hMpos := hμ.trans_le hM
    positivity
  by_cases hw : 1 ≤ ‖SheetMeasures.join w‖
  · unfold weight
    rw [JetThermalKernel.J_zero hw]
    simp
  have hw' : |w.2| ≤ 1 := by
    have hn := SheetMeasures.norm_join_sq w
    have hn0 := norm_nonneg (SheetMeasures.join w)
    have hlt := lt_of_not_ge hw
    nlinarith [sq_nonneg ‖w.1‖,sq_abs w.2,abs_nonneg w.2]
  have hc := compressed_axial_decay hK hα hγ hμ ht hM hZ
    (sourceFoot_abs_lower hα hd hdmax ht htT γ μ a x.2 w.2 hw' hx)
  have hj := JetThermalKernel.J_nonneg (SheetMeasures.join w)
  unfold weight
  by_cases hy : x.1-t • (d • w.1) ∈ JetGeometry.mask η μ a
  · by_cases hz : sourceFoot (JetPrototype.sign a) α γ μ d t x.2 w.2 ∈ Ioo (-(1/8:ℝ)) (1/8)
    · simp only [indicator_of_mem hy,indicator_of_mem hz,one_mul]
      exact mul_le_mul_of_nonneg_right hc hj
    · simp only [indicator_of_notMem hz,mul_zero,zero_mul]
      exact mul_nonneg hA hj
  · simp only [indicator_of_notMem hy,zero_mul]
    exact mul_nonneg hA hj

theorem gaussian_axial_decay {K α γ μ d t T M Z : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 < γ) (hμ : 0 < μ)
    (hd : 0 ≤ d) (hdmax : d ≤ 1) (ht : 0 ≤ t) (htT : t ≤ T)
    (hM : μ ≤ M) (hZ : 0 < Z) (η : ℝ) (a : Bool) (x : JetPrototype.Space)
    (hx : Z+T*(α+2) ≤ |x.2|) (w : Transverse × ℝ) :
    weight η K α γ μ d t a x w ≤
      ((4*K*M/(γ^2*Z^2))*JetGaussianProduct.coefficient)*JetGaussianProduct.density w := by
  apply (weight_axial_decay hK hα hγ hμ hd hdmax ht htT hM hZ η a x hx w).trans
  have hA : 0 ≤ 4*K*M/(γ^2*Z^2) := by
    have hMpos := hμ.trans_le hM
    positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (JetGaussianProduct.kernel_bound w) hA

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Dilation identities for the implicit axial flow and compressed core -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.AxialFlow

theorem profile_dilation {r : ℝ} (hr : r ≠ 0) (σ α γ s z : ℝ) :
    profile σ α γ (r*s) (r*z) = profile σ α γ s z := by
  unfold profile
  congr 2
  field_simp

theorem velocity_dilation {r α γ s t : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) (σ z : ℝ) :
    velocity σ α γ (r*s) (r*t) (r*z) = velocity σ α γ s t z := by
  symm
  apply velocity_unique hα hγ (mul_pos hr hs) (mul_nonneg hr.le ht)
  rw [show r*z-r*t*velocity σ α γ s t z = r*(z-t*velocity σ α γ s t z) by ring,
    profile_dilation hr.ne']
  exact velocity_spec hα

theorem foot_dilation {r α γ s t : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) (σ z : ℝ) :
    foot σ α γ (r*s) (r*t) (r*z) = r*foot σ α γ s t z := by
  unfold foot
  rw [velocity_dilation hr hα hγ hs ht]
  ring

theorem velocity_scale_tendsto {s : ℕ → ℝ} {α γ μ t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ n, 0 < s n) (hμ : 0 < μ) (ht : 0 ≤ t)
    (hslim : Tendsto s atTop (𝓝 μ)) (σ z : ℝ) :
    Tendsto (fun n => velocity σ α γ (s n) t z) atTop (𝓝 (velocity σ α γ μ t z)) := by
  let u := velocity σ α γ μ t z
  have htanh : Continuous Real.tanh := by
    convert continuous_profile 0 1 1 1 using 1
    funext z
    simp [profile]
  have harg : Tendsto (fun n => γ*(z-t*u)/s n) atTop (𝓝 (γ*(z-t*u)/μ)) :=
    tendsto_const_nhds.div hslim hμ.ne'
  have hp : Tendsto (fun n => profile σ α γ (s n) (z-t*u)) atTop
      (𝓝 (profile σ α γ μ (z-t*u))) :=
    tendsto_const_nhds.add ((htanh.continuousAt.tendsto.comp harg).const_mul α)
  have hres : Tendsto (fun n => residual σ α γ (s n) t z u) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := u)).sub hp
    have hu : u-profile σ α γ μ (z-t*u) = 0 := sub_eq_zero.mpr (velocity_spec hα)
    simpa only [residual,hu] using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => ?_) (by simpa only [abs_zero] using hres.abs)
  have h := residual_inverse_lipschitz (σ := σ) (z := z) (u := velocity σ α γ (s n) t z) (v := u)
    hα hγ (hs n) ht
  have hz : residual σ α γ (s n) t z (velocity σ α γ (s n) t z) = 0 :=
    sub_eq_zero.mpr (velocity_spec hα)
  simpa only [hz,zero_sub,abs_neg,Real.norm_eq_abs,u] using h

end BoltzmannNonuniqueness.AxialFlow

namespace BoltzmannNonuniqueness.JetCoreMap

theorem axialMap_dilation {r α γ s t : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) (σ d z w : ℝ) :
    axialMap σ α γ (r*s) d (r*t) (r*z) w = axialMap σ α γ s d t z w := by
  unfold axialMap
  rw [show r*z-r*t*d*w = r*(z-t*d*w) by ring,
    AxialFlow.velocity_dilation hr hα hγ hs ht]

theorem axialMap_error_le {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 ≤ d) (ht : 0 ≤ t) (σ z w : ℝ) :
    |axialMap σ α γ s d t z w-AxialFlow.velocity σ α γ s t z| ≤ d*|w| := by
  have h := AxialFlow.thermal_velocity_error hα hγ hs ht (axialMap_spec hα σ γ s d t z w)
  simpa only [abs_mul,abs_of_nonneg hd] using h

end BoltzmannNonuniqueness.JetCoreMap

end

end

section

/-! # The two atomic velocity measures on one limiting mesh annulus -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.AxialBackground

/-- The stripe fraction is exactly one quarter in the supplied manuscript. -/
def weight (K α γ μ t σ z : ℝ) : ℝ :=
  (1/4)*JetCoreDensity.compressed K α γ μ t (AxialFlow.foot σ α γ μ t z)

def atom (K α γ μ t σ z : ℝ) : Measure Velocity :=
  ENNReal.ofReal (weight K α γ μ t σ z) •
    Measure.dirac (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z))

def cell (K α γ μ t z : ℝ) : Measure Velocity :=
  atom K α γ μ t 1 z+atom K α γ μ t (-1) z

theorem weight_nonneg {K α γ μ t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hμ : 0 < μ) (ht : 0 ≤ t) (σ z : ℝ) :
    0 ≤ weight K α γ μ t σ z :=
  mul_nonneg (by norm_num) (JetCoreDensity.compressed_nonneg hK hα hγ hμ ht _)

theorem weight_bound {K α γ μ t : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hμ : 0 < μ) (ht : 0 ≤ t) (σ z : ℝ) :
    weight K α γ μ t σ z ≤ (1/4)*((K*max 1 (α*γ)⁻¹)/(μ+t)) :=
  mul_le_mul_of_nonneg_left (JetCoreDensity.compressed_bound hK hα hγ hμ ht _) (by norm_num)

theorem integrable_atom (K α γ μ t σ z : ℝ) (ψ : Velocity → ℝ) :
    Integrable ψ (atom K α γ μ t σ z) :=
  (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

theorem integral_atom {K α γ μ t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hμ : 0 < μ) (ht : 0 ≤ t) (σ z : ℝ) (ψ : Velocity → ℝ) :
    (∫ v, ψ v ∂atom K α γ μ t σ z) =
      weight K α γ μ t σ z*ψ (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z)) := by
  rw [atom,integral_smul_measure,integral_dirac,
    ENNReal.toReal_ofReal (weight_nonneg hK hα hγ hμ ht σ z),smul_eq_mul]

theorem integral_cell {K α γ μ t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hμ : 0 < μ) (ht : 0 ≤ t) (z : ℝ) (ψ : Velocity → ℝ) :
    (∫ v, ψ v ∂cell K α γ μ t z) =
      weight K α γ μ t 1 z*ψ (PlaneChart.join 0 (AxialFlow.velocity 1 α γ μ t z))+
      weight K α γ μ t (-1) z*ψ (PlaneChart.join 0 (AxialFlow.velocity (-1) α γ μ t z)) := by
  rw [cell,integral_add_measure (integrable_atom _ _ _ _ _ _ _ _) (integrable_atom _ _ _ _ _ _ _ _),
    integral_atom hK hα hγ hμ ht,integral_atom hK hα hγ hμ ht]

theorem atom_gain_bound {K α γ μ t q σ z : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hμ : 0 < μ) (ht : 0 ≤ t)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hσ : |σ| = 1)
    {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedChartGain (atom K α γ μ t σ z) q v ≤
      ENNReal.ofReal ((1/4)*((K*max 1 (α*γ)⁻¹)/(μ+t)))*
        SheetTotal.bound q (Real.exp (8*(1+α)^2)) := by
  unfold atom normalizedChartGain
  rw [chartGain_smul_measure]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (weight_bound hK hα hγ hμ ht σ z))
    (AxialAtomicSheet.normalized_gain_bound hq₁ hq₂ hα.le hσ hv)

theorem cell_gain_bound {K α γ μ t q z : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hμ : 0 < μ) (ht : 0 ≤ t)
    (hq₁ : 1 < q) (hq₂ : q < 2) {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedChartGain (cell K α γ μ t z) q v ≤
      2*(ENNReal.ofReal ((1/4)*((K*max 1 (α*γ)⁻¹)/(μ+t)))*
        SheetTotal.bound q (Real.exp (8*(1+α)^2))) := by
  unfold cell normalizedChartGain
  rw [chartGain_add_measure]
  exact (add_le_add (atom_gain_bound hK hα hγ hμ ht hq₁ hq₂ (by norm_num) hv)
    (atom_gain_bound hK hα hγ hμ ht hq₁ hq₂ (by norm_num) hv)).trans_eq (two_mul _).symm

end BoltzmannNonuniqueness.AxialBackground

end

end

section

/-! # The three collapsed axial speeds, uniformly for positive times -/

noncomputable section

namespace BoltzmannNonuniqueness.AxialFlow

theorem velocity_collapsed_uniform {α γ a ε : ℝ}
    (hα : 0 < α) (hγ : 0 < γ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ (σ s t z : ℝ), 0 < s → s < μ₀ → a ≤ t →
      |velocity σ α γ s t z-(σ-α)| < ε ∨
      |velocity σ α γ s t z-(σ+α)| < ε ∨
      |velocity σ α γ s t z-z/t| < ε := by
  let C := interiorArgumentBound (1-(ε/2)/α)/(γ*a)
  have hC : 0 ≤ C := div_nonneg (interiorArgumentBound_nonneg _) (mul_pos hγ ha).le
  refine ⟨ε/(C+1),div_pos hε (by positivity),?_⟩
  intro σ s t z hs hs₀ ht
  by_cases hl : |velocity σ α γ s t z-(σ-α)| < ε
  · exact Or.inl hl
  by_cases hu : |velocity σ α γ s t z-(σ+α)| < ε
  · exact Or.inr (Or.inl hu)
  right; right
  have hb := abs_le.mp (velocity_sub_center_le (σ := σ) (γ := γ) (s := s)
    (t := t) (z := z) hα.le)
  have hlow : ε/2 ≤ velocity σ α γ s t z-(σ-α) := by
    rw [abs_of_nonneg (by linarith : 0 ≤ velocity σ α γ s t z-(σ-α))] at hl
    linarith
  have hupp : ε/2 ≤ (σ+α)-velocity σ α γ s t z := by
    rw [abs_of_nonpos (by linarith : velocity σ α γ s t z-(σ+α) ≤ 0)] at hu
    linarith
  have h := velocity_interior_small_scale hα hγ ha (half_pos hε) hs ht hlow hupp
  have hsC := (lt_div_iff₀ (show 0 < C+1 by positivity)).mp hs₀
  exact h.trans_lt (by change C*s < ε; nlinarith)

theorem thermal_velocity_collapsed_uniform {α γ a ε : ℝ}
    (hα : 0 < α) (hγ : 0 < γ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ (σ s d t z w : ℝ), 0 < s → s < μ₀ → a ≤ t →
      |d*w| < ε/2 →
      |JetCoreMap.axialMap σ α γ s d t z w-(σ-α)| < ε ∨
      |JetCoreMap.axialMap σ α γ s d t z w-(σ+α)| < ε ∨
      |JetCoreMap.axialMap σ α γ s d t z w-z/t| < ε := by
  obtain ⟨μ₀,hμ₀,hμ⟩ := velocity_collapsed_uniform hα hγ ha (half_pos hε)
  refine ⟨μ₀,hμ₀,?_⟩
  intro σ s d t z w hs hs₀ ht hd
  have he := thermal_velocity_error hα.le hγ.le hs (ha.le.trans ht)
    (JetCoreMap.axialMap_spec hα.le σ γ s d t z w)
  have hadd (c : ℝ) (hc : |velocity σ α γ s t z-c| < ε/2) :
      |JetCoreMap.axialMap σ α γ s d t z w-c| < ε := by
    have hh := abs_sub_le (JetCoreMap.axialMap σ α γ s d t z w)
      (velocity σ α γ s t z) c
    linarith
  rcases hμ σ s t z hs hs₀ ht with h | h | h
  · exact Or.inl (hadd _ h)
  · exact Or.inr (Or.inl (hadd _ h))
  · exact Or.inr (Or.inr (hadd _ h))

end BoltzmannNonuniqueness.AxialFlow

end

end

section

/-! # Axial decay survives the Gaussian-sheet normalization -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetCoreMeasure

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem axial_measure_domination {K α γ μ d t T M Z : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 < γ) (hμ : 0 < μ)
    (hd : 0 < d) (hdmax : d ≤ 1) (ht : 0 ≤ t) (htT : t ≤ T)
    (hM : μ ≤ M) (hZ : 0 < Z) (η : ℝ) (a : Bool) (x : JetPrototype.Space)
    (hx : Z+T*(α+2) ≤ |x.2|) :
    volume.withDensity (fun v => ENNReal.ofReal (JetFreeTransport.free η K α γ μ d t a (x,v))) ≤
      ENNReal.ofReal ((4*K*M/(γ^2*Z^2))*JetGaussianProduct.coefficient) •
        SheetMeasures.sheetLaw d (JetAxialLaw.law (JetPrototype.sign a) α γ μ d t x.2) := by
  rw [← JetCoreDensity.measure_identity hα hγ.le hμ hd ht,
    ← JetGaussianProduct.parameterLaw_map hα hγ.le hμ hd ht]
  have hm := (velocity_measurePreserving hα hγ.le hμ hd ht (JetPrototype.sign a) x.2).measurable
  rw [← Measure.map_smul _ hm.aemeasurable]
  apply Measure.map_mono _ hm
  rw [JetGaussianProduct.parameterLaw_density]
  have hg : Measurable (fun w => ENNReal.ofReal (JetGaussianProduct.density w)) := by
    unfold JetGaussianProduct.density GaussianDiskMixture.gaussianDensity
    fun_prop
  rw [← withDensity_smul _ hg]
  apply withDensity_mono
  filter_upwards [] with w
  change ENNReal.ofReal (JetCoreDensity.weight η K α γ μ d t a x w) ≤
    ENNReal.ofReal ((4*K*M/(γ^2*Z^2))*JetGaussianProduct.coefficient)*
      ENNReal.ofReal (JetGaussianProduct.density w)
  have hnonneg : 0 ≤ (4*K*M/(γ^2*Z^2))*JetGaussianProduct.coefficient := by
    have hMpos := hμ.trans_le hM
    have := JetThermalKernel.bound_pos
    unfold JetGaussianProduct.coefficient
    positivity
  rw [← ENNReal.ofReal_mul hnonneg]
  exact ENNReal.ofReal_le_ofReal
    (JetCoreDensity.gaussian_axial_decay hK hα hγ hμ hd.le hdmax ht htT hM hZ η a x hx w)

theorem normalized_core_axial_decay {K α γ μ d t T M Z q : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 < γ) (hμ : 0 < μ)
    (hd : 0 < d) (hdmax : d ≤ 1/16) (ht : 0 ≤ t) (htT : t ≤ T)
    (hM : μ ≤ M) (hZ : 0 < Z) (hq₁ : 1 < q) (hq₂ : q < 2)
    (η : ℝ) (a : Bool) (x : JetPrototype.Space) (hx : Z+T*(α+2) ≤ |x.2|)
    {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedCoreKernel η K α γ μ d q a ((t,x),v) univ ≤
      ENNReal.ofReal ((4*K*M/(γ^2*Z^2))*JetGaussianProduct.coefficient)*
        SheetTotal.bound q (2*Real.exp (16*(1+α)^2)) := by
  rw [normalizedCoreKernel,ChartKernel.inputKernel_mass,coreKernel_apply]
  unfold normalizedChartGain
  have hp := JetAxialLaw.probability (JetPrototype.sign a) α γ μ d t x.2
  have hm := JetAxialLaw.moment hα hγ.le hμ hd hdmax ht (JetPrototype.sign a) x.2
  have hsign : |JetPrototype.sign a| = 1 := by cases a <;> norm_num [JetPrototype.sign]
  rw [hsign] at hm
  have he : SheetClass.IsElementary (2*Real.exp (16*(1+α)^2))
      (SheetMeasures.sheetLaw d (JetAxialLaw.law (JetPrototype.sign a) α γ μ d t x.2)) :=
    ⟨d,_,hd.le,by linarith,hp,hm,rfl⟩
  apply (chartGain_mono_measure
    (axial_measure_domination hK hα hγ hμ hd (by linarith) ht htT hM hZ η a x hx) _ v).trans
  rw [chartGain_smul_measure]
  exact mul_le_mul' le_rfl (SheetClass.elementary_bound hq₁ hq₂ he hv)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Uniform second-collision mismatch away from the exceptional axial speeds -/

noncomputable section

namespace BoltzmannNonuniqueness.AxialFlow

theorem ballistic_axial_gap_identity {t₁ t₂ : ℝ} (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0)
    (z w : ℝ) :
    w-(z-(t₁-t₂)*w)/t₂ = (t₁/t₂)*(w-z/t₁) := by
  field_simp
  ring

theorem ballistic_axial_gap {t₁ t₂ : ℝ} (ht₂ : 0 < t₂) (htt : t₂ ≤ t₁)
    (z w : ℝ) :
    |w-z/t₁| ≤ |w-(z-(t₁-t₂)*w)/t₂| := by
  have ht₁ : 0 < t₁ := lt_of_lt_of_le ht₂ htt
  rw [ballistic_axial_gap_identity ht₁.ne' ht₂.ne',abs_mul,
    abs_of_pos (div_pos ht₁ ht₂)]
  have hr : 1 ≤ t₁/t₂ := (le_div_iff₀ ht₂).mpr (by simpa using htt)
  nlinarith [abs_nonneg (w-z/t₁)]

/-- A gap at the first collision persists at the next collision up to the thermal error. -/
theorem thermal_second_gap {σ α γ s t₁ t₂ z w d ω b : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht₂ : 0 ≤ t₂) (htt : t₂ ≤ t₁)
    (hgap : b ≤ |w-velocity σ α γ s t₁ z|) (herr : |d*ω| ≤ b/2) :
    b/2 ≤ |w-JetCoreMap.axialMap σ α γ s d t₂ (z-(t₁-t₂)*w) ω| := by
  have hm := characteristic_matching (σ := σ) (z := z) (w := w) hα hγ hs ht₂ htt
  have he := thermal_velocity_error hα hγ hs ht₂
    (JetCoreMap.axialMap_spec hα σ γ s d t₂ (z-(t₁-t₂)*w) ω)
  have htri := abs_sub_le w
    (JetCoreMap.axialMap σ α γ s d t₂ (z-(t₁-t₂)*w) ω)
    (velocity σ α γ s t₂ (z-(t₁-t₂)*w))
  linarith

/-- Small scales need only exclude the two endpoint speeds and the ballistic speed
at the first collision. The scale threshold is independent of both collision positions. -/
theorem small_scale_second_gap {α γ a δ : ℝ}
    (hα : 0 < α) (hγ : 0 < γ) (ha : 0 < a) (hδ : 0 < δ) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ (σ s d t₁ t₂ z w ω : ℝ),
      0 < s → s < μ₀ → a ≤ t₂ → t₂ ≤ t₁ → |d*ω| < δ/4 →
      δ ≤ |w-(σ-α)| → δ ≤ |w-(σ+α)| → δ ≤ |w-z/t₁| →
      δ/2 ≤ |w-JetCoreMap.axialMap σ α γ s d t₂ (z-(t₁-t₂)*w) ω| := by
  obtain ⟨μ₀,hμ₀,hμ⟩ := thermal_velocity_collapsed_uniform hα hγ ha (half_pos hδ)
  refine ⟨μ₀,hμ₀,?_⟩
  intro σ s d t₁ t₂ z w ω hs hs₀ ht₂ htt herr hlo hhi hball
  have herr' : |d*ω| < (δ/2)/2 := by linarith
  have hb := ballistic_axial_gap (ha.trans_le ht₂) htt z w
  have hc := hμ σ s d t₂ (z-(t₁-t₂)*w) ω hs hs₀ ht₂ herr'
  rcases hc with hc | hc | hc
  · have h := abs_sub_le w
      (JetCoreMap.axialMap σ α γ s d t₂ (z-(t₁-t₂)*w) ω) (σ-α)
    linarith
  · have h := abs_sub_le w
      (JetCoreMap.axialMap σ α γ s d t₂ (z-(t₁-t₂)*w) ω) (σ+α)
    linarith
  · have h := abs_sub_le w
      (JetCoreMap.axialMap σ α γ s d t₂ (z-(t₁-t₂)*w) ω) ((z-(t₁-t₂)*w)/t₂)
    linarith

end BoltzmannNonuniqueness.AxialFlow

end

end

end OAI
