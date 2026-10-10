import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.RawThomasFermiEnergy
import OAI.Analysis.CoulombRadii.ThomasFermi.TfFunctionalUniformBound

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
include hΩ
omit [IsFiniteMeasure (volume.restrict Ω)] in
lemma tfExtend_nonneg {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    ∀ᵐ x, 0 ≤ tfExtend Ω f x := by
  filter_upwards [(ae_restrict_iff' hΩ).mp hf] with x hx
  by_cases hs : x ∈ Ω
  · simpa only [tfExtend,Set.indicator_of_mem hs] using hx hs
  · simp [tfExtend,hs]
omit [IsFiniteMeasure (volume.restrict Ω)] in
lemma tfPotential_nonneg {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) (x : Space) :
    0 ≤ tfPotential f x := by
  apply integral_nonneg_of_ae
  filter_upwards [tfExtend_nonneg hΩ hf] with y hy
  exact mul_nonneg (coulombKernel_nonneg _) hy
omit [IsFiniteMeasure (volume.restrict Ω)] in
lemma tfPotential_restrict (f : TFLp (volume.restrict Ω)) (x : Space) :
    tfPotential f x = ∫ y in Ω, coulombKernel (x-y)*f y := by
  unfold tfPotential tfExtend
  rw [←integral_indicator hΩ]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ Ω <;> simp [hy]
lemma tfPotential_restrict_integrable (f : TFLp (volume.restrict Ω)) (x : Space) :
    Integrable (fun y => coulombKernel (x-y)*f y) (volume.restrict Ω) := by
  apply (integrable_indicator_iff hΩ).mp
  apply (tfPotential_integrand hΩ f x).congr
  filter_upwards [] with y
  by_cases hy : y ∈ Ω <;> simp [tfExtend,hy]
lemma tfPotential_mass_lower {D : ℝ} (_hD : 0 < D)
    (hd : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖x-y‖ ≤ D) {f : TFLp (volume.restrict Ω)}
    (hf : TFNonneg f) {x : Space} (hx : x ∈ Ω) :
    (∫ y in Ω,f y)/D ≤ tfPotential f x := by
  rw [tfPotential_restrict hΩ,←integral_div]
  apply integral_mono_ae ((Lp.memLp f).integrable (by norm_num [TFExponent]) |>.div_const D)
    (tfPotential_restrict_integrable hΩ f x)
  filter_upwards [hf,ae_restrict_mem hΩ,(volume.restrict Ω).ae_ne x] with y hy hs hn
  have hk : 1/D ≤ coulombKernel (x-y) := by
    rw [coulombKernel,←one_div]
    apply one_div_le_one_div_of_le
    · exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hn))
    · exact hd x hx y hs
  simpa only [div_eq_mul_inv,one_mul,mul_comm (D⁻¹) (f y)] using mul_le_mul_of_nonneg_right hk hy
omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma tfMass_nonneg {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    0 ≤ ∫ x in Ω,f x := integral_nonneg_of_ae hf
lemma tfCoulomb_mass_lower {D : ℝ} (hD : 0 < D)
    (hd : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖x-y‖ ≤ D) {f : TFLp (volume.restrict Ω)}
    (hf : TFNonneg f) :
    (∫ x in Ω,f x)^2/D ≤ tfCoulomb Ω f f := by
  rw [tfCoulomb_eq_potential hΩ]
  have hi : Integrable (fun x => f x*tfPotential f x) (volume.restrict Ω) := by
    apply (tfFieldPairing_integrable (tfPotentialField hΩ f) f).congr
    filter_upwards [tfPotentialField_coe hΩ f] with x hx
    rw [hx,mul_comm]
  calc
    _ = ∫ x in Ω,f x*((∫ y in Ω,f y)/D) := by rw [integral_mul_const]; ring
    _ ≤ _ := integral_mono_ae ((Lp.memLp f).integrable (by norm_num [TFExponent]) |>.mul_const _) hi
      (by
        filter_upwards [hf,ae_restrict_mem hΩ] with x hx hs
        exact mul_le_mul_of_nonneg_left (tfPotential_mass_lower hΩ hD hd hf hs) hx)
lemma tfEnergy_mass_lower {D c F : ℝ} (hD : 0 < D)
    (hd : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖x-y‖ ≤ D) (W : TFLq (volume.restrict Ω))
    (hF : ∀ᵐ x ∂volume.restrict Ω,W x ≤ F) {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    c*‖f‖^(5/3:ℝ)+(∫ x in Ω,f x)^2/(2*D)-F*(∫ x in Ω,f x) ≤ tfEnergy hΩ c W f := by
  have Hf : tfFieldContinuous W f ≤ F*(∫ x in Ω,f x) := by
    rw [tfFieldContinuous_apply,←integral_const_mul]
    apply integral_mono_ae (tfFieldPairing_integrable W f)
      ((Lp.memLp f).integrable (by norm_num [TFExponent]) |>.const_mul F)
    filter_upwards [hf,hF] with x hx hy
    exact mul_le_mul_of_nonneg_right hy hx
  have HB := tfCoulomb_mass_lower hΩ hD hd hf
  change _ ≤ c*‖f‖^(5/3:ℝ)-tfFieldContinuous W f+tfCoulomb Ω f f/2
  have he : (∫ x in Ω,f x)^2/(2*D) = ((∫ x in Ω,f x)^2/D)/2 := by ring
  rw [he]
  linarith
lemma tfEnergy_sublevel_mass_bound {D c F : ℝ} (hD : 0 < D) (hc : 0 < c) (hF0 : 0 ≤ F)
    (hd : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖x-y‖ ≤ D) (W : TFLq (volume.restrict Ω))
    (hF : ∀ᵐ x ∂volume.restrict Ω,W x ≤ F) {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (he : tfEnergy hΩ c W f ≤ 0) :
    (∫ x in Ω,f x) ≤ 2*D*F ∧ ‖f‖^(5/3:ℝ) ≤ D*F^2/(2*c) := by
  have H := tfEnergy_mass_lower hΩ (c := c) hD hd W hF hf
  have hm := tfMass_nonneg hf
  have hk := Real.rpow_nonneg (norm_nonneg f) (5/3:ℝ)
  have H1 : c*‖f‖^(5/3:ℝ)+(∫ x in Ω,f x)^2/(2*D)-F*(∫ x in Ω,f x) ≤ 0 := H.trans he
  have H2 : 2*D*c*‖f‖^(5/3:ℝ)+(∫ x in Ω,f x)^2-2*D*F*(∫ x in Ω,f x) ≤ 0 := by
    have H3 := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 2*D by positivity) H1
    field_simp at H3
    nlinarith
  refine ⟨?_,?_⟩
  · have Hkin : 0 ≤ 2*D*c*‖f‖^(5/3:ℝ) := by positivity
    by_contra! hn
    have hmpos : 0 < ∫ x in Ω,f x := (show 0 ≤ 2*D*F by positivity).trans_lt hn
    have Hp := mul_pos hmpos (sub_pos.mpr hn)
    nlinarith
  · apply (le_div_iff₀ (show 0<2*c by positivity)).mpr
    have Hsq := sq_nonneg ((∫ x in Ω,f x)-D*F)
    nlinarith
end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical BigOperators Topology SchwartzMap Pointwise
namespace Coulomb

lemma coulombBilinear_congr_ae {f f' g g' : Space → ℝ}
    (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') :
    coulombBilinear f g = coulombBilinear f' g' := by
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Space)) (ν := (volume : Measure Space))).ae_eq_comp hf
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Space)) (ν := (volume : Measure Space))).ae_eq_comp hg
  unfold coulombBilinear
  rw [Measure.volume_eq_prod]
  apply integral_congr_ae
  filter_upwards [h1,h2] with xy hx hy
  simp only [Function.comp_def] at hx hy
  rw [hx,hy]

lemma rawThomasFermiEnergy_congr_ae (Φ : Space → ℝ) {f g : Space → ℝ}
    (h : f =ᵐ[volume] g) : rawThomasFermiEnergy Φ f = rawThomasFermiEnergy Φ g := by
  have h1 : (∫ x, f x^(5/3:ℝ)) = ∫ x, g x^(5/3:ℝ) :=
    integral_congr_ae (h.mono fun _ hx => congrArg (·^(5/3:ℝ)) hx)
  have h2 : (∫ x, Φ x*f x) = ∫ x, Φ x*g x :=
    integral_congr_ae (h.mono fun x hx => congrArg (Φ x*·) hx)
  simp only [rawThomasFermiEnergy, h1, h2, coulombBilinear_congr_ae h h]

lemma rawThomasFermiEnergy_tfExtend {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    rawThomasFermiEnergy Φ (tfExtend Ω f) = tfEnergy hΩ thomasFermiKineticConstant W f := by
  have hk : (∫ x, (tfExtend Ω f x)^(5/3:ℝ)) = ∫ x in Ω, (f x)^(5/3:ℝ) := by
    rw [← integral_indicator hΩ]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ Ω <;> simp [tfExtend,hx]
  have hw : (∫ x, Φ x*tfExtend Ω f x) = ∫ x in Ω, W x*f x := by
    calc
      _ = ∫ x in Ω, Φ x*f x := by
        rw [← integral_indicator hΩ]
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ Ω <;> simp [tfExtend,hx]
      _ = _ := integral_congr_ae (hW.mono fun x hx => by rw [hx])
  rw [rawThomasFermiEnergy, hk, hw, tfEnergy_formula hΩ _ _ hf]
  rfl

def tfDensity (Ω : Set Space) (f : TFLp (volume.restrict Ω)) (x : Space) : ℝ :=
  max (tfExtend Ω f x) 0

lemma tfDensity_nonneg {Ω : Set Space} (f : TFLp (volume.restrict Ω)) (x : Space) :
    0 ≤ tfDensity Ω f x := le_max_right _ _
lemma tfDensity_measurable {Ω : Set Space} (hΩ : MeasurableSet Ω) (f : TFLp (volume.restrict Ω)) :
    Measurable (tfDensity Ω f) := (tfExtend_measurable hΩ f).max measurable_const
lemma tfDensity_eq_zero {Ω : Set Space} (f : TFLp (volume.restrict Ω)) {x : Space} (hx : x ∉ Ω) :
    tfDensity Ω f x = 0 := by simp [tfDensity,tfExtend,hx]
lemma tfDensity_ae_tfExtend {Ω : Set Space} (hΩ : MeasurableSet Ω)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    tfDensity Ω f =ᵐ[volume] tfExtend Ω f :=
  (tfExtend_nonneg hΩ hf).mono fun _ hx => max_eq_left hx
lemma tfDensity_memLp {Ω : Set Space} (hΩ : MeasurableSet Ω)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    MemLp (tfDensity Ω f) TFExponent volume :=
  (memLp_congr_ae (tfDensity_ae_tfExtend hΩ hf)).mpr (tfExtend_memLp hΩ f)
lemma tfDensity_power_integrable {Ω : Set Space} (hΩ : MeasurableSet Ω)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    Integrable (fun x => (tfDensity Ω f x)^(5/3:ℝ)) :=
  integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3)
    (tfDensity_memLp hΩ hf) (Eventually.of_forall (tfDensity_nonneg f))
lemma rawThomasFermiEnergy_tfDensity {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    rawThomasFermiEnergy Φ (tfDensity Ω f) = tfEnergy hΩ thomasFermiKineticConstant W f := by
  rw [rawThomasFermiEnergy_congr_ae Φ (tfDensity_ae_tfExtend hΩ hf)]
  exact rawThomasFermiEnergy_tfExtend hΩ Φ W hW hf

lemma thomasFermiKineticConstant_pos : 0 < thomasFermiKineticConstant := by
  unfold thomasFermiKineticConstant
  positivity

def localTFMinimizer {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (W : TFLq (volume.restrict Ω)) : TFLp (volume.restrict Ω) :=
  tfMinimizer hΩ thomasFermiKineticConstant_pos W
lemma localTFMinimizer_nonneg {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (W : TFLq (volume.restrict Ω)) :
    TFNonneg (localTFMinimizer hΩ W) :=
  tfMinimizer_nonneg hΩ thomasFermiKineticConstant_pos W
lemma localTFMinimizer_minimizes {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (W : TFLq (volume.restrict Ω))
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    tfEnergy hΩ thomasFermiKineticConstant W (localTFMinimizer hΩ W) ≤
      tfEnergy hΩ thomasFermiKineticConstant W f :=
  tfMinimizer_min hΩ thomasFermiKineticConstant_pos W f hf

lemma continuous_localTFMinimizer {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] : Continuous (localTFMinimizer hΩ) :=
  tfMinimizer_continuous hΩ thomasFermiKineticConstant_pos

def localTFDensity {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (W : TFLq (volume.restrict Ω)) : Space → ℝ :=
  tfDensity Ω (localTFMinimizer hΩ W)

lemma localTFDensity_hole {M k : ℕ} {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (W : TFLq (volume.restrict Ω))
    (S : Nuclei M) (u : H1Vector k) (g : 𝓢(Space,ℝ)) (R : ℝ)
    (K A : Set Space) (hK : IsCompact K) (hA : IsClosed A) (hΩK : Ω ⊆ K)
    (hu : SpatiallySupported u A) (hsep : Disjoint A (K+tsupport (g : Space → ℝ)))
    (hcore : ∀ a ∈ A, ∀ y ∈ Ω, R ≤ ‖a-y‖)
    (hnuc : ∀ j y, y ∈ Ω → R ≤ ‖S.position j-y‖) :
    SourceFreeHoleDensity S u g R (localTFDensity hΩ W) K A := by
  have hs (y : Space) (hy : localTFDensity hΩ W y ≠ 0) : y ∈ Ω := by
    by_contra hn
    exact hy (tfDensity_eq_zero _ hn)
  refine ⟨tfDensity_nonneg _,tfDensity_measurable hΩ _,
    tfDensity_power_integrable hΩ (localTFMinimizer_nonneg hΩ W),hK,hA,?_,hu,hsep,?_,?_⟩
  · intro y hy
    exact tfDensity_eq_zero _ (fun h => hy (hΩK h))
  · intro a ha y hy
    exact hcore a ha y (hs y hy)
  · intro j y hy
    exact hnuc j y (hs y hy)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical BigOperators Topology SchwartzMap Pointwise
namespace Coulomb

def rawTFBregman (ρ σ : Space → ℝ) : ℝ :=
  thomasFermiKineticConstant*∫ x, σ x^(5/3:ℝ)-ρ x^(5/3:ℝ)-
    (5/3:ℝ)*ρ x^(2/3:ℝ)*(σ x-ρ x)

lemma tfExtend_sub_ae {Ω : Set Space} (hΩ : MeasurableSet Ω)
    (f g : TFLp (volume.restrict Ω)) :
    tfExtend Ω (g-f) =ᵐ[volume] fun x => tfExtend Ω g x-tfExtend Ω f x := by
  filter_upwards [(ae_restrict_iff' hΩ).mp (Lp.coeFn_sub g f)] with x hx
  by_cases h : x ∈ Ω
  · simpa only [tfExtend,Set.indicator_of_mem h,Pi.sub_apply] using hx h
  · simp [tfExtend,h]

lemma coulombBilinear_tfDensity_sub {Ω : Set Space} (hΩ : MeasurableSet Ω)
    {f g : TFLp (volume.restrict Ω)} (hf : TFNonneg f) (hg : TFNonneg g) :
    coulombBilinear (fun x => tfDensity Ω g x-tfDensity Ω f x)
      (fun x => tfDensity Ω g x-tfDensity Ω f x) = tfCoulomb Ω (g-f) (g-f) := by
  have h : (fun x => tfDensity Ω g x-tfDensity Ω f x) =ᵐ[volume] tfExtend Ω (g-f) := by
    filter_upwards [tfDensity_ae_tfExtend hΩ hf,tfDensity_ae_tfExtend hΩ hg,tfExtend_sub_ae hΩ f g]
      with x hx hy hz
    rw [hx,hy,hz]
  exact coulombBilinear_congr_ae h h

lemma rawTFBregman_congr_ae {ρ σ ρ' σ' : Space → ℝ}
    (hρ : ρ =ᵐ[volume] ρ') (hσ : σ =ᵐ[volume] σ') :
    rawTFBregman ρ σ = rawTFBregman ρ' σ' := by
  unfold rawTFBregman
  congr 1
  apply integral_congr_ae
  filter_upwards [hρ,hσ] with x hx hy
  rw [hx,hy]

lemma rawTFBregman_tfDensity {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)]
    {f g : TFLp (volume.restrict Ω)} (hf : TFNonneg f) (hg : TFNonneg g) :
    rawTFBregman (tfDensity Ω f) (tfDensity Ω g) = thomasFermiKineticConstant*tfBregman f g := by
  rw [rawTFBregman_congr_ae (tfDensity_ae_tfExtend hΩ hf) (tfDensity_ae_tfExtend hΩ hg),
    rawTFBregman, tfBregman_formula hf hg, ← integral_indicator hΩ]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Ω <;> simp [tfExtend,hx]

lemma raw_localTF_gap {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    coulombBilinear (fun x => tfDensity Ω f x-localTFDensity hΩ W x)
      (fun x => tfDensity Ω f x-localTFDensity hΩ W x)/2+
      rawTFBregman (localTFDensity hΩ W) (tfDensity Ω f) ≤
    rawThomasFermiEnergy Φ (tfDensity Ω f)-rawThomasFermiEnergy Φ (localTFDensity hΩ W) := by
  unfold localTFDensity
  rw [coulombBilinear_tfDensity_sub hΩ (localTFMinimizer_nonneg hΩ W) hf,
    rawTFBregman_tfDensity hΩ (localTFMinimizer_nonneg hΩ W) hf,
    rawThomasFermiEnergy_tfDensity hΩ Φ W hW hf,
    rawThomasFermiEnergy_tfDensity hΩ Φ W hW (localTFMinimizer_nonneg hΩ W)]
  exact tfEnergy_gap_controls hΩ _ W (localTFMinimizer_nonneg hΩ W) hf
    (fun _ hf => localTFMinimizer_minimizes hΩ W hf)

def rawToTFLp {Ω : Set Space} (σ : Space → ℝ) (hσ : MemLp σ TFExponent (volume.restrict Ω)) :
    TFLp (volume.restrict Ω) := hσ.toLp σ

lemma rawToTFLp_nonneg {Ω : Set Space} {σ : Space → ℝ}
    (hσ : MemLp σ TFExponent (volume.restrict Ω)) (hp : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ σ x) :
    TFNonneg (rawToTFLp σ hσ) := by
  filter_upwards [hσ.coeFn_toLp,hp] with x hx hy
  exact hx.symm ▸ hy

lemma tfDensity_rawToTFLp {Ω : Set Space} (hΩ : MeasurableSet Ω) {σ : Space → ℝ}
    (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ σ x) (hs : ∀ x ∉ Ω, σ x = 0) :
    tfDensity Ω (rawToTFLp σ hσ) =ᵐ[volume] σ := by
  refine (tfDensity_ae_tfExtend hΩ (rawToTFLp_nonneg hσ hp)).trans ?_
  filter_upwards [(ae_restrict_iff' hΩ).mp hσ.coeFn_toLp] with x hx
  by_cases hy : x ∈ Ω
  · simpa only [tfExtend,rawToTFLp,Set.indicator_of_mem hy] using hx hy
  · simp [tfExtend,hy,hs x hy]

lemma raw_localTF_gap_density {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {σ : Space → ℝ} (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ σ x) (hs : ∀ x ∉ Ω, σ x = 0) :
    coulombBilinear (fun x => σ x-localTFDensity hΩ W x)
      (fun x => σ x-localTFDensity hΩ W x)/2+
      rawTFBregman (localTFDensity hΩ W) σ ≤
    rawThomasFermiEnergy Φ σ-rawThomasFermiEnergy Φ (localTFDensity hΩ W) := by
  have he := tfDensity_rawToTFLp hΩ hσ hp hs
  have hd : (fun x => tfDensity Ω (rawToTFLp σ hσ) x-localTFDensity hΩ W x) =ᵐ[volume]
      (fun x => σ x-localTFDensity hΩ W x) := he.sub EventuallyEq.rfl
  have H := raw_localTF_gap hΩ Φ W hW (rawToTFLp_nonneg hσ hp)
  rwa [coulombBilinear_congr_ae hd hd,rawTFBregman_congr_ae EventuallyEq.rfl he,
    rawThomasFermiEnergy_congr_ae Φ he] at H

end Coulomb

end

end OAI
