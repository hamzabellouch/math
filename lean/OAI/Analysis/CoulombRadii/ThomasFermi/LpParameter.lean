import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.TfExtendNonneg
import OAI.Analysis.CoulombRadii.RandomFields.JointSlice

namespace OAI

noncomputable section

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Classical BigOperators Topology
namespace Coulomb

lemma aestronglyMeasurable_of_dist {α B : Type*} [MeasurableSpace α]
    {μ : Measure α} [MetricSpace B] [CompleteSpace B] [SecondCountableTopology B]
    [MeasurableSpace B] [BorelSpace B] [Nonempty B] (f : α → B)
    (h : ∀ b, AEMeasurable (fun x => dist (f x) b) μ) : AEStronglyMeasurable f μ := by
  obtain ⟨v,hv⟩ := TopologicalSpace.exists_dense_seq B
  let e : B → ℕ → ℝ := fun b n => dist b (v n)
  have he : Continuous e := continuous_pi (fun n => continuous_id.dist continuous_const)
  have hei : Function.Injective e := by
    intro a b hab
    have H : (fun z => dist a z)=(fun z => dist b z) :=
      Continuous.ext_on hv (continuous_const.dist continuous_id)
        (continuous_const.dist continuous_id) (by
          rintro _ ⟨n,rfl⟩
          exact congrFun hab n)
    have HH := congrFun H b
    simpa only [dist_self,dist_eq_zero] using HH
  have hem := he.measurableEmbedding hei
  apply (hem.aemeasurable_comp_iff.mp (AEMeasurable.of_eval (fun index => h (v index)))).aestronglyMeasurable

lemma tfField_parameter_aestronglyMeasurable {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {Ω : Set Space} [IsFiniteMeasure (volume.restrict Ω)]
    (W : A → TFLq (volume.restrict Ω)) (Φ : A × Space → ℝ)
    (hΦ : AEStronglyMeasurable Φ (μ.prod (volume.restrict Ω)))
    (hW : ∀ᵐ a ∂μ, W a =ᵐ[volume.restrict Ω] fun y => Φ (a,y)) :
    AEStronglyMeasurable W μ := by
  have : Fact (TFFieldExponent ≠ ∞) := ⟨by simp [TFFieldExponent]⟩
  let : MeasurableSpace (TFLq (volume.restrict Ω)) := borel _
  let : BorelSpace (TFLq (volume.restrict Ω)) := ⟨rfl⟩
  apply aestronglyMeasurable_of_dist
  intro g
  have hD := hΦ.sub ((Lp.aestronglyMeasurable g).comp_snd (μ := μ))
  have hI := (hD.enorm.pow_const (5/2:ℝ)).lintegral_prod_right'
  have hM := (hI.pow_const (2/5:ℝ)).ennreal_toReal
  apply hM.congr
  filter_upwards [hW] with a ha
  rw [Lp.dist_def]
  have he : (⇑(W a)-⇑g) =ᵐ[volume.restrict Ω] fun y => Φ (a,y)-g y := by
    filter_upwards [ha] with y hy
    simp only [Pi.sub_apply,hy]
  rw [eLpNorm_congr_ae he]
  have hmeas := ((Lp.aestronglyMeasurable (W a)).sub (Lp.aestronglyMeasurable g)).congr he
  norm_num [eLpNorm,eLpNorm',TFFieldExponent,hmeas]

lemma coreScreenedField_memLp {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
    {d : ℝ} (hd : 0<d) (hn : ∀ j x, x∈Ω → d≤‖x-S.position j‖) :
    MemLp (coreScreenedField S u) TFFieldExponent (volume.restrict Ω) := by
  let C := ∑ s : Spins k, ∑ i : Fin k,
      (4*(∑ b : Fin 3, ∫ x, ‖u.gradient s (i,b) x‖^2)+(1/4:ℝ)*(∫ x, ‖u.value s x‖^2))
  apply MemLp.of_bound ((coreField_aestronglyMeasurable S u).mono_measure Measure.restrict_le_self)
    (totalCharge S/d+C)
  filter_upwards [ae_restrict_mem hΩ] with x hx
  have ha := attraction_le_totalCharge_div S hd x (fun j => hn j x hx)
  have hc : coreCoulombPotential u x≤C := coreCoulombPotential_bound u x
  have hp := coreCoulombPotential_nonneg u x
  have hA := attraction_nonneg S x
  have hC : 0≤C := hp.trans hc
  have hT : 0≤totalCharge S/d := hA.trans ha
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  dsimp [coreScreenedField]
  constructor <;> linarith

def coreTFField {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
    {d : ℝ} (hd : 0<d) (hn : ∀ j x, x∈Ω → d≤‖x-S.position j‖) : TFLq (volume.restrict Ω) :=
  (coreScreenedField_memLp S u hΩ hd hn).toLp _

lemma coreTFField_coe {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
    {d : ℝ} (hd : 0<d) (hn : ∀ j x, x∈Ω → d≤‖x-S.position j‖) :
    coreTFField S u hΩ hd hn =ᵐ[volume.restrict Ω] coreScreenedField S u := MemLp.coeFn_toLp _

lemma coreScreenedField_normalized_slice_joint {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m) :
    AEStronglyMeasurable (fun z : Configuration m × Space =>
      coreScreenedField S (u.coreSlice s z.1).normalized z.2) (volume.prod volume) := by
  have H := restrictedCorePotential_normalized_slice_joint u s MeasurableSet.univ
  have he (v : H1Vector k) : restrictedCorePotential v univ=coreCoulombPotential v := by
    funext x
    simp only [restrictedCorePotential,mem_univ,ite_true,coreCoulombPotential]
  simp_rw [he] at H
  exact ((attraction_measurable S).comp measurable_snd).aestronglyMeasurable.sub H

lemma coreTFField_slice_aestronglyMeasurable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m)
    {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
    {d : ℝ} (hd : 0<d) (hn : ∀ j x, x∈Ω → d≤‖x-S.position j‖) :
    AEStronglyMeasurable (fun x => coreTFField S (u.coreSlice s x).normalized hΩ hd hn) volume := by
  apply tfField_parameter_aestronglyMeasurable _
    (fun z => coreScreenedField S (u.coreSlice s z.1).normalized z.2)
  · exact (coreScreenedField_normalized_slice_joint S u s).mono_measure
      (Measure.prod_mono le_rfl Measure.restrict_le_self)
  · exact Eventually.of_forall (fun x => coreTFField_coe S _ hΩ hd hn)

end Coulomb

end
open MeasureTheory Filter Set
open scoped ENNReal NNReal Classical BigOperators Topology SchwartzMap
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

lemma continuous_tfEnergy_joint (c : ℝ) :
    Continuous (fun z : TFLq (volume.restrict Ω) × TFLp (volume.restrict Ω) => tfEnergy hΩ c z.1 z.2) := by
  unfold tfEnergy tfFunctional
  apply (((continuous_snd.norm.rpow_const (fun _ => Or.inr (by norm_num : (0:ℝ)≤5/3))).const_mul c).sub
    tfFieldContinuous.continuous₂).add
  exact ((tfCoulombContinuous hΩ).continuous₂.comp (continuous_snd.prodMk continuous_snd)).div_const 2

lemma continuous_tfMass : Continuous (fun f : TFLp (volume.restrict Ω) => ∫ x in Ω, f x) := by
  let h1 : MemLp (fun _ : Space => (1:ℝ)) TFFieldExponent (volume.restrict Ω) := memLp_const 1
  let W : TFLq (volume.restrict Ω) := h1.toLp _
  have he : (fun f : TFLp (volume.restrict Ω) => ∫ x in Ω, f x) = tfFieldContinuous W := by
    funext f
    rw [tfFieldContinuous_apply]
    apply integral_congr_ae
    filter_upwards [h1.coeFn_toLp] with x hx
    simp only [W,hx,one_mul]
  rw [he]
  exact (tfFieldContinuous W).continuous

omit [IsFiniteMeasure (volume.restrict Ω)] in
include hΩ in
lemma integral_tfDensity [IsFiniteMeasure (volume.restrict Ω)]
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    (∫ x, tfDensity Ω f x)=∫ x in Ω, f x := by
  rw [integral_congr_ae (tfDensity_ae_tfExtend hΩ hf)]
  exact integral_indicator hΩ

lemma localTFEnergy_nonpos (W : TFLq (volume.restrict Ω)) :
    tfEnergy hΩ thomasFermiKineticConstant W (localTFMinimizer hΩ W)≤0 := by
  have H := localTFMinimizer_minimizes hΩ W (f := 0) (by
    filter_upwards [Lp.coeFn_zero ℝ TFExponent (volume.restrict Ω)] with x hx
    simp only [hx,Pi.zero_apply,le_refl])
  simpa only [tfEnergy,tfFunctional,norm_zero,Real.zero_rpow (by norm_num : (5/3:ℝ)≠0),
    mul_zero,map_zero,sub_zero,_root_.zero_apply,zero_div,add_zero] using H

lemma localTFEnergy_abs_bound {D F : ℝ} (hD : 0<D) (_ : 0≤F)
    (hd : ∀ x∈Ω, ∀ y∈Ω, ‖x-y‖≤D) (W : TFLq (volume.restrict Ω))
    (hW : ∀ᵐ x ∂volume.restrict Ω, W x≤F) :
    |tfEnergy hΩ thomasFermiKineticConstant W (localTFMinimizer hΩ W)|≤D*F^2/2 := by
  have H := tfEnergy_mass_lower hΩ (c := thomasFermiKineticConstant) hD hd W hW
    (localTFMinimizer_nonneg hΩ W)
  have hp : 0≤thomasFermiKineticConstant*‖localTFMinimizer hΩ W‖^(5/3:ℝ) :=
    mul_nonneg thomasFermiKineticConstant_pos.le (Real.rpow_nonneg (norm_nonneg _) _)
  rw [abs_of_nonpos (localTFEnergy_nonpos hΩ W)]
  have hs := sq_nonneg ((∫ x in Ω, localTFMinimizer hΩ W x)-D*F)
  have hh := mul_le_mul_of_nonneg_left H (show 0≤2*D by positivity)
  field_simp at hh
  nlinarith

lemma localTFMass_bound {D F : ℝ} (hD : 0<D) (hF : 0≤F)
    (hd : ∀ x∈Ω, ∀ y∈Ω, ‖x-y‖≤D) (W : TFLq (volume.restrict Ω))
    (hW : ∀ᵐ x ∂volume.restrict Ω, W x≤F) :
    0≤(∫ y, localTFDensity hΩ W y) ∧ (∫ y, localTFDensity hΩ W y)≤2*D*F := by
  rw [localTFDensity,integral_tfDensity hΩ (localTFMinimizer_nonneg hΩ W)]
  exact ⟨tfMass_nonneg (localTFMinimizer_nonneg hΩ W),
    (tfEnergy_sublevel_mass_bound hΩ hD thomasFermiKineticConstant_pos hF hd W hW
      (localTFMinimizer_nonneg hΩ W) (localTFEnergy_nonpos hΩ W)).1⟩

lemma conditional_localTF_integrable {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (W : A → TFLq (volume.restrict Ω)) (hWm : AEStronglyMeasurable W μ)
    (w F : A → ℝ) (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0≤w x)
    (hF : ∀ᵐ x ∂μ, 0≤F x) (hFi : Integrable (fun x => w x*(F x)^2) μ)
    {D : ℝ} (hD : 0<D) (hd : ∀ x∈Ω, ∀ y∈Ω, ‖x-y‖≤D)
    (hcap : ∀ᵐ x ∂μ, ∀ᵐ y ∂volume.restrict Ω, W x y≤F x) :
    Integrable (fun x => w x*(∫ y, localTFDensity hΩ (W x) y)) μ ∧
    Integrable (fun x => w x*tfEnergy hΩ thomasFermiKineticConstant (W x) (localTFMinimizer hΩ (W x))) μ := by
  have hf := (continuous_localTFMinimizer hΩ).comp_aestronglyMeasurable hWm
  have hm : AEStronglyMeasurable (fun x => ∫ y, localTFDensity hΩ (W x) y) μ := by
    have he : (fun x => ∫ y, localTFDensity hΩ (W x) y)=
        (fun x => ∫ y in Ω, localTFMinimizer hΩ (W x) y) := by
      funext x
      exact integral_tfDensity hΩ (localTFMinimizer_nonneg hΩ (W x))
    rw [he]
    exact (continuous_tfMass).comp_aestronglyMeasurable hf
  have he := (continuous_tfEnergy_joint hΩ thomasFermiKineticConstant).comp_aestronglyMeasurable
    (hWm.prodMk hf)
  constructor
  · apply ((hw.add hFi).const_mul D).mono' (hw.aestronglyMeasurable.mul hm)
    filter_upwards [hw0,hF,hcap] with x hx hf hc
    have H := localTFMass_bound hΩ hD hf hd (W x) hc
    dsimp only [Pi.mul_apply, Pi.add_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hx H.1)]
    have HH := mul_le_mul_of_nonneg_left H.2 hx
    have hsq := mul_nonneg hx (sq_nonneg (F x-1))
    have hmul := mul_nonneg hD.le hsq
    nlinarith
  · apply (hFi.const_mul (D/2)).mono' (hw.aestronglyMeasurable.mul he)
    filter_upwards [hw0,hF,hcap] with x hx hf hc
    dsimp only [Pi.mul_apply]
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hx,Real.norm_eq_abs]
    have H := mul_le_mul_of_nonneg_left (localTFEnergy_abs_bound hΩ hD hf hd (W x) hc) hx
    calc
      _ ≤ w x*(D*F x^2/2) := H
      _ = _ := by ring

lemma coreTF_conditional_integrable {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    (s : Spins m) {d : ℝ} (hd : 0<d) (hn : ∀ j x, x∈Ω → d≤‖x-S.position j‖)
    {D : ℝ} (hD : 0<D) (hdiam : ∀ x∈Ω, ∀ y∈Ω, ‖x-y‖≤D)
    (F : Configuration m → ℝ) (hF : ∀ᵐ x, 0≤F x)
    (hFi : Integrable (fun x => mass (u.coreSlice s x)*(F x)^2))
    (hcap : ∀ᵐ x, ∀ y∈Ω, coreScreenedField S (u.coreSlice s x).normalized y≤F x) :
    Integrable (fun x => mass (u.coreSlice s x)*(∫ y,
      localTFDensity hΩ (coreTFField S (u.coreSlice s x).normalized hΩ hd hn) y)) ∧
    Integrable (fun x => mass (u.coreSlice s x)*rawThomasFermiEnergy
      (coreScreenedField S (u.coreSlice s x).normalized)
      (localTFDensity hΩ (coreTFField S (u.coreSlice s x).normalized hΩ hd hn))) := by
  have H := conditional_localTF_integrable hΩ _ (coreTFField_slice_aestronglyMeasurable S u s hΩ hd hn)
    (fun x => mass (u.coreSlice s x)) F (mass_coreSlice_integrable u s)
    (Eventually.of_forall (fun x => mass_nonneg _)) hF hFi hD hdiam (show ∀ᵐ x,
      ∀ᵐ y ∂volume.restrict Ω, coreTFField S (u.coreSlice s x).normalized hΩ hd hn y≤F x from ?_)
  · refine ⟨H.1,H.2.congr (Eventually.of_forall (fun x => ?_))⟩
    apply congrArg (fun E => mass (u.coreSlice s x)*E)
    exact (rawThomasFermiEnergy_tfDensity hΩ _ _ (coreTFField_coe S _ hΩ hd hn)
      (localTFMinimizer_nonneg hΩ _)).symm
  · filter_upwards [hcap] with x hx
    filter_upwards [ae_restrict_mem hΩ,coreTFField_coe S (u.coreSlice s x).normalized hΩ hd hn] with y hy he
    rw [he]
    exact hx y hy

end Coulomb

end

end OAI
