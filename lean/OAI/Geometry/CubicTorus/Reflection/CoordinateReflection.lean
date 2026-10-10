import Mathlib
import OAI.Geometry.CubicTorus.Estimates.HolderNear

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coordinateReflection (i : Fin 3) : Torus → Torus :=
  fun x => WithLp.toLp 2 (fun j => if j=i then -x j else x j)

@[simp] lemma coordinateReflection_apply (i : Fin 3) (x : Torus) (j : Fin 3) :
    coordinateReflection i x j=if j=i then -x j else x j := rfl

@[simp] lemma coordinateReflection_involutive (i : Fin 3) (x : Torus) :
    coordinateReflection i (coordinateReflection i x)=x := by
  ext j
  by_cases h : j=i <;> simp [h]

lemma coordinateReflection_isometry (i : Fin 3) : Isometry (coordinateReflection i) := by
  apply Isometry.of_dist_eq
  intro x y
  simp only [dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j=i <;> simp [h,neg_add_eq_sub,norm_sub_rev]

def coordinateReflectionEquiv (i : Fin 3) : Torus ≃ᵢ Torus where
  toFun := coordinateReflection i
  invFun := coordinateReflection i
  left_inv := coordinateReflection_involutive i
  right_inv := coordinateReflection_involutive i
  isometry_toFun := coordinateReflection_isometry i

lemma coordinateReflection_continuous (i : Fin 3) : Continuous (coordinateReflection i) :=
  (coordinateReflection_isometry i).continuous

lemma coordinateReflection_measurePreserving (i : Fin 3) :
    MeasurePreserving (coordinateReflection i) torusVolume torusVolume := by
  have h (j : Fin 3) : MeasurePreserving
      (fun a : AddCircle (1 : ℝ) => if j=i then -a else a) volume volume := by
    by_cases hj : j=i
    · simpa only [ite_eq_left hj] using (Measure.measurePreserving_neg (volume : Measure (AddCircle (1 : ℝ))))
    · simp only [ite_eq_right hj]
      constructor
      · exact measurable_id
      · exact Measure.map_id
  exact product_to_torus_measurePreserving.comp ((volume_preserving_pi h).comp torus_to_product_measurePreserving)

def coverCoordinateReflection (i : Fin 3) : Cover ≃ₗᵢ[ℝ] Cover :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun j =>
    if j=i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

@[simp] lemma coverCoordinateReflection_apply (i : Fin 3) (x : Cover) (j : Fin 3) :
    coverCoordinateReflection i x j=if j=i then -x j else x j := by
  simp only [coverCoordinateReflection,LinearIsometryEquiv.piLpCongrRight_apply]
  split_ifs <;> rfl

@[simp] lemma coverCoordinateReflection_involutive (i : Fin 3) (x : Cover) :
    coverCoordinateReflection i (coverCoordinateReflection i x)=x := by
  ext j
  by_cases h : j=i <;> simp [h]

lemma quotientMap_coordinateReflection (i : Fin 3) (x : Cover) :
    quotientMap (coverCoordinateReflection i x)=coordinateReflection i (quotientMap x) := by
  ext j
  by_cases h : j=i <;> simp [quotientMap,h]

lemma coverCoordinateReflection_lattice (i : Fin 3) (m : Fin 3 → ℤ) :
    coverCoordinateReflection i (latticeVector m)=latticeVector (fun j => if j=i then -m j else m j) := by
  ext j
  by_cases h : j=i <;> simp [latticeVector,h]

lemma coverCoordinateReflection_single (i j : Fin 3) :
    coverCoordinateReflection i (EuclideanSpace.single j 1)=
      (if j=i then (-1 : ℝ) else 1) • EuclideanSpace.single j 1 := by
  ext k
  by_cases h : j=i
  · subst j
    by_cases hk : k=i <;> simp [hk]
  · by_cases hk : k=j
    · subst k; simp [h]
    · by_cases hi : k=i <;> simp [h,hk,hi]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coordinateReflectedField (i : Fin 3) (F : Cover → Cover) : Cover → Cover :=
  fun x => coverCoordinateReflection i (F (coverCoordinateReflection i x))

lemma coordinateReflectedField_contDiff (i : Fin 3) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (coordinateReflectedField i F) :=
  (coverCoordinateReflection i).toContinuousLinearEquiv.contDiff.comp
    (hF.comp (coverCoordinateReflection i).toContinuousLinearEquiv.contDiff)

lemma coordinateReflectedField_periodic (i : Fin 3) {F : Cover → Cover}
    (hp : ∀ n x,F (x+latticeVector n)=F x) :
    ∀ n x,coordinateReflectedField i F (x+latticeVector n)=coordinateReflectedField i F x := by
  intro n x
  simp only [coordinateReflectedField,map_add,coverCoordinateReflection_lattice,hp]

lemma coordinateReflectedField_admissible (i : Fin 3) {F : Cover → Cover}
    (hF : AdmissibleField F) : AdmissibleField (coordinateReflectedField i F) := by
  refine ⟨coordinateReflectedField_contDiff i hF.1,coordinateReflectedField_periodic i hF.2.1,?_⟩
  intro x
  simpa only [coordinateReflectedField,LinearIsometryEquiv.norm_map] using hF.2.2 (coverCoordinateReflection i x)

lemma coordinateReflectedField_divergence (i : Fin 3) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (coordinateReflectedField i F) x=divergence F (coverCoordinateReflection i x) := by
  have hd : HasFDerivAt (coordinateReflectedField i F)
      ((coverCoordinateReflection i).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((fderiv ℝ F (coverCoordinateReflection i x)).comp
          (coverCoordinateReflection i).toContinuousLinearEquiv.toContinuousLinearMap)) x :=
    (coverCoordinateReflection i).toContinuousLinearEquiv.hasFDerivAt.comp x
      (((hF.differentiable (by simp)) _).hasFDerivAt.comp x
        (coverCoordinateReflection i).toContinuousLinearEquiv.hasFDerivAt)
  unfold divergence
  rw [hd.fderiv]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,coverCoordinateReflection_single,map_smul,
    coverCoordinateReflection_apply,PiLp.smul_apply,smul_eq_mul]
  by_cases h : j=i <;> simp [h]

def coordinateEvenField (i : Fin 3) (F : Cover → Cover) : Cover → Cover :=
  fun x => (1/2 : ℝ) • (F x+coordinateReflectedField i F x)

lemma coordinateEvenField_admissible (i : Fin 3) {F : Cover → Cover}
    (hF : AdmissibleField F) : AdmissibleField (coordinateEvenField i F) := by
  have hr := coordinateReflectedField_admissible i hF
  refine ⟨(hF.1.add hr.1).const_smul (1/2 : ℝ),?_,?_⟩
  · intro n x
    simp only [coordinateEvenField,hF.2.1,hr.2.1]
  · intro x
    calc
      ‖coordinateEvenField i F x‖ = (1/2 : ℝ)*‖F x+coordinateReflectedField i F x‖ := by
        rw [coordinateEvenField,norm_smul]; norm_num
      _ ≤ (1/2 : ℝ)*(‖F x‖+‖coordinateReflectedField i F x‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
      _ ≤ 1 := by linarith [hF.2.2 x,hr.2.2 x]

lemma coordinateEvenField_reflection (i : Fin 3) (F : Cover → Cover) (x : Cover) :
    coordinateEvenField i F (coverCoordinateReflection i x)=
      coverCoordinateReflection i (coordinateEvenField i F x) := by
  simp only [coordinateEvenField,coordinateReflectedField,map_smul,map_add,coverCoordinateReflection_involutive]
  rw [add_comm]

lemma coordinateEvenField_divergence (i : Fin 3) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (coordinateEvenField i F) x=(1/2 : ℝ)*
      (divergence F x+divergence F (coverCoordinateReflection i x)) := by
  unfold coordinateEvenField
  rw [divergence_const_smul ((hF.add (coordinateReflectedField_contDiff i hF)).differentiable (by simp) x),
    divergence_add_fields (hF.differentiable (by simp) x)
      ((coordinateReflectedField_contDiff i hF).differentiable (by simp) x),coordinateReflectedField_divergence i hF]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma flux_coordinateReflection (i : Fin 3) {F : Cover → Cover} (hF : AdmissibleField F)
    {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (coordinateReflection i ⁻¹' E),divergence F x)=
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,divergence (coordinateReflectedField i F) x := by
  have hm := (coordinateReflection_continuous i).measurable
  have hr := coordinateReflectedField_admissible i hF
  rw [← setIntegral_lift (continuous_divergence hF.1) (divergence_periodic hF.2.1) (hm hE),
    ← setIntegral_lift (continuous_divergence hr.1) (divergence_periodic hr.2.1) hE]
  have he : (fun z : Torus => divergence F (representative z)) =
      (fun z => divergence (coordinateReflectedField i F) (representative (coordinateReflection i z))) := by
    funext z
    rw [coordinateReflectedField_divergence i hF.1,← periodic_representative (divergence_periodic hF.2.1)
      (coverCoordinateReflection i (representative (coordinateReflection i z))),
      quotientMap_coordinateReflection,quotientMap_representative,coordinateReflection_involutive]
  rw [he]
  exact (coordinateReflection_measurePreserving i).setIntegral_preimage_emb
    (coordinateReflectionEquiv i).toHomeomorph.measurableEmbedding
    (fun z => divergence (coordinateReflectedField i F) (representative z)) E

lemma perimeter_coordinateReflection_le (i : Fin 3) {E : Set Torus} (hE : MeasurableSet E) :
    perimeter (coordinateReflection i ⁻¹' E)≤perimeter E := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  rw [flux_coordinateReflection i hF hE]
  exact le_iSup_of_le (coordinateReflectedField i F)
    (le_iSup_of_le (coordinateReflectedField_admissible i hF) le_rfl)

lemma perimeter_coordinateReflection_measurable (i : Fin 3) {E : Set Torus} (hE : MeasurableSet E) :
    perimeter (coordinateReflection i ⁻¹' E)=perimeter E := by
  apply le_antisymm (perimeter_coordinateReflection_le i hE)
  have hh := perimeter_coordinateReflection_le i ((coordinateReflection_continuous i).measurable hE)
  have he : coordinateReflection i ⁻¹' (coordinateReflection i ⁻¹' E)=E := by
    ext z; simp
  rwa [he] at hh

theorem perimeter_coordinateReflection (i : Fin 3) {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume) :
    perimeter (coordinateReflection i ⁻¹' E)=perimeter E := by
  have he := hE.toMeasurable_ae_eq
  have hp := (coordinateReflection_measurePreserving i).quasiMeasurePreserving.preimage_ae_eq he
  rw [← perimeter_congr_ae hp,← perimeter_congr_ae he]
  exact perimeter_coordinateReflection_measurable i (measurableSet_toMeasurable _ _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def reflectionCompetitor (i : Fin 3) (E B : Set Torus) : Set Torus :=
  (E∩B) ∪ coordinateReflection i ⁻¹' (E∩B)

lemma reflectionCompetitor_measurable (i : Fin 3) {E B : Set Torus}
    (hE : MeasurableSet E) (hB : MeasurableSet B) : MeasurableSet (reflectionCompetitor i E B) :=
  (hE.inter hB).union ((coordinateReflection_continuous i).measurable (hE.inter hB))

lemma reflectionCompetitor_disjoint_parts (i : Fin 3) (E : Set Torus) {B : Set Torus}
    (hb : Disjoint B (coordinateReflection i ⁻¹' B)) :
    Disjoint (E∩B) (coordinateReflection i ⁻¹' (E∩B)) :=
  hb.mono inter_subset_right (preimage_mono inter_subset_right)

lemma reflectionCompetitor_volume (i : Fin 3) {E B : Set Torus}
    (hE : MeasurableSet E) (hB : MeasurableSet B)
    (hb : Disjoint B (coordinateReflection i ⁻¹' B)) :
    torusVolume (reflectionCompetitor i E B)=2*torusVolume (E∩B) := by
  rw [reflectionCompetitor,measure_union (reflectionCompetitor_disjoint_parts i E hb)
    ((coordinateReflection_continuous i).measurable (hE.inter hB)),
    (coordinateReflection_measurePreserving i).measure_preimage (hE.inter hB).nullMeasurableSet,two_mul]

lemma reflectionCompetitor_realVolume (i : Fin 3) {E B : Set Torus}
    (hE : MeasurableSet E) (hB : MeasurableSet B)
    (hb : Disjoint B (coordinateReflection i ⁻¹' B)) :
    torusVolume.real (reflectionCompetitor i E B)=2*torusVolume.real (E∩B) := by
  simp only [Measure.real_def,reflectionCompetitor_volume i hE hB hb,ENNReal.toReal_mul,ENNReal.toReal_ofNat]

lemma reflectionCompetitor_flux (i : Fin 3) {E B : Set Torus}
    (hE : MeasurableSet E) (hB : MeasurableSet B)
    (hb : Disjoint B (coordinateReflection i ⁻¹' B))
    {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' reflectionCompetitor i E B,divergence F x)=
      2*∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E∩B),divergence (coordinateEvenField i F) x := by
  let A := fundamentalCube ∩ quotientMap ⁻¹' (E∩B)
  let C := fundamentalCube ∩ quotientMap ⁻¹' (coordinateReflection i ⁻¹' (E∩B))
  have hd : Disjoint A C := ((reflectionCompetitor_disjoint_parts i E hb).preimage quotientMap).mono
    inter_subset_right inter_subset_right
  have hc : MeasurableSet C := measurableSet_fundamentalCube.inter
    (measurable_quotientMap ((coordinateReflection_continuous i).measurable (hE.inter hB)))
  have hi : IntegrableOn (divergence F) A := (integrableOn_divergence hF.1).mono_set inter_subset_left
  have hic : IntegrableOn (divergence F) C := (integrableOn_divergence hF.1).mono_set inter_subset_left
  have hu : fundamentalCube ∩ quotientMap ⁻¹' reflectionCompetitor i E B=A∪C := by
    ext x; simp only [A,C,reflectionCompetitor,mem_inter_iff,mem_union,mem_preimage]; tauto
  rw [hu,setIntegral_union hd hc hi hic]
  change (∫ x in A,divergence F x)+
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (coordinateReflection i ⁻¹' (E∩B)),divergence F x)=_
  rw [flux_coordinateReflection i hF (hE.inter hB)]
  have hr := coordinateReflectedField_admissible i hF
  have hir : IntegrableOn (divergence (coordinateReflectedField i F)) A :=
    (integrableOn_divergence hr.1).mono_set inter_subset_left
  simp_rw [coordinateEvenField_divergence i hF.1]
  rw [integral_const_mul]
  have he : (fun x => divergence F x+divergence F (coverCoordinateReflection i x))=
      fun x => divergence F x+divergence (coordinateReflectedField i F) x := by
    funext x; rw [coordinateReflectedField_divergence i hF.1]
  rw [he,integral_add hi hir]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma sublevelCutoff_direction_zero {q : Cover → ℝ} (hq : Differentiable ℝ q)
    {F : Cover → Cover} {ε : ℝ} (hε : 0<ε) {x : Cover}
    (hx : q x ≤ -ε ∨ 0 ≤ q x) :
    fderiv ℝ (sublevelCutoff q 0 ε) x (F x)=0 := by
  rw [← inner_gradient_left,sublevelCutoff_gradient_zero hq hε 0 x (by simpa using hx),inner_zero_left]

lemma sublevelCutoff_direction_bound {q : Cover → ℝ} (hq : Differentiable ℝ q)
    {F : Cover → Cover} {K M : ℝ} (hK : 0≤K) (hM : 0≤M)
    (hd : ∀ t,‖deriv Real.smoothTransition t‖≤M)
    (ht : ∀ x,|fderiv ℝ q x (F x)|≤K*|q x|)
    {ε : ℝ} (hε : 0<ε) (x : Cover) :
    ‖fderiv ℝ (sublevelCutoff q 0 ε) x (F x)‖≤M*K := by
  by_cases hx : q x ≤ -ε ∨ 0 ≤ q x
  · rw [sublevelCutoff_direction_zero hq hε hx,norm_zero]
    positivity
  push Not at hx
  have hqx : |q x|≤ε := by rw [abs_of_neg hx.2]; linarith
  rw [fderiv_sublevelCutoff (hq x)]
  simp only [smul_apply,neg_apply,smul_eq_mul,
    norm_mul,norm_neg,norm_div,Real.norm_of_nonneg hε.le]
  calc
    _ ≤ (M/ε)*(K*|q x|) := mul_le_mul (div_le_div_of_nonneg_right (hd _) hε.le)
      (ht x) (abs_nonneg _) (div_nonneg hM hε.le)
    _ ≤ (M/ε)*(K*ε) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hqx hK) (div_nonneg hM hε.le)
    _ = M*K := by field_simp

lemma sublevelCutoff_direction_tendsto {q : Cover → ℝ} (hq : Differentiable ℝ q)
    {F : Cover → Cover} {ε : ℕ → ℝ} (hε : ∀ n,0<ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (x : Cover) :
    Tendsto (fun n => fderiv ℝ (sublevelCutoff q 0 (ε n)) x (F x)) atTop (𝓝 0) := by
  have hz : ∀ᶠ n in atTop,fderiv ℝ (sublevelCutoff q 0 (ε n)) x (F x)=0 := by
    by_cases hx : 0≤q x
    · exact Eventually.of_forall fun n => sublevelCutoff_direction_zero hq (hε n) (Or.inr hx)
    · have hx' : 0 < -q x := by linarith
      filter_upwards [hlim.eventually (gt_mem_nhds hx')] with n hn
      exact sublevelCutoff_direction_zero hq (hε n) (Or.inl (by linarith))
  exact tendsto_const_nhds.congr' (hz.mono fun _ hn => hn.symm)

lemma sublevelCutoff_direction_integral_tendsto {E : Set Torus}
    {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    {K : ℝ} (hK : 0≤K) (ht : ∀ x,|fderiv ℝ q x (F x)|≤K*|q x|)
    {ε : ℕ → ℝ} (hε : ∀ n,0<ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      fderiv ℝ (sublevelCutoff q 0 (ε n)) x (F x)) atTop (𝓝 0) := by
  obtain ⟨M,hM,hd⟩ := smoothTransition_exists_deriv_bound
  have hi : IntegrableOn (fun _ : Cover => M*K)
      (fundamentalCube ∩ quotientMap ⁻¹' E) :=
    (integrableOn_periodic_continuous continuous_const (fun _ _ => rfl)).mono_set inter_subset_left
  have hh := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E))
    (bound := fun _ => M*K)
    (F := fun n x => fderiv ℝ (sublevelCutoff q 0 (ε n)) x (F x)) (f := fun _ => (0 : ℝ))
    (fun n => (((sublevelCutoff_contDiff hq 0 (ε n)).continuous_fderiv (by simp)).clm_apply
      hF.continuous).aestronglyMeasurable) hi
    (fun n => Eventually.of_forall (sublevelCutoff_direction_bound
      (hq.differentiable (by simp)) hK hM.le hd ht (hε n)))
    (Eventually.of_forall (sublevelCutoff_direction_tendsto (hq.differentiable (by simp)) hε hlim))
  simpa only [integral_zero] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalMeasure_tangential_sublevel_flux {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hp : ∀ n x,q (x+latticeVector n)=q x) {F : Cover → Cover} (hF : AdmissibleField F)
    {K : ℝ} (hK : 0≤K) (ht : ∀ x,|fderiv ℝ q x (F x)|≤K*|q x|) :
    (∫ z in {z : NormalBundle | q z.1<0},normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle)) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E∩sublevelRegion q 0),divergence F x := by
  let ε : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hε : ∀ n,0<ε n := fun n => by dsimp [ε]; positivity
  have helim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let T := normalTest F hF.1.continuous
  let b : Set NormalBundle := {z | q z.1<0}
  have hbm : MeasurableSet b := isOpen_lt
    (hq.continuous.comp (continuous_subtype_val.comp continuous_fst)) continuous_const |>.measurableSet
  have hnt : ∀ z : NormalBundle,Tendsto (fun n => sublevelCutoff q 0 (ε n) z.1*T z)
      atTop (𝓝 (b.indicator T z)) := by
    intro z
    have hh := (sublevelCutoff_tendsto hp hε helim 0 (z.1 : Cover)).mul
      (tendsto_const_nhds (x := T z))
    convert hh using 1
    classical
    by_cases hz : q (z.1 : Cover)<0
    · simp [b,characteristic,indicator_of_mem, (mem_sublevelRegion_quotient hp 0 _).2 hz,hz]
    · have hn : quotientMap (z.1 : Cover) ∉ sublevelRegion q 0 :=
        fun h => hz ((mem_sublevelRegion_quotient hp 0 _).1 h)
      simp [b,characteristic,hn,hz]
  have hiT : Integrable (fun z => ‖T z‖) (μ : Measure NormalBundle) :=
    T.continuous.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnlim := tendsto_integral_of_dominated_convergence
    (μ := (μ : Measure NormalBundle)) (bound := fun z => ‖T z‖)
    (F := fun n z => sublevelCutoff q 0 (ε n) z.1*T z) (f := b.indicator T)
    (fun n => (((sublevelCutoff_contDiff hq 0 (ε n)).continuous.comp
      (continuous_subtype_val.comp continuous_fst)).mul T.continuous).aestronglyMeasurable)
    hiT (fun n => Eventually.of_forall fun z => ?_) (Eventually.of_forall hnt)
  · rw [integral_indicator hbm] at hnlim
    have hvlim := partition_flux_tendsto (E := E) (measurableSet_sublevelRegion hq.continuous.measurable 0)
      (fun n => (sublevelCutoff_contDiff hq 0 (ε n)).continuous)
      (fun n x => sublevelCutoff_mem_Icc q 0 (ε n) x)
      (sublevelCutoff_tendsto hp hε helim 0) hF admissible_zero
    simp only [divergence_zero,mul_zero,add_zero,integral_zero] at hvlim
    have hel := sublevelCutoff_direction_integral_tendsto (E := E) hq hF.1 hK ht hε helim
    have heq (n : ℕ) : (∫ z,sublevelCutoff q 0 (ε n) z.1*T z ∂(μ : Measure NormalBundle)) =
        (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,sublevelCutoff q 0 (ε n) x*divergence F x)+
        ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
          fderiv ℝ (sublevelCutoff q 0 (ε n)) x (F x) := by
      rw [normalMeasure_weighted_flux hμ (sublevelCutoff_contDiff hq 0 (ε n))
        (sublevelCutoff_periodic hp 0 (ε n)) hF]
      simp_rw [divergence_smul_function ((sublevelCutoff_contDiff hq 0 (ε n)).differentiable (by simp) _)
        (hF.1.differentiable (by simp) _),inner_gradient_left]
      apply integral_add
      · exact (integrableOn_periodic_continuous
          ((sublevelCutoff_contDiff hq 0 (ε n)).continuous.mul (continuous_divergence hF.1))
          (fun m x => by simp only [Pi.mul_apply,sublevelCutoff_periodic hp,divergence_periodic hF.2.1])).mono_set inter_subset_left
      · exact (integrableOn_periodic_continuous
          (((sublevelCutoff_contDiff hq 0 (ε n)).continuous_fderiv (by simp)).clm_apply hF.1.continuous)
          (fun m x => by rw [fderiv_periodic (sublevelCutoff_periodic hp 0 (ε n)),hF.2.1])).mono_set inter_subset_left
    have hv := hvlim.add hel
    simp only [add_zero] at hv
    exact tendsto_nhds_unique hnlim (hv.congr (fun n => (heq n).symm))
  · rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (sublevelCutoff_mem_Icc q 0 (ε n) z.1).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (sublevelCutoff_mem_Icc q 0 (ε n) z.1).2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma halfInteger_distance_le_sine (t : ℝ) :
    |t-(round (2*t) : ℝ)/2| ≤ |Real.sin (2*Real.pi*t)| := by
  let k := round (2*t)
  let r := t-(k : ℝ)/2
  have hr : |r|≤1/4 := by
    have hh := abs_sub_round (2*t)
    have he : 2*t-(k : ℝ)=2*r := by dsimp [r]; ring
    rw [he,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)] at hh
    linarith
  have harg : |2*Real.pi*r|≤Real.pi/2 := by
    rw [abs_mul,abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    nlinarith [Real.pi_pos]
  have hh := Real.mul_abs_le_abs_sin harg
  rw [abs_mul,abs_of_pos (mul_pos (by norm_num) Real.pi_pos)] at hh
  have hm : 2/Real.pi*(2*Real.pi*|r|)=4*|r| := by field_simp; ring
  rw [hm] at hh
  have he : |Real.sin (2*Real.pi*t)|=|Real.sin (2*Real.pi*r)| := by
    have ha : 2*Real.pi*t=2*Real.pi*r+(k : ℝ)*Real.pi := by dsimp [r]; ring
    rw [ha,Real.sin_add_int_mul_pi,abs_mul,abs_zpow]
    norm_num
  change |r|≤_
  rw [he]
  linarith [abs_nonneg r]

def coordinateSine (i : Fin 3) (x : Cover) : ℝ := Real.sin (2*Real.pi*x i)

lemma coordinateSine_contDiff (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (coordinateSine i) :=
  (contDiff_const.mul (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff).sin

lemma coordinateSine_periodic (i : Fin 3) :
    ∀ n x,coordinateSine i (x+latticeVector n)=coordinateSine i x := by
  intro n x
  unfold coordinateSine
  simp only [PiLp.add_apply,latticeVector]
  rw [show 2*Real.pi*(x i+(n i : ℝ))=2*Real.pi*x i+(n i : ℝ)*(2*Real.pi) by ring,
    Real.sin_add_int_mul_two_pi]

lemma coordinateSine_reflection (i : Fin 3) (x : Cover) :
    coordinateSine i (coverCoordinateReflection i x)= -coordinateSine i x := by
  simp [coordinateSine]

lemma coordinateSine_fderiv (i : Fin 3) (x v : Cover) :
    fderiv ℝ (coordinateSine i) x v=Real.cos (2*Real.pi*x i)*(2*Real.pi*v i) := by
  have hh := (((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).hasFDerivAt (x := x) |>.const_mul (2*Real.pi)).sin).fderiv
  convert! congrArg (fun L : Cover →L[ℝ] ℝ => L v) hh using 1

lemma coordinateSymmetricField_seam {i : Fin 3} {G : Cover → Cover}
    (hp : ∀ n x,G (x+latticeVector n)=G x)
    (hr : ∀ x,G (coverCoordinateReflection i x)=coverCoordinateReflection i (G x))
    (y : Cover) (k : ℤ) (hy : y i=(k : ℝ)/2) : G y i=0 := by
  have he : coverCoordinateReflection i y=y+latticeVector (Pi.single i (-k)) := by
    ext j
    by_cases hj : j=i
    · subst j
      simp [latticeVector,hy]; ring
    · simp [latticeVector,hj]
  have hh := congrArg (fun z : Cover => z i) (hr y)
  rw [he,hp] at hh
  simp [coverCoordinateReflection_apply] at hh
  linarith

theorem coordinateSymmetricField_tangency {i : Fin 3} {G : Cover → Cover}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hp : ∀ n x,G (x+latticeVector n)=G x)
    (hr : ∀ x,G (coverCoordinateReflection i x)=coverCoordinateReflection i (G x)) :
    ∃ K : ℝ,0≤K ∧ ∀ x,|fderiv ℝ (coordinateSine i) x (G x)|≤K*|coordinateSine i x| := by
  obtain ⟨M,hM,hb⟩ := periodic_bounded (hG.continuous_fderiv (by simp))
    (fun n x => fderiv_periodic hp n x)
  have hLip : LipschitzWith ⟨M,hM⟩ G := lipschitzWith_of_nnnorm_fderiv_le
    (hG.differentiable (by simp)) (fun x => by exact_mod_cast hb x)
  refine ⟨2*Real.pi*M,by positivity,?_⟩
  intro x
  let k := round (2*x i)
  let r := x i-(k : ℝ)/2
  let y := x-r • EuclideanSpace.single i 1
  have hy : y i=(k : ℝ)/2 := by simp [y,r,PiLp.sub_apply,PiLp.smul_apply]
  have hz := coordinateSymmetricField_seam hp hr y k hy
  have hxy : x-y=r • EuclideanSpace.single i 1 := by dsimp [y]; module
  have hnorm : ‖x-y‖=|r| := by rw [hxy,norm_smul]; simp [Real.norm_eq_abs]
  have hcomp : |G x i|≤M*|r| := by
    have hh := (PiLp.norm_apply_le (G x-G y) i).trans (hLip.norm_sub_le x y)
    convert! hh using 1
    · simp [hz,Real.norm_eq_abs]
    · rw [hnorm]
      rfl
  have hs : |r|≤|coordinateSine i x| := halfInteger_distance_le_sine (x i)
  rw [coordinateSine_fderiv,abs_mul,abs_mul,abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  calc
    _ ≤ 1*(2*Real.pi*(M*|r|)) := mul_le_mul (Real.abs_cos_le_one _)
      (mul_le_mul_of_nonneg_left hcomp (by positivity)) (by positivity) (by norm_num)
    _ ≤ (2*Real.pi*M)*|coordinateSine i x| := by
      have hh := mul_le_mul_of_nonneg_left hs (show 0≤2*Real.pi*M by positivity)
      nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma reflection_sublevel_disjoint {i : Fin 3} {q : Cover → ℝ}
    (hp : ∀ n x,q (x+latticeVector n)=q x)
    (hr : ∀ x,q (coverCoordinateReflection i x)= -q x) :
    Disjoint (sublevelRegion q 0) (coordinateReflection i ⁻¹' sublevelRegion q 0) := by
  rw [disjoint_left]
  intro z hz hz'
  let x := representative z
  have hx : quotientMap x=z := quotientMap_representative z
  have h1 := (mem_sublevelRegion_quotient hp 0 x).1 (hx ▸ hz)
  have h2 := (mem_sublevelRegion_quotient hp 0 (coverCoordinateReflection i x)).1 (by
    simpa only [quotientMap_coordinateReflection,hx,mem_preimage] using hz')
  rw [hr] at h2
  linarith

theorem reflectionCompetitor_perimeter_le {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hE : MeasurableSet E) (hμ : IsNormalMeasure E μ) (i : Fin 3) {q : Cover → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hp : ∀ n x,q (x+latticeVector n)=q x)
    (hr : ∀ x,q (coverCoordinateReflection i x)= -q x)
    (ht : ∀ F,AdmissibleField F → ∃ K : ℝ,0≤K ∧
      ∀ x,|fderiv ℝ q x (coordinateEvenField i F x)|≤K*|q x|) :
    perimeter (reflectionCompetitor i E (sublevelRegion q 0)) ≤
      2*(μ : Measure NormalBundle) {z | q z.1<0} := by
  let b : Set NormalBundle := {z | q z.1<0}
  have hb := measurableSet_sublevelRegion hq.continuous.measurable 0
  have hd := reflection_sublevel_disjoint hp hr
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  rw [reflectionCompetitor_flux i hE hb hd hF]
  obtain ⟨K,hK,htK⟩ := ht F hF
  have hG := coordinateEvenField_admissible i hF
  rw [← normalMeasure_tangential_sublevel_flux hμ hq hp hG hK htK]
  have hi : IntegrableOn (normalTest (coordinateEvenField i F) hG.1.continuous) b
      (μ : Measure NormalBundle) :=
    ((normalTest _ hG.1.continuous).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).integrableOn
  have hbound : (∫ z in b,normalTest (coordinateEvenField i F) hG.1.continuous z
      ∂(μ : Measure NormalBundle)) ≤ (μ : Measure NormalBundle).real b := by
    have hh := integral_mono hi (integrable_const (μ := (μ : Measure NormalBundle).restrict b) (1 : ℝ))
      (fun z => normalTest_le_one hG z)
    simpa only [integral_const,smul_eq_mul,mul_one,Measure.real_def,Measure.restrict_apply_univ] using hh
  calc
    _ ≤ ENNReal.ofReal (2*(μ : Measure NormalBundle).real b) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hbound (by norm_num))
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_ofNat,Measure.real_def,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem reflectionCompetitor_sine_perimeter_le {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hE : MeasurableSet E) (hμ : IsNormalMeasure E μ) (i : Fin 3) :
    perimeter (reflectionCompetitor i E (sublevelRegion (coordinateSine i) 0)) ≤
      2*(μ : Measure NormalBundle) {z | coordinateSine i z.1<0} := by
  apply reflectionCompetitor_perimeter_le hE hμ i (coordinateSine_contDiff i)
    (coordinateSine_periodic i) (coordinateSine_reflection i)
  intro F hF
  have hG := coordinateEvenField_admissible i hF
  exact coordinateSymmetricField_tangency hG.1 hG.2.1 (coordinateEvenField_reflection i F)

theorem reflectionCompetitor_negSine_perimeter_le {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hE : MeasurableSet E) (hμ : IsNormalMeasure E μ) (i : Fin 3) :
    perimeter (reflectionCompetitor i E (sublevelRegion (fun x => -coordinateSine i x) 0)) ≤
      2*(μ : Measure NormalBundle) {z | 0<coordinateSine i z.1} := by
  have hs : {z : NormalBundle | -coordinateSine i z.1<0}={z | 0<coordinateSine i z.1} := by
    ext z; simp
  rw [← hs]
  apply reflectionCompetitor_perimeter_le hE hμ i (coordinateSine_contDiff i).neg
    (fun n x => by rw [coordinateSine_periodic]) (fun x => by rw [coordinateSine_reflection])
  intro F hF
  have hG := coordinateEvenField_admissible i hF
  obtain ⟨K,hK,ht⟩ := coordinateSymmetricField_tangency hG.1 hG.2.1
    (coordinateEvenField_reflection i F)
  refine ⟨K,hK,?_⟩
  intro x
  change |fderiv ℝ (-coordinateSine i) x (coordinateEvenField i F x)|≤K*|-coordinateSine i x|
  simpa only [fderiv_neg,neg_apply,abs_neg] using ht x

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_reflection_competitors {V : ℝ} {E : Set Torus}
    (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (hminus : 2*torusVolume (E∩sublevelRegion (coordinateSine i) 0)=ENNReal.ofReal V)
    (hplus : 2*torusVolume (E∩sublevelRegion (fun x => -coordinateSine i x) 0)=ENNReal.ofReal V) :
    IsMinimizerAt V (reflectionCompetitor i E (sublevelRegion (coordinateSine i) 0)) ∧
    IsMinimizerAt V (reflectionCompetitor i E (sublevelRegion (fun x => -coordinateSine i x) 0)) ∧
    (μ : Measure NormalBundle) {z | coordinateSine i z.1=0}=0 := by
  let B := sublevelRegion (coordinateSine i) 0
  let C := sublevelRegion (fun x => -coordinateSine i x) 0
  let F := reflectionCompetitor i E B
  let G := reflectionCompetitor i E C
  let b : Set NormalBundle := {z | coordinateSine i z.1<0}
  let c : Set NormalBundle := {z | 0<coordinateSine i z.1}
  have hB : MeasurableSet B := measurableSet_sublevelRegion (coordinateSine_contDiff i).continuous.measurable 0
  have hC : MeasurableSet C := measurableSet_sublevelRegion (coordinateSine_contDiff i).neg.continuous.measurable 0
  have hF : MeasurableSet F := reflectionCompetitor_measurable i hE hB
  have hG : MeasurableSet G := reflectionCompetitor_measurable i hE hC
  have hFb : perimeter F≤2*(μ : Measure NormalBundle) b := reflectionCompetitor_sine_perimeter_le hE hμ i
  have hGb : perimeter G≤2*(μ : Measure NormalBundle) c := reflectionCompetitor_negSine_perimeter_le hE hμ i
  have hFP : FinitePerimeter F := ⟨hF.nullMeasurableSet,hFb.trans_lt (by finiteness)⟩
  have hGP : FinitePerimeter G := ⟨hG.nullMeasurableSet,hGb.trans_lt (by finiteness)⟩
  have hvF : torusVolume F=ENNReal.ofReal V := by
    rw [reflectionCompetitor_volume i hE hB
      (reflection_sublevel_disjoint (coordinateSine_periodic i) (coordinateSine_reflection i))]
    exact hminus
  have hvG : torusVolume G=ENNReal.ofReal V := by
    rw [reflectionCompetitor_volume i hE hC
      (reflection_sublevel_disjoint (fun n x => by rw [coordinateSine_periodic i])
        (fun x => by rw [coordinateSine_reflection i]))]
    exact hplus
  have hmF := hmin.2.2 F hFP hvF
  have hmG := hmin.2.2 G hGP hvG
  have hmass : (μ : Measure NormalBundle).real univ=(perimeter E).toReal := by
    rw [Measure.real,← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal,hμ.1]
  have hb : MeasurableSet b := (isOpen_lt
    ((coordinateSine_contDiff i).continuous.comp (continuous_subtype_val.comp continuous_fst))
    continuous_const).measurableSet
  have hc : MeasurableSet c := (isOpen_lt continuous_const
    ((coordinateSine_contDiff i).continuous.comp (continuous_subtype_val.comp continuous_fst))).measurableSet
  have hd : Disjoint b c := by
    apply disjoint_left.mpr
    intro z hz hz'
    change coordinateSine i z.1<0 at hz
    change 0<coordinateSine i z.1 at hz'
    linarith
  have hsum : (μ : Measure NormalBundle).real b+(μ : Measure NormalBundle).real c≤(perimeter E).toReal := by
    rw [← measureReal_union hd hc]
    exact (measureReal_mono (subset_univ _)).trans_eq hmass
  have hfr := ENNReal.toReal_mono (by finiteness) hFb
  have hgr := ENNReal.toReal_mono (by finiteness) hGb
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofNat,← Measure.real_def] at hfr hgr
  have hmf := ENNReal.toReal_mono hFP.2.ne hmF
  have hmg := ENNReal.toReal_mono hGP.2.ne hmG
  have heF : perimeter F=perimeter E := (ENNReal.toReal_eq_toReal_iff' hFP.2.ne hmin.1.2.ne).mp (by linarith)
  have heG : perimeter G=perimeter E := (ENNReal.toReal_eq_toReal_iff' hGP.2.ne hmin.1.2.ne).mp (by linarith)
  refine ⟨⟨hFP,hvF,fun A hA hvA => heF ▸ hmin.2.2 A hA hvA⟩,
    ⟨hGP,hvG,fun A hA hvA => heG ▸ hmin.2.2 A hA hvA⟩,?_⟩
  have heq : (μ : Measure NormalBundle) (b∪c)=(μ : Measure NormalBundle) univ := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    rw [← Measure.real_def,← Measure.real_def,measureReal_union hd hc,hmass]
    linarith
  have hz : {z : NormalBundle | coordinateSine i z.1=0}=(b∪c)ᶜ := by
    ext z
    simp only [b,c,mem_ofPred_eq,mem_compl_iff,mem_union]
    constructor
    · intro hh
      rw [hh]
      simp
    · intro hh
      push Not at hh
      linarith
  rw [hz,measure_compl (hb.union hc) (measure_ne_top _ _),heq,tsub_self]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coordinateHalf (i : Fin 3) (a : ℝ) : Set Torus :=
  {z | Real.sin (2*Real.pi*((representative z) i-a))<0}

lemma coordinateHalf_measurable (i : Fin 3) (a : ℝ) : MeasurableSet (coordinateHalf i a) := by
  apply measurableSet_lt _ measurable_const
  exact (((EuclideanSpace.proj i).continuous.measurable.comp measurable_representative).sub_const a).const_mul _ |>.sin

lemma coordinateHalf_seam_zero (i : Fin 3) (a : ℝ) :
    torusVolume {z | Real.sin (2*Real.pi*((representative z) i-a))=0}=0 := by
  have hz (k : ℤ) : torusVolume {z : Torus | z i=((a+(k : ℝ)/2 : ℝ) : AddCircle (1 : ℝ))}=0 := by
    have hh := (torus_coordinate_measurePreserving i).measure_preimage
      (measurableSet_singleton (((a+(k : ℝ)/2 : ℝ) : AddCircle (1 : ℝ)))).nullMeasurableSet
    change torusVolume {z : Torus | z i=((a+(k : ℝ)/2 : ℝ) : AddCircle (1 : ℝ))}=volume {((a+(k : ℝ)/2 : ℝ) : AddCircle (1 : ℝ))} at hh
    rw [hh,← Metric.closedBall_zero,AddCircle.volume_closedBall]; norm_num
  apply measure_mono_null (t := ⋃ k : ℤ,{z : Torus | z i=((a+(k : ℝ)/2 : ℝ) : AddCircle (1 : ℝ))}) _
    (measure_iUnion_null hz)
  intro z hz'
  obtain ⟨k,hk⟩ := Real.sin_eq_zero_iff.mp hz'
  apply mem_iUnion.mpr
  refine ⟨k,?_⟩
  have hc : (representative z) i=a+(k : ℝ)/2 := by nlinarith [Real.pi_pos]
  have he := congrArg (fun w : Torus => w i) (quotientMap_representative z)
  change (((representative z) i : ℝ) : AddCircle (1 : ℝ))=z i at he
  change z i=_
  rw [← he,hc]

lemma coordinateHalf_halfturn (i : Fin 3) (a : ℝ) (z : Torus) :
    z∈coordinateHalf i (a+1/2) ↔ 0<Real.sin (2*Real.pi*((representative z) i-a)) := by
  change Real.sin (2*Real.pi*((representative z) i-(a+1/2)))<0 ↔ _
  rw [show 2*Real.pi*((representative z) i-(a+1/2))=
    2*Real.pi*((representative z) i-a)-Real.pi by ring,Real.sin_sub_pi]
  simp

lemma coordinateHalf_complement_ae (i : Fin 3) (a : ℝ) :
    coordinateHalf i (a+1/2) =ᵐ[torusVolume] (coordinateHalf i a)ᶜ := by
  have hh : ∀ᵐ z ∂torusVolume,Real.sin (2*Real.pi*((representative z) i-a))≠0 := by
    simpa only [ae_iff,not_not] using coordinateHalf_seam_zero i a
  filter_upwards [hh] with z hz
  apply propext
  rw [coordinateHalf_halfturn]
  change (0 : ℝ)<Real.sin (2*Real.pi*((representative z) i-a)) ↔
    ¬Real.sin (2*Real.pi*((representative z) i-a))<0
  constructor
  · exact fun h => not_lt.mpr h.le
  · exact fun h => lt_of_le_of_ne (le_of_not_gt h) hz.symm

lemma coordinateHalf_volume_sum (i : Fin 3) (a : ℝ) {E : Set Torus}
    (hE : MeasurableSet E) :
    torusVolume.real (E∩coordinateHalf i a)+torusVolume.real (E∩coordinateHalf i (a+1/2))=
      torusVolume.real E := by
  have he : (E∩coordinateHalf i (a+1/2) : Set Torus) =ᵐ[torusVolume] (E∩(coordinateHalf i a)ᶜ : Set Torus) :=
    by
      filter_upwards [coordinateHalf_complement_ae i a] with z hz
      exact congrArg (fun halfMembership : Prop => z∈E ∧ halfMembership) hz
  simp_rw [Measure.real_def]
  rw [measure_congr he]
  change torusVolume.real (E∩coordinateHalf i a)+torusVolume.real (E∩(coordinateHalf i a)ᶜ)=torusVolume.real E
  rw [← measureReal_union (Disjoint.mono inter_subset_right inter_subset_right disjoint_compl_right)
    (hE.inter (coordinateHalf_measurable i a).compl)]
  congr 1
  ext z; simp only [mem_union,mem_inter_iff,mem_compl_iff]; tauto

lemma coordinateHalf_volume_continuous (i : Fin 3) {E : Set Torus} (hE : MeasurableSet E) :
    Continuous (fun a : ℝ => torusVolume.real (E∩coordinateHalf i a)) := by
  have he (a : ℝ) : torusVolume.real (E∩coordinateHalf i a)=
      ∫ z in E,characteristic (coordinateHalf i a) z ∂torusVolume := by
    unfold characteristic
    rw [integral_indicator (coordinateHalf_measurable i a),integral_const]
    simp only [smul_eq_mul,mul_one,Measure.real_def,Measure.restrict_restrict' hE,
      Measure.restrict_apply_univ,inter_comm]
  simp_rw [he]
  apply continuous_iff_continuousAt.mpr
  intro a
  apply continuousAt_of_dominated (bound := fun _ => (1 : ℝ))
  · exact Eventually.of_forall fun t => (measurable_characteristic (coordinateHalf_measurable i t)).aestronglyMeasurable
  · exact Eventually.of_forall fun t => Eventually.of_forall fun z =>
      by simpa only [Real.norm_eq_abs] using characteristic_bound (coordinateHalf i t) z
  · exact integrable_const _
  · have hh : ∀ᵐ z ∂torusVolume.restrict E,Real.sin (2*Real.pi*((representative z) i-a))≠0 :=
      ae_restrict_of_ae (by simpa only [ae_iff,not_not] using coordinateHalf_seam_zero i a)
    filter_upwards [hh] with z hz
    have hc : Continuous (fun t : ℝ => Real.sin (2*Real.pi*((representative z) i-t))) := by fun_prop
    rcases lt_or_gt_of_ne hz with hn|hp
    · have hh := hc.continuousAt.eventually (gt_mem_nhds hn)
      have heq : (fun t => characteristic (coordinateHalf i t) z) =ᶠ[𝓝 a] fun _ => (1 : ℝ) := by
        filter_upwards [hh] with t ht
        simp [characteristic,coordinateHalf,ht]
      exact continuousAt_const.congr_of_eventuallyEq heq
    · have hh := hc.continuousAt.eventually (lt_mem_nhds hp)
      have heq : (fun t => characteristic (coordinateHalf i t) z) =ᶠ[𝓝 a] fun _ => (0 : ℝ) := by
        filter_upwards [hh] with t ht
        simp [characteristic,coordinateHalf,not_lt.mpr ht.le]
      exact continuousAt_const.congr_of_eventuallyEq heq

theorem exists_coordinateHalf_bisects (i : Fin 3) {E : Set Torus} (hE : MeasurableSet E) :
    ∃ a∈Icc (0 : ℝ) (1/2),torusVolume.real (E∩coordinateHalf i a)=torusVolume.real E/2 := by
  have hc := (coordinateHalf_volume_continuous i hE).continuousOn (s := Icc (0 : ℝ) (1/2))
  have hs := coordinateHalf_volume_sum i 0 hE
  norm_num only [zero_add] at hs
  by_cases hh : torusVolume.real (E∩coordinateHalf i 0)≤torusVolume.real E/2
  · exact intermediate_value_Icc (by norm_num : (0 : ℝ)≤1/2) hc ⟨hh,by linarith⟩
  · exact intermediate_value_Icc' (by norm_num : (0 : ℝ)≤1/2) hc ⟨by linarith,le_of_not_ge hh⟩

end CubicTorus

end
end

end OAI
