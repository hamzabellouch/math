import Mathlib
import OAI.Analysis.HardSphere.Geometry.SpatialPartitionEnergy

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HardSphere.SphericalCoordinates
open scoped BigOperators

noncomputable def subsetPointLinear {I : Type*} [Fintype I] (p : I → Prop) [DecidablePred p] :
    ({i // p i} → Point) →L[ℝ] (I → Point) :=
  ContinuousLinearMap.pi (fun i ↦ if hi : p i then ContinuousLinearMap.proj ⟨i,hi⟩ else 0)

def subsetPointFill {I : Type*} (p : I → Prop) [DecidablePred p]
    (Y : {i // ¬p i} → Point) (X : {i // p i} → Point) (i : I) : Point :=
  if hi : p i then X ⟨i,hi⟩ else Y ⟨i,hi⟩

lemma subsetPointFill_affine {I : Type*} [Fintype I] (p : I → Prop) [DecidablePred p]
    (Y : {i // ¬p i} → Point) (X : {i // p i} → Point) :
    subsetPointFill p Y X=subsetPointLinear p X+subsetPointFill p Y 0 := by
  funext i
  by_cases hi : p i <;> simp [subsetPointFill,subsetPointLinear,hi]

lemma subsetPointLinear_single {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → Prop) [DecidablePred p] (i : {i // p i}) (v : Point) :
    subsetPointLinear p (Pi.single i v)=Pi.single i.val v := by
  funext j
  by_cases hj : p j
  · by_cases he : j=i.val
    · subst j
      simp [subsetPointLinear,hj]
    · have hn : (⟨j,hj⟩ : Subtype p)≠i := fun h ↦ he (congrArg Subtype.val h)
      simp [subsetPointLinear,hj,he,hn]
  · have he : j≠i.val := by rintro rfl; exact hj i.property
    simp [subsetPointLinear,hj,he]

lemma contDiff_subsetPointFill {I : Type*} [Fintype I]
    (p : I → Prop) [DecidablePred p] (Y : {i // ¬p i} → Point) :
    ContDiff ℝ 1 (subsetPointFill p Y) := by
  have he : subsetPointFill p Y=fun X ↦ subsetPointLinear p X+subsetPointFill p Y 0 :=
    funext (subsetPointFill_affine p Y)
  rw [he]
  exact (subsetPointLinear p).contDiff.add contDiff_const

lemma indexGradSq_subset {I : Type*} [Fintype I] [DecidableEq I]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (I → Point) → E} (hF : ContDiff ℝ 1 F)
    (p : I → Prop) [DecidablePred p] (Y : {i // ¬p i} → Point)
    (X : {i // p i} → Point) (i : {i // p i}) :
    indexGradSq (F ∘ subsetPointFill p Y) i X=indexGradSq F i.val (subsetPointFill p Y X) := by
  have hd : HasFDerivAt (subsetPointFill p Y) (subsetPointLinear p) X := by
    have he : subsetPointFill p Y=fun X ↦ subsetPointLinear p X+subsetPointFill p Y 0 :=
      funext (subsetPointFill_affine p Y)
    rw [he]
    exact (subsetPointLinear p).hasFDerivAt.add_const _
  have hf := ((hF.differentiable (by norm_num) (subsetPointFill p Y X)).hasFDerivAt).comp X hd
  simp only [indexGradSq,hf.fderiv,ContinuousLinearMap.comp_apply,subsetPointLinear_single]

lemma lintegral_subsetPointFill {I : Type*} [Fintype I]
    (μ : I → Measure Point) [∀i,SigmaFinite (μ i)]
    (p : I → Prop) [DecidablePred p] (H : (I → Point) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ X,H X ∂Measure.pi μ)=
      ∫⁻ Y, ∫⁻ X, H (subsetPointFill p Y X)
        ∂Measure.pi (fun i : {i // p i} ↦ μ i.val)
        ∂Measure.pi (fun i : {i // ¬p i} ↦ μ i.val) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I ↦ Point) p
  have he := (measurePreserving_piEquivPiSubtypeProd μ p).symm
  rw [← he.lintegral_comp_emb e.symm.measurableEmbedding H]
  apply lintegral_prod_symm
  exact (hH.comp e.symm.measurable).aemeasurable

lemma subset_cube_energy {I : Type*} [Fintype I] [DecidableEq I]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (I → Point) → E} (hF : ContDiff ℝ 1 F)
    (p : I → Prop) [DecidablePred p] {r l : ℝ} (hr : 0<r) (hl : 0<l)
    (b : I → Point) (b₀ : Point) (hb : ∀i : {i // p i}, b i.val=b₀)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c)≤r^2 → F X=0) :
    ENNReal.ofReal (1/(64*Real.sqrt 3)*r/l^3*(Fintype.card {i // p i}:ℝ)*
      ((Fintype.card {i // p i}:ℝ)-1))*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun i ↦ volume.restrict (cube (b i) l))) ≤
        ∑ i : {i // p i}, (∫⁻ X, ENNReal.ofReal (indexGradSq F i.val X)
          ∂Measure.pi (fun i ↦ volume.restrict (cube (b i) l))) := by
  let μ := fun i ↦ (volume : Measure Point).restrict (cube (b i) l)
  have hslice (Y : {i // ¬p i} → Point) := finite_cube_energy
    (hF.comp (contDiff_subsetPointFill p Y)) hr hl b₀ (F := F ∘ subsetPointFill p Y) (by
      intro X a c hac hd
      apply hz (subsetPointFill p Y X) a.val c.val (fun h ↦ hac (Subtype.ext h))
      simpa only [subsetPointFill,dite_eq_left a.property,dite_eq_left c.property] using hd)
  have hμ : (fun i : {i // p i} ↦ μ i.val)=fun _ ↦ volume.restrict (cube b₀ l) := by
    funext i
    simp only [μ,hb]
  have hm : Measurable (fun X ↦ ENNReal.ofReal (‖F X‖^2)) := by
    simpa only [Pi.pow_apply] using (hF.continuous.norm.pow 2).measurable.ennreal_ofReal
  have hn := lintegral_subsetPointFill μ p (fun X ↦ ENNReal.ofReal (‖F X‖^2)) hm
  rw [hn,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hi := lintegral_mono hslice (μ := Measure.pi (fun i : {i // ¬p i} ↦ μ i.val))
  rw [←hμ] at hi
  simp only [Function.comp_apply,indexGradSq_subset hF] at hi
  apply hi.trans_eq
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact (lintegral_subsetPointFill μ p _
      (continuous_indexGradSq hF i.val).measurable.ennreal_ofReal).symm
  · intro i _
    have he := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I ↦ Point) p).symm.measurable
    exact (((continuous_indexGradSq hF i.val).measurable.ennreal_ofReal.comp he).lintegral_prod_left')

lemma sector_cell_energy {I C : Type*} [Fintype I] [Fintype C] [DecidableEq I] [DecidableEq C]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (I → Point) → E} (hF : ContDiff ℝ 1 F) {r l : ℝ} (hr : 0<r) (hl : 0<l)
    (b : C → Point) (σ : I → C)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c)≤r^2 → F X=0) :
    (∑ v : C, ENNReal.ofReal (1/(64*Real.sqrt 3)*r/l^3*(Fintype.card {i // σ i=v}:ℝ)*
      ((Fintype.card {i // σ i=v}:ℝ)-1)))*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun i ↦ volume.restrict (cube (b (σ i)) l))) ≤
        ∑ i : I, (∫⁻ X, ENNReal.ofReal (indexGradSq F i X)
          ∂Measure.pi (fun i ↦ volume.restrict (cube (b (σ i)) l))) := by
  rw [Finset.sum_mul]
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset C)) (fun v _ ↦
    subset_cube_energy hF (fun i ↦ σ i=v) hr hl (b ∘ σ) (b v)
      (fun i ↦ congrArg b i.property) hz)
  dsimp only [Function.comp_apply] at h
  rw [Fintype.sum_fiberwise σ (fun i ↦ ∫⁻ X,ENNReal.ofReal (indexGradSq F i X)
    ∂Measure.pi (fun i ↦ volume.restrict (cube (b (σ i)) l)))] at h
  exact h

lemma subdivided_cell_energy {n j : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin n → Point) → E} (hF : ContDiff ℝ 1 F)
    {r l : ℝ} (hr : 0<r) (hl : 0<l) (b : Point)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c)≤r^2 → F X=0) :
    (∑ σ : Fin n → (Fin j × Fin j × Fin j),
      (∑ v : Fin j × Fin j × Fin j,
        ENNReal.ofReal (1/(64*Real.sqrt 3)*r/l^3*(Fintype.card {i // σ i=v}:ℝ)*
          ((Fintype.card {i // σ i=v}:ℝ)-1)))*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2)
        ∂Measure.pi (fun i ↦ volume.restrict (cube (subcubeBase b l (σ i)) l)))) ≤
      ∑ i : Fin n, ∫⁻ X,ENNReal.ofReal (particleGradSq F i X)
        ∂Measure.pi (fun _ ↦ volume.restrict (cube b ((j:ℝ)*l))) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n → (Fin j × Fin j × Fin j))))
    (fun σ _ ↦ sector_cell_energy hF hr hl (subcubeBase b l) σ hz)
  apply h.trans_eq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [cube_configuration_subdivision b hl.le,Measure.sum_fintype,MeasureTheory.lintegral_finsetSum_measure]
  rfl

end HardSphere.SphericalCoordinates

end

end OAI
