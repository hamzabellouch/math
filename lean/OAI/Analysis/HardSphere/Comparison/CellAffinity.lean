import Mathlib
import OAI.Analysis.HardSphere.Comparison.AffinityNormalization

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {α : Type*} [MeasurableSpace α]
lemma affinity_withDensity_real (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α→ℝ) (hp : Integrable p μ) (hq : Integrable q μ)
    (hp0 : ∀ᵐx ∂μ,0≤p x) (hq0 : ∀ᵐx ∂μ,0≤q x) :
    measureAffinity (μ.withDensity fun x ↦ ENNReal.ofReal (p x))
      (μ.withDensity fun x ↦ ENNReal.ofReal (q x))=affinity μ p q := by
  let := isFiniteMeasure_withDensity_ofReal hp.2
  let := isFiniteMeasure_withDensity_ofReal hq.2
  rw [measureAffinity_eq_dominated _ _ μ (withDensity_absolutelyContinuous _ _) (withDensity_absolutelyContinuous _ _)]
  unfold affinity
  apply integral_congr_ae
  filter_upwards [Measure.rnDeriv_withDensity₀ μ hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal,
    Measure.rnDeriv_withDensity₀ μ hq.aestronglyMeasurable.aemeasurable.ennreal_ofReal,hp0,hq0] with x hx hy hp' hq'
  rw [hx,hy,ENNReal.toReal_ofReal hp',ENNReal.toReal_ofReal hq']

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
lemma swapLast_preserving :
    MeasurePreserving (fun p : (Y×X)×X ↦ ((p.1.1,p.2),p.1.2))
      ((ν.prod μ).prod μ) ((ν.prod μ).prod μ) := by
  have h := (measurePreserving_prodAssoc ν μ μ).symm.comp
    (((MeasurePreserving.id ν).prod (Measure.measurePreserving_swap (μ:=μ) (ν:=μ))).comp
      (measurePreserving_prodAssoc ν μ μ))
  exact h

lemma full_affinity_square (f : Y×X→ℝ) (hf : MemLp f 2 (ν.prod μ))
    (hf0 : ∀p,0≤f p) (V : ℝ) (hV : 0≤V) :
    measureAffinity
      (((ν.prod μ).prod μ).withDensity fun p ↦ ENNReal.ofReal (V*f p.1^2))
      (((ν.prod μ).prod μ).withDensity fun p ↦ ENNReal.ofReal (V*f (p.1.1,p.2)^2))=
      V*∫Y,(∫x,f (Y,x) ∂μ)^2 ∂ν := by
  have h₁ := hf.comp_fst μ
  have h₂ : MemLp (fun p : (Y×X)×X ↦ f (p.1.1,p.2)) 2 ((ν.prod μ).prod μ) :=
    h₁.comp_measurePreserving (swapLast_preserving μ ν)
  have hi₁ : Integrable (fun p : (Y×X)×X ↦ V*f p.1^2) ((ν.prod μ).prod μ) :=
    ((memLp_two_iff_integrable_sq h₁.aestronglyMeasurable).1 h₁).const_mul V
  have hi₂ : Integrable (fun p : (Y×X)×X ↦ V*f (p.1.1,p.2)^2) ((ν.prod μ).prod μ) :=
    ((memLp_two_iff_integrable_sq h₂.aestronglyMeasurable).1 h₂).const_mul V
  rw [affinity_withDensity_real _ _ _ hi₁ hi₂
    (Eventually.of_forall fun _ ↦ mul_nonneg hV (sq_nonneg _))
    (Eventually.of_forall fun _ ↦ mul_nonneg hV (sq_nonneg _))]
  unfold affinity
  have he : (fun p : (Y×X)×X ↦ Real.sqrt (V*f p.1^2)*Real.sqrt (V*f (p.1.1,p.2)^2))=
      (fun p ↦ V*(f p.1*f (p.1.1,p.2))) := by
    funext p
    rw [Real.sqrt_mul hV,Real.sqrt_mul hV,Real.sqrt_sq (hf0 _),Real.sqrt_sq (hf0 _)]
    have hh := Real.sq_sqrt hV
    calc
      _ = (Real.sqrt V)^2*(f p.1*f (p.1.1,p.2)) := by ring
      _ = _ := by rw [hh]
  rw [he,integral_const_mul]
  congr 1
  have hprod := h₁.integrable_mul h₂
  have hA := (measurePreserving_prodAssoc ν μ μ).symm.integral_comp
    (MeasurableEquiv.prodAssoc (α:=Y) (β:=X) (γ:=X)).symm.measurableEmbedding
    (fun p : (Y×X)×X ↦ f p.1*f (p.1.1,p.2))
  rw [←hA]
  rw [integral_prod]
  · apply integral_congr_ae
    exact Eventually.of_forall fun Y ↦ by
      simpa [sq, MeasurableEquiv.prodAssoc] using (integral_prod_mul (μ:=μ) (ν:=μ) (fun x ↦ f (Y,x)) (fun x ↦ f (Y,x)))
  · have hi : Integrable (fun p : (Y×X)×X ↦ f p.1*f (p.1.1,p.2))
        ((ν.prod (μ.prod μ)).map MeasurableEquiv.prodAssoc.symm) := by
      rw [(measurePreserving_prodAssoc ν μ μ).symm.map_eq]
      exact hprod
    apply hi.comp_measurable
    exact (measurePreserving_prodAssoc ν μ μ).symm.measurable

end HardSphere.Comparison

end

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HardSphere.Comparison
variable {X : Type*} [MeasurableSpace X]

lemma cell_density_normalization (μ : Measure X) (g : X→ℝ≥0∞)
    (hg : Measurable g) (s : Set X) (N : ℕ) (V : ℝ) (hV : 0<V) :
    ENNReal.ofReal ((N:ℝ)/V) •
      ((μ.withDensity (fun x ↦ ENNReal.ofReal V*g x)).restrict s)=
      N • ((μ.withDensity g).restrict s) := by
  have he : μ.withDensity (fun x ↦ ENNReal.ofReal V*g x)=
      ENNReal.ofReal V • μ.withDensity g := by
    exact withDensity_smul _ hg
  rw [he,Measure.restrict_smul,smul_smul]
  have hc : ENNReal.ofReal ((N:ℝ)/V)*ENNReal.ofReal V=(N:ℝ≥0∞) := by
    rw [←ENNReal.ofReal_mul (by positivity),div_mul_cancel₀ _ hV.ne']
    simp
  rw [hc,Nat.cast_smul_eq_nsmul]

end HardSphere.Comparison

end

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

lemma sum_restrict_partition (μ : Measure α) (cell : α→ι)
    (hcell : ∀i,MeasurableSet {x | cell x=i}) :
    (∑i,μ.restrict {x | cell x=i})=μ := by
  have hd : Pairwise (fun i j ↦ Disjoint {x | cell x=i} {x | cell x=j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun x hi hj ↦ hij (hi.symm.trans hj))
  have hu : (⋃i,{x | cell x=i})=univ := by ext x; simp
  rw [←Measure.sum_fintype,←Measure.restrict_iUnion hd hcell,hu,Measure.restrict_univ]

lemma affinity_partition_le (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (cell : α→ι) (hcell : ∀i,MeasurableSet {x | cell x=i}) :
    (∑i,measureAffinity (P.restrict {x | cell x=i}) (Q.restrict {x | cell x=i}))≤
      measureAffinity P Q := by
  have h := measureAffinity_finset_sum Finset.univ
    (fun i ↦ P.restrict {x | cell x=i}) (fun i ↦ Q.restrict {x | cell x=i})
  simpa only [sum_restrict_partition P cell hcell,
    sum_restrict_partition Q cell hcell] using h

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

lemma cell_affinity_sum_le (f : Y×X→ℝ) (hf : MemLp f 2 (ν.prod μ))
    (hf0 : ∀p,0≤f p) (V : ℝ) (hV : 0≤V) (cell : X→ι)
    (hcell : ∀i,MeasurableSet {x | cell x=i}) :
    (∑ij : ι×ι,measureAffinity
      ((((ν.prod μ).prod μ).withDensity fun p ↦ ENNReal.ofReal (V*f p.1^2)).restrict
        {p | (cell p.1.2,cell p.2)=ij})
      ((((ν.prod μ).prod μ).withDensity fun p ↦ ENNReal.ofReal (V*f (p.1.1,p.2)^2)).restrict
        {p | (cell p.1.2,cell p.2)=ij}))≤
      V*∫Y,(∫x,f (Y,x) ∂μ)^2 ∂ν := by
  have h₁ := hf.comp_fst μ
  have h₂ : MemLp (fun p : (Y×X)×X ↦ f (p.1.1,p.2)) 2 ((ν.prod μ).prod μ) :=
    h₁.comp_measurePreserving (swapLast_preserving μ ν)
  have hi₁ : Integrable (fun p : (Y×X)×X ↦ V*f p.1^2) ((ν.prod μ).prod μ) :=
    ((memLp_two_iff_integrable_sq h₁.aestronglyMeasurable).1 h₁).const_mul V
  have hi₂ : Integrable (fun p : (Y×X)×X ↦ V*f (p.1.1,p.2)^2) ((ν.prod μ).prod μ) :=
    ((memLp_two_iff_integrable_sq h₂.aestronglyMeasurable).1 h₂).const_mul V
  let := isFiniteMeasure_withDensity_ofReal hi₁.2
  let := isFiniteMeasure_withDensity_ofReal hi₂.2
  rw [←full_affinity_square μ ν f hf hf0 V hV]
  apply affinity_partition_le
  intro ij
  have he : {p : (Y×X)×X | (cell p.1.2,cell p.2)=ij}=
      {p | cell p.1.2=ij.1}∩{p | cell p.2=ij.2} := by
    ext p
    exact Prod.ext_iff
  rw [he]
  exact ((hcell ij.1).preimage (measurable_snd.comp measurable_fst)).inter
    ((hcell ij.2).preimage measurable_snd)

end HardSphere.Comparison

end

end OAI
