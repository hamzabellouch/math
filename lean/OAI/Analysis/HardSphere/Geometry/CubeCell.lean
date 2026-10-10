import Mathlib
import OAI.Analysis.HardSphere.Geometry.PointFin
import OAI.Analysis.HardSphere.Geometry.SubsetPointLinear

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HardSphere
open SphericalCoordinates
open scoped BigOperators

abbrev CubeCell (K : ℕ) := Fin K × Fin K × Fin K

noncomputable def unitSectorMeasure (n K : ℕ) (σ : Fin n → CubeCell K) : Measure (Fin n → Point) :=
  Measure.pi (fun i ↦ volume.restrict (cube (subcubeBase 0 1 (σ i)) 1))

lemma unitSectorMeasure_le {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (σ : Fin n → CubeCell K) :
    unitSectorMeasure n K σ≤Measure.pi (fun _ : Fin n ↦ volume.restrict (cube 0 L.val)) := by
  rw [hL,← mul_one (K:ℝ),cube_configuration_subdivision 0 (by norm_num : (0:ℝ)≤1)]
  exact Measure.le_sum _ σ

noncomputable def unitSectorRestriction {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (σ : Fin n → CubeCell K) : ScalarL2 n L →L[ℝ] Lp ℂ 2 (unitSectorMeasure n K σ) :=
  (Lp.LpToLpOfMeasureLeSMul (c := (1:ℝ≥0∞)) (by norm_num)
    (show unitSectorMeasure n K σ≤1 • Measure.pi (fun _ : Fin n ↦ volume.restrict (cube 0 L.val)) by
      simpa only [one_smul] using unitSectorMeasure_le hL σ)).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (cubeParameter n L) (cubeParameter_preserving n L)).toContinuousLinearMap

lemma unitSectorRestriction_ae {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (σ : Fin n → CubeCell K) (u : ScalarL2 n L) :
    unitSectorRestriction hL σ u=ᵐ[unitSectorMeasure n K σ] fun X ↦ u (cubeParameter n L X) := by
  have h₁ := Lp.coeFn_LpToLpOfMeasureLeSMul (c := (1:ℝ≥0∞)) (by norm_num)
    (show unitSectorMeasure n K σ≤1 • Measure.pi (fun _ : Fin n ↦ volume.restrict (cube 0 L.val)) by
      simpa only [one_smul] using unitSectorMeasure_le hL σ)
    ((Lp.compMeasurePreservingₗᵢ ℝ (cubeParameter n L) (cubeParameter_preserving n L)) u)
  apply h₁.trans
  apply (Measure.absolutelyContinuous_of_le (unitSectorMeasure_le hL σ)).ae_eq
  exact Lp.coeFn_compMeasurePreserving u (cubeParameter_preserving n L)

lemma SmoothTest.unitSector_norm {n K : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a)
    (hL : L.val=(K:ℝ)) (σ : Fin n → CubeCell K) :
    ENNReal.ofReal (‖unitSectorRestriction hL σ f.jet.1‖^2)=
      ∫⁻ X,ENNReal.ofReal (‖f.toFun (cubeParameter n L X)‖^2) ∂unitSectorMeasure n K σ := by
  have h₁ := unitSectorRestriction_ae hL σ f.jet.1
  have h₂ : (fun X ↦ f.jet.1 (cubeParameter n L X))=ᵐ[unitSectorMeasure n K σ]
      fun X ↦ f.toFun (cubeParameter n L X) := by
    apply (Measure.absolutelyContinuous_of_le (unitSectorMeasure_le hL σ)).ae_eq
    exact (cubeParameter_preserving n L).quasiMeasurePreserving.ae_eq_comp f.memLp.coeFn_toLp
  have hn := smooth_norm_lintegral (Lp.memLp (unitSectorRestriction hL σ f.jet.1))
  rw [Lp.toLp_coeFn] at hn
  rw [hn]
  apply lintegral_congr_ae
  filter_upwards [h₁.trans h₂] with X hX
  rw [hX]

noncomputable def unitCellPenalty {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (a : ℝ) (u : ScalarL2 n L) : ℝ :=
  ∑ σ : Fin n → CubeCell K,
    (∑ v : CubeCell K,1/(64*Real.sqrt 3)*a*(Fintype.card {i // σ i=v}:ℝ)*
      ((Fintype.card {i // σ i=v}:ℝ)-1))*‖unitSectorRestriction hL σ u‖^2

lemma continuous_unitCellPenalty {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (a : ℝ) :
    Continuous (unitCellPenalty (n := n) hL a) := by
  apply continuous_finsetSum
  intro σ _
  exact continuous_const.mul ((unitSectorRestriction hL σ).continuous.norm.pow 2)

lemma SmoothTest.cell_energy {n K : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a)
    (hL : L.val=(K:ℝ)) (ha : 0<a) : unitCellPenalty hL a f.jet.1≤energy f.jet := by
  have h := subdivided_cell_energy (j := K) f.cube_smooth ha (by norm_num : (0:ℝ)<1) 0
    (f.cube_zero ha.le)
  simp only [one_pow,div_one,mul_one,←hL] at h
  have hn (σ : Fin n → CubeCell K) := f.unitSector_norm hL σ
  simp only [unitSectorMeasure] at hn
  simp_rw [←hn,f.cube_gradient_lintegral] at h
  have hco (σ : Fin n → CubeCell K) (v : CubeCell K) :
      0≤1/(64*Real.sqrt 3)*a*(Fintype.card {i // σ i=v}:ℝ)*
        ((Fintype.card {i // σ i=v}:ℝ)-1) := by
    simpa only [one_pow,div_one] using cube_energy_coefficient_nonneg
      (Fintype.card {i // σ i=v}) ha.le (by norm_num : (0:ℝ)≤1)
  have hp : ENNReal.ofReal (unitCellPenalty hL a f.jet.1)=
      ∑ σ : Fin n → CubeCell K,
        (∑ v : CubeCell K,ENNReal.ofReal (1/(64*Real.sqrt 3)*a*(Fintype.card {i // σ i=v}:ℝ)*
          ((Fintype.card {i // σ i=v}:ℝ)-1)))*ENNReal.ofReal (‖unitSectorRestriction hL σ f.jet.1‖^2) := by
    rw [unitCellPenalty,ENNReal.ofReal_sum_of_nonneg (fun σ _ ↦ mul_nonneg (Finset.sum_nonneg (fun v _ ↦ hco σ v)) (sq_nonneg _))]
    apply Finset.sum_congr rfl
    intro σ _
    rw [ENNReal.ofReal_mul (Finset.sum_nonneg (fun v _ ↦ hco σ v)),ENNReal.ofReal_sum_of_nonneg (fun v _ ↦ hco σ v)]
  have he : ENNReal.ofReal (energy f.jet)=∑ i : Fin n,∑ q : Fin 3, ENNReal.ofReal (‖f.jet.2 (i,q)‖^2) := by
    rw [energy,Fintype.sum_prod_type,ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
    apply Finset.sum_congr rfl
    intro i _
    exact ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _)
  apply (ENNReal.ofReal_le_ofReal_iff (by unfold energy; positivity)).mp
  rw [hp,he]
  exact h

lemma dirichlet_cell_energy {n K : ℕ} {L : Length} {a : ℝ}
    (hL : L.val=(K:ℝ)) (ha : 0<a) (u : Jet n L) (hu : u∈dirichletDomain n L a) :
    unitCellPenalty hL a u.1≤energy u := by
  have hc : IsClosed {u : Jet n L | unitCellPenalty hL a u.1≤energy u} := by
    apply isClosed_le
    · exact (continuous_unitCellPenalty hL a).comp continuous_fst
    · exact continuous_finsetSum _ (fun p _ ↦ ((continuous_apply p).comp continuous_snd).norm.pow 2)
  exact hc.closure_subset_iff.mpr (by rintro _ ⟨f,rfl⟩; exact f.cell_energy hL ha) hu

end HardSphere

namespace HardSphere.SphericalCoordinates
open scoped BigOperators

lemma selected_sector_cell_energy {I C : Type*} [Fintype I] [Fintype C] [DecidableEq I] [DecidableEq C]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (I → Point) → E} (hF : ContDiff ℝ 1 F) (p : I → Prop) [DecidablePred p]
    {r l : ℝ} (hr : 0<r) (hl : 0<l) (b : C → Point) (σ : I → C)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c)≤r^2 → F X=0) :
    (∑ v : C, ENNReal.ofReal (1/(64*Real.sqrt 3)*r/l^3*
      (Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)*
      ((Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)-1)))*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun i ↦ volume.restrict (cube (b (σ i)) l))) ≤
        ∑ i : {i // p i}, (∫⁻ X, ENNReal.ofReal (indexGradSq F i.val X)
          ∂Measure.pi (fun i ↦ volume.restrict (cube (b (σ i)) l))) := by
  let μ := fun i ↦ (volume : Measure Point).restrict (cube (b (σ i)) l)
  have hslice (Y : {i // ¬p i} → Point) := sector_cell_energy
    (hF.comp (contDiff_subsetPointFill p Y)) hr hl b (fun i : {i // p i} ↦ σ i.val)
    (F := F ∘ subsetPointFill p Y) (by
      intro X a c hac hd
      apply hz (subsetPointFill p Y X) a.val c.val (fun h ↦ hac (Subtype.ext h))
      simpa only [subsetPointFill,dite_eq_left a.property,dite_eq_left c.property] using hd)
  have hm : Measurable (fun X ↦ ENNReal.ofReal (‖F X‖^2)) := by
    simpa only [Pi.pow_apply] using (hF.continuous.norm.pow 2).measurable.ennreal_ofReal
  have hn := lintegral_subsetPointFill μ p (fun X ↦ ENNReal.ofReal (‖F X‖^2)) hm
  rw [hn,← lintegral_const_mul' _ _ (by simp)]
  have hi := lintegral_mono hslice (μ := Measure.pi (fun i : {i // ¬p i} ↦ μ i.val))
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

lemma selected_subdivided_cell_energy {n j : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin n → Point) → E} (hF : ContDiff ℝ 1 F) (p : Fin n → Prop) [DecidablePred p]
    {r l : ℝ} (hr : 0<r) (hl : 0<l) (b : Point)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c)≤r^2 → F X=0) :
    (∑ σ : Fin n → (Fin j × Fin j × Fin j),
      (∑ v : Fin j × Fin j × Fin j,
        ENNReal.ofReal (1/(64*Real.sqrt 3)*r/l^3*
          (Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)*
          ((Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)-1)))*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2)
        ∂Measure.pi (fun i ↦ volume.restrict (cube (subcubeBase b l (σ i)) l)))) ≤
      ∑ i : {i // p i}, ∫⁻ X,ENNReal.ofReal (particleGradSq F i.val X)
        ∂Measure.pi (fun _ ↦ volume.restrict (cube b ((j:ℝ)*l))) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n → (Fin j × Fin j × Fin j))))
    (fun σ _ ↦ selected_sector_cell_energy hF p hr hl (subcubeBase b l) σ hz)
  apply h.trans_eq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [cube_configuration_subdivision b hl.le,Measure.sum_fintype,MeasureTheory.lintegral_finsetSum_measure]
  rfl

end HardSphere.SphericalCoordinates

end
end
end
end
end
end
end
end
end

end OAI
