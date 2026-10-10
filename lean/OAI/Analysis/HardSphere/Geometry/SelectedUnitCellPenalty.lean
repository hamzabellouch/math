import Mathlib
import OAI.Analysis.HardSphere.Geometry.CubeCell

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
namespace HardSphere
open SphericalCoordinates
open scoped BigOperators

noncomputable def selectedUnitCellPenalty {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] (a : ℝ) (u : ScalarL2 n L) : ℝ :=
  ∑ σ : Fin n → CubeCell K,
    (∑ v : CubeCell K,1/(64*Real.sqrt 3)*a*(Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)*
      ((Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)-1))*‖unitSectorRestriction hL σ u‖^2

lemma continuous_selectedUnitCellPenalty {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (p : Fin n → Prop) [DecidablePred p] (a : ℝ) :
    Continuous (selectedUnitCellPenalty (n := n) hL p a) := by
  apply continuous_finsetSum
  intro σ _
  exact continuous_const.mul ((unitSectorRestriction hL σ).continuous.norm.pow 2)

lemma SmoothTest.selected_cell_energy {n K : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a)
    (hL : L.val=(K:ℝ)) (p : Fin n → Prop) [DecidablePred p] (ha : 0<a) : selectedUnitCellPenalty hL p a f.jet.1≤ selectedEnergy p f.jet := by
  have h := selected_subdivided_cell_energy (j := K) f.cube_smooth p ha (by norm_num : (0:ℝ)<1) 0
    (f.cube_zero ha.le)
  simp only [one_pow,div_one,mul_one,←hL] at h
  have hn (σ : Fin n → CubeCell K) := f.unitSector_norm hL σ
  simp only [unitSectorMeasure] at hn
  simp_rw [←hn,f.cube_gradient_lintegral] at h
  have hco (σ : Fin n → CubeCell K) (v : CubeCell K) :
      0≤1/(64*Real.sqrt 3)*a*(Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)*
        ((Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)-1) := by
    simpa only [one_pow,div_one] using cube_energy_coefficient_nonneg
      (Fintype.card {i : {i // p i} // σ i.val=v}) ha.le (by norm_num : (0:ℝ)≤1)
  have hp : ENNReal.ofReal (selectedUnitCellPenalty hL p a f.jet.1)=
      ∑ σ : Fin n → CubeCell K,
        (∑ v : CubeCell K,ENNReal.ofReal (1/(64*Real.sqrt 3)*a*(Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)*
          ((Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)-1)))*ENNReal.ofReal (‖unitSectorRestriction hL σ f.jet.1‖^2) := by
    rw [selectedUnitCellPenalty,ENNReal.ofReal_sum_of_nonneg (fun σ _ ↦ mul_nonneg (Finset.sum_nonneg (fun v _ ↦ hco σ v)) (sq_nonneg _))]
    apply Finset.sum_congr rfl
    intro σ _
    rw [ENNReal.ofReal_mul (Finset.sum_nonneg (fun v _ ↦ hco σ v)),ENNReal.ofReal_sum_of_nonneg (fun v _ ↦ hco σ v)]
  have he : ENNReal.ofReal (selectedEnergy p f.jet)=∑ i : {i // p i},∑ q : Fin 3, ENNReal.ofReal (‖f.jet.2 (i.val,q)‖^2) := by
    rw [selectedEnergy,ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
    apply Finset.sum_congr rfl
    intro i _
    exact ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _)
  apply (ENNReal.ofReal_le_ofReal_iff (by unfold selectedEnergy; positivity)).mp
  rw [hp,he]
  exact h

lemma dirichlet_selected_cell_energy {n K : ℕ} {L : Length} {a : ℝ}
    (hL : L.val=(K:ℝ)) (p : Fin n → Prop) [DecidablePred p] (ha : 0<a) (u : Jet n L) (hu : u∈dirichletDomain n L a) :
    selectedUnitCellPenalty hL p a u.1≤ selectedEnergy p u := by
  have hc : IsClosed {u : Jet n L | selectedUnitCellPenalty hL p a u.1≤ selectedEnergy p u} := by
    apply isClosed_le
    · exact (continuous_selectedUnitCellPenalty hL p a).comp continuous_fst
    · exact continuous_finsetSum _ (fun i _ ↦ continuous_finsetSum _
        (fun q _ ↦ ((continuous_apply (i.val,q)).comp continuous_snd).norm.pow 2))
  exact hc.closure_subset_iff.mpr (by rintro _ ⟨f,rfl⟩; exact f.selected_cell_energy hL p ha) hu

noncomputable def unitIndex {K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (x : AddCircle L.val) : Fin K :=
  ⟨⌊((AddCircle.equivIco L.val 0) x).val⌋₊, by
    apply (Nat.floor_lt (by simpa only [zero_add] using ((AddCircle.equivIco L.val 0) x).property.1)).mpr
    simpa only [zero_add,hL] using ((AddCircle.equivIco L.val 0) x).property.2⟩

lemma measurable_unitIndex {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) :
    Measurable (unitIndex hL) := by
  apply measurable_to_countable'
  intro v
  have hm := (measurable_subtype_coe.comp (AddCircle.measurableEquivIco L.val 0).measurable).nat_floor
  have he : unitIndex hL ⁻¹' {v}=(fun x ↦ ⌊((AddCircle.equivIco L.val 0) x).val⌋₊) ⁻¹' {v.val} := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,Fin.ext_iff,unitIndex]
  rw [he]
  exact hm (measurableSet_singleton _)

noncomputable def unitSite {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (x : Torus L) : CubeCell K :=
  (unitIndex hL (x 0),unitIndex hL (x 1),unitIndex hL (x 2))

lemma measurable_unitSite {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) :
    Measurable (unitSite hL) :=
  ((measurable_unitIndex hL).comp (measurable_pi_apply 0)).prodMk
    (((measurable_unitIndex hL).comp (measurable_pi_apply 1)).prodMk
      ((measurable_unitIndex hL).comp (measurable_pi_apply 2)))

lemma unitIndex_coe {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (v : Fin K) {x : ℝ}
    (hx : x∈Ico (v:ℝ) ((v:ℝ)+1)) : unitIndex hL (x : AddCircle L.val)=v := by
  have hx0 : 0≤x := (Nat.cast_nonneg v.val).trans hx.1
  have hxL : x<L.val := by
    rw [hL]
    have hv : (v:ℝ)+1≤(K:ℝ) := by exact_mod_cast v.isLt
    exact hx.2.trans_le hv
  apply Fin.ext
  change ⌊((AddCircle.equivIco L.val 0) (x : AddCircle L.val)).val⌋₊=v.val
  rw [AddCircle.equivIco_coe_eq ⟨hx0,by simpa only [zero_add] using hxL⟩]
  exact (Nat.floor_eq_iff hx0).mpr hx

lemma cube_ae_halfOpen (b : Point) (l : ℝ) :
    ∀ᵐ x ∂volume.restrict (cube b l),
      x.1∈Ico b.1 (b.1+l) ∧ x.2.1∈Ico b.2.1 (b.2.1+l) ∧ x.2.2∈Ico b.2.2 (b.2.2+l) := by
  rw [cube_volume,← restrict_Ico_eq_restrict_Icc,← restrict_Ico_eq_restrict_Icc,
    ← restrict_Ico_eq_restrict_Icc]
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
  filter_upwards [ae_restrict_mem measurableSet_Ico] with z hz
  exact ⟨hx,hy,hz⟩

lemma unitSector_site_ae {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (σ : Fin n → CubeCell K) :
    ∀ᵐ X ∂unitSectorMeasure n K σ, ∀ i, unitSite hL (cubeParameter n L X i)=σ i := by
  rw [ae_all_iff]
  intro i
  have h : ∀ᵐ X ∂unitSectorMeasure n K σ,
      (X i).1∈Ico (subcubeBase 0 1 (σ i)).1 ((subcubeBase 0 1 (σ i)).1+1) ∧
      (X i).2.1∈Ico (subcubeBase 0 1 (σ i)).2.1 ((subcubeBase 0 1 (σ i)).2.1+1) ∧
      (X i).2.2∈Ico (subcubeBase 0 1 (σ i)).2.2 ((subcubeBase 0 1 (σ i)).2.2+1) :=
    (Measure.tendsto_eval_ae_ae (μ := fun k : Fin n ↦ volume.restrict (cube (subcubeBase 0 1 (σ k)) 1)) (i := i)).eventually (cube_ae_halfOpen (subcubeBase 0 1 (σ i)) 1)
  filter_upwards [h] with X hX
  rcases hX with ⟨h0,h1,h2⟩
  apply Prod.ext
  · apply unitIndex_coe hL (σ i).1
    change (X i).1∈Ico _ _
    simpa only [subcubeBase,zero_add,mul_one,Prod.fst_zero] using h0
  · apply Prod.ext
    · apply unitIndex_coe hL (σ i).2.1
      change (X i).2.1∈Ico _ _
      simpa only [subcubeBase,zero_add,mul_one,Prod.fst_zero,Prod.snd_zero] using h1
    · apply unitIndex_coe hL (σ i).2.2
      change (X i).2.2∈Ico _ _
      simpa only [subcubeBase,zero_add,mul_one,Prod.snd_zero] using h2

noncomputable def unitOccupation {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] (v : CubeCell K) (X : Configuration n L) : ℕ :=
  Fintype.card {i : {i // p i} // unitSite hL (X i.val)=v}

noncomputable def occupationWeight {n K : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (a : ℝ) (σ : Fin n → CubeCell K) : ℝ :=
  ∑ v : CubeCell K,1/(64*Real.sqrt 3)*a*(Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)*
      ((Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)-1)

lemma occupationWeight_nonneg {n K : ℕ} (p : Fin n → Prop) [DecidablePred p]
    {a : ℝ} (ha : 0≤a) (σ : Fin n → CubeCell K) : 0≤occupationWeight p a σ := by
  apply Finset.sum_nonneg
  intro v _
  simpa only [one_pow,div_one] using cube_energy_coefficient_nonneg
    (Fintype.card {i : {i // p i} // σ i.val=v}) ha (by norm_num : (0:ℝ)≤1)

lemma unitSector_norm {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (σ : Fin n → CubeCell K)
    (u : ScalarL2 n L) : ENNReal.ofReal (‖unitSectorRestriction hL σ u‖^2)=
      ∫⁻ X,ENNReal.ofReal (‖u (cubeParameter n L X)‖^2) ∂unitSectorMeasure n K σ := by
  have hn := smooth_norm_lintegral (Lp.memLp (unitSectorRestriction hL σ u))
  rw [Lp.toLp_coeFn] at hn
  rw [hn]
  apply lintegral_congr_ae
  filter_upwards [unitSectorRestriction_ae hL σ u] with X hX
  rw [hX]

lemma selectedUnitCellPenalty_eq_integral {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] {a : ℝ} (ha : 0≤a) (u : ScalarL2 n L) :
    ENNReal.ofReal (selectedUnitCellPenalty hL p a u)=
      ∫⁻ X, ENNReal.ofReal (∑ v : CubeCell K, 1/(64*Real.sqrt 3)*a*
        (unitOccupation hL p v X:ℝ)*((unitOccupation hL p v X:ℝ)-1))*
          ENNReal.ofReal (‖u X‖^2) := by
  let H : Configuration n L → ℝ≥0∞ := fun X ↦
    ENNReal.ofReal (occupationWeight p a (fun i ↦ unitSite hL (X i)))*ENNReal.ofReal (‖u X‖^2)
  have hm : Measurable H := by
    dsimp only [H]
    have h₁ : Measurable (fun X : Configuration n L ↦ ENNReal.ofReal (occupationWeight p a (fun i ↦ unitSite hL (X i)))) :=
      ((measurable_of_finite (occupationWeight (K := K) p a)).comp
        (Measurable.of_eval fun i ↦ (measurable_unitSite hL).comp (measurable_pi_apply i))).ennreal_ofReal
    have h₂ : Measurable (fun X : Configuration n L ↦ ENNReal.ofReal (‖u X‖^2)) :=
      ((Lp.stronglyMeasurable u).measurable.norm.pow_const 2).ennreal_ofReal
    exact h₁.mul h₂
  change _ = ∫⁻ X,H X
  rw [← (cubeParameter_preserving n L).lintegral_comp hm]
  have hmμ : Measure.pi (fun _ : Fin n ↦ volume.restrict (cube 0 L.val))=
      ∑ σ : Fin n → CubeCell K, unitSectorMeasure n K σ := by
    rw [hL,← mul_one (K:ℝ),cube_configuration_subdivision 0 (by norm_num : (0:ℝ)≤1),Measure.sum_fintype]
    rfl
  rw [hmμ,MeasureTheory.lintegral_finsetSum_measure]
  change ENNReal.ofReal (∑ σ : Fin n → CubeCell K,
    occupationWeight p a σ*‖unitSectorRestriction hL σ u‖^2)=_
  rw [ENNReal.ofReal_sum_of_nonneg (fun σ _ ↦ mul_nonneg (occupationWeight_nonneg p ha σ) (sq_nonneg _))]
  apply Finset.sum_congr rfl
  intro σ _
  rw [ENNReal.ofReal_mul (occupationWeight_nonneg p ha σ),unitSector_norm]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [unitSector_site_ae hL σ] with X hX
  have he : (fun i ↦ unitSite hL (cubeParameter n L X i))=σ := funext hX
  change _ = ENNReal.ofReal (occupationWeight p a (fun i ↦ unitSite hL (cubeParameter n L X i)))*_
  rw [he]

lemma dirichlet_physical_cell_energy {n K : ℕ} {L : Length} {a : ℝ}
    (hL : L.val=(K:ℝ)) (p : Fin n → Prop) [DecidablePred p] (ha : 0<a)
    (u : Jet n L) (hu : u∈dirichletDomain n L a) :
    (∫⁻ X, ENNReal.ofReal (∑ v : CubeCell K, 1/(64*Real.sqrt 3)*a*
      (unitOccupation hL p v X:ℝ)*((unitOccupation hL p v X:ℝ)-1))*
        ENNReal.ofReal (‖u.1 X‖^2)) ≤ ENNReal.ofReal (selectedEnergy p u) := by
  rw [← selectedUnitCellPenalty_eq_integral hL p ha.le]
  exact ENNReal.ofReal_le_ofReal (dirichlet_selected_cell_energy hL p ha u hu)

end HardSphere

end

end OAI
