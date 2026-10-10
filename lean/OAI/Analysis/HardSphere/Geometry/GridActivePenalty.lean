import Mathlib
import OAI.Analysis.HardSphere.Geometry.SelectedUnitCellPenalty
import OAI.Analysis.HardSphere.Capacity.SectorActiveCapacity
import OAI.Analysis.HardSphere.Geometry.HalfShiftCover

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
open Set Function MeasureTheory
open scoped ENNReal
namespace HardSphere
open SphericalCoordinates
open scoped BigOperators
noncomputable def gridActivePenalty {n j : ℕ} {L : Length} {l : ℝ}
    (hl : 0≤l) (hL : L.val=(j:ℝ)*l) (b : Point) (p : Fin n → Prop) [DecidablePred p]
    (u : ScalarL2 n L) : ℝ :=
  ∑ σ : Fin n → CubeCell j, ((activeLabels (fun i : {i // p i} ↦ σ i.val)).card:ℝ)*
    ‖gridSectorRestriction hl hL b σ u‖^2

lemma continuous_gridActivePenalty {n j : ℕ} {L : Length} {l : ℝ}
    (hl : 0≤l) (hL : L.val=(j:ℝ)*l) (b : Point) (p : Fin n → Prop) [DecidablePred p] :
    Continuous (gridActivePenalty (n := n) hl hL b p) := by
  apply continuous_finsetSum
  intro σ _
  exact continuous_const.mul ((gridSectorRestriction hl hL b σ).continuous.norm.pow 2)

lemma selectedEnergy_nonneg {n : ℕ} {L : Length} (p : Fin n → Prop) [DecidablePred p] (u : Jet n L) :
    0≤ selectedEnergy p u := by unfold selectedEnergy; positivity

lemma selectedEnergy_ofReal {n : ℕ} {L : Length} (p : Fin n → Prop) [DecidablePred p] (u : Jet n L) :
    ENNReal.ofReal (selectedEnergy p u)=∑ i : {i // p i},∑ q : Fin 3, ENNReal.ofReal (‖u.2 (i.val,q)‖^2) := by
  rw [selectedEnergy,ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
  apply Finset.sum_congr rfl
  intro i _
  exact ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _)

lemma SmoothTest.active_grid_energy {n j : ℕ} {L : Length} {a l : ℝ} (f : SmoothTest n L a)
    (hl : 0≤l) (hL : L.val=(j:ℝ)*l) (b : Point) (p : Fin n → Prop) [DecidablePred p] (ha : 0<a) :
    gridActivePenalty hl hL b p f.jet.1≤Real.sqrt 3*l^3/a*selectedEnergy p f.jet := by
  have h := selected_subdivided_active_capacity (j := j) f.cube_smooth p ha hl b (f.cube_zero ha.le)
  rw [←hL] at h
  have hn (σ : Fin n → CubeCell j) := f.gridSector_norm hl hL b σ
  simp only [gridSectorMeasure] at hn
  simp_rw [←hn,f.cube_gradient_lintegral_base b] at h
  have hp : ENNReal.ofReal (gridActivePenalty hl hL b p f.jet.1)=
      ∑ σ : Fin n → CubeCell j,
        ((activeLabels (fun i : {i // p i} ↦ σ i.val)).card:ℝ≥0∞)*ENNReal.ofReal (‖gridSectorRestriction hl hL b σ f.jet.1‖^2) := by
    rw [gridActivePenalty,ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
    apply Finset.sum_congr rfl
    intro σ _
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) (selectedEnergy_nonneg p f.jet))).mp
  rw [hp,ENNReal.ofReal_mul (by positivity),selectedEnergy_ofReal]
  exact h

lemma dirichlet_active_grid_energy {n j : ℕ} {L : Length} {a l : ℝ}
    (hl : 0≤l) (hL : L.val=(j:ℝ)*l) (b : Point) (p : Fin n → Prop) [DecidablePred p] (ha : 0<a)
    (u : Jet n L) (hu : u∈dirichletDomain n L a) :
    gridActivePenalty hl hL b p u.1≤Real.sqrt 3*l^3/a*selectedEnergy p u := by
  have hc : IsClosed {u : Jet n L | gridActivePenalty hl hL b p u.1≤Real.sqrt 3*l^3/a*selectedEnergy p u} := by
    apply isClosed_le
    · exact (continuous_gridActivePenalty hl hL b p).comp continuous_fst
    · exact continuous_const.mul (continuous_finsetSum _ (fun i _ ↦ continuous_finsetSum _
        (fun q _ ↦ ((continuous_apply (i.val,q)).comp continuous_snd).norm.pow 2)))
  exact hc.closure_subset_iff.mpr (by rintro _ ⟨f,rfl⟩; exact f.active_grid_energy hl hL b p ha) hu

noncomputable def gridSite {j : ℕ} [NeZero j] {L : Length} {l : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (b : Point) (x : Torus L) : CubeCell j :=
  ((ZMod.finEquiv j).symm (GridGeometry.index hl hL b.1 (x 0)),
    (ZMod.finEquiv j).symm (GridGeometry.index hl hL b.2.1 (x 1)),
    (ZMod.finEquiv j).symm (GridGeometry.index hl hL b.2.2 (x 2)))

lemma measurable_gridSite {j : ℕ} [NeZero j] {L : Length} {l : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (b : Point) : Measurable (gridSite hl hL b) := by
  have hm (c : ℝ) (q : Fin 3) : Measurable (fun x : Torus L ↦ (ZMod.finEquiv j).symm (GridGeometry.index hl hL c (x q))) :=
    (measurable_of_finite (ZMod.finEquiv j).symm).comp ((GridGeometry.measurable_index hl hL c).comp (measurable_pi_apply q))
  exact (hm b.1 0).prodMk ((hm b.2.1 1).prodMk (hm b.2.2 2))

lemma gridSector_site_ae {n j : ℕ} [NeZero j] {L : Length} {l : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (b : Point) (σ : Fin n → CubeCell j) :
    ∀ᵐ X ∂gridSectorMeasure n j b l σ, ∀ i, gridSite hl hL b (cubeParameter n L X i)=σ i := by
  rw [ae_all_iff]
  intro i
  have h : ∀ᵐ X ∂gridSectorMeasure n j b l σ,
      (X i).1∈Ico (subcubeBase b l (σ i)).1 ((subcubeBase b l (σ i)).1+l) ∧
      (X i).2.1∈Ico (subcubeBase b l (σ i)).2.1 ((subcubeBase b l (σ i)).2.1+l) ∧
      (X i).2.2∈Ico (subcubeBase b l (σ i)).2.2 ((subcubeBase b l (σ i)).2.2+l) :=
    (Measure.tendsto_eval_ae_ae (μ := fun k : Fin n ↦ volume.restrict (cube (subcubeBase b l (σ k)) l)) (i := i)).eventually (cube_ae_halfOpen (subcubeBase b l (σ i)) l)
  filter_upwards [h] with X hX
  rcases hX with ⟨h0,h1,h2⟩
  have he0 := GridGeometry.index_in_cell hl hL b.1 (σ i).1 h0
  have he1 := GridGeometry.index_in_cell hl hL b.2.1 (σ i).2.1 h1
  have he2 := GridGeometry.index_in_cell hl hL b.2.2 (σ i).2.2 h2
  change ((ZMod.finEquiv j).symm (GridGeometry.index hl hL b.1 ((X i).1 : AddCircle L.val)),
    (ZMod.finEquiv j).symm (GridGeometry.index hl hL b.2.1 ((X i).2.1 : AddCircle L.val)),
    (ZMod.finEquiv j).symm (GridGeometry.index hl hL b.2.2 ((X i).2.2 : AddCircle L.val)))=σ i
  rw [he0,he1,he2]
  simp only [RingEquiv.symm_apply_apply,Prod.eta]

noncomputable def gridActiveCount {n j : ℕ} [NeZero j] {L : Length} {l : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (b : Point) (p : Fin n → Prop) [DecidablePred p]
    (X : Configuration n L) : ℕ :=
  (activeLabels (fun i : {i // p i} ↦ gridSite hl hL b (X i.val))).card

lemma measurable_gridActiveCount {n j : ℕ} [NeZero j] {L : Length} {l : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (b : Point) (p : Fin n → Prop) [DecidablePred p] :
    Measurable (gridActiveCount (n := n) hl hL b p) :=
  (measurable_of_finite (fun σ : {i // p i} → CubeCell j ↦ (activeLabels σ).card)).comp
    (Measurable.of_eval fun i ↦ (measurable_gridSite hl hL b).comp (measurable_pi_apply i.val))

lemma gridActivePenalty_eq_integral {n j : ℕ} [NeZero j] {L : Length} {l : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (b : Point) (p : Fin n → Prop) [DecidablePred p]
    (u : ScalarL2 n L) : ENNReal.ofReal (gridActivePenalty hl.le hL b p u)=
      ∫⁻ X, (gridActiveCount hl hL b p X:ℝ≥0∞)*ENNReal.ofReal (‖u X‖^2) := by
  let H : Configuration n L → ℝ≥0∞ := fun X ↦ (gridActiveCount hl hL b p X:ℝ≥0∞)*ENNReal.ofReal (‖u X‖^2)
  have hm : Measurable H := by
    have h₁ : Measurable (fun X : Configuration n L ↦ (gridActiveCount hl hL b p X:ℝ≥0∞)) :=
      (measurable_of_countable (fun k : ℕ ↦ (k:ℝ≥0∞))).comp (measurable_gridActiveCount hl hL b p)
    have h₂ : Measurable (fun X : Configuration n L ↦ ENNReal.ofReal (‖u X‖^2)) :=
      ((Lp.stronglyMeasurable u).measurable.norm.pow_const 2).ennreal_ofReal
    exact h₁.mul h₂
  change _ = ∫⁻ X,H X
  rw [← (cubeParameter_preserving_base n L b).lintegral_comp hm]
  have hmμ : Measure.pi (fun _ : Fin n ↦ volume.restrict (cube b L.val))=
      ∑ σ : Fin n → CubeCell j, gridSectorMeasure n j b l σ := by
    rw [hL,cube_configuration_subdivision b hl.le,Measure.sum_fintype]
    rfl
  rw [hmμ,MeasureTheory.lintegral_finsetSum_measure]
  rw [gridActivePenalty,ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
  apply Finset.sum_congr rfl
  intro σ _
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,gridSector_norm]
  rw [← lintegral_const_mul' _ _ (by simp)]
  apply lintegral_congr_ae
  filter_upwards [gridSector_site_ae hl hL b σ] with X hX
  have he : (fun i : {i // p i} ↦ gridSite hl hL b (cubeParameter n L X i.val))=fun i : {i // p i} ↦ σ i.val := funext (fun i ↦ hX i.val)
  change _ = ((activeLabels (fun i : {i // p i} ↦ gridSite hl hL b (cubeParameter n L X i.val))).card:ℝ≥0∞)*_
  rw [he]

lemma dirichlet_physical_grid_energy {n j : ℕ} [NeZero j] {L : Length} {a l : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (b : Point) (p : Fin n → Prop) [DecidablePred p] (ha : 0<a)
    (u : Jet n L) (hu : u∈dirichletDomain n L a) :
    (∫⁻ X, (gridActiveCount hl hL b p X:ℝ≥0∞)*ENNReal.ofReal (‖u.1 X‖^2)) ≤
      ENNReal.ofReal (Real.sqrt 3*l^3/a*selectedEnergy p u) := by
  rw [←gridActivePenalty_eq_integral]
  exact ENNReal.ofReal_le_ofReal (dirichlet_active_grid_energy hl.le hL b p ha u hu)

lemma coordinate_distance_le (L : Length) (x y : Torus L) (q : Fin 3) :
    dist (x q) (y q)≤torusDistance L x y := by
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (fun t _ ↦ sq_nonneg (dist (x t) (y t))) (Finset.mem_univ q)

noncomputable def halfGridBase (l : ℝ) (s : Fin 3 → Bool) : Point :=
  (if s 0 then l/2 else 0,if s 1 then l/2 else 0,if s 2 then l/2 else 0)

lemma halfGrid_pair_cover {j : ℕ} [NeZero j] {L : Length} {l : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (x y : Torus L) (hd : torusDistance L x y<l/2) :
    ∃ b : Fin 3 → Bool, gridSite hl hL (halfGridBase l b) x=gridSite hl hL (halfGridBase l b) y := by
  have hh (q : Fin 3) : ∃ t : Bool, GridGeometry.index hl hL (if t then l/2 else 0) (x q)=GridGeometry.index hl hL (if t then l/2 else 0) (y q) := by
    rcases GridGeometry.index_pair_cover hl hL (x q) (y q) ((coordinate_distance_le L x y q).trans_lt hd) with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  choose b hb using hh
  refine ⟨b,?_⟩
  change ((ZMod.finEquiv j).symm (GridGeometry.index hl hL (if b 0 then l/2 else 0) (x 0)),
    (ZMod.finEquiv j).symm (GridGeometry.index hl hL (if b 1 then l/2 else 0) (x 1)),
    (ZMod.finEquiv j).symm (GridGeometry.index hl hL (if b 2 then l/2 else 0) (x 2)))=_
  rw [hb 0,hb 1,hb 2]
  rfl

noncomputable def nearLabels {n : ℕ} {L : Length} (p : Fin n → Prop) [DecidablePred p]
    (s : ℝ) (X : Configuration n L) : Finset {i // p i} := by
  classical
  exact Finset.univ.filter (fun i ↦ ∃ k : {i // p i}, k≠i ∧ torusDistance L (X k.val) (X i.val)≤2*s)

lemma nearLabels_card_le_grids {n j : ℕ} [NeZero j] {L : Length} {l s : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (hs : 4*s<l) (p : Fin n → Prop) [DecidablePred p]
    (X : Configuration n L) :
    (nearLabels p s X).card≤∑ b : Fin 3 → Bool, gridActiveCount hl hL (halfGridBase l b) p X := by
  classical
  let A := fun b : Fin 3 → Bool ↦ activeLabels (fun i : {i // p i} ↦ gridSite hl hL (halfGridBase l b) (X i.val))
  have hsub : nearLabels p s X⊆Finset.univ.biUnion A := by
    intro i hi
    obtain ⟨k,hki,hkd⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨b,hb⟩ := halfGrid_pair_cover hl hL (X k.val) (X i.val) (lt_of_le_of_lt hkd (by linarith))
    exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,(mem_activeLabels _ _).mpr ⟨k,hki,hb⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

lemma dirichlet_near_energy_grid {n j : ℕ} [NeZero j] {L : Length} {a l s : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (hs : 4*s<l) (p : Fin n → Prop) [DecidablePred p] (ha : 0<a)
    (u : Jet n L) (hu : u∈dirichletDomain n L a) :
    (∫⁻ X, ((nearLabels p s X).card:ℝ≥0∞)*ENNReal.ofReal (‖u.1 X‖^2)) ≤
      ENNReal.ofReal (8*Real.sqrt 3*l^3/a*selectedEnergy p u) := by
  calc
    _ ≤ ∫⁻ X, (∑ b : Fin 3 → Bool,(gridActiveCount hl hL (halfGridBase l b) p X:ℝ≥0∞))*ENNReal.ofReal (‖u.1 X‖^2) := by
      apply lintegral_mono
      intro X
      apply mul_le_mul_of_nonneg_right _ zero_le
      exact_mod_cast nearLabels_card_le_grids hl hL hs p X
    _ = ∑ b : Fin 3 → Bool, ∫⁻ X,(gridActiveCount hl hL (halfGridBase l b) p X:ℝ≥0∞)*ENNReal.ofReal (‖u.1 X‖^2) := by
      simp_rw [Finset.sum_mul]
      apply lintegral_finsetSum
      intro b _
      have h₁ : Measurable (fun X : Configuration n L ↦ (gridActiveCount hl hL (halfGridBase l b) p X:ℝ≥0∞)) :=
        (measurable_of_countable (fun k : ℕ ↦ (k:ℝ≥0∞))).comp (measurable_gridActiveCount hl hL (halfGridBase l b) p)
      have h₂ : Measurable (fun X : Configuration n L ↦ ENNReal.ofReal (‖u.1 X‖^2)) :=
        ((Lp.stronglyMeasurable u.1).measurable.norm.pow_const 2).ennreal_ofReal
      exact h₁.mul h₂
    _ ≤ ∑ _b : Fin 3 → Bool, ENNReal.ofReal (Real.sqrt 3*l^3/a*selectedEnergy p u) :=
      Finset.sum_le_sum (fun b _ ↦ dirichlet_physical_grid_energy hl hL (halfGridBase l b) p ha u hu)
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
      norm_num only [show 2^3=8 by norm_num]
      rw [show (8:ℝ≥0∞)=ENNReal.ofReal (8:ℝ) by norm_num,← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤8)]
      congr 1
      ring
end HardSphere

end

end OAI
