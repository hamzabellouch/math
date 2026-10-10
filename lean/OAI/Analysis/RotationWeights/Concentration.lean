import OAI.Analysis.RotationWeights.Rounding

namespace OAI

noncomputable section

namespace CircleConcentration

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

section
open Set Filter MeasureTheory
open scoped Topology ENNReal
abbrev X := AddCircle (1:ℝ)
def orbitMin (θ : X) (j : ℕ) (x : X) : ℝ :=
  (Finset.range (j+1)).inf' (by simp) (fun b => dist (x+b • θ) 0)
lemma orbitMin_continuous (θ : X) (j : ℕ) : Continuous (orbitMin θ j) := by
  unfold orbitMin
  exact (Continuous.finset_inf'_apply (f := fun b : ℕ => fun x : X => dist (x+b • θ) 0) (by simp : (Finset.range (j+1)).Nonempty) (fun _ _ => by fun_prop))
lemma orbitMin_nonneg (θ : X) (j : ℕ) (x : X) : 0 ≤ orbitMin θ j x :=
  Finset.le_inf' _ _ (fun _ _ => dist_nonneg)
lemma orbitMin_le (θ : X) (j b : ℕ) (hb : b≤j) (x : X) : orbitMin θ j x ≤ dist (x+b • θ) 0 :=
  Finset.inf'_le _ (Finset.mem_range.mpr (by omega))
lemma orbitMin_max (θ : X) (j : ℕ) : ∃ x : X, ∀ y, orbitMin θ j y ≤ orbitMin θ j x := by
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty : (Set.univ:Set X).Nonempty) (orbitMin_continuous θ j).continuousOn
  exact ⟨x,fun y => hx (Set.mem_univ y)⟩
def orbitRadius (θ : X) (j : ℕ) : ℝ := orbitMin θ j (Classical.choose (orbitMin_max θ j))
lemma orbitMin_le_radius (θ : X) (j : ℕ) (x : X) : orbitMin θ j x ≤ orbitRadius θ j :=
  Classical.choose_spec (orbitMin_max θ j) x
lemma orbitRadius_nonneg (θ : X) (j : ℕ) : 0 ≤ orbitRadius θ j := orbitMin_nonneg _ _ _
lemma finite_orbit_cover (θ : X) (hd : DenseRange (fun n : ℕ => n • θ)) {ε : ℝ} (hε : 0<ε) :
    ∃ N : ℕ, ∀ x : X, ∃ b≤N, dist (x+b • θ) 0<ε := by
  have hx : ∀ x : X, ∃ b : ℕ, dist (x+b • θ) 0<ε := by
    intro x
    obtain ⟨b,hb⟩ := hd.exists_dist_lt (-x) hε
    refine ⟨b,?_⟩
    rw [dist_eq_norm] at hb ⊢
    rw [show -x-b • θ=-(x+b • θ) by abel,norm_neg] at hb
    simpa using hb
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover (fun b : ℕ => {x : X | dist (x+b • θ) 0<ε})
    (fun _ => isOpen_lt (by fun_prop) continuous_const) (by simpa only [subset_def,mem_univ,mem_iUnion,mem_ofPred_eq,true_implies] using hx)
  refine ⟨s.sup id,fun x => ?_⟩
  obtain ⟨b,hb,hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact ⟨b,Finset.le_sup (f:=id) hb,hx⟩
lemma orbitRadius_tendsto (θ : X) (hd : DenseRange (fun n : ℕ => n • θ)) : Tendsto (orbitRadius θ) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha; exact Eventually.of_forall (fun j => ha.trans_le (orbitRadius_nonneg θ j))
  · intro ε hε
    obtain ⟨N,hN⟩ := finite_orbit_cover θ hd hε
    filter_upwards [eventually_ge_atTop N] with j hj
    obtain ⟨b,hb,hx⟩ := hN (Classical.choose (orbitMin_max θ j))
    exact (orbitMin_le θ j b (hb.trans hj) _).trans_lt hx

def supportRadius (θ : X) (j : ℕ) : ℝ := orbitRadius θ j+1/((j:ℝ)+1)
lemma orbitRadius_lt_supportRadius (θ : X) (j : ℕ) : orbitRadius θ j<supportRadius θ j := by
  unfold supportRadius
  have : (0:ℝ)<1/((j:ℝ)+1) := by positivity
  linarith
lemma supportRadius_pos (θ : X) (j : ℕ) : 0<supportRadius θ j := (orbitRadius_nonneg θ j).trans_lt (orbitRadius_lt_supportRadius θ j)
lemma supportRadius_tendsto (θ : X) (hd : DenseRange (fun n : ℕ => n • θ)) : Tendsto (supportRadius θ) atTop (𝓝 0) := by
  change Tendsto (fun j : ℕ => orbitRadius θ j+1/((j:ℝ)+1)) atTop (𝓝 0)
  simpa only [add_zero] using (orbitRadius_tendsto θ hd).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
def bump (θ : X) (j : ℕ) (x : X) : ℝ := max 0 (1-dist x 0/supportRadius θ j)
lemma bump_continuous (θ : X) (j : ℕ) : Continuous (bump θ j) := by unfold bump; fun_prop
lemma bump_nonneg (θ : X) (j : ℕ) (x : X) : 0≤bump θ j x := le_max_left _ _
lemma bump_le_one (θ : X) (j : ℕ) (x : X) : bump θ j x≤1 := by
  apply max_le (by norm_num)
  have := div_nonneg (dist_nonneg (x:=x) (y:=0)) (supportRadius_pos θ j).le
  linarith
lemma bump_zero (θ : X) (j : ℕ) : bump θ j 0=1 := by simp [bump]
lemma bump_eq_zero (θ : X) (j : ℕ) (x : X) (hx : supportRadius θ j ≤ dist x 0) : bump θ j x=0 := by
  apply max_eq_left
  have hh : (1:ℝ)≤dist x 0/supportRadius θ j := (le_div_iff₀ (supportRadius_pos θ j)).mpr (by simpa using hx)
  linarith
lemma bump_pos (θ : X) (j : ℕ) (x : X) (hx : dist x 0<supportRadius θ j) : 0<bump θ j x := by
  apply lt_max_of_lt_right
  have := (div_lt_one (supportRadius_pos θ j)).mpr hx
  linarith

def partitionDenom (θ : X) (j : ℕ) (x : X) : ℝ := ∑ b∈Finset.range (j+1), bump θ j (x+b • θ)
lemma partitionDenom_continuous (θ : X) (j : ℕ) : Continuous (partitionDenom θ j) := by
  apply continuous_finsetSum
  intro b _
  exact (bump_continuous θ j).comp (continuous_id.add continuous_const)
lemma partitionDenom_pos (θ : X) (j : ℕ) (x : X) : 0<partitionDenom θ j x := by
  apply Finset.sum_pos' (fun _ _ => bump_nonneg _ _ _)
  obtain ⟨b,hb,he⟩ := Finset.exists_mem_eq_inf' (by simp : (Finset.range (j+1)).Nonempty) (fun b => dist (x+b • θ) 0)
  refine ⟨b,hb,bump_pos θ j _ ?_⟩
  rw [←he]
  exact (orbitMin_le_radius θ j x).trans_lt (orbitRadius_lt_supportRadius θ j)
lemma partitionDenom_le (θ : X) (j : ℕ) (x : X) : partitionDenom θ j x ≤ (j:ℝ)+1 := by
  calc
    _ ≤ ∑ _b∈Finset.range (j+1), (1:ℝ) := Finset.sum_le_sum (fun b _=>bump_le_one θ j _)
    _ = _ := by simp

def partition (θ : X) (j b : ℕ) (x : X) : ℝ := bump θ j (x+b • θ)/partitionDenom θ j x
lemma partition_continuous (θ : X) (j b : ℕ) : Continuous (partition θ j b) :=
  ((bump_continuous θ j).comp (continuous_id.add continuous_const)).div (partitionDenom_continuous θ j) (fun x => ne_of_gt (partitionDenom_pos θ j x))
lemma partition_nonneg (θ : X) (j b : ℕ) (x : X) : 0≤partition θ j b x := div_nonneg (bump_nonneg _ _ _) (partitionDenom_pos _ _ _).le
lemma partition_sum (θ : X) (j : ℕ) (x : X) : ∑ b∈Finset.range (j+1),partition θ j b x=1 := by
  simp only [partition,←Finset.sum_div]
  exact div_self (ne_of_gt (partitionDenom_pos θ j x))
lemma partition_zero_lower (θ : X) (j : ℕ) : 1/((j:ℝ)+1)≤partition θ j 0 0 := by
  simp only [partition,zero_nsmul,add_zero,bump_zero]
  exact one_div_le_one_div_of_le (partitionDenom_pos θ j 0) (partitionDenom_le θ j 0)
end

open Set Filter MeasureTheory
open scoped Topology ENNReal

def moveTerm (θ : X) (j b : ℕ) (h : X → ℝ) (x : X) : ℝ := partition θ j b x*h x
def movedDrop (θ : X) (j : ℕ) (h : X → ℝ) (x : X) : ℝ :=
  ∑ b∈Finset.range (j+1),moveTerm θ j b h (x-b • θ)
def moveCorrection (θ : X) (j : ℕ) (h : X → ℝ) (x : X) : ℝ :=
  -(∑ b∈Finset.range (j+1), ∑ r∈Finset.range b,moveTerm θ j b h (x-(r+1) • θ))
lemma moveTerm_continuous (θ : X) (j b : ℕ) {h : X → ℝ} (hc : Continuous h) : Continuous (moveTerm θ j b h) :=
  (partition_continuous θ j b).mul hc
lemma movedDrop_continuous (θ : X) (j : ℕ) {h : X → ℝ} (hc : Continuous h) : Continuous (movedDrop θ j h) := by
  apply continuous_finsetSum
  intro b _
  exact (moveTerm_continuous θ j b hc).comp (continuous_id.sub continuous_const)
lemma moveCorrection_continuous (θ : X) (j : ℕ) {h : X → ℝ} (hc : Continuous h) : Continuous (moveCorrection θ j h) := by
  apply Continuous.neg
  apply continuous_finsetSum
  intro b _
  apply continuous_finsetSum
  intro r _
  exact (moveTerm_continuous θ j b hc).comp (continuous_id.sub continuous_const)
lemma moveTerm_nonneg (θ : X) (j b : ℕ) {h : X → ℝ} (hh : ∀ x,0≤h x) (x : X) : 0≤ moveTerm θ j b h x :=
  mul_nonneg (partition_nonneg θ j b x) (hh x)
lemma movedDrop_nonneg (θ : X) (j : ℕ) {h : X → ℝ} (hh : ∀ x,0≤h x) (x : X) : 0≤ movedDrop θ j h x :=
  Finset.sum_nonneg (fun _ _ => moveTerm_nonneg _ _ _ hh _)
lemma movedDrop_zero_off (θ : X) (j : ℕ) (h : X → ℝ) (x : X) (hx : supportRadius θ j ≤ dist x 0) : movedDrop θ j h x=0 := by
  apply Finset.sum_eq_zero
  intro b _
  simp only [moveTerm,partition,sub_add_cancel,bump_eq_zero θ j x hx,zero_div,zero_mul]
lemma movedDrop_zero_lower (θ : X) (j : ℕ) {h : X → ℝ} (hh : ∀ x,0≤h x) : h 0/((j:ℝ)+1)≤ movedDrop θ j h 0 := by
  calc
    h 0/((j:ℝ)+1) = (1/((j:ℝ)+1))*h 0 := by ring
    _ ≤ partition θ j 0 0*h 0 := mul_le_mul_of_nonneg_right (partition_zero_lower θ j) (hh 0)
    _ = moveTerm θ j 0 h (0-0 • θ) := by simp [moveTerm]
    _ ≤ movedDrop θ j h 0 := Finset.single_le_sum (f := fun b => moveTerm θ j b h (0-b • θ)) (fun _ _ => moveTerm_nonneg θ j _ hh _) (by simp : 0∈Finset.range (j+1))
lemma moveTerm_sum (θ : X) (j : ℕ) (h : X → ℝ) (x : X) : ∑ b∈Finset.range (j+1),moveTerm θ j b h x=h x := by
  simp only [moveTerm,←Finset.sum_mul,partition_sum,one_mul]
lemma moveCorrection_coboundary (θ : X) (j : ℕ) (h : X → ℝ) (x : X) :
    movedDrop θ j h x-h x=moveCorrection θ j h (x+θ)-moveCorrection θ j h x := by
  have he (r : ℕ) : x+θ-(r+1) • θ=x-r • θ := by rw [add_nsmul,one_nsmul]; abel
  have ht (b : ℕ) :
      (∑ r∈Finset.range b,moveTerm θ j b h (x-r • θ))-
      (∑ r∈Finset.range b,moveTerm θ j b h (x-(r+1) • θ))=moveTerm θ j b h x-moveTerm θ j b h (x-b • θ) := by
    rw [←Finset.sum_sub_distrib]
    simpa using Finset.sum_range_sub' (fun r => moveTerm θ j b h (x-r • θ)) b
  unfold movedDrop moveCorrection
  simp_rw [he]
  rw [←moveTerm_sum θ j h x,←Finset.sum_sub_distrib]
  calc
    _ = ∑ b∈Finset.range (j+1),-((∑ r∈Finset.range b,moveTerm θ j b h (x-r • θ))-(∑ r∈Finset.range b,moveTerm θ j b h (x-(r+1) • θ))) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [ht]
      ring
    _ = _ := by rw [Finset.sum_neg_distrib,Finset.sum_sub_distrib]; ring
lemma measurePreserving_sub (a : X) : MeasurePreserving (fun x : X => x-a) volume volume := by
  simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure X) (-a)
lemma integral_sub_circle (a : X) (f : X → ℝ) : (∫ x : X, f (x-a))=∫ x : X,f x := by
  have he : MeasurableEmbedding (fun x : X => x-a) := by
    convert (Homeomorph.addRight (-a)).isClosedEmbedding.measurableEmbedding using 1
    ext x; simp [sub_eq_add_neg]
  exact (measurePreserving_sub a).integral_comp he f
lemma moveTerm_integrable (θ : X) (j b : ℕ) {h : X → ℝ} (hc : Continuous h) :
    Integrable (moveTerm θ j b h) (volume : Measure X) :=
  (moveTerm_continuous θ j b hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma movedTerm_integrable (θ : X) (j b : ℕ) {h : X → ℝ} (hc : Continuous h) :
    Integrable (fun x : X => moveTerm θ j b h (x-b • θ)) volume :=
  ((moveTerm_continuous θ j b hc).comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma movedDrop_integral (θ : X) (j : ℕ) {h : X → ℝ} (hc : Continuous h) :
    (∫ x : X,movedDrop θ j h x)=∫ x : X,h x := by
  change (∫ x : X, ∑ b ∈ Finset.range (j+1), moveTerm θ j b h (x-b • θ))= _
  rw [integral_finsetSum _ (fun b _ => movedTerm_integrable θ j b hc)]
  calc
    _ = ∑ b ∈ Finset.range (j+1), ∫ x : X, moveTerm θ j b h x :=
      Finset.sum_congr rfl (fun b _ => integral_sub_circle (b • θ) (moveTerm θ j b h))
    _ = ∫ x : X, ∑ b ∈ Finset.range (j+1), moveTerm θ j b h x :=
      (integral_finsetSum _ (fun b _ => moveTerm_integrable θ j b hc)).symm
    _ = ∫ x : X, h x := integral_congr_ae (Eventually.of_forall (moveTerm_sum θ j h))
lemma moveCorrection_support (θ : X) (j : ℕ) (h : X → ℝ) :
    {x | moveCorrection θ j h x≠0} ⊆ ⋃ r∈Finset.range j,{x : X | h (x-(r+1) • θ)≠0} := by
  intro x hx
  by_contra hh
  have hh' : ∀ r<j,h (x-(r+1) • θ)=0 := by simpa only [mem_iUnion,Finset.mem_range,mem_ofPred_eq,not_exists,not_and,not_not] using hh
  apply hx
  unfold moveCorrection
  rw [neg_eq_zero,Finset.sum_eq_zero]
  intro b hb
  apply Finset.sum_eq_zero
  intro r hr
  have hrj : r<j := by simp only [Finset.mem_range] at hr hb; omega
  simp [moveTerm,hh' r hrj]
lemma moveCorrection_measure (θ : X) (j : ℕ) {h : X → ℝ} (hm : Measurable h) :
    volume {x : X | moveCorrection θ j h x≠0} ≤ (j:ℝ≥0∞)*volume {x : X | h x≠0} := by
  apply (measure_mono (moveCorrection_support θ j h)).trans
  apply (measure_biUnion_finset_le _ _).trans
  have hs (r : ℕ) : volume {x : X | h (x-(r+1) • θ)≠0}=volume {x : X | h x≠0} := by
    have hσ : MeasurePreserving (fun x : X => x-(r+1) • θ) volume volume := by
      simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume:Measure X) (-((r+1) • θ))
    change volume ((fun x : X => x-(r+1) • θ) ⁻¹' {x : X | h x≠0}) = _
    exact hσ.measure_preimage (hm (measurableSet_singleton 0).compl).nullMeasurableSet
  simp only [hs,Finset.sum_const,Finset.card_range,nsmul_eq_mul,le_refl]


end CircleConcentration

end

end OAI
