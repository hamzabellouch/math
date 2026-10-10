import Mathlib
import OAI.Probability.UnimodularPercolation.TwoCluster.Transport

namespace OAI

/-! Quantitative two-cluster probability bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem localDensityLoss_integral_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (d : ℕ) (hd : ∀ y, {e | y ∈ G e}.ncard ≤ d) (n : ℕ) (hn : 0 < n)
    (p : unitInterval) (hp : 0 < (p:ℝ))
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite) (y : V) :
    (∫⁻ ω, localDensityLoss G n ω y ∂law p) ≤
      ENNReal.ofReal (10*c*Real.sqrt (d*n:ℕ)/(p:ℝ)) := by
  obtain ⟨i,a,ha,hai⟩ := hcov y
  obtain ⟨b,hab⟩ := hΓ ha
  have he : (∫⁻ ω, localDensityLoss G n ω (root i) ∂law p) =
      ∫⁻ ω, localDensityLoss G n ω y ∂law p := by
    have ht := lintegral_map (μ := law p) (measurable_localDensityLoss G hloc n (root i))
      (measurable_set_preimage b)
    rw [law_map_preimage_equiv] at ht
    rw [ht]
    apply lintegral_congr
    intro ω
    rw [localDensityLoss_aut G n hab,hai]
  have hwi : (1:ℝ≥0∞) ≤ ENNReal.ofReal c * ENNReal.ofReal (weight i) := by
    rw [←ENNReal.ofReal_mul hc]
    exact_mod_cast ENNReal.ofReal_le_ofReal (hmin i)
  have hsingle : ENNReal.ofReal (weight i) * (∫⁻ ω, localDensityLoss G n ω (root i) ∂law p) ≤
      ∑ j, ENNReal.ofReal (weight j) * ∫⁻ ω, localDensityLoss G n ω (root j) ∂law p :=
    Finset.single_le_sum (f := fun j => ENNReal.ofReal (weight j) *
      ∫⁻ ω, localDensityLoss G n ω (root j) ∂law p) (fun j _ => zero_le) (Finset.mem_univ i)
  calc
    _ = 1 * (∫⁻ ω, localDensityLoss G n ω (root i) ∂law p) := by rw [he,one_mul]
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal (weight i) *
      ∫⁻ ω, localDensityLoss G n ω (root i) ∂law p) := by
      rw [←mul_assoc]
      exact mul_le_mul_left hwi _
    _ ≤ ENNReal.ofReal c * (∑ j, ENNReal.ofReal (weight j) *
      ∫⁻ ω, localDensityLoss G n ω (root j) ∂law p) := mul_le_mul_right hsingle _
    _ ≤ ENNReal.ofReal c * (2 * ENNReal.ofReal (5*Real.sqrt (d*n:ℕ)/(p:ℝ))) :=
      mul_le_mul_right (weighted_localDensityLoss_bound G hconn hloc root weight Γ hΓ htr hw hw1
        d hd n hn p hp hfin) _
    _ = _ := by
      rw [←ENNReal.ofReal_ofNat 2,←ENNReal.ofReal_mul (by norm_num),←ENNReal.ofReal_mul hc]
      congr 1
      ring

 
theorem cluster_insert_left_eq_union (G : BondGraph V E) (ω : Set E)
    (e : E) (a b : V) (he : G e = s(a,b)) :
    cluster G (insert e ω) a = cluster G ω a ∪ cluster G ω b := by
  ext y
  change Conn G (insert e ω) a y ↔ Conn G ω a y ∨ Conn G ω b y
  rw [conn_insert_iff G ω e a b a y he]
  constructor
  · rintro (h | ⟨_,h⟩ | ⟨_,h⟩)
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨conn_refl G ω a,h⟩)

theorem endpoint_density_defect (G : BondGraph V E) (ω : Set E)
    (e : E) (a b : V) (he : G e = s(a,b)) (hab : ¬Conn G ω a b)
    (ha : (cluster G ω a).Finite) (hb : (cluster G ω b).Finite)
    (n : ℕ) (hna : n ≤ (cluster G ω a).ncard) (hnb : n ≤ (cluster G ω b).ncard) :
    ((cluster G ω a).ncard:ℝ)*densityInfluence G n a e ω +
      ((cluster G ω b).ncard:ℝ)*densityInfluence G n b e ω = n := by
  have hc : e ∉ ω := fun h => hab (.single ⟨e,h,he⟩)
  have hdis : Disjoint (cluster G ω a) (cluster G ω b) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact hab (conn_trans G ω hz (conn_symm G ω hz'))
  have hins : Conn G (insert e ω) a b := .single ⟨e,Set.mem_insert e ω,he⟩
  have hs : (cluster G (insert e ω) a).ncard = (cluster G ω a).ncard+(cluster G ω b).ncard := by
    rw [cluster_insert_left_eq_union G ω e a b he,Set.ncard_union_eq hdis ha hb]
  have hsa : 0 < ((cluster G ω a).ncard:ℝ) := by exact_mod_cast cluster_ncard_pos G ω a ha
  have hsb : 0 < ((cluster G ω b).ncard:ℝ) := by exact_mod_cast cluster_ncard_pos G ω b hb
  have hna' : (n:ℝ) ≤ (cluster G ω a).ncard := by exact_mod_cast hna
  have hnb' : (n:ℝ) ≤ (cluster G ω b).ncard := by exact_mod_cast hnb
  unfold densityInfluence clusterDensity cappedDensity
  rw [ite_eq_right hc,ite_eq_right hc,←cluster_eq_of_conn G (insert e ω) hins,hs,Nat.cast_add,
    min_eq_left hna',min_eq_left hnb',min_eq_left (by linarith : (n:ℝ) ≤
      (cluster G ω a).ncard+(cluster G ω b).ncard)]
  field_simp
  ring

theorem localDensityLoss_ge_edge (G : BondGraph V E) (n : ℕ) (ω : Set E)
    (e : E) (a : V) (ha : a ∈ G e) :
    ((cluster G ω a).ncard:ℝ≥0∞)*ENNReal.ofReal (densityInfluence G n a e ω) ≤
      localDensityLoss G n ω a := by
  apply mul_le_mul_right
  exact (le_of_eq (ite_eq_left ha).symm).trans
    (ENNReal.le_tsum (f := fun edge =>
      if a ∈ G edge then ENNReal.ofReal (densityInfluence G n a edge ω) else 0) e)

theorem two_large_endpoint_loss (G : BondGraph V E) (ω : Set E)
    (e : E) (a b : V) (he : G e = s(a,b)) (ha : (cluster G ω a).Finite)
    (hb : (cluster G ω b).Finite) (n : ℕ)
    (h : ¬Conn G ω a b ∧ ω ∈ clusterLarge G a n ∧ ω ∈ clusterLarge G b n) :
    (n:ℝ≥0∞) ≤ localDensityLoss G n ω a + localDensityLoss G n ω b := by
  have hsz (v : V) (hv : (cluster G ω v).Finite) (hh : ω ∈ clusterLarge G v n) :
      n ≤ (cluster G ω v).ncard := by
    obtain ⟨t,ht,hct⟩ := hh
    exact ht.trans (by rw [←Set.ncard_coe_finset]; exact Set.ncard_le_ncard hct hv)
  have hid := endpoint_density_defect G ω e a b he h.1 ha hb n (hsz a ha h.2.1) (hsz b hb h.2.2)
  have hid' := congrArg ENNReal.ofReal hid
  rw [ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) (densityInfluence_nonneg ..))
    (mul_nonneg (Nat.cast_nonneg _) (densityInfluence_nonneg ..)),
    ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hid'
  simp only [ENNReal.ofReal_natCast] at hid'
  rw [←hid']
  exact add_le_add (localDensityLoss_ge_edge G n ω e a (by rw [he]; simp))
    (localDensityLoss_ge_edge G n ω e b (by rw [he]; simp))

end Percolation

 

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

 

def twoLargeEvent (G : BondGraph V E) (a b : V) (n : ℕ) : Set (Set E) :=
  {ω | ¬Conn G ω a b ∧ ω ∈ clusterLarge G a n ∧ ω ∈ clusterLarge G b n}

theorem measurableSet_twoLargeEvent [Countable V] [Countable E] (G : BondGraph V E) (a b : V) (n : ℕ) :
    MeasurableSet (twoLargeEvent G a b n) :=
  (measurableSet_conn G a b).compl.inter
    ((measurableSet_clusterLarge G a n).inter (measurableSet_clusterLarge G b n))

theorem twoLarge_probability_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (d : ℕ) (hd : ∀ y, {e | y ∈ G e}.ncard ≤ d) (n : ℕ) (hn : 0 < n)
    (p : unitInterval) (hp : 0 < (p:ℝ))
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite)
    (e : E) (a b : V) (he : G e = s(a,b)) :
    (n:ℝ) * (law p).real (twoLargeEvent G a b n) ≤
      20*c*Real.sqrt (d*n:ℕ)/(p:ℝ) := by
  have hpoint : ∀ᵐ ω ∂law p,
      (twoLargeEvent G a b n).indicator (fun _ => (n:ℝ≥0∞)) ω ≤
        localDensityLoss G n ω a + localDensityLoss G n ω b := by
    filter_upwards [hfin a,hfin b] with ω ha hb
    by_cases h : ω ∈ twoLargeEvent G a b n
    · rw [Set.indicator_of_mem h]
      exact two_large_endpoint_loss G ω e a b he ha hb n h
    · rw [Set.indicator_of_notMem h]
      exact zero_le
  have hi := lintegral_mono_ae hpoint
  rw [lintegral_indicator (measurableSet_twoLargeEvent G a b n),lintegral_const,
    lintegral_add_left (measurable_localDensityLoss G hloc n a)] at hi
  have hbnd (y : V) := localDensityLoss_integral_bound G hconn hloc root weight Γ hΓ htr
    hcov hw hw1 c hc hmin d hd n hn p hp hfin y
  have hi' := hi.trans (add_le_add (hbnd a) (hbnd b))
  rw [←ENNReal.ofReal_add (by positivity : 0 ≤ 10*c*Real.sqrt (d*n:ℕ)/(p:ℝ))
    (by positivity : 0 ≤ 10*c*Real.sqrt (d*n:ℕ)/(p:ℝ))] at hi'
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hi'
  rw [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal (by positivity)] at ht
  simp only [Measure.restrict_apply_univ] at ht
  dsimp [Measure.real] at ht ⊢
  convert ht using 1
  ring

 

theorem finiteWitness_eventually_iff (A : Set (Set E)) (hu : IsUpperSet A)
    (hf : FiniteWitness A) (ω : ℕ → Set E) (hm : Monotone ω) :
    ∀ᶠ j in atTop, ω j ∈ A ↔ (⋃ k, ω k) ∈ A := by
  by_cases h : (⋃ k, ω k) ∈ A
  · obtain ⟨t,ht,htA⟩ := hf _ h
    have ht' : ∀ e ∈ t, ∃ k, e ∈ ω k := by
      intro e he
      exact Set.mem_iUnion.mp (ht he)
    choose k hk using fun e : t => ht' e e.property
    let N := t.attach.sup k
    have hN : (t : Set E) ⊆ ω N := by
      intro e he
      exact hm (Finset.le_sup (f := k) (Finset.mem_attach t ⟨e,he⟩)) (hk ⟨e,he⟩)
    filter_upwards [eventually_ge_atTop N] with j hj
    exact iff_of_true (hu (hN.trans (hm hj)) htA) h
  · exact Eventually.of_forall (fun j => iff_of_false
      (fun hj => h (hu (Set.subset_iUnion ω j) hj)) h)

theorem twoLarge_probability_tendsto [Countable V] [Countable E] (G : BondGraph V E)
    (p : ℕ → unitInterval) (hp : Monotone p) (q : unitInterval)
    (hle : ∀ j, p j ≤ q) (hlim : Tendsto p atTop (𝓝 q)) (a b : V) (n : ℕ) :
    Tendsto (fun j => (law (p j)).real (twoLargeEvent G a b n)) atTop
      (𝓝 ((law q).real (twoLargeEvent G a b n))) := by
  let A := twoLargeEvent G a b n
  let f := fun r labels => A.indicator (fun _ => (1:ℝ)) (openEdges labels r)
  have hfi (r : unitInterval) : Integrable (f r) labelLaw := by
    have hi : Integrable (A.indicator (fun _ => (1:ℝ))) (law r) :=
      (integrable_const _).indicator (measurableSet_twoLargeEvent G a b n)
    rw [←map_openEdges r] at hi
    exact hi.comp_measurable (measurable_openEdges r)
  have ht : ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)),
      Tendsto (fun j => f (p j) labels) atTop (𝓝 (f q labels)) := by
    filter_upwards [ae_labels_ne (E := E) q] with labels hlabels
    have hm : Monotone (fun j => openEdges labels (p j)) :=
      fun j k hjk => openEdges_mono labels (hp hjk)
    have he := openEdges_eq_iUnion_of_tendsto labels q hlabels p hle hlim
    have hC := finiteWitness_eventually_iff {ω | Conn G ω a b}
      (fun _ _ hω h => conn_mono G hω h) (finiteWitness_conn G a b) _ hm
    have ha := finiteWitness_eventually_iff (clusterLarge G a n)
      (clusterLarge_upper G a n) (finiteWitness_clusterLarge G a n) _ hm
    have hb := finiteWitness_eventually_iff (clusterLarge G b n)
      (clusterLarge_upper G b n) (finiteWitness_clusterLarge G b n) _ hm
    rw [←he] at hC ha hb
    apply tendsto_const_nhds.congr'
    filter_upwards [hC,ha,hb] with j hC ha hb
    have hi : openEdges labels (p j) ∈ A ↔ openEdges labels q ∈ A := by
      exact and_congr (not_congr hC) (and_congr ha hb)
    simp only [f,Set.indicator_apply]
    rw [hi]
  have ht' := tendsto_integral_of_dominated_convergence (fun _ : E → unitInterval => (1:ℝ))
    (fun j => (hfi (p j)).aestronglyMeasurable) (integrable_const _)
    (fun j => Eventually.of_forall (fun labels => by
      simp only [f,Set.indicator_apply]
      split <;> norm_num)) ht
  have heq (r : unitInterval) : (∫ labels, f r labels ∂labelLaw) = (law r).real A := by
    calc
      _ = ∫ ω, A.indicator (fun _ => (1:ℝ)) ω ∂law r := by
        rw [←map_openEdges r]
        exact (integral_map (measurable_openEdges r).aemeasurable
          ((measurable_const.indicator (measurableSet_twoLargeEvent G a b n)).aestronglyMeasurable)).symm
      _ = _ := by rw [integral_indicator_const _ (measurableSet_twoLargeEvent G a b n)]; simp [A]
  simpa only [heq] using ht'

end Percolation

end OAI
