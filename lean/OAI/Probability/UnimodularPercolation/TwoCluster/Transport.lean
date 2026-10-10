import Mathlib
import OAI.Probability.UnimodularPercolation.Clusters.LargeContacts
import OAI.Probability.UnimodularPercolation.TwoCluster.Score

namespace OAI

/-! Infinite-volume two-cluster limits and transport. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def clusterDensity (G : BondGraph V E) (n : ℕ) (x : V) (ω : Set E) : ℝ :=
  cappedDensity n (cluster G ω x).ncard

noncomputable def densityInfluence (G : BondGraph V E) (n : ℕ) (x : V)
    (e : E) (ω : Set E) : ℝ :=
  if e ∈ ω then 0 else clusterDensity G n x ω - clusterDensity G n x (insert e ω)

theorem clusterDensity_nonneg (G : BondGraph V E) (n : ℕ) (x : V) (ω : Set E) :
    0 ≤ clusterDensity G n x ω := cappedDensity_nonneg ..

theorem clusterDensity_le_one (G : BondGraph V E) (n : ℕ) (x : V) (ω : Set E) :
    clusterDensity G n x ω ≤ 1 := cappedDensity_le_one ..

theorem clusterDensity_antitone (G : BondGraph V E) (n : ℕ) (x : V)
    {ω η : Set E} (h : ω ⊆ η) : clusterDensity G n x η ≤ clusterDensity G n x ω := by
  by_cases hη : (cluster G η x).Finite
  · have hω : (cluster G ω x).Finite := hη.subset (fun y hy => conn_mono G h hy)
    exact cappedDensity_antitone n ((Set.ncard_pos hω).mpr ⟨x,mem_cluster_self G ω x⟩)
      (Set.ncard_le_ncard (fun y hy => conn_mono G h hy) hη)
  · rw [clusterDensity,Set.Infinite.ncard hη]
    simpa [cappedDensity] using clusterDensity_nonneg G n x ω

theorem densityInfluence_nonneg (G : BondGraph V E) (n : ℕ) (x : V) (e : E) (ω : Set E) :
    0 ≤ densityInfluence G n x e ω := by
  unfold densityInfluence
  split_ifs
  · exact le_rfl
  · exact sub_nonneg.mpr (clusterDensity_antitone G n x (Set.subset_insert e ω))

theorem densityInfluence_le_one (G : BondGraph V E) (n : ℕ) (x : V) (e : E) (ω : Set E) :
    densityInfluence G n x e ω ≤ 1 := by
  unfold densityInfluence
  split_ifs
  · norm_num
  · exact (sub_le_self _ (clusterDensity_nonneg ..)).trans (clusterDensity_le_one ..)

theorem measurable_clusterDensity (G : BondGraph V E) (hloc : LocallyFinite G) (n : ℕ) (x : V) :
    Measurable (clusterDensity G n x) :=
  (measurable_of_countable (cappedDensity n)).comp (measurable_cluster_ncard G hloc x)

theorem measurable_densityInfluence (G : BondGraph V E) (hloc : LocallyFinite G)
    (n : ℕ) (x : V) (e : E) : Measurable (densityInfluence G n x e) := by
  exact measurable_const.ite (measurableSet_mem e)
    ((measurable_clusterDensity G hloc n x).sub
      ((measurable_clusterDensity G hloc n x).comp (measurable_set_insert e)))

theorem integrable_densityInfluence (G : BondGraph V E) (hloc : LocallyFinite G)
    (n : ℕ) (x : V) (e : E) (p : unitInterval) :
    Integrable (densityInfluence G n x e) (law p) := by
  apply Integrable.mono' (integrable_const (1:ℝ)) (measurable_densityInfluence G hloc n x e).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (densityInfluence_nonneg ..)]
    exact densityInfluence_le_one ..

theorem cluster_insert_finite (G : BondGraph V E) (ω : Set E) (e : E) (x a b : V)
    (he : G e = s(a,b)) (hx : (cluster G ω x).Finite)
    (ha : (cluster G ω a).Finite) (hb : (cluster G ω b).Finite) :
    (cluster G (insert e ω) x).Finite := by
  apply (hx.union (ha.union hb)).subset
  intro y hy
  rcases (conn_insert_iff G ω e a b x y he).mp hy with hy | ⟨_,hy⟩ | ⟨_,hy⟩
  · exact Or.inl hy
  · exact Or.inr (Or.inr hy)
  · exact Or.inr (Or.inl hy)

theorem cluster_insert_finite_ae (G : BondGraph V E) (p : unitInterval)
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite) (x : V) (e : E) :
    ∀ᵐ ω ∂law p, (cluster G (insert e ω) x).Finite := by
  obtain ⟨a,b,he⟩ : ∃ a b, G e = s(a,b) := by
    obtain ⟨⟨a,b⟩,h⟩ := Quot.exists_rep (G e)
    exact ⟨a,b,h.symm⟩
  filter_upwards [hfin x,hfin a,hfin b] with ω hx ha hb
  exact cluster_insert_finite G ω e x a b he hx ha hb

theorem finiteDensity_eq_clusterDensity (G : BondGraph V E) (hloc : LocallyFinite G)
    (n : ℕ) (x : V) (ω : Set E) (hx : (cluster G ω x).Finite)
    (Q : Finset E) (hQ : incidentSupport G hloc hx.toFinset ⊆ Q) :
    finiteDensity G n x (domainBits Q ω) = clusterDensity G n x ω := by
  have hc : cluster G (domainBits Q ω:Set E) x = cluster G ω x := by
    rw [coe_domainBits]
    have hh := (cluster_restrict_incident_eq_iff G hloc hx.toFinset Q hQ ω x).mpr
      (Set.Finite.coe_toFinset hx).symm
    simpa only [Set.Finite.coe_toFinset] using hh
  unfold finiteDensity clusterDensity
  rw [←Set.ncard_coe_finset,coe_finiteRootComponent,hc]

theorem domainBits_insert (Q : Finset E) (e : E) (he : e ∈ Q) (ω : Set E) :
    domainBits Q (insert e ω) = insert e (domainBits Q ω) := by
  ext f
  simp only [mem_domainBits,Set.mem_insert_iff,Finset.mem_insert]
  aesop

theorem densityInfluence_tendsto_finite [Encodable E] (G : BondGraph V E) (hloc : LocallyFinite G)
    (n : ℕ) (x : V) (e : E) (ω : Set E) (hx : (cluster G ω x).Finite)
    (he : (cluster G (insert e ω) x).Finite) (F : Finset E) :
    Tendsto (fun j => finiteDensityInfluence G n x e
      (domainBits (F ∪ vertexExhaustion (V := E) j) ω)) atTop
      (nhds (densityInfluence G n x e ω)) := by
  obtain ⟨jx,hjx⟩ := subset_vertexExhaustion (incidentSupport G hloc hx.toFinset)
  obtain ⟨je,hje⟩ := subset_vertexExhaustion (incidentSupport G hloc he.toFinset)
  obtain ⟨j₀,hj₀'⟩ := subset_vertexExhaustion ({e}:Finset E)
  have hj₀ : e ∈ vertexExhaustion (V := E) j₀ := hj₀' (by simp)
  have hev : (fun j => finiteDensityInfluence G n x e
      (domainBits (F ∪ vertexExhaustion (V := E) j) ω)) =ᶠ[atTop]
      (fun _ => densityInfluence G n x e ω) := by
    filter_upwards [eventually_ge_atTop (max jx (max je j₀))] with j hj
    let Q := F ∪ vertexExhaustion (V := E) j
    have hxQ : incidentSupport G hloc hx.toFinset ⊆ Q := fun z hz =>
      Finset.mem_union_right _ (vertexExhaustion_mono (by omega) (hjx hz))
    have heQ : incidentSupport G hloc he.toFinset ⊆ Q := fun z hz =>
      Finset.mem_union_right _ (vertexExhaustion_mono (by omega) (hje hz))
    have heQ' : e ∈ Q := Finset.mem_union_right _ (vertexExhaustion_mono (by omega) hj₀)
    change finiteDensityInfluence G n x e (domainBits Q ω) = _
    unfold finiteDensityInfluence densityInfluence
    simp only [mem_domainBits,heQ',true_and]
    split_ifs
    · rfl
    · rw [finiteDensity_eq_clusterDensity G hloc n x ω hx Q hxQ,
        ←domainBits_insert Q e heQ' ω,finiteDensity_eq_clusterDensity G hloc n x (insert e ω) he Q heQ]
  exact tendsto_const_nhds.congr' hev.symm

theorem densityInfluence_integral_tendsto [Encodable E] (G : BondGraph V E)
    (hloc : LocallyFinite G) (n : ℕ) (x : V) (e : E) (p : unitInterval)
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite) (F : Finset E) :
    Tendsto (fun j => bernoulliPolynomial (F ∪ vertexExhaustion (V := E) j)
      (finiteDensityInfluence G n x e) p) atTop
      (nhds (∫ ω, densityInfluence G n x e ω ∂law p)) := by
  let Q := fun j => F ∪ vertexExhaustion (V := E) j
  let f := fun j ω => finiteDensityInfluence G n x e (domainBits (Q j) ω)
  have hfi (j : ℕ) : Integrable (f j) (law p) :=
    integrable_finite_local (Q j) p (f j) (fun ω => by dsimp [f]; rw [domainBits_local])
  have ht : ∀ᵐ ω ∂law p, Tendsto (fun j => f j ω) atTop (nhds (densityInfluence G n x e ω)) := by
    filter_upwards [hfin x,cluster_insert_finite_ae G p hfin x e] with ω hx he
    exact densityInfluence_tendsto_finite G hloc n x e ω hx he F
  have hd := tendsto_integral_of_dominated_convergence (fun _ : Set E => (1:ℝ))
    (fun j => (hfi j).aestronglyMeasurable) (integrable_const _)
    (fun j => Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (finiteDensityInfluence_nonneg ..)]
      exact finiteDensityInfluence_le_one ..)) ht
  simpa only [f,integral_domainBits,Q] using hd

 
theorem densityInfluence_finite_sum_bound [Countable E] (G : BondGraph V E)
    (hloc : LocallyFinite G) (d : ℕ) (hd : ∀ y, {e | y ∈ G e}.ncard ≤ d)
    (n : ℕ) (hn : 0 < n) (x : V) (p : unitInterval)
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite) (F : Finset E) :
    (p:ℝ) * ∑ e ∈ F, (∫ ω, densityInfluence G n x e ω ∂law p) ≤
      5*Real.sqrt (d*n:ℕ) := by
  let : Encodable E := Encodable.ofCountable E
  let Q := fun j => F ∪ vertexExhaustion (V := E) j
  have ht := (tendsto_const_nhds (x := (p:ℝ)) (f := atTop)).mul (tendsto_finsetSum F
    (fun e _ => densityInfluence_integral_tendsto G hloc n x e p hfin F))
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro j
  have hdeg (y : V) : ((Q j).filter fun e => y ∈ G e).card ≤ d := by
    calc
      _ = (((Q j).filter fun e => y ∈ G e):Set E).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ {e | y ∈ G e}.ncard := Set.ncard_le_ncard (fun e he => (Finset.mem_filter.mp he).2) (hloc y)
      _ ≤ d := hd y
  have hs : (∑ e ∈ F, bernoulliPolynomial (Q j) (finiteDensityInfluence G n x e) p) ≤
      ∑ e ∈ Q j, bernoulliPolynomial (Q j) (finiteDensityInfluence G n x e) p := by
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      (fun e _ _ => bernoulliPolynomial_nonneg (Q j) _ p p.2 (fun ω _ => finiteDensityInfluence_nonneg ..))
  exact (mul_le_mul_of_nonneg_left hs p.2.1).trans
    (finiteDensityInfluence_sum_bound G (Q j) x p d n hn hdeg)

 
theorem densityInfluence_lintegral_sum_bound [Countable E] (G : BondGraph V E)
    (hloc : LocallyFinite G) (d : ℕ) (hd : ∀ y, {e | y ∈ G e}.ncard ≤ d)
    (n : ℕ) (hn : 0 < n) (x : V) (p : unitInterval) (hp : 0 < (p:ℝ))
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite) :
    (∑' e, ∫⁻ ω, ENNReal.ofReal (densityInfluence G n x e ω) ∂law p) ≤
      ENNReal.ofReal (5*Real.sqrt (d*n:ℕ)/(p:ℝ)) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro F
  simp_rw [←ofReal_integral_eq_lintegral_ofReal (integrable_densityInfluence G hloc n x _ p)
    (Eventually.of_forall (densityInfluence_nonneg G n x _))]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun e _ => integral_nonneg (densityInfluence_nonneg G n x e))]
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ hp).mpr
  simpa only [mul_comm] using densityInfluence_finite_sum_bound G hloc d hd n hn x p hfin F

end Percolation

 

 

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def boundaryDensityInfluence (G : BondGraph V E) (n : ℕ)
    (ω : Set E) (y : V) : ℝ≥0∞ :=
  ∑' e, if y ∈ G e then ENNReal.ofReal (densityInfluence G n y e ω) else 0

noncomputable def localDensityLoss (G : BondGraph V E) (n : ℕ)
    (ω : Set E) (y : V) : ℝ≥0∞ :=
  (cluster G ω y).ncard * boundaryDensityInfluence G n ω y

theorem measurable_boundaryDensityInfluence [Countable E] (G : BondGraph V E)
    (hloc : LocallyFinite G) (n : ℕ) (y : V) :
    Measurable (fun ω => boundaryDensityInfluence G n ω y) := by
  apply Measurable.tsum
  intro e
  by_cases h : y ∈ G e
  · simpa only [ite_eq_left h] using (measurable_densityInfluence G hloc n y e).ennreal_ofReal
  · simp only [ite_eq_right h]; exact measurable_const

theorem measurable_localDensityLoss [Countable E] (G : BondGraph V E)
    (hloc : LocallyFinite G) (n : ℕ) (y : V) :
    Measurable (fun ω => localDensityLoss G n ω y) := by
  exact ((measurable_of_countable (fun k : ℕ => (k:ℝ≥0∞))).comp
    (measurable_cluster_ncard G hloc y)).mul (measurable_boundaryDensityInfluence G hloc n y)

theorem densityInfluence_eq_of_conn (G : BondGraph V E) (n : ℕ) (ω : Set E)
    (x y : V) (hxy : Conn G ω x y) (e : E) :
    densityInfluence G n x e ω = densityInfluence G n y e ω := by
  unfold densityInfluence clusterDensity
  rw [cluster_eq_of_conn G ω hxy,
    cluster_eq_of_conn G (insert e ω) (conn_mono G (Set.subset_insert e ω) hxy)]

theorem densityInfluence_aut (G : BondGraph V E) (n : ℕ) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) (e : E) :
    densityInfluence G n x e (b ⁻¹' ω) = densityInfluence G n (a x) (b e) ω := by
  have hins : insert e (b ⁻¹' ω) = b ⁻¹' (insert (b e) ω) := by
    ext f
    simp only [Set.mem_insert_iff,Set.mem_preimage,b.injective.eq_iff]
  simp only [densityInfluence,Set.mem_preimage,clusterDensity,hins,
    cluster_ncard_covariant G hab]

theorem localDensityLoss_aut (G : BondGraph V E) (n : ℕ) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) :
    localDensityLoss G n (b ⁻¹' ω) x = localDensityLoss G n ω (a x) := by
  unfold localDensityLoss boundaryDensityInfluence
  rw [cluster_ncard_covariant G hab,←b.tsum_eq (fun e =>
    if a x ∈ G e then ENNReal.ofReal (densityInfluence G n (a x) e ω) else 0)]
  congr 1
  apply tsum_congr
  intro e
  have hm : a x ∈ G (b e) ↔ x ∈ G e := by
    rw [hab e,Sym2.mem_map]
    constructor
    · rintro ⟨z,hz,hzx⟩
      exact a.injective hzx ▸ hz
    · intro h; exact ⟨x,h,rfl⟩
  simp only [hm,densityInfluence_aut G n hab]

 
theorem tsum_bond_endpoints_le_two (G : BondGraph V E) (e : E) (c : ℝ≥0∞) :
    (∑' y, if y ∈ G e then c else 0) ≤ 2*c := by
  obtain ⟨a,b,he⟩ : ∃ a b, G e = s(a,b) := by
    obtain ⟨⟨a,b⟩,h⟩ := Quot.exists_rep (G e)
    exact ⟨a,b,h.symm⟩
  calc
    _ ≤ ∑' y, ((if y = a then c else 0)+(if y = b then c else 0)) := by
      apply ENNReal.tsum_le_tsum
      intro y
      by_cases h : y ∈ G e
      · rw [ite_eq_left h]
        rw [he,Sym2.mem_iff] at h
        rcases h with rfl | rfl <;> simp
      · rw [ite_eq_right h]; exact zero_le
    _ = 2*c := by rw [ENNReal.tsum_add]; simp; ring

 

theorem clusterAveraged_localDensityLoss_le (G : BondGraph V E) (n : ℕ)
    (ω : Set E) (x : V) (hx : (cluster G ω x).Finite) :
    (∑' y, clusterAveragingKernel G ω x y * localDensityLoss G n ω y) ≤
      2 * ∑' e, ENNReal.ofReal (densityInfluence G n x e ω) := by
  have hf (y : V) : clusterAveragingKernel G ω x y * localDensityLoss G n ω y ≤
      ∑' e, if y ∈ G e then ENNReal.ofReal (densityInfluence G n x e ω) else 0 := by
    by_cases hxy : Conn G ω x y
    · have hc := cluster_eq_of_conn G ω hxy
      have hpos : ((cluster G ω x).ncard:ℝ≥0∞) ≠ 0 := by
        exact_mod_cast (cluster_ncard_pos G ω x hx).ne'
      unfold clusterAveragingKernel localDensityLoss
      rw [ite_eq_left hxy,←hc,←mul_assoc,ENNReal.inv_mul_cancel hpos (ENNReal.natCast_ne_top _),one_mul]
      unfold boundaryDensityInfluence
      simp_rw [densityInfluence_eq_of_conn G n ω x y hxy]
      exact le_rfl
    · simp only [clusterAveragingKernel,ite_eq_right hxy,zero_mul]; exact zero_le
  calc
    _ ≤ ∑' y, ∑' e, if y ∈ G e then ENNReal.ofReal (densityInfluence G n x e ω) else 0 :=
      ENNReal.tsum_le_tsum hf
    _ = ∑' e, ∑' y, if y ∈ G e then ENNReal.ofReal (densityInfluence G n x e ω) else 0 :=
      ENNReal.tsum_comm
    _ ≤ ∑' e, 2*ENNReal.ofReal (densityInfluence G n x e ω) :=
      ENNReal.tsum_le_tsum (fun e => tsum_bond_endpoints_le_two G e _)
    _ = _ := ENNReal.tsum_mul_left

theorem clusterAveraged_localDensityLoss_integral_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (d : ℕ)
    (hd : ∀ y, {e | y ∈ G e}.ncard ≤ d) (n : ℕ) (hn : 0 < n)
    (p : unitInterval) (hp : 0 < (p:ℝ))
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite) (x : V) :
    (∫⁻ ω, ∑' y, clusterAveragingKernel G ω x y * localDensityLoss G n ω y ∂law p) ≤
      2 * ENNReal.ofReal (5*Real.sqrt (d*n:ℕ)/(p:ℝ)) := by
  calc
    _ ≤ ∫⁻ ω, 2 * ∑' e, ENNReal.ofReal (densityInfluence G n x e ω) ∂law p := by
      apply lintegral_mono_ae
      filter_upwards [hfin x] with ω hω
      exact clusterAveraged_localDensityLoss_le G n ω x hω
    _ = 2 * ∑' e, ∫⁻ ω, ENNReal.ofReal (densityInfluence G n x e ω) ∂law p := by
      rw [lintegral_const_mul _ (Measurable.tsum (fun e =>
        (measurable_densityInfluence G hloc n x e).ennreal_ofReal)),lintegral_tsum]
      exact fun e => (measurable_densityInfluence G hloc n x e).ennreal_ofReal.aemeasurable
    _ ≤ _ := mul_le_mul_right (densityInfluence_lintegral_sum_bound G hloc d hd n hn x p hp hfin) 2

 
theorem weighted_localDensityLoss_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (d : ℕ) (hd : ∀ y, {e | y ∈ G e}.ncard ≤ d) (n : ℕ) (hn : 0 < n)
    (p : unitInterval) (hp : 0 < (p:ℝ))
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite) :
    (∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, localDensityLoss G n ω (root i) ∂law p) ≤
      2 * ENNReal.ofReal (5*Real.sqrt (d*n:ℕ)/(p:ℝ)) := by
  rw [←root_cluster_average G hconn hloc root weight Γ hΓ htr hw p hfin
    (localDensityLoss G n) (measurable_localDensityLoss G hloc n)
    (fun a ha b hab ω x => localDensityLoss_aut G n hab ω x)]
  calc
    _ ≤ ∑ i, ENNReal.ofReal (weight i) * (2 * ENNReal.ofReal (5*Real.sqrt (d*n:ℕ)/(p:ℝ))) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_right
        (clusterAveraged_localDensityLoss_integral_bound G hloc d hd n hn p hp hfin (root i)) _
    _ = _ := by
      rw [←Finset.sum_mul,←ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i),hw1]
      simp

end Percolation

end OAI
