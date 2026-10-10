import OAI.Probability.BenjaminiSchramm.LayerFrontierGeometry

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def newLayerCount (I J : Set E) (A : Set V) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, if y ∈ A ∧ ¬Conn G (ω ∩ I) x y ∧ Conn G (ω ∩ J) x y then 1 else 0

def frontierCount (I J : Set E) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' z, if z ∈ openFrontier G (ω ∩ J) (cluster G (ω ∩ I) x) then 1 else 0

lemma measurable_newLayerCount (I J : Set E) (A : Set V) (x : V) :
    Measurable (fun ω => newLayerCount G I J A ω x) := by
  have hm (Q : Set E) : Measurable (fun ω : Set E => ω ∩ Q) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact Measurable.tsum fun y => Measurable.ite
    (measurable_const.and (((measurableSet_conn G x y).mem.comp (hm I)).not.and
      ((measurableSet_conn G x y).mem.comp (hm J)))).setOf
    measurable_const measurable_const

lemma measurable_frontierCount (I J : Set E) (x : V) :
    Measurable (fun ω => frontierCount G I J ω x) := by
  have hm : Measurable (fun ω : Set E => ω ∩ I) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  have hc (y : V) : Measurable (fun ω => Conn G (ω ∩ I) x y) :=
    (measurableSet_conn G x y).mem.comp hm
  exact Measurable.tsum fun z => Measurable.ite
    ((hc z).not.and (Measurable.exists fun u => (hc u).and
      (Measurable.exists fun e => ((measurable_set_mem e).and measurable_const).and
        measurable_const))).setOf measurable_const measurable_const

omit [Countable V] [Countable E] in
lemma newLayerCount_eq_on_cell (I J : Set E) (x : V) (S F A : Set V)
    {ω : Set E} (hω : ω ∈ lowerFrontierCell G I J x S F) :
    newLayerCount G I J A ω x = restrictedLayerCount G J (A \ S) ω x := by
  apply tsum_congr
  intro y
  have he : Conn G (ω ∩ I) x y ↔ y ∈ S := by
    change y ∈ cluster G (ω ∩ I) x ↔ y ∈ S
    rw [hω.1]
  simp only [Set.mem_sdiff,he,and_assoc]

omit [Countable V] [Countable E] in
lemma frontierCount_eq_card_on_cell (I J : Set E) (x : V) (S : Set V)
    (F : Finset V) {ω : Set E}
    (hω : ω ∈ lowerFrontierCell G I J x S (F : Set V)) :
    frontierCount G I J ω x = F.card := by
  unfold frontierCount
  rw [hω.1,hω.2]
  simp only [Finset.mem_coe]
  rw [tsum_eq_sum (s := F) (fun z hz => ite_eq_right hz)]
  calc
    _ = ∑ _z ∈ F, (1 : ℝ≥0∞) := Finset.sum_congr rfl (fun _ hz => ite_eq_left hz)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_one]

theorem lintegral_lowerFrontier_partition
    (hloc : LocallyFinite G) (q : E → unitInterval) (I J : Set E) (x : V)
    (hfin : ∀ᵐ ω ∂CriticalPercolation.BernoulliProduct.law q,
      (cluster G (ω ∩ I) x).Finite)
    (g : Set E → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, g ω ∂CriticalPercolation.BernoulliProduct.law q) =
      ∑' B : Finset V × Finset V, ∫⁻ ω,
        (lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)).indicator g ω
          ∂CriticalPercolation.BernoulliProduct.law q := by
  have heq : g =ᵐ[CriticalPercolation.BernoulliProduct.law q]
      (fun ω => ∑' B : Finset V × Finset V,
        (lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)).indicator g ω) := by
    filter_upwards [hfin] with ω hω
    let S := hω.toFinset
    have hF := openFrontier_finite G hloc (ω ∩ J) hω
    let F := hF.toFinset
    have hS : (S : Set V) = cluster G (ω ∩ I) x := hω.coe_toFinset
    have hFF : (F : Set V) = openFrontier G (ω ∩ J) (cluster G (ω ∩ I) x) :=
      hF.coe_toFinset
    have hmem : ω ∈ lowerFrontierCell G I J x (S : Set V) (F : Set V) := by
      exact ⟨hS.symm,by rw [hS,hFF]⟩
    have huniq (B : Finset V × Finset V)
        (hB : ω ∈ lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)) : B = (S,F) := by
      have hs : B.1 = S := Finset.coe_injective (hB.1.symm.trans hS.symm)
      have hf : B.2 = F := Finset.coe_injective (by
        rw [←hB.2,←hB.1,hFF])
      exact Prod.ext hs hf
    rw [tsum_eq_single (S,F) (fun B hB => Set.indicator_of_notMem
      (fun hm => hB (huniq B hm)) g)]
    exact (Set.indicator_of_mem hmem g).symm
  rw [lintegral_congr_ae heq,lintegral_tsum]
  intro B
  exact (hg.indicator (measurableSet_lowerFrontierCell G I J x _ _)).aemeasurable

theorem newLayerCount_fractional_bound_on_frontier
    (hloc : LocallyFinite G) (q : E → unitInterval) (I J : Set E) (x : V)
    (hfin : ∀ᵐ ω ∂CriticalPercolation.BernoulliProduct.law q,
      (cluster G (ω ∩ I) x).Finite)
    (A : Set V) {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hb : 0 < b) (hb1 : b ≤ 1) (L : ℝ≥0∞)
    (Z : Set V) (hZ : ∀ ω, openFrontier G (ω ∩ J) (cluster G (ω ∩ I) x) ⊆ Z)
    (hL : ∀ z ∈ Z, (∫⁻ ω, restrictedLayerCount G J A ω z^a
      ∂CriticalPercolation.BernoulliProduct.law q) ≤ L) :
    (∫⁻ ω, newLayerCount G I J A ω x^(a*b)
      ∂CriticalPercolation.BernoulliProduct.law q) ≤
      (∫⁻ ω, frontierCount G I J ω x^b
        ∂CriticalPercolation.BernoulliProduct.law q)*L^b := by
  let μ := CriticalPercolation.BernoulliProduct.law q
  rw [lintegral_lowerFrontier_partition G hloc q I J x hfin _
    ((measurable_newLayerCount G I J A x).pow_const (a*b))]
  have hbound (B : Finset V × Finset V) :
      (∫⁻ ω, (lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)).indicator
        (fun ω => newLayerCount G I J A ω x^(a*b)) ω ∂μ) ≤
      μ (lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)) *
        (B.2.card : ℝ≥0∞)^b*L^b := by
    have he : (lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)).indicator
        (fun ω => newLayerCount G I J A ω x^(a*b)) =
        (lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)).indicator
          (fun ω => restrictedLayerCount G J (A \ (B.1 : Set V)) ω x^(a*b)) := by
      apply Set.indicator_congr
      intro ω hω
      exact congrArg (fun t : ℝ≥0∞ => t^(a*b))
        (newLayerCount_eq_on_cell G I J x _ _ A hω)
    rw [he]
    by_cases hcell : (lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)).Nonempty
    · obtain ⟨η,hη⟩ := hcell
      exact lowerFrontierCell_fractional_bound G q I J x _ _ A ha ha1 hb hb1 L
        (fun z hz => hL z (hZ η (by
          rw [hη.1,hη.2]
          exact hz)))
    · rw [Set.not_nonempty_iff_eq_empty.mp hcell]
      simp only [Set.indicator_empty,lintegral_zero,measure_empty,zero_mul,le_refl]
  apply (ENNReal.tsum_le_tsum hbound).trans_eq
  rw [ENNReal.tsum_mul_right]
  congr 1
  rw [lintegral_lowerFrontier_partition G hloc q I J x hfin _
    ((measurable_frontierCount G I J x).pow_const b)]
  apply tsum_congr
  intro B
  have he : (lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)).indicator
      (fun ω => frontierCount G I J ω x^b) =
      (lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)).indicator
        (fun _ => (B.2.card : ℝ≥0∞)^b) := by
    apply Set.indicator_congr
    intro ω hω
    exact congrArg (fun t : ℝ≥0∞ => t^b)
      (frontierCount_eq_card_on_cell G I J x _ _ hω)
  rw [he,lintegral_indicator_const (measurableSet_lowerFrontierCell G I J x _ _),mul_comm]

theorem newLayerCount_fractional_bound
    (hloc : LocallyFinite G) (q : E → unitInterval) (I J : Set E) (x : V)
    (hfin : ∀ᵐ ω ∂CriticalPercolation.BernoulliProduct.law q,
      (cluster G (ω ∩ I) x).Finite)
    (A : Set V) {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hb : 0 < b) (hb1 : b ≤ 1) (L : ℝ≥0∞)
    (hL : ∀ z, (∫⁻ ω, restrictedLayerCount G J A ω z^a
      ∂CriticalPercolation.BernoulliProduct.law q) ≤ L) :
    (∫⁻ ω, newLayerCount G I J A ω x^(a*b)
      ∂CriticalPercolation.BernoulliProduct.law q) ≤
      (∫⁻ ω, frontierCount G I J ω x^b
        ∂CriticalPercolation.BernoulliProduct.law q)*L^b :=
  newLayerCount_fractional_bound_on_frontier G hloc q I J x hfin A ha ha1 hb hb1 L
    Set.univ (fun _ _ _ => Set.mem_univ _) (fun z _ => hL z)

end Percolation.BenjaminiSchramm

end

end OAI
