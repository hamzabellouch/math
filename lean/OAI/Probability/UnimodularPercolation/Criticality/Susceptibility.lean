import Mathlib
import OAI.Probability.UnimodularPercolation.Kernel.DistinctMoments

namespace OAI

/-! Susceptibility for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SusceptibilityPivotalGain
attribute [local instance] Classical.propDecidable Classical.decEq

theorem sprinkleParameter_ge_left (p a : unitInterval) : p ≤ sprinkleParameter p a := by
  change (p:ℝ) ≤ (p:ℝ)+(1-(p:ℝ))*(a:ℝ)
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr p.2.2) a.2.1)

 

theorem susceptibility_sprinkling_gain [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p a : unitInterval) (hq : sprinkleParameter p a < pc G) (x : V)
    (Q : Finset E) (F : Finset V) :
    (a:ℝ)*(1-(a:ℝ))^(Q.card-1) *
      (∑ y ∈ F, ∑ e ∈ Q, (law p).real (closedPivotal {ω | Conn G ω x y} e)) ≤
      susceptibility G (sprinkleParameter p a) x - susceptibility G p x := by
  have hpa := sprinkleParameter_ge_left p a
  have hp : p < pc G := lt_of_le_of_lt hpa hq
  have hsum := (summable_twoPoint_subcritical G hloc hqt (sprinkleParameter p a) hq x).sub
    (summable_twoPoint_subcritical G hloc hqt p hp x)
  calc
    _ = ∑ y ∈ F, (a:ℝ)*(1-(a:ℝ))^(Q.card-1)*
      (∑ e ∈ Q, (law p).real (closedPivotal {ω | Conn G ω x y} e)) := Finset.mul_sum _ _ _
    _ ≤ ∑ y ∈ F, (twoPoint G (sprinkleParameter p a) x y - twoPoint G p x y) := by
      apply Finset.sum_le_sum
      intro y _
      exact event_sprinkling_gain p a Q {ω | Conn G ω x y} (measurableSet_conn G x y)
        (fun _ _ h hc => conn_mono G h hc)
    _ ≤ ∑' y, (twoPoint G (sprinkleParameter p a) x y - twoPoint G p x y) :=
      hsum.sum_le_tsum F (fun y _ => sub_nonneg.mpr (twoPoint_mono G x y hpa))
    _ = _ := (summable_twoPoint_subcritical G hloc hqt (sprinkleParameter p a) hq x).tsum_sub
      (summable_twoPoint_subcritical G hloc hqt p hp x)

 
theorem rootSusceptibility_sprinkling_gain [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (p a : unitInterval) (hq : sprinkleParameter p a < pc G)
    (Q : Finset E) (F : Finset V) :
    (a:ℝ)*(1-(a:ℝ))^(Q.card-1) *
      (∑ i, weight i*(∑ y ∈ F, ∑ e ∈ Q, (law p).real (closedPivotal {ω | Conn G ω (root i) y} e))) ≤
      rootSusceptibility G root weight (sprinkleParameter p a) - rootSusceptibility G root weight p := by
  rw [rootSusceptibility,rootSusceptibility,←Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left
    (susceptibility_sprinkling_gain G hloc hqt p a hq (root i) Q F) (hw i)
  convert h using 1 <;> ring

end SusceptibilityPivotalGain
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section OrientedPivotalConnections
attribute [local instance] Classical.propDecidable Classical.decEq

 

def orientedPivotalEvent (G : BondGraph V E) (x y a b : V) : Set (Set E) :=
  {ω | Conn G ω x a ∧ Conn G ω b y ∧ ¬ Conn G ω a b}

theorem measurableSet_orientedPivotalEvent [Countable V] [Countable E]
    (G : BondGraph V E) (x y a b : V) : MeasurableSet (orientedPivotalEvent G x y a b) :=
  (measurableSet_conn G x a).inter ((measurableSet_conn G b y).inter (measurableSet_conn G a b).compl)

theorem orientedPivotalEvent_disjoint (G : BondGraph V E) (x y a b : V) :
    Disjoint (orientedPivotalEvent G x y a b) (orientedPivotalEvent G x y b a) := by
  apply Set.disjoint_left.mpr
  intro ω h h'
  exact h.2.2 ((conn_symm G ω h.1).trans h'.1)

theorem closedPivotal_conn (G : BondGraph V E) (e : E) (a b x y : V)
    (he : G e = s(a,b)) :
    closedPivotal {ω | Conn G ω x y} e =
      orientedPivotalEvent G x y a b ∪ orientedPivotalEvent G x y b a := by
  ext ω
  constructor
  · rintro ⟨_,hn,hc⟩
    rcases (conn_insert_iff G ω e a b x y he).mp hc with h | h | h
    · exact (hn h).elim
    · exact Or.inl ⟨h.1,h.2,fun hab => hn (h.1.trans (hab.trans h.2))⟩
    · exact Or.inr ⟨h.1,h.2,fun hba => hn (h.1.trans (hba.trans h.2))⟩
  · intro h
    have hi : ∀ a b : V, G e = s(a,b) → ω ∈ orientedPivotalEvent G x y a b →
        ω ∈ closedPivotal {ω | Conn G ω x y} e := by
      intro a b he h
      refine ⟨?_,?_,?_⟩
      · intro heω
        exact h.2.2 (.single ⟨e,heω,he⟩)
      · intro hxy
        exact h.2.2 ((conn_symm G ω h.1).trans (hxy.trans (conn_symm G ω h.2.1)))
      · exact (conn_insert_iff G ω e a b x y he).mpr (Or.inr (Or.inl ⟨h.1,h.2.1⟩))
    exact h.elim (hi a b he) (hi b a (he.trans (Sym2.eq_swap ..)))

theorem closedPivotal_conn_probability [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (e : E) (a b x y : V) (he : G e = s(a,b)) :
    (law p).real (closedPivotal {ω | Conn G ω x y} e) =
      (law p).real (orientedPivotalEvent G x y a b) +
      (law p).real (orientedPivotalEvent G x y b a) := by
  rw [closedPivotal_conn G e a b x y he]
  exact measureReal_union (orientedPivotalEvent_disjoint G x y a b)
    (measurableSet_orientedPivotalEvent G x y b a)

 
theorem orientedPivotalEvent_subset_disjoint (G : BondGraph V E) (x y a b : V) :
    orientedPivotalEvent G x y a b ⊆
      DisjointOccurrence {ω | Conn G ω x a} {ω | Conn G ω b y} := by
  intro ω hω
  have hx : x ∈ cluster G ω a := conn_symm G ω hω.1
  have hb : b ∉ cluster G ω a := hω.2.2
  obtain ⟨Q,hQ,hQa⟩ := finiteWitness_conn G x a _ (conn_restrict_cluster G ω a hx hω.1)
  obtain ⟨R,hR,hRb⟩ := finiteWitness_conn G b y _ (conn_restrict_cluster_compl G ω a hb hω.2.1)
  refine ⟨Q,R,fun e he => (hQ he).1,fun e he => (hR he).1,?_,hQa,hRb⟩
  apply Finset.disjoint_left.mpr
  intro e heQ heR
  obtain ⟨⟨z,w⟩,he⟩ := Quot.exists_rep (G e)
  have hz : z ∈ G e := by rw [←he]; exact Sym2.mem_mk_left z w
  exact (hR heR).2 z hz ((hQ heQ).2 z hz)

end OrientedPivotalConnections
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section PivotalMomentIdentity
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem distinctClusterMass_eq_pivotal (G : BondGraph V E) (ω : Set E) (a b : V) :
    (if ¬Conn G ω a b then clusterMass G ω a * clusterMass G ω b else 0) =
      ∑' x, ∑' y, if ω ∈ orientedPivotalEvent G x y a b then (1:ℝ≥0∞) else 0 := by
  by_cases hab : Conn G ω a b
  · simp only [hab,not_true_eq_false,ite_false,orientedPivotalEvent,Set.mem_ofPred_eq,
       and_false,ite_false,tsum_zero]
  · rw [ite_eq_left hab,clusterMass_mul]
    apply tsum_congr
    intro x
    apply tsum_congr
    intro y
    apply if_congr _ rfl rfl
    simp only [orientedPivotalEvent,Set.mem_ofPred_eq,hab,not_false_eq_true,and_true]
    exact and_congr (show Conn G ω a x ↔ Conn G ω x a from ⟨conn_symm G ω,conn_symm G ω⟩) Iff.rfl

theorem lintegral_distinctClusterMass [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (a b : V) :
    (∫⁻ ω, (if ¬Conn G ω a b then clusterMass G ω a * clusterMass G ω b else 0) ∂law p) =
      ∑' x, ∑' y, law p (orientedPivotalEvent G x y a b) := by
  have hm (x y : V) : Measurable (fun ω : Set E =>
      if ω ∈ orientedPivotalEvent G x y a b then (1:ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_orientedPivotalEvent G x y a b) measurable_const measurable_const
  simp_rw [distinctClusterMass_eq_pivotal]
  rw [lintegral_tsum (fun x => (Measurable.tsum (fun y => hm x y)).aemeasurable)]
  apply tsum_congr
  intro x
  rw [lintegral_tsum (fun y => (hm x y).aemeasurable)]
  apply tsum_congr
  intro y
  simpa only [Set.indicator,Pi.one_apply] using
    (lintegral_indicator_one (μ := law p) (measurableSet_orientedPivotalEvent G x y a b))

theorem ennreal_distinctClusterMoment [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (a b : V) :
    ENNReal.ofReal (distinctClusterMoment G p a b) =
      ∑' x, ∑' y, law p (orientedPivotalEvent G x y a b) := by
  have hi := integrable_distinct_cluster_product G hloc hqt p hp a b
  have hn : 0 ≤ᵐ[law p] (fun ω => if ¬Conn G ω a b
      then ((cluster G ω a).ncard:ℝ)*((cluster G ω b).ncard:ℝ) else 0) := by
    exact Filter.Eventually.of_forall (fun ω => by dsimp only; split_ifs <;> positivity)
  have he : (fun ω => ENNReal.ofReal (if ¬Conn G ω a b
      then ((cluster G ω a).ncard:ℝ)*((cluster G ω b).ncard:ℝ) else 0)) =ᵐ[law p]
      (fun ω => if ¬Conn G ω a b then clusterMass G ω a * clusterMass G ω b else 0) := by
    filter_upwards [subcritical_cluster_finite_ae G p hp a,
      subcritical_cluster_finite_ae G p hp b] with ω ha hb
    by_cases hab : Conn G ω a b
    · simp only [hab,not_true_eq_false,ite_false,ENNReal.ofReal_zero]
    · simp only [hab,not_false_eq_true,ite_true]
      rw [clusterMass_eq_ncard G ω a ha,clusterMass_eq_ncard G ω b hb,
        ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      simp only [ENNReal.ofReal_natCast]
  rw [←lintegral_distinctClusterMass,←lintegral_congr_ae he]
  exact ofReal_integral_eq_lintegral_ofReal hi hn

theorem summable_orientedPivotal_pairs [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (a b : V) :
    Summable (fun xy : V × V => (law p).real (orientedPivotalEvent G xy.1 xy.2 a b)) := by
  apply ENNReal.summable_toReal
  rw [ENNReal.tsum_prod',←ennreal_distinctClusterMoment G hloc hqt p hp a b]
  exact ENNReal.ofReal_ne_top

theorem distinctClusterMoment_eq_pivotal [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (a b : V) :
    distinctClusterMoment G p a b =
      ∑' x, ∑' y, (law p).real (orientedPivotalEvent G x y a b) := by
  rw [←(summable_orientedPivotal_pairs G hloc hqt p hp a b).tsum_prod]
  change distinctClusterMoment G p a b =
    ∑' xy : V × V, (law p (orientedPivotalEvent G xy.1 xy.2 a b)).toReal
  rw [←ENNReal.tsum_toReal_eq (f := fun xy : V × V => law p (orientedPivotalEvent G xy.1 xy.2 a b))
    (fun _ => measure_ne_top _ _), ENNReal.tsum_prod',
    ←ennreal_distinctClusterMoment G hloc hqt p hp a b,
    ENNReal.toReal_ofReal (distinctClusterMoment_nonneg G p a b)]

end PivotalMomentIdentity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section PivotalTransport
attribute [local instance] Classical.propDecidable Classical.decEq

theorem orientedPivotal_probability_covariant [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x y z w : V) :
    (law p).real (orientedPivotalEvent G (a x) (a y) (a z) (a w)) =
      (law p).real (orientedPivotalEvent G x y z w) := by
  have he : orientedPivotalEvent G (a x) (a y) (a z) (a w) =
      (fun ω => b ⁻¹' ω) ⁻¹' orientedPivotalEvent G x y z w := by
    ext ω
    simp only [orientedPivotalEvent,Set.mem_ofPred_eq,Set.mem_preimage,conn_aut_iff G hab]
  unfold Measure.real
  rw [he,←Measure.map_apply (measurable_set_preimage b)
    (measurableSet_orientedPivotalEvent G x y z w),law_map_preimage_equiv]

noncomputable def pivotalTransportMass (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x a : V) : ℝ :=
  ∑ b ∈ neighbors G hloc a, ∑' y, (law p).real (orientedPivotalEvent G x y a b)

theorem pivotalTransportMass_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x a : V) : 0 ≤ pivotalTransportMass G hloc p x a :=
  Finset.sum_nonneg (fun _ _ => tsum_nonneg (fun _ => measureReal_nonneg))

theorem pivotalTransportMass_covariant [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x z : V) :
    pivotalTransportMass G hloc p (a x) (a z) = pivotalTransportMass G hloc p x z := by
  simp only [pivotalTransportMass,neighbors_covariant G hloc hab,Finset.sum_map,Equiv.coe_toEmbedding]
  apply Finset.sum_congr rfl
  intro w _
  rw [←a.tsum_eq (fun y => (law p).real (orientedPivotalEvent G (a x) y (a z) (a w)))]
  exact tsum_congr (fun y => orientedPivotal_probability_covariant G p hab x y z w)

theorem pivotalTransportMass_incoming_summable [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (a : V) :
    Summable (fun x => pivotalTransportMass G hloc p x a) := by
  apply summable_sum
  intro b _
  exact (summable_orientedPivotal_pairs G hloc hqt p hp a b).prod

theorem pivotalTransportMass_incoming [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (a : V) :
    (∑' x, pivotalTransportMass G hloc p x a) = neighborClusterMoment G hloc p a := by
  unfold pivotalTransportMass neighborClusterMoment
  rw [Summable.tsum_finsetSum (fun b _ =>
    (summable_orientedPivotal_pairs G hloc hqt p hp a b).prod)]
  exact Finset.sum_congr rfl (fun b _ => (distinctClusterMoment_eq_pivotal G hloc hqt p hp a b).symm)

end PivotalTransport
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section PivotalTransportTotal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem pivotalTransportMass_outgoing_summable
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Summable (pivotalTransportMass G hloc p x) := by
  have hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i) := by
    intro x
    obtain ⟨i,a,ha,hax⟩ := hcov x
    obtain ⟨b,hab⟩ := hΓ ha
    exact ⟨i,a,b,hab,hax⟩
  exact (transported_column_of_row_bound G hconn hloc root weight Γ hΓ htr hcov hw hw1 c hc hmin
    (fun a x => pivotalTransportMass G hloc p x a)
    (fun a x => pivotalTransportMass_nonneg G hloc p x a)
    (fun a ha x y => by obtain ⟨b,hab⟩ := hΓ ha; exact pivotalTransportMass_covariant G hloc p hab y x)
    (pivotalTransportMass_incoming_summable G hloc hqt p hp)
    (c*rootNeighborMoment G hloc root weight p)
    (fun a => by
      rw [pivotalTransportMass_incoming G hloc hqt p hp]
      exact neighborMoment_le_rootMoment G hloc root weight hw hcover c hc hmin p a) x).1

 

theorem rootPivotalMass_eq_neighborMoment
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) :
    (∑ i, weight i * ∑' a, pivotalTransportMass G hloc p (root i) a) =
      rootNeighborMoment G hloc root weight p := by
  rw [htr.real root weight Γ (pivotalTransportMass G hloc p)
    (fun a ha x y => by obtain ⟨b,hab⟩ := hΓ ha; exact pivotalTransportMass_covariant G hloc p hab x y)
    (pivotalTransportMass_outgoing_summable G hconn hloc hqt root weight Γ hΓ htr hcov hw hw1 c hc hmin p hp)
    (pivotalTransportMass_incoming_summable G hloc hqt p hp)]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun t => weight i*t)
    (pivotalTransportMass_incoming G hloc hqt p hp (root i)))

end PivotalTransportTotal
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FinitePivotalComparison
attribute [local instance] Classical.propDecidable Classical.decEq

theorem orientedPivotal_probability_le_closed [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (e : E) (x y a b : V) (he : G e = s(a,b)) :
    (law p).real (orientedPivotalEvent G x y a b) ≤
      (law p).real (closedPivotal {ω | Conn G ω x y} e) := by
  rw [closedPivotal_conn_probability G p e a b x y he]
  exact le_add_of_nonneg_right measureReal_nonneg

 

theorem finite_neighbor_pivotal_le_incident [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (x y a : V) :
    (∑ b ∈ neighbors G hloc a, (law p).real (orientedPivotalEvent G x y a b)) ≤
      ∑ e ∈ (hloc a).toFinset, (law p).real (closedPivotal {ω | Conn G ω x y} e) := by
  let B := neighbors G hloc a
  have he (b : B) : ∃ e, G e = s(a,(b:V)) := (mem_neighbors G hloc a b).mp b.property
  choose edge hedge using he
  have hinj : Function.Injective edge := by
    intro b c h
    apply Subtype.ext
    have hh := (hedge b).symm.trans ((congrArg G h).trans (hedge c))
    rcases Sym2.eq_iff.mp hh with h | h
    · exact h.2
    · exact h.2.trans h.1
  calc
    _ = ∑ b : B, (law p).real (orientedPivotalEvent G x y a b) := (Finset.sum_coe_sort B _).symm
    _ ≤ ∑ b : B, (law p).real (closedPivotal {ω | Conn G ω x y} (edge b)) :=
      Finset.sum_le_sum (fun b _ => orientedPivotal_probability_le_closed G p (edge b) x y a b (hedge b))
    _ = ∑ e ∈ Finset.univ.image edge, (law p).real (closedPivotal {ω | Conn G ω x y} e) :=
      (Finset.sum_image (f := fun e => (law p).real (closedPivotal {ω | Conn G ω x y} e))
        (s := Finset.univ) (fun _ _ _ _ h => hinj h)).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp he
        rw [Set.Finite.mem_toFinset]
        change a ∈ G (edge b)
        rw [hedge b]
        exact Sym2.mem_mk_left _ _
      · intro _ _ _
        exact measureReal_nonneg

theorem finite_incident_sum_le_twice (G : BondGraph V E) (hloc : LocallyFinite G)
    (A : Finset V) (f : E → ℝ) (hf : ∀ e, 0 ≤ f e) :
    (∑ a ∈ A, ∑ e ∈ (hloc a).toFinset, f e) ≤ 2*∑ e ∈ incidentSupport G hloc A, f e := by
  let Q := incidentSupport G hloc A
  have heq (a : V) (ha : a ∈ A) :
      (∑ e ∈ (hloc a).toFinset, f e) = ∑ e ∈ Q, if a ∈ G e then f e else 0 := by
    rw [←Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext e
    simp only [Set.Finite.mem_toFinset,Finset.mem_filter]
    exact ⟨fun he => ⟨(mem_incidentSupport G hloc A e).mpr ⟨a,ha,he⟩,he⟩,fun h => h.2⟩
  calc
    _ = ∑ a ∈ A, ∑ e ∈ Q, if a ∈ G e then f e else 0 := Finset.sum_congr rfl heq
    _ = ∑ e ∈ Q, ∑ a ∈ A, if a ∈ G e then f e else 0 := Finset.sum_comm
    _ ≤ ∑ e ∈ Q, 2*f e := by
      apply Finset.sum_le_sum
      intro e _
      have hsub : A.filter (fun a => a ∈ G e) ⊆ (G e).toFinset := by
        intro a ha
        exact Sym2.mem_toFinset.mpr (Finset.mem_filter.mp ha).2
      rw [←Finset.sum_filter,Finset.sum_const, nsmul_eq_mul]
      have hc : (A.filter (fun a => a ∈ G e)).card ≤ 2 := (Finset.card_le_card hsub).trans (by
        rw [Sym2.card_toFinset]; split_ifs <;> omega)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hf e)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem finite_oriented_pivotal_sum_le [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (x y : V) (A : Finset V) :
    (∑ a ∈ A, ∑ b ∈ neighbors G hloc a, (law p).real (orientedPivotalEvent G x y a b)) ≤
      2*∑ e ∈ incidentSupport G hloc A, (law p).real (closedPivotal {ω | Conn G ω x y} e) := by
  exact (Finset.sum_le_sum (fun a _ => finite_neighbor_pivotal_le_incident G hloc p x y a)).trans
    (finite_incident_sum_le_twice G hloc A _ (fun _ => measureReal_nonneg))

end FinitePivotalComparison
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section SubcriticalSusceptibilityContinuity
attribute [local instance] Classical.propDecidable Classical.decEq

theorem eventually_cluster_eq_at_finite (G : BondGraph V E) (hloc : LocallyFinite G)
    (labels : E → unitInterval) (p : unitInterval) (x : V)
    (hneq : ∀ e, labels e ≠ p) (hfin : (cluster G (openEdges labels p) x).Finite) :
    ∀ᶠ q in nhds p, cluster G (openEdges labels q) x = cluster G (openEdges labels p) x := by
  let Q := incidentSupport G hloc hfin.toFinset
  have he (e : E) : ∀ᶠ q in nhds p, (e ∈ openEdges labels q ↔ e ∈ openEdges labels p) := by
    change ∀ᶠ q in nhds p, (labels e ≤ q ↔ labels e ≤ p)
    by_cases hp : labels e ≤ p
    · have hlt : labels e < p := lt_of_le_of_ne hp (hneq e)
      filter_upwards [eventually_gt_nhds hlt] with q hq
      exact iff_of_true hq.le hp
    · have hlt : p < labels e := lt_of_not_ge hp
      filter_upwards [eventually_lt_nhds hlt] with q hq
      exact iff_of_false (not_le.mpr hq) hp
  filter_upwards [(eventually_all_finset Q).mpr (fun e _ => he e)] with q hq
  apply cluster_eq_of_incident_agreement G
  intro e he
  apply (hq e _).symm
  obtain ⟨v,hv,hve⟩ := he
  exact (mem_incidentSupport G hloc hfin.toFinset e).mpr ⟨v,hfin.mem_toFinset.mpr hv,hve⟩

theorem label_cluster_finite_ae_subcritical [Countable E]
    (G : BondGraph V E) (p : unitInterval) (hp : p < pc G) (x : V) :
    ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)), (cluster G (openEdges labels p) x).Finite := by
  apply ae_of_ae_map (μ := (labelLaw : Measure (E → unitInterval)))
    (p := fun ω : Set E => (cluster G ω x).Finite) (measurable_openEdges p).aemeasurable
  rw [map_openEdges]
  exact subcritical_cluster_finite_ae G p hp x

theorem susceptibility_eq_label_integral [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Integrable (fun labels : E → unitInterval => ((cluster G (openEdges labels p) x).ncard:ℝ)) labelLaw ∧
    susceptibility G p x = ∫ labels : E → unitInterval, ((cluster G (openEdges labels p) x).ncard:ℝ) ∂labelLaw := by
  obtain ⟨hi,he⟩ := susceptibility_eq_integral G hloc hqt p hp x
  have hi' : Integrable (fun ω : Set E => ((cluster G ω x).ncard:ℝ))
      ((labelLaw : Measure (E → unitInterval)).map (fun labels => openEdges labels p)) := by
    rwa [map_openEdges]
  refine ⟨hi'.comp_measurable (measurable_openEdges p),?_⟩
  rw [he,←integral_map (measurable_openEdges p).aemeasurable hi'.aestronglyMeasurable,map_openEdges]

 

theorem continuousAt_susceptibility_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) : ContinuousAt (fun q => susceptibility G q x) p := by
  obtain ⟨r,hpr,hr⟩ := exists_between hp
  let F (q : unitInterval) (labels : E → unitInterval) : ℝ := ((cluster G (openEdges labels q) x).ncard:ℝ)
  have hm (q : unitInterval) : Measurable (F q) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
      ((measurable_cluster_ncard G hloc x).comp (measurable_openEdges q))
  have hcont : ContinuousAt (fun q => ∫ labels, F q labels ∂labelLaw) p := by
    apply continuousAt_of_dominated
      (bound := F r) (Filter.Eventually.of_forall (fun q => (hm q).aestronglyMeasurable))
    · filter_upwards [eventually_lt_nhds hpr] with q hqr
      filter_upwards [label_cluster_finite_ae_subcritical G r hr x] with labels hfin
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
      dsimp only [F]
      exact_mod_cast Set.ncard_le_ncard (show cluster G (openEdges labels q) x ⊆ cluster G (openEdges labels r) x from
        fun y hy => conn_mono G (openEdges_mono labels hqr.le) hy) hfin
    · exact (susceptibility_eq_label_integral G hloc hqt r hr x).1
    · filter_upwards [ae_labels_ne (E := E) p,label_cluster_finite_ae_subcritical G p hp x] with labels hneq hfin
      apply Filter.EventuallyEq.continuousAt
      filter_upwards [eventually_cluster_eq_at_finite G hloc labels p x hneq hfin] with q hq
      exact congrArg (fun S : Set V => (S.ncard:ℝ)) hq
  apply (continuousAt_congr _).mpr hcont
  filter_upwards [eventually_lt_nhds hp] with q hq
  exact (susceptibility_eq_label_integral G hloc hqt q hq x).2

theorem continuousAt_rootSusceptibility_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (p : unitInterval) (hp : p < pc G) :
    ContinuousAt (rootSusceptibility G root weight) p := by
  exact tendsto_finsetSum Finset.univ (fun i _ => continuousAt_const.mul
    (continuousAt_susceptibility_subcritical G hloc hqt p hp (root i)))

end SubcriticalSusceptibilityContinuity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section FiniteRootPivotalApproximation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem summable_orientedPivotal_targets [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x a b : V) :
    Summable (fun y => (law p).real (orientedPivotalEvent G x y a b)) := by
  apply (summable_twoPoint_subcritical G hloc hqt p hp b).of_nonneg_of_le
  · exact fun _ => measureReal_nonneg
  · intro y
    exact measureReal_mono (fun _ h => h.2.1)

noncomputable def finiteRootPivotalMass (G : BondGraph V E)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (p : unitInterval) (Q : Finset E) (F : Finset V) : ℝ :=
  ∑ i, weight i*(∑ y ∈ F, ∑ e ∈ Q, (law p).real (closedPivotal {ω | Conn G ω (root i) y} e))

theorem finiteRootPivotalMass_nonneg (G : BondGraph V E)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (p : unitInterval) (Q : Finset E) (F : Finset V) :
    0 ≤ finiteRootPivotalMass G root weight p Q F :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i)
    (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => measureReal_nonneg))))

 

theorem exists_finiteRootPivotalMass_gt
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (B : ℝ)
    (hB : B < rootNeighborMoment G hloc root weight p / 2) :
    ∃ Q : Finset E, ∃ F : Finset V, B < finiteRootPivotalMass G root weight p Q F := by
  have hs (x : V) := pivotalTransportMass_outgoing_summable G hconn hloc hqt root weight Γ hΓ htr hcov hw hw1 c hc hmin p hp x
  let f (a : V) := ∑ i, weight i*pivotalTransportMass G hloc p (root i) a
  have hsf : Summable f := summable_sum (fun i _ => (hs (root i)).mul_left (weight i))
  have htf : (∑' a, f a) = rootNeighborMoment G hloc root weight p := by
    rw [Summable.tsum_finsetSum (fun i _ => (hs (root i)).mul_left (weight i))]
    simp_rw [tsum_mul_left]
    exact rootPivotalMass_eq_neighborMoment G hconn hloc hqt root weight Γ hΓ htr hcov hw hw1 c hc hmin p hp
  have hB' : 2*B < ∑' a, f a := by rw [htf]; linarith
  obtain ⟨A,hA⟩ := ((tendsto_order.mp hsf.hasSum).1 (2*B) hB').exists
  let g (y : V) := ∑ i, weight i*(∑ a ∈ A, ∑ b ∈ neighbors G hloc a,
    (law p).real (orientedPivotalEvent G (root i) y a b))
  have hst (i : ι) (a b : V) := summable_orientedPivotal_targets G hloc hqt p hp (root i) a b
  have hsg : Summable g := summable_sum (fun i _ =>
    (summable_sum (fun a _ => summable_sum (fun b _ => hst i a b))).mul_left (weight i))
  have htg : (∑' y, g y) = ∑ a ∈ A, f a := by
    rw [Summable.tsum_finsetSum (fun i _ =>
      (summable_sum (fun a _ => summable_sum (fun b _ => hst i a b))).mul_left (weight i))]
    simp_rw [tsum_mul_left]
    simp_rw [Summable.tsum_finsetSum (fun a _ => summable_sum (fun b _ => hst _ a b))]
    simp_rw [Summable.tsum_finsetSum (fun b _ => hst _ _ b)]
    simp only [f,Finset.mul_sum,pivotalTransportMass]
    rw [Finset.sum_comm]
  obtain ⟨F,hF⟩ := ((tendsto_order.mp hsg.hasSum).1 (2*B) (by rwa [htg])).exists
  refine ⟨incidentSupport G hloc A,F,?_⟩
  have hb : (∑ y ∈ F, g y) ≤ 2*finiteRootPivotalMass G root weight p (incidentSupport G hloc A) F := by
    unfold g finiteRootPivotalMass
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.mul_sum, mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (hw i)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun y _ => finite_oriented_pivotal_sum_le G hloc p (root i) y A)
  linarith

end FiniteRootPivotalApproximation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section VanishingSprinkles
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def vanishingSprinkle (n : ℕ) : unitInterval :=
  ⟨1/((n:ℝ)+1), by
    constructor
    · positivity
    · apply (div_le_one (by positivity : 0 < (n:ℝ)+1)).mpr
      linarith [show (0:ℝ) ≤ (n:ℝ) by positivity]
  ⟩

theorem vanishingSprinkle_pos (n : ℕ) : 0 < (vanishingSprinkle n : ℝ) := by
  dsimp [vanishingSprinkle]
  positivity

theorem tendsto_vanishingSprinkle :
    Tendsto (fun n => (vanishingSprinkle n:ℝ)) atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem sprinkle_sequence_gt (p : unitInterval) (hp : (p:ℝ) < 1) (n : ℕ) :
    p < sprinkleParameter p (vanishingSprinkle n) := by
  change (p:ℝ) < (p:ℝ)+(1-(p:ℝ))*(vanishingSprinkle n:ℝ)
  exact lt_add_of_pos_right _ (mul_pos (sub_pos.mpr hp) (vanishingSprinkle_pos n))

theorem tendsto_sprinkle_sequence (p : unitInterval) :
    Tendsto (fun n => sprinkleParameter p (vanishingSprinkle n)) atTop (nhds p) := by
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun n => (p:ℝ)+(1-(p:ℝ))*(vanishingSprinkle n:ℝ)) atTop (nhds (p:ℝ))
  convert tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_vanishingSprinkle) using 1; simp

theorem tendsto_sprinkle_sequence_right (p : unitInterval) (hp : (p:ℝ) < 1) :
    Tendsto (fun n => (sprinkleParameter p (vanishingSprinkle n):ℝ)) atTop (nhdsWithin (p:ℝ) (Set.Ioi (p:ℝ))) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨continuous_subtype_val.continuousAt.tendsto.comp (tendsto_sprinkle_sequence p),
    Eventually.of_forall (sprinkle_sequence_gt p hp)⟩

 

theorem rootSusceptibility_sequence_slope_lower
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (p : unitInterval) (hp : p < pc G) (Q : Finset E) (F : Finset V) (d : ℝ)
    (hd : d < finiteRootPivotalMass G root weight p Q F) :
    ∀ᶠ n in atTop,
      ((sprinkleParameter p (vanishingSprinkle n):ℝ)-(p:ℝ))*d ≤
      rootSusceptibility G root weight (sprinkleParameter p (vanishingSprinkle n)) -
      rootSusceptibility G root weight p := by
  have ht : Tendsto (fun n => (1-(vanishingSprinkle n:ℝ))^(Q.card-1) *
      finiteRootPivotalMass G root weight p Q F) atTop
      (nhds (finiteRootPivotalMass G root weight p Q F)) := by
    convert ((tendsto_const_nhds.sub tendsto_vanishingSprinkle).pow (Q.card-1)).mul tendsto_const_nhds using 1; simp
  have hnn := finiteRootPivotalMass_nonneg G root weight hw p Q F
  filter_upwards [(tendsto_sprinkle_sequence p).eventually (eventually_lt_nhds hp),
      ht.eventually (eventually_gt_nhds hd)] with n hn hdn
  have hgain := rootSusceptibility_sprinkling_gain G hloc hqt root weight hw
    p (vanishingSprinkle n) hn Q F
  change (vanishingSprinkle n:ℝ)*(1-(vanishingSprinkle n:ℝ))^(Q.card-1)*
    finiteRootPivotalMass G root weight p Q F ≤ _ at hgain
  by_cases hd0 : 0 ≤ d
  · have hdp : (1-(p:ℝ))*d ≤ (1-(vanishingSprinkle n:ℝ))^(Q.card-1)*
        finiteRootPivotalMass G root weight p Q F := by
      calc
        _ ≤ d := by nlinarith [p.2.1]
        _ ≤ _ := hdn.le
    have hm := mul_le_mul_of_nonneg_left hdp (vanishingSprinkle n).2.1
    calc
      _ = (vanishingSprinkle n:ℝ)*((1-(p:ℝ))*d) := by
        change ((p:ℝ)+(1-(p:ℝ))*(vanishingSprinkle n:ℝ)-(p:ℝ))*d = _
        ring
      _ ≤ (vanishingSprinkle n:ℝ)*((1-(vanishingSprinkle n:ℝ))^(Q.card-1)*
          finiteRootPivotalMass G root weight p Q F) := hm
      _ ≤ _ := by simpa only [mul_assoc] using hgain
  · have hmono : 0 ≤ rootSusceptibility G root weight (sprinkleParameter p (vanishingSprinkle n)) - rootSusceptibility G root weight p :=
      (mul_nonneg (mul_nonneg (vanishingSprinkle n).2.1 (pow_nonneg (sub_nonneg.mpr (vanishingSprinkle n).2.2) _)) hnn).trans hgain
    have hdp : ((sprinkleParameter p (vanishingSprinkle n):ℝ)-(p:ℝ))*d ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (sprinkleParameter_ge_left _ _)) (le_of_not_ge hd0)
    linarith

end VanishingSprinkles
end Percolation

 
namespace Percolation
open Filter
section NegativePowerRightSlopes

 

theorem frequently_rpow_slope_le_of_sequence
    (f : ℝ → ℝ) (x d e : ℝ) (hx : 0 < f x) (hd : 0 < d) (he : e < 0)
    (z : ℕ → ℝ) (hz : Tendsto z atTop (nhdsWithin x (Set.Ioi x)))
    (hgain : ∀ᶠ n in atTop, (z n-x)*d ≤ f (z n)-f x) :
    ∀ r, e*(f x)^(e-1)*d < r →
      ∃ᶠ y in nhdsWithin x (Set.Ioi x), slope (fun t => (f t)^e) x y < r := by
  let A (t : ℝ) := f x+(t-x)*d
  have hA : HasDerivAt A d x := by
    simpa only [zero_add, one_mul] using! (hasDerivAt_const x (f x)).add (((hasDerivAt_id x).sub_const x).mul_const d)
  have hAx : A x = f x := by simp [A]
  have hR : HasDerivAt (fun t => (A t)^e) (e*(f x)^(e-1)*d) x := by
    simpa only [hAx] using! (Real.hasDerivAt_rpow_const (p := e) (Or.inl (show A x ≠ 0 by rw [hAx]; exact hx.ne'))).comp x hA
  intro r hr
  have hlim := hR.tendsto_slope.comp (hz.mono_right (nhdsWithin_mono x (show Set.Ioi x ⊆ {x}ᶜ from fun y hy => by simpa using ne_of_gt hy)))
  have hright : ∀ᶠ n in atTop, x < z n := (tendsto_nhdsWithin_iff.mp hz).2
  apply hz.frequently
  apply Filter.Eventually.frequently
  filter_upwards [hgain, hright, hlim.eventually (eventually_lt_nhds hr)] with n hn hzn hnr
  have hApos : 0 < A (z n) := by dsimp [A]; positivity
  have hAr : A (z n) ≤ f (z n) := by dsimp [A]; linarith
  have hp := Real.rpow_le_rpow_of_nonpos hApos hAr he.le
  apply lt_of_le_of_lt _ hnr
  simp only [Function.comp_apply, slope_def_field, hAx]
  exact div_le_div_of_nonneg_right (sub_le_sub_right hp _) (sub_pos.mpr hzn).le

end NegativePowerRightSlopes
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section ActualSusceptibilityRightSlope
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def realRootSusceptibility (G : BondGraph V E)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (t : ℝ) : ℝ :=
  rootSusceptibility G root weight (Set.projIcc 0 1 zero_le_one t)

@[simp] theorem realRootSusceptibility_coe (G : BondGraph V E)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (p : unitInterval) :
    realRootSusceptibility G root weight (p:ℝ) = rootSusceptibility G root weight p := by
  simp only [realRootSusceptibility, Set.projIcc_val]

theorem rootSusceptibility_one_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (p : unitInterval) (hp : p < pc G) : 1 ≤ rootSusceptibility G root weight p := by
  calc
    1 = ∑ i, weight i*1 := by simp only [mul_one, hw1]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
      (susceptibility_one_le G hloc hqt p hp (root i)) (hw i))

theorem continuousAt_realRootSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (p : unitInterval) (hp : p < pc G) :
    ContinuousAt (realRootSusceptibility G root weight) (p:ℝ) := by
  apply ContinuousAt.comp (f := Set.projIcc 0 1 zero_le_one)
  · simpa only [Set.projIcc_val] using continuousAt_rootSusceptibility_subcritical G hloc hqt root weight p hp
  · exact continuous_projIcc.continuousAt

 

theorem rootSusceptibility_power_right_slope
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (b γ : ℝ) (hb : 0 < b) (hγ : γ < 1)
    (hD : b*(rootSusceptibility G root weight p)^(2-γ) ≤ rootNeighborMoment G hloc root weight p) :
    ∀ r, -(1-γ)*b/4 < r → ∃ᶠ y in nhdsWithin (p:ℝ) (Set.Ioi (p:ℝ)),
      slope (fun t => (realRootSusceptibility G root weight t)^(γ-1)) (p:ℝ) y < r := by
  let χ := rootSusceptibility G root weight p
  have hχ : 0 < χ := lt_of_lt_of_le zero_lt_one (rootSusceptibility_one_le G hloc hqt root weight hw hw1 p hp)
  let d := (b/4)*χ^(2-γ)
  have hd : 0 < d := mul_pos (by positivity) (Real.rpow_pos_of_pos hχ _)
  have hBd : d < rootNeighborMoment G hloc root weight p/2 := by
    dsimp [d, χ] at *
    nlinarith [Real.rpow_pos_of_pos hχ (2-γ)]
  obtain ⟨Q,F,hQ⟩ := exists_finiteRootPivotalMass_gt G hconn hloc hqt root weight Γ hΓ htr hcov hw hw1 c hc hmin p hp d hBd
  have hg := rootSusceptibility_sequence_slope_lower G hloc hqt root weight hw p hp Q F d hQ
  have hp1 : (p:ℝ) < 1 := lt_of_lt_of_le hp (pc G).2.2
  have hsl := frequently_rpow_slope_le_of_sequence (realRootSusceptibility G root weight)
    (p:ℝ) d (γ-1) (by simpa only [realRootSusceptibility_coe] using hχ) hd (by linarith)
    (fun n => (sprinkleParameter p (vanishingSprinkle n):ℝ)) (tendsto_sprinkle_sequence_right p hp1)
    (by simpa only [realRootSusceptibility_coe] using hg)
  have heq : (γ-1)*(realRootSusceptibility G root weight (p:ℝ))^(γ-1-1)*d = -(1-γ)*b/4 := by
    rw [realRootSusceptibility_coe]
    change (γ-1)*χ^(γ-1-1)*((b/4)*χ^(2-γ)) = _
    rw [show γ-1-1 = γ-2 by ring]
    calc
      _ = ((γ-1)*b/4)*(χ^(γ-2)*χ^(2-γ)) := by ring
      _ = _ := by rw [←Real.rpow_add hχ, sub_add_sub_cancel, sub_self, Real.rpow_zero]; ring
  rwa [heq] at hsl

end ActualSusceptibilityRightSlope
end Percolation

 
namespace Percolation
open Filter
section IntegratedRightSlopes

 

theorem interval_decrease_of_right_slope (f : ℝ → ℝ) (a b k : ℝ)
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (hs : ∀ x ∈ Set.Ico a b, ∀ r, -k < r →
      ∃ᶠ y in nhdsWithin x (Set.Ioi x), slope f x y < r) :
    k*(b-a) ≤ f a-f b := by
  let B (t : ℝ) := f a-k*(t-a)
  have hB : ContinuousOn B (Set.Icc a b) := by fun_prop
  have hB' (x : ℝ) : HasDerivAt B (-k) x := by
    simpa only [one_mul, sub_zero, mul_one, zero_sub] using!
      (hasDerivAt_const x (f a)).sub (((hasDerivAt_id x).sub_const a).const_mul k)
  have h := image_le_of_liminf_slope_right_le_deriv_boundary hf
    (show f a ≤ B a by simp [B]) hB (fun x _ => (hB' x).hasDerivWithinAt) hs ⟨hab,le_rfl⟩
  dsimp [B] at h
  linarith

 

theorem right_slope_distance_bound (f : ℝ → ℝ) (a b k : ℝ)
    (hab : a < b) (hk : 0 < k)
    (hpos : ∀ x ∈ Set.Ico a b, 0 ≤ f x)
    (hc : ContinuousOn f (Set.Ico a b))
    (hs : ∀ x ∈ Set.Ico a b, ∀ r, -k < r →
      ∃ᶠ y in nhdsWithin x (Set.Ioi x), slope f x y < r) :
    k*(b-a) ≤ f a := by
  have hbound (r : ℝ) (hr : r ∈ Set.Ico a b) : k*(r-a) ≤ f a := by
    have hsub : Set.Icc a r ⊆ Set.Ico a b := fun t ht => ⟨ht.1,lt_of_le_of_lt ht.2 hr.2⟩
    have h := interval_decrease_of_right_slope f a r k hr.1 (hc.mono hsub)
      (fun x hx => hs x ⟨hx.1,lt_trans hx.2 hr.2⟩)
    linarith [hpos r hr]
  by_contra h
  have hd : a+f a/k < b := by
    have hh : f a < k*(b-a) := lt_of_not_ge h
    have hv : f a/k < b-a := (div_lt_iff₀ hk).mpr (by nlinarith)
    linarith
  obtain ⟨r,hr1,hr2⟩ := exists_between hd
  have ha : a ≤ r := by
    have hf := hpos a ⟨le_rfl,hab⟩
    have hd0 := div_nonneg hf hk.le
    linarith
  have hb := hbound r ⟨ha,hr2⟩
  have hr : f a < (r-a)*k := (div_lt_iff₀ hk).mp (by linarith : f a/k < r-a)
  nlinarith

end IntegratedRightSlopes
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section ActualIntegratedSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem susceptibility_bound_of_neighborMoment
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (b γ : ℝ) (hb : 0 < b) (hγ : γ < 1)
    (hD : ∀ q, p ≤ q → q < pc G → b*(rootSusceptibility G root weight q)^(2-γ) ≤
      rootNeighborMoment G hloc root weight q) :
    rootSusceptibility G root weight p ≤
      (((1-γ)*b/4)*((pc G:ℝ)-(p:ℝ)))^(-1/(1-γ)) := by
  let k := (1-γ)*b/4
  have hk : 0 < k := by dsimp [k]; positivity
  let f (t : ℝ) := (realRootSusceptibility G root weight t)^(γ-1)
  have hparam (t : ℝ) (ht : t ∈ Set.Ico (p:ℝ) (pc G:ℝ)) : t ∈ Set.Icc (0:ℝ) 1 :=
    ⟨le_trans p.2.1 ht.1, le_trans ht.2.le (pc G).2.2⟩
  have hcp (t : ℝ) (ht : t ∈ Set.Ico (p:ℝ) (pc G:ℝ)) :
      ContinuousAt (realRootSusceptibility G root weight) t :=
    continuousAt_realRootSusceptibility G hloc hqt root weight ⟨t,hparam t ht⟩ ht.2
  have hpos (t : ℝ) (ht : t ∈ Set.Ico (p:ℝ) (pc G:ℝ)) :
      0 < realRootSusceptibility G root weight t := by
    have hh := rootSusceptibility_one_le G hloc hqt root weight hw hw1 ⟨t,hparam t ht⟩ ht.2
    rw [←realRootSusceptibility_coe] at hh
    exact lt_of_lt_of_le zero_lt_one hh
  have hcont : ContinuousOn f (Set.Ico (p:ℝ) (pc G:ℝ)) := by
    intro t ht
    exact ((hcp t ht).rpow_const (Or.inl (hpos t ht).ne')).continuousWithinAt
  have hs (t : ℝ) (ht : t ∈ Set.Ico (p:ℝ) (pc G:ℝ)) :=
    rootSusceptibility_power_right_slope G hconn hloc hqt root weight Γ hΓ htr hcov hw hw1 c hc hmin
      ⟨t,hparam t ht⟩ ht.2 b γ hb hγ (hD ⟨t,hparam t ht⟩ ht.1 ht.2)
  have hdist : k*((pc G:ℝ)-(p:ℝ)) ≤ f (p:ℝ) := by
    apply right_slope_distance_bound f (p:ℝ) (pc G:ℝ) k hp hk
      (fun t ht => (Real.rpow_pos_of_pos (hpos t ht) _).le) hcont
    intro t ht r hr
    apply hs t ht r
    dsimp [k] at hr
    linarith
  have hχ := lt_of_lt_of_le zero_lt_one (rootSusceptibility_one_le G hloc hqt root weight hw hw1 p hp)
  have hd : 0 < k*((pc G:ℝ)-(p:ℝ)) := mul_pos hk (sub_pos.mpr hp)
  have he : -1/(1-γ) = 1/(γ-1) := by rw [show γ-1=-(1-γ) by ring, div_neg, neg_div]
  have he0 : 1/(γ-1) < 0 := one_div_neg.mpr (by linarith)
  have hinv := Real.rpow_le_rpow_of_nonpos hd hdist he0.le
  rw [he]
  apply le_trans _ hinv
  change rootSusceptibility G root weight p ≤
    ((realRootSusceptibility G root weight (p:ℝ))^(γ-1))^(1/(γ-1))
  rw [realRootSusceptibility_coe,←Real.rpow_mul hχ.le]
  rw [mul_one_div_cancel (by linarith : γ-1 ≠ 0),Real.rpow_one]

end ActualIntegratedSusceptibility
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section SusceptibilityGrowthConsequence
attribute [local instance] Classical.propDecidable Classical.decEq

theorem eventually_upper_interval_unit (p₀ : unitInterval) (P : unitInterval → Prop)
    (h : ∀ᶠ p in nhds p₀, P p) :
    ∀ᶠ p in nhds p₀, p < p₀ → ∀ q, p ≤ q → q < p₀ → P q := by
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp h
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨ε,hε,?_⟩
  intro p hp hpp q hpq hq
  apply hball
  have hd : dist q p₀ ≤ dist p p₀ := by
    change |(q:ℝ)-(p₀:ℝ)| ≤ |(p:ℝ)-(p₀:ℝ)|
    rw [abs_of_nonpos (sub_nonpos.mpr (show (q:ℝ) ≤ (p₀:ℝ) from hq.le)),abs_of_nonpos (sub_nonpos.mpr (show (p:ℝ) ≤ (p₀:ℝ) from hpp.le))]
    have hpqR : (p:ℝ) ≤ (q:ℝ) := hpq
    linarith
  exact lt_of_le_of_lt hd hp

 

theorem susceptibility_growth_of_divergent_moment
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (α β ε : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hε : 0 < ε) (hε1 : ε < 1/2) (hsmall : β+(1/2+ε) < 1)
    (hdiv : ∃ i, ¬ Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law (pc G))) :
    ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ C : ℝ, 0 < C ∧ ∀ᶠ p in nhds (pc G), p < pc G →
      rootSusceptibility G root weight p ≤ C*((pc G:ℝ)-(p:ℝ))^(-1/(1-γ)) := by
  intro γ hγ hγ1
  obtain ⟨b,hb,hnear⟩ := neighborMoment_growth_of_divergent_moment G hloc hconn hqt hh root weight Γ hΓ htr
    hcov hw hw1 (pc G) hp₀ hp₁ hfin α β ε hα hαβ hε hε1 hsmall hdiv γ hγ
  let c : ℝ := ∑ i, 1/weight i
  have hc : 0 ≤ c := Finset.sum_nonneg (fun i _ => (one_div_pos.mpr (hw i)).le)
  have hmin (i : ι) : 1 ≤ c*weight i := by
    apply (div_le_iff₀ (hw i)).mp
    exact Finset.single_le_sum (fun j _ => (one_div_pos.mpr (hw j)).le) (Finset.mem_univ i)
  let k := (1-γ)*b/4
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨k^(-1/(1-γ)),Real.rpow_pos_of_pos hk _,?_⟩
  filter_upwards [eventually_upper_interval_unit (pc G) _ hnear] with p hp
  intro hpc
  have hD (q : unitInterval) (hpq : p ≤ q) (hq : q < pc G) := hp hpc q hpq hq hq
  have hs := susceptibility_bound_of_neighborMoment G hconn hloc hqt root weight Γ hΓ htr hcov
    (fun i => (hw i).le) hw1 c hc hmin p hpc b γ hb hγ1 hD
  rwa [Real.mul_rpow hk.le (sub_pos.mpr (show (p:ℝ) < (pc G:ℝ) from hpc)).le] at hs

end SusceptibilityGrowthConsequence
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section MarkedSearchTransfer
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exponential_transfer_of_deriv_bound (H : ℝ → ℝ) (a b K : ℝ)
    (hH : Differentiable ℝ H) (hab : a ≤ b)
    (hb : ∀ t ∈ Set.Icc a b, deriv H t ≤ K*H t) :
    H b ≤ Real.exp (K*(b-a))*H a := by
  let F (t : ℝ) := Real.exp (-K*(t-a))*H t
  have hF (t : ℝ) : HasDerivAt F (Real.exp (-K*(t-a))*(deriv H t-K*H t)) t := by
    have he := (((hasDerivAt_id t).sub_const a).const_mul (-K)).exp
    convert! he.mul (hH t).hasDerivAt using 1
    simp only [id_eq]
    ring
  have hanti : AntitoneOn F (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (fun t _ => (hF t).continuousAt.continuousWithinAt)
      (fun t _ => (hF t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hF t).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (hb t (interior_subset ht)))
  have h := hanti ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (K*(b-a))).le
  simpa only [F, sub_self,mul_zero,Real.exp_zero,one_mul,←mul_assoc,←Real.exp_add,
    neg_mul,add_neg_cancel,Real.exp_zero,one_mul,neg_zero,add_zero] using hm

 

theorem markedConnection_transfer (G : BondGraph V E) (Q : Finset E) (x : V)
    (d : ℕ) (hd : 0 < d) (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d)
    (p q h : unitInterval) (hp : 0 < (p:ℝ)) (hpq : p ≤ q) (hq : (q:ℝ) < 1)
    (hh : 0 < (h:ℝ)) :
    markedConnectionPolynomial G Q x h q ≤
      Real.exp ((Real.sqrt ((d:ℝ)/2)/((p:ℝ)*(1-(q:ℝ)))) *
        Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*((q:ℝ)-(p:ℝ))) *
      markedConnectionPolynomial G Q x h p := by
  let H := markedConnectionPolynomial G Q x h
  have hdiff : Differentiable ℝ H := fun t => (hasDerivAt_bernoulliPolynomial Q _ t).differentiableAt
  apply exponential_transfer_of_deriv_bound H p q _ hdiff hpq
  intro t ht
  let r : unitInterval := ⟨t,⟨le_trans p.2.1 ht.1,le_trans ht.2 q.2.2⟩⟩
  have hr0 : 0 < t := lt_of_lt_of_le hp ht.1
  have hr1 : t < 1 := lt_of_le_of_lt ht.2 hq
  have HB := markedConnection_derivative_bound G Q x r h hr1 hh d hd hdeg
  have hH : 0 ≤ H t := by
    change 0 ≤ markedConnectionPolynomial G Q x h r
    rw [markedConnectionPolynomial_eq_tree]
    exact ProbeTree.successMass_nonneg r h _
  have hs : 0 ≤ Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ)) := Real.sqrt_nonneg _
  have hden : (p:ℝ)*(1-(q:ℝ)) ≤ t*(1-t) := by
    exact mul_le_mul ht.1 (by linarith [ht.2]) (sub_pos.mpr hq).le (by positivity)
  have hratio : Real.sqrt ((d:ℝ)/2)/(t*(1-t)) ≤
      Real.sqrt ((d:ℝ)/2)/((p:ℝ)*(1-(q:ℝ))) :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (mul_pos hp (sub_pos.mpr hq)) hden
  have hle : deriv H t ≤ (Real.sqrt ((d:ℝ)/2)/(t*(1-t)))*
      Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*H t := by
    have HBr : deriv H t ≤ ((Real.sqrt ((d:ℝ)/2)/(1-t))*
        Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*H t)/t := by
      apply (le_div_iff₀ hr0).mpr
      simpa only [mul_comm (deriv H t) t] using HB
    convert HBr using 1
    field_simp
  exact hle.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hratio hs) hH)

end MarkedSearchTransfer
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section MarkedComponentIdentity
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem markedConnection_component_polynomial (G : BondGraph V E)
    (Q : Finset E) (x : V) (h p : ℝ) :
    markedConnectionPolynomial G Q x h p =
      bernoulliPolynomial Q (fun ω => 1-(1-h)^(finiteRootComponent G ω x).card) p := by
  apply bernoulliPolynomial_congr
  intro ω hω
  let C := finiteRootComponent G ω x
  let F := insert x (searchVertices G Q)
  have hCF : C ⊆ F := finiteRootComponent_subset G Q F x ω hω le_rfl
  have he (m : Finset V) : (∃ y ∈ m, Conn G (ω:Set E) x y) ↔ m ∩ C ≠ ∅ := by
    rw [Finset.nonempty_iff_ne_empty.symm]
    constructor
    · rintro ⟨y,hy,hxy⟩
      exact ⟨y,Finset.mem_inter.mpr ⟨hy,by change y ∈ (C:Set V); simpa only [C,coe_finiteRootComponent,cluster,Set.mem_ofPred_eq] using hxy⟩⟩
    · rintro ⟨y,hy⟩
      refine ⟨y,(Finset.mem_inter.mp hy).1,?_⟩
      have hm : y ∈ (C:Set V) := (Finset.mem_inter.mp hy).2
      simpa only [C,coe_finiteRootComponent,cluster,Set.mem_ofPred_eq] using hm
  have hid : bernoulliPolynomial F (fun m => if ∃ y ∈ m, Conn G (ω:Set E) x y then 1 else 0) h =
      1-bernoulliPolynomial F (fun m => if m ∩ C = ∅ then 1 else 0) h := by
    calc
      _ = bernoulliPolynomial F (fun m => 1-(if m ∩ C = ∅ then 1 else 0)) h := by
        apply bernoulliPolynomial_congr
        intro m _
        by_cases hm : m ∩ C = ∅
        · have hn : ¬∃ y ∈ m, Conn G (ω:Set E) x y := fun hc => (he m).mp hc hm
          simp only [hm,hn,ite_false,ite_true,sub_self]
        · have hy := (he m).mpr hm
          simp only [hm,hy,ite_false,ite_true,sub_zero]
      _ = _ := by rw [bernoulliPolynomial_sub,bernoulliPolynomial_const]
  rw [hid,bernoulliPolynomial_restrict C F hCF (fun m => if m = ∅ then 1 else 0) h,
    bernoulliPolynomial_empty_indicator]

theorem one_sub_pow_one_sub_le (h : unitInterval) (n : ℕ) :
    1-(1-(h:ℝ))^n ≤ (h:ℝ)*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,Nat.cast_succ]
    have hm := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr h.2.2)
    have hn : 0 ≤ (h:ℝ)^2*n := by positivity
    nlinarith

end MarkedComponentIdentity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section MarkedConnectionLaw
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem markedConnection_integral (G : BondGraph V E) (Q : Finset E) (x : V)
    (h p : unitInterval) :
    markedConnectionPolynomial G Q x h p =
      ∫ ω, (1-(1-(h:ℝ))^(cluster G (ω ∩ (Q:Set E)) x).ncard) ∂law p := by
  rw [integral_eq_bernoulliPolynomial Q p _ (by intro ω; simp only [Set.inter_assoc,Set.inter_self]),
    markedConnection_component_polynomial]
  apply bernoulliPolynomial_congr
  intro ω hω
  rw [Set.inter_eq_left.mpr (show (ω:Set E) ⊆ Q from hω)]
  congr 2
  rw [←coe_finiteRootComponent,Set.ncard_coe_finset]

theorem markedConnection_le_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (Q : Finset E) (x : V) (h p : unitInterval) (hp : p < pc G) :
    markedConnectionPolynomial G Q x h p ≤ (h:ℝ)*susceptibility G p x := by
  obtain ⟨hi,he⟩ := susceptibility_eq_integral G hloc hqt p hp x
  rw [markedConnection_integral,he,←integral_const_mul]
  apply integral_mono_ae
  · exact integrable_finite_local Q p _ (by intro ω; simp only [Set.inter_assoc,Set.inter_self])
  · exact hi.const_mul _
  · filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
    apply (one_sub_pow_one_sub_le h _).trans
    apply mul_le_mul_of_nonneg_left _ h.2.1
    exact_mod_cast Set.ncard_le_ncard (fun y hy => conn_mono G Set.inter_subset_left hy) hω

 

theorem one_sub_pow_one_sub_ge_half (h : unitInterval) (n : ℕ)
    (hn : 1 ≤ (h:ℝ)*n) : (1:ℝ)/2 ≤ 1-(1-(h:ℝ))^n := by
  have hb (m : ℕ) : (1+(h:ℝ)*m)*(1-(h:ℝ))^m ≤ 1 := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hp : 0 ≤ (1-(h:ℝ))^m := pow_nonneg (sub_nonneg.mpr h.2.2) _
      have ha : (1+(h:ℝ)*(m+1))*(1-(h:ℝ)) ≤ 1+(h:ℝ)*m := by
        have hh : 0 ≤ (h:ℝ)^2*((m:ℝ)+1) := by positivity
        nlinarith
      have hm := mul_le_mul_of_nonneg_right ha hp
      rw [Nat.cast_succ,pow_succ]
      nlinarith
  have hp : 0 ≤ (1-(h:ℝ))^n := pow_nonneg (sub_nonneg.mpr h.2.2) _
  have hm := mul_le_mul_of_nonneg_right hn hp
  have hb' := hb n
  nlinarith

 

theorem clusterWindow_le_markedConnection (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (lo hi : ℕ) (p h : unitInterval) (hh : 1 ≤ (h:ℝ)*lo) :
    clusterWindowProbability G p x lo hi ≤ 2*markedConnectionPolynomial G
      (incidentSupport G hloc (finite_reachBall hloc x hi).toFinset) x h p := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x hi).toFinset
  let f (ω : Set E) := 1-(1-(h:ℝ))^(cluster G (ω ∩ (Q:Set E)) x).ncard
  let A := {ω | ClusterWindow G x lo hi ω}
  have hA : MeasurableSet A := measurableSet_clusterWindow G hloc x lo hi
  have hf : Integrable f (law p) := integrable_finite_local Q p _
    (by intro ω; simp only [f,Set.inter_assoc,Set.inter_self])
  have hnon (ω : Set E) : 0 ≤ f ω := by
    apply sub_nonneg.mpr
    exact pow_le_one₀ (sub_nonneg.mpr h.2.2) (by linarith [h.2.1])
  have hbound (ω : Set E) : A.indicator (fun _ => (1:ℝ)/2) ω ≤ f ω := by
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      have hs : cluster G ω x ⊆ (finite_reachBall hloc x hi).toFinset := by
        simpa only [Set.Finite.coe_toFinset] using finite_cluster_subset_reachBall G ω x hω.1 hi hω.2.2.le
      have he := cluster_restrict_incident_of_full G hloc _ ω x hs
      change 1/2 ≤ 1-(1-(h:ℝ))^(cluster G (ω ∩ (Q:Set E)) x).ncard
      rw [he]
      apply one_sub_pow_one_sub_ge_half
      exact hh.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hω.2.1) h.2.1)
    · rw [Set.indicator_of_notMem hω]
      exact hnon ω
  have hib := integral_mono ((integrable_const _).indicator hA) hf hbound
  rw [integral_indicator_const _ hA] at hib
  have he := markedConnection_integral G Q x h p
  change markedConnectionPolynomial G Q x h p = ∫ ω, f ω ∂law p at he
  rw [←he] at hib
  change (law p).real A ≤ 2*markedConnectionPolynomial G Q x h p
  simp only [smul_eq_mul] at hib
  linarith

end MarkedConnectionLaw
end Percolation

end OAI
