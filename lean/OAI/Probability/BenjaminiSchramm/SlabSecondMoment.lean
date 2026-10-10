import OAI.Probability.BenjaminiSchramm.LayerFrontierGeometry
import OAI.Probability.UnimodularPercolation.Clusters.KernelMoments

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma disjointOccurrence_restrict (I : Set E) (A B : Set (Set E)) :
    (fun ω : Set E => ω ∩ I) ⁻¹' DisjointOccurrence A B ⊆
      DisjointOccurrence ((fun ω : Set E => ω ∩ I) ⁻¹' A)
        ((fun ω : Set E => ω ∩ I) ⁻¹' B) := by
  rintro ω ⟨s,t,hs,ht,hd,ha,hb⟩
  have hsI : (s : Set E) ⊆ I := fun e he => (hs he).2
  have htI : (t : Set E) ⊆ I := fun e he => (ht he).2
  refine ⟨s,t,fun e he => (hs he).1,fun e he => (ht he).1,hd,?_,?_⟩
  · change (s : Set E) ∩ I ∈ A
    rwa [Set.inter_eq_self_of_subset_left hsI]
  · change (t : Set E) ∩ I ∈ B
    rwa [Set.inter_eq_self_of_subset_left htI]

lemma conn_restricted_three_disjoint_arms (I : Set E) (ω : Set E) (x y z : V)
    (hxy : Conn G (ω ∩ I) x y) (hxz : Conn G (ω ∩ I) x z) :
    ∃ w, ω ∈ DisjointOccurrence {η | Conn G (η ∩ I) x w}
      (DisjointOccurrence {η | Conn G (η ∩ I) w y} {η | Conn G (η ∩ I) w z}) := by
  obtain ⟨w,hw⟩ := conn_three_disjoint_arms G (ω ∩ I) x y z hxy hxz
  refine ⟨w,?_⟩
  have hh := disjointOccurrence_restrict I {η | Conn G η x w}
    (DisjointOccurrence {η | Conn G η w y} {η | Conn G η w z}) hw
  exact disjointOccurrence_mono (Set.Subset.refl _)
    (disjointOccurrence_restrict I _ _) hh

lemma finiteWitness_conn_restricted (I : Set E) (x y : V) :
    FiniteWitness {ω | Conn G (ω ∩ I) x y} := by
  intro ω hω
  obtain ⟨s,hs,hconn⟩ := finiteWitness_conn G x y (ω ∩ I) hω
  refine ⟨s,fun e he => (hs he).1,?_⟩
  have hsub : (s : Set E) ⊆ (s : Set E) ∩ I := fun e he => ⟨he,(hs he).2⟩
  exact conn_mono G hsub hconn

lemma restricted_three_arm_bound [Countable V] [Countable E]
    (I : Set E) (p : unitInterval) (x y z : V) :
    law p {ω | Conn G (ω ∩ I) x y ∧ Conn G (ω ∩ I) x z} ≤
      ∑' w, law p {ω | Conn G (ω ∩ I) x w} *
        law p {ω | Conn G (ω ∩ I) w y} * law p {ω | Conn G (ω ∩ I) w z} := by
  let C := fun a b : V => {ω : Set E | Conn G (ω ∩ I) a b}
  have hup (a b : V) : IsUpperSet (C a b) :=
    fun _ _ h hconn => conn_mono G (Set.inter_subset_inter_left _ h) hconn
  have hf (a b : V) : FiniteWitness (C a b) := finiteWitness_conn_restricted G I a b
  have hb (w : V) : law p (DisjointOccurrence (C x w) (DisjointOccurrence (C w y) (C w z))) ≤
      law p (C x w)*law p (C w y)*law p (C w z) := by
    calc
      _ ≤ law p (C x w)*law p (DisjointOccurrence (C w y) (C w z)) :=
        bk_ennreal p _ _ (hup x w) (disjointOccurrence_upper _ _) (hf x w)
          (finiteWitness_disjointOccurrence _ _)
      _ ≤ law p (C x w)*(law p (C w y)*law p (C w z)) :=
        mul_le_mul' le_rfl (bk_ennreal p _ _ (hup w y) (hup w z) (hf w y) (hf w z))
      _ = _ := (mul_assoc _ _ _).symm
  calc
    _ ≤ law p (⋃ w, DisjointOccurrence (C x w) (DisjointOccurrence (C w y) (C w z))) := by
      apply measure_mono
      intro ω hω
      obtain ⟨w,hw⟩ := conn_restricted_three_disjoint_arms G I ω x y z hω.1 hω.2
      exact Set.mem_iUnion.mpr ⟨w,hw⟩
    _ ≤ ∑' w, law p (DisjointOccurrence (C x w) (DisjointOccurrence (C w y) (C w z))) :=
      measure_iUnion_le _
    _ ≤ _ := ENNReal.tsum_le_tsum hb

lemma lintegral_restrictedLayerCount [Countable V] [Countable E]
    (I : Set E) (A : Set V) (p : unitInterval) (x : V) :
    (∫⁻ ω, restrictedLayerCount G I A ω x ∂law p) =
      ∑' y, if y ∈ A then law p {ω | Conn G (ω ∩ I) x y} else 0 := by
  unfold restrictedLayerCount
  have hm (y : V) : Measurable (fun ω : Set E =>
      if y ∈ A ∧ Conn G (ω ∩ I) x y then (1 : ℝ≥0∞) else 0) := by
    have hi : Measurable (fun ω : Set E => ω ∩ I) :=
      measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
    exact Measurable.ite (measurable_const.and
      ((measurableSet_conn G x y).mem.comp hi)).setOf measurable_const measurable_const
  rw [lintegral_tsum (fun y => (hm y).aemeasurable)]
  apply tsum_congr
  intro y
  by_cases hy : y ∈ A
  · simp only [hy,true_and,ite_true]
    have hi : Measurable (fun ω : Set E => ω ∩ I) :=
      measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
    have hset : MeasurableSet {ω : Set E | Conn G (ω ∩ I) x y} :=
      (measurableSet_conn G x y).preimage hi
    simpa only [Set.indicator,Pi.one_apply,Set.mem_ofPred_eq] using
      lintegral_indicator_one (μ := law p) hset
  · simp only [hy,false_and,ite_false,lintegral_zero]

lemma restrictedLayerCount_mul (I : Set E) (A B : Set V) (ω : Set E) (x : V) :
    restrictedLayerCount G I A ω x * restrictedLayerCount G I B ω x =
      ∑' y, ∑' z, if y ∈ A ∧ z ∈ B ∧ Conn G (ω ∩ I) x y ∧
        Conn G (ω ∩ I) x z then (1 : ℝ≥0∞) else 0 := by
  unfold restrictedLayerCount
  rw [←ENNReal.tsum_mul_right]
  apply tsum_congr
  intro y
  rw [←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro z
  split_ifs <;> simp_all

lemma lintegral_restrictedLayerCount_mul [Countable V] [Countable E]
    (I : Set E) (A B : Set V) (p : unitInterval) (x : V) :
    (∫⁻ ω, restrictedLayerCount G I A ω x*restrictedLayerCount G I B ω x ∂law p) =
      ∑' y, ∑' z, if y ∈ A ∧ z ∈ B then law p
        {ω | Conn G (ω ∩ I) x y ∧ Conn G (ω ∩ I) x z} else 0 := by
  have hi : Measurable (fun ω : Set E => ω ∩ I) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  have hset (y z : V) : MeasurableSet
      {ω : Set E | Conn G (ω ∩ I) x y ∧ Conn G (ω ∩ I) x z} :=
    ((measurableSet_conn G x y).preimage hi).inter ((measurableSet_conn G x z).preimage hi)
  have hm (y z : V) : Measurable (fun ω : Set E =>
      if y ∈ A ∧ z ∈ B ∧ Conn G (ω ∩ I) x y ∧ Conn G (ω ∩ I) x z
      then (1 : ℝ≥0∞) else 0) := by
    by_cases h : y ∈ A ∧ z ∈ B
    · simpa only [←and_assoc,h,true_and] using
        Measurable.ite (hset y z) measurable_const measurable_const
    · have he : (fun ω : Set E => if y ∈ A ∧ z ∈ B ∧ Conn G (ω ∩ I) x y ∧
          Conn G (ω ∩ I) x z then (1 : ℝ≥0∞) else 0) = fun _ => 0 := by
        funext ω
        exact ite_eq_right (by tauto)
      rw [he]
      exact measurable_const
  simp_rw [restrictedLayerCount_mul]
  rw [lintegral_tsum (fun y => (Measurable.tsum (hm y)).aemeasurable)]
  apply tsum_congr
  intro y
  rw [lintegral_tsum (fun z => (hm y z).aemeasurable)]
  apply tsum_congr
  intro z
  by_cases h : y ∈ A ∧ z ∈ B
  · simp only [←and_assoc,h,true_and,ite_true]
    simpa only [Set.indicator,Pi.one_apply,Set.mem_ofPred_eq] using
      lintegral_indicator_one (μ := law p) (hset y z)
  · simp only [ite_eq_right h]
    have he : (fun ω : Set E => if y ∈ A ∧ z ∈ B ∧ Conn G (ω ∩ I) x y ∧
        Conn G (ω ∩ I) x z then (1 : ℝ≥0∞) else 0) = fun _ => 0 := by
      funext ω
      exact ite_eq_right (by tauto)
    rw [he,lintegral_zero]

theorem restricted_layer_second_moment [Countable V] [Countable E]
    (I : Set E) (A B : Set V) (p : unitInterval) (x : V) :
    (∫⁻ ω, restrictedLayerCount G I A ω x*restrictedLayerCount G I B ω x ∂law p) ≤
      ∑' w, law p {ω | Conn G (ω ∩ I) x w} *
        (∫⁻ ω, restrictedLayerCount G I A ω w ∂law p) *
          (∫⁻ ω, restrictedLayerCount G I B ω w ∂law p) := by
  simp_rw [lintegral_restrictedLayerCount_mul,lintegral_restrictedLayerCount]
  calc
    _ ≤ ∑' y, ∑' z, ∑' w, law p {ω | Conn G (ω ∩ I) x w} *
        (if y ∈ A then law p {ω | Conn G (ω ∩ I) w y} else 0) *
        (if z ∈ B then law p {ω | Conn G (ω ∩ I) w z} else 0) := by
      apply ENNReal.tsum_le_tsum
      intro y
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases h : y ∈ A ∧ z ∈ B
      · simp only [ite_eq_left h,ite_eq_left h.1,ite_eq_left h.2]
        exact restricted_three_arm_bound G I p x y z
      · simp only [ite_eq_right h]
        exact bot_le
    _ = ∑' w, ∑' y, ∑' z, law p {ω | Conn G (ω ∩ I) x w} *
        (if y ∈ A then law p {ω | Conn G (ω ∩ I) w y} else 0) *
        (if z ∈ B then law p {ω | Conn G (ω ∩ I) w z} else 0) := by
      rw [show (∑' y, ∑' z, ∑' w, law p {ω | Conn G (ω ∩ I) x w} *
          (if y ∈ A then law p {ω | Conn G (ω ∩ I) w y} else 0) *
          (if z ∈ B then law p {ω | Conn G (ω ∩ I) w z} else 0)) =
        ∑' y, ∑' w, ∑' z, law p {ω | Conn G (ω ∩ I) x w} *
          (if y ∈ A then law p {ω | Conn G (ω ∩ I) w y} else 0) *
          (if z ∈ B then law p {ω | Conn G (ω ∩ I) w z} else 0) from
          tsum_congr (fun _ => ENNReal.tsum_comm),ENNReal.tsum_comm]
    _ = _ := by simp_rw [ENNReal.tsum_mul_left,ENNReal.tsum_mul_right,ENNReal.tsum_mul_left]

end Percolation.BenjaminiSchramm

end

end OAI
