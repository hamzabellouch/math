import Mathlib
import OAI.Probability.Ballisticity.Walk.FixedQuenchedKernel

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def SurvivingLane {d : ℕ} (U T A : Set (Lattice d)) : Set (Path d) :=
  Stay U ∩ Hit (U \ T) (T ∩ A)

lemma measurableSet_survivingLane {d : ℕ} (U T A : Set (Lattice d)) :
    MeasurableSet (SurvivingLane U T A) :=
  (measurableSet_stay U).inter (measurableSet_hit _ _)

lemma future_stay_iff {d : ℕ} {U : Set (Lattice d)} {X : Path d} {n : ℕ}
    (hpre : ∀ j < n, X j ∈ U) :
    (fun j => X (n+j)) ∈ Stay U ↔ X ∈ Stay U := by
  constructor
  · intro h j
    by_cases hj : j < n
    · exact hpre j hj
    · have hh := h (j-n)
      simpa only [Nat.add_sub_of_le (by omega : n ≤ j)] using hh
  · intro h j
    exact h (n+j)

lemma future_hit_iff {d : ℕ} {S T A : Set (Lattice d)} (hST : Disjoint S T)
    {X : Path d} {n : ℕ} (hpre : ∀ j < n, X j ∈ S) :
    (fun j => X (n+j)) ∈ Hit S (T ∩ A) ↔ X ∈ Hit S (T ∩ A) := by
  constructor
  · intro h
    obtain ⟨m,hm⟩ := Set.mem_iUnion.mp h
    refine Set.mem_iUnion.mpr ⟨n+m,hm.1,?_⟩
    intro j hj
    by_cases hjn : j < n
    · exact hpre j hjn
    · have hh := hm.2 (j-n) (by omega)
      simpa only [Nat.add_sub_of_le (by omega : n ≤ j)] using hh
  · intro h
    obtain ⟨m,hm⟩ := Set.mem_iUnion.mp h
    have hnm : n ≤ m := by
      by_contra! h
      exact Set.disjoint_left.mp hST (hpre m h) hm.1.1
    refine Set.mem_iUnion.mpr ⟨m-n,?_,?_⟩
    · simpa only [Nat.add_sub_of_le hnm] using hm.1
    · intro j hj
      exact hm.2 (n+j) (by omega)

lemma hit_survival_factorization {d : ℕ} (ω : Environment d) (x : Lattice d)
    (U S V : Set (Lattice d)) (hS : S ⊆ U) :
    quenchedKernel (ω,x) (Hit (S \ V) V ∩ Stay U) =
      ∫⁻ z, quenchedKernel (ω,z) (Stay U) ∂hitKernel (S \ V) V (ω,x) := by
  rw [hitKernel_future ω x Set.disjoint_sdiff_left (fun _ => Stay U)
    (fun _ => measurableSet_stay U)]
  congr 1
  ext X
  simp only [Hit,Set.mem_inter_iff,Set.mem_iUnion]
  constructor
  · rintro ⟨⟨n,hn⟩,hD⟩
    exact ⟨n,hn,fun j => hD (n+j)⟩
  · rintro ⟨n,hn,hD⟩
    exact ⟨⟨n,hn⟩,(future_stay_iff (fun j hj => hS (hn.2 j hj).1)).mp hD⟩

lemma hit_laneError_factorization {d : ℕ} (ω : Environment d) (x : Lattice d)
    (U T A V : Set (Lattice d)) :
    quenchedKernel (ω,x) (Hit ((U \ T) \ V) V ∩ (Stay U \ SurvivingLane U T A)) =
      ∫⁻ z, quenchedKernel (ω,z) (Stay U \ SurvivingLane U T A)
        ∂hitKernel ((U \ T) \ V) V (ω,x) := by
  rw [hitKernel_future ω x Set.disjoint_sdiff_left (fun _ => Stay U \ SurvivingLane U T A)
    (fun _ => (measurableSet_stay U).diff (measurableSet_survivingLane U T A))]
  congr 1
  ext X
  have hh (n : ℕ) (hn : X ∈ HitAt ((U \ T) \ V) V n) :
      (fun j => X (n+j)) ∈ Stay U \ SurvivingLane U T A ↔ X ∈ Stay U \ SurvivingLane U T A := by
    have hd := future_stay_iff (fun j hj => (hn.2 j hj).1.1)
    have he := future_hit_iff (A := A) Set.disjoint_sdiff_left (fun j hj => (hn.2 j hj).1)
    change (_ ∧ ¬(_ ∧ _)) ↔ (_ ∧ ¬(_ ∧ _))
    rw [hd,he]
  simp only [Hit,Set.mem_inter_iff,Set.mem_iUnion]
  constructor
  · rintro ⟨⟨n,hn⟩,hD⟩
    exact ⟨n,hn,(hh n hn).mpr hD⟩
  · rintro ⟨n,hn,hD⟩
    exact ⟨⟨n,hn⟩,(hh n hn).mp hD⟩

lemma hitKernel_ae_target {d : ℕ} (S V : Set (Lattice d)) (z : State d) :
    ∀ᵐ y ∂hitKernel S V z, y ∈ V := by
  apply ae_iff.mpr
  rw [hitKernel_apply]
  have he : V ∩ {a | a ∉ V} = ∅ := by ext a; simp
  rw [he]
  simp only [HitAt,Set.mem_empty_iff_false,false_and,Set.ofPred_false,measure_empty,tsum_zero]

lemma quenched_lowLane_visit_bound {d : ℕ} (ω : Environment d) (x : Lattice d)
    (U T A V : Set (Lattice d))
    (hlow : ∀ z ∈ V, quenchedKernel (ω,z) (Stay U) ≤
      2 * quenchedKernel (ω,z) (Stay U \ SurvivingLane U T A)) :
    quenchedKernel (ω,x) (Hit ((U \ T) \ V) V ∩ Stay U) ≤
      2 * quenchedKernel (ω,x) (Stay U \ SurvivingLane U T A) := by
  rw [hit_survival_factorization ω x U (U \ T) V Set.sdiff_subset]
  calc
    _ ≤ ∫⁻ z, 2 * quenchedKernel (ω,z) (Stay U \ SurvivingLane U T A)
        ∂hitKernel ((U \ T) \ V) V (ω,x) := by
      apply lintegral_mono_ae
      filter_upwards [hitKernel_ae_target ((U \ T) \ V) V (ω,x)] with z hz
      exact hlow z hz
    _ = 2 * quenchedKernel (ω,x)
        (Hit ((U \ T) \ V) V ∩ (Stay U \ SurvivingLane U T A)) := by
      rw [lintegral_const_mul _ (measurable_of_countable _),hit_laneError_factorization]
    _ ≤ _ := mul_le_mul_right (measure_mono Set.inter_subset_right) 2

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma survivingLane_disjoint {d : ℕ} (U T A B : Set (Lattice d)) (hAB : Disjoint A B) :
    Disjoint (SurvivingLane U T A) (SurvivingLane U T B) := by
  apply Set.disjoint_left.mpr
  intro X hA hB
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hA.2
  obtain ⟨m,hm⟩ := Set.mem_iUnion.mp hB.2
  have he : n = m := by
    by_contra h
    exact Set.disjoint_left.mp (hitAt_pairwise_disjoint (S := U \ T) (T := T)
      Set.disjoint_sdiff_left h) ⟨hn.1.1,hn.2⟩ ⟨hm.1.1,hm.2⟩
  subst m
  exact Set.disjoint_left.mp hAB hn.1.2 hm.1.2

lemma measure_low_complement_or {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D A B : Set Ω) (hAB : Disjoint A B) :
    μ D ≤ 2*μ (D \ A) ∨ μ D ≤ 2*μ (D \ B) := by
  have hh : μ D ≤ μ (D \ A)+μ (D \ B) := by
    apply (measure_mono (s := D) (t := (D \ A) ∪ (D \ B)) ?_).trans (measure_union_le _ _)
    intro x hx
    by_cases ha : x ∈ A
    · exact Or.inr ⟨hx,fun hb => Set.disjoint_left.mp hAB ha hb⟩
    · exact Or.inl ⟨hx,ha⟩
  rcases le_total (μ (D \ A)) (μ (D \ B)) with h | h
  · right
    exact (hh.trans (add_le_add h le_rfl)).trans_eq (two_mul _).symm
  · left
    exact (hh.trans (add_le_add le_rfl h)).trans_eq (two_mul _).symm

def PrefixContact {d : ℕ} (S : Set (Lattice d)) : Set (Path d × Path d) :=
  {Z | ∃ n m, Z.1 n = Z.2 m ∧ (∀ j < n, Z.1 j ∈ S) ∧ (∀ j < m, Z.2 j ∈ S)}

lemma measurableSet_prefixContact {d : ℕ} (S : Set (Lattice d)) :
    MeasurableSet (PrefixContact S) := by
  simp only [PrefixContact,Set.ofPred_exists,Set.ofPred_and,Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro m
  refine (measurableSet_eq_fun (by fun_prop) (by fun_prop)).inter ?_
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      ((measurable_pi_apply j).comp measurable_fst) S.to_countable.measurableSet
  · exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      ((measurable_pi_apply j).comp measurable_snd) S.to_countable.measurableSet

lemma prefix_visit_first {d : ℕ} (S V : Set (Lattice d)) (X : Path d)
    {n : ℕ} (hn : X n ∈ V) (hpre : ∀ j < n, X j ∈ S) :
    X ∈ Hit (S \ V) V := by
  classical
  let h : ∃ j, X j ∈ V := ⟨n,hn⟩
  let m := Nat.find h
  have hm : m ≤ n := Nat.find_min' h hn
  refine Set.mem_iUnion.mpr ⟨m,Nat.find_spec h,?_⟩
  intro j hj
  exact ⟨hpre j (hj.trans_le hm),Nat.find_min h hj⟩

lemma quenched_pair_contact_bound {d : ℕ} (ω : Environment d) (x y : Lattice d)
    (U T A B : Set (Lattice d)) (hAB : Disjoint A B) :
    ((quenchedKernel (ω,x)).prod (quenchedKernel (ω,y)))
      (PrefixContact (U \ T) ∩ (Stay U ×ˢ Stay U)) ≤
      2 * (quenchedKernel (ω,x) (Stay U \ SurvivingLane U T A) * quenchedKernel (ω,y) (Stay U) +
        quenchedKernel (ω,x) (Stay U) * quenchedKernel (ω,y) (Stay U \ SurvivingLane U T B)) := by
  let V := fun C : Set (Lattice d) => {z | quenchedKernel (ω,z) (Stay U) ≤
    2*quenchedKernel (ω,z) (Stay U \ SurvivingLane U T C)}
  let E := fun C : Set (Lattice d) => Hit ((U \ T) \ V C) (V C) ∩ Stay U
  have hlow : ∀ z, z ∈ V A ∨ z ∈ V B := fun z =>
    measure_low_complement_or _ _ _ _ (survivingLane_disjoint U T A B hAB)
  have hsub : PrefixContact (U \ T) ∩ (Stay U ×ˢ Stay U) ⊆
      (E A ×ˢ Stay U) ∪ (Stay U ×ˢ E B) := by
    intro Z hZ
    obtain ⟨n,m,he,hpre,hpre'⟩ := hZ.1
    rcases hlow (Z.1 n) with h | h
    · exact Or.inl ⟨⟨prefix_visit_first _ _ _ h hpre,hZ.2.1⟩,hZ.2.2⟩
    · rw [he] at h
      exact Or.inr ⟨hZ.2.1,⟨prefix_visit_first _ _ _ h hpre',hZ.2.2⟩⟩
  have hE (C : Set (Lattice d)) : MeasurableSet (E C) :=
    (measurableSet_hit _ _).inter (measurableSet_stay U)
  calc
    _ ≤ ((quenchedKernel (ω,x)).prod (quenchedKernel (ω,y))) (E A ×ˢ Stay U) +
        ((quenchedKernel (ω,x)).prod (quenchedKernel (ω,y))) (Stay U ×ˢ E B) :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ = quenchedKernel (ω,x) (E A)*quenchedKernel (ω,y) (Stay U) +
        quenchedKernel (ω,x) (Stay U)*quenchedKernel (ω,y) (E B) := by
      rw [Measure.prod_prod,Measure.prod_prod]
    _ ≤ (2*quenchedKernel (ω,x) (Stay U \ SurvivingLane U T A))*quenchedKernel (ω,y) (Stay U) +
        quenchedKernel (ω,x) (Stay U)*(2*quenchedKernel (ω,y) (Stay U \ SurvivingLane U T B)) := by
      apply add_le_add
      · exact mul_le_mul_left (quenched_lowLane_visit_bound ω x U T A (V A) (fun _ hz => hz)) _
      · exact mul_le_mul_right (quenched_lowLane_visit_bound ω y U T B (V B) (fun _ hz => hz)) _
    _ = _ := by ring

lemma shared_pair_contact_bound {d : ℕ} (ν : Measure (Row d)) (x y : Lattice d)
    (U T A B : Set (Lattice d)) (hAB : Disjoint A B) :
    sharedPairLaw ν x y (PrefixContact (U \ T) ∩ (Stay U ×ˢ Stay U)) ≤
      2 * (sharedPairLaw ν x y ((Stay U \ SurvivingLane U T A) ×ˢ Stay U) +
        sharedPairLaw ν x y (Stay U ×ˢ (Stay U \ SurvivingLane U T B))) := by
  have hD := measurableSet_stay U
  have hA := hD.diff (measurableSet_survivingLane U T A)
  have hB := hD.diff (measurableSet_survivingLane U T B)
  conv_lhs => rw [sharedPairLaw,Measure.bind_apply ((measurableSet_prefixContact _).inter (hD.prod hD)) (Kernel.aemeasurable _)]
  rw [sharedPairLaw_rectangle ν x y _ _ hA hD,sharedPairLaw_rectangle ν x y _ _ hD hB]
  have hm (C D : Set (Path d)) (hC : MeasurableSet C) (hD : MeasurableSet D) :
      Measurable (fun ω : Environment d => quenchedKernel (ω,x) C * quenchedKernel (ω,y) D) :=
    ((Kernel.measurable_coe _ hC).comp (measurable_id.prodMk measurable_const)).mul
      ((Kernel.measurable_coe _ hD).comp (measurable_id.prodMk measurable_const))
  rw [← lintegral_add_left (hm _ _ hA hD)]
  rw [← lintegral_const_mul _ (show Measurable (fun ω : Environment d =>
    quenchedKernel (ω,x) (Stay U \ SurvivingLane U T A)*quenchedKernel (ω,y) (Stay U) +
    quenchedKernel (ω,x) (Stay U)*quenchedKernel (ω,y) (Stay U \ SurvivingLane U T B)) from
      (hm _ _ hA hD).add (hm _ _ hD hB))]
  apply lintegral_mono
  intro ω
  dsimp only
  rw [sharedPairKernel,Kernel.prod_apply]
  exact quenched_pair_contact_bound ω x y U T A B hAB

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
