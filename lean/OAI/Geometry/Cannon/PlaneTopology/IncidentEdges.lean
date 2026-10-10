import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.Plane
import OAI.Geometry.Cannon.PlaneTopology.Consecutive

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
namespace CannonEmbeddedArc
open Set Metric unitInterval
open scoped BigOperators

namespace Arc
variable {X : Type*} [MetricSpace X]

theorem repair_local {ι : Type*} [Fintype ι] (E : ι → Arc X)
    (hE : Pairwise (fun e f => Compatible (E e) (E f))) (a : Arc X)
    {B : ℝ} (hB : 0≤B) (hdiam : ∀ e, diam (range (E e))≤B) :
    ∃ b : Arc X, b 0=a 0 ∧ b 1=a 1 ∧
      (∀ e, OrdConnected (b ⁻¹' range (E e))) ∧
      (∀ x∈range b, x∈range a ∨ ∃ e, x∈range (E e)) ∧
      (∀ x∈range b, ∃ y∈range a, dist x y≤B) ∧
      (∀ e, (range b ∩ range (E e)).Nonempty → (range a ∩ range (E e)).Nonempty) ∧
      diam (range b)≤diam (range a)+2*B := by
  classical
  let S := Finset.univ.filter (fun e => (range a ∩ range (E e)).Nonempty)
  obtain ⟨b,h₀,h₁,hconn,hsupp,hcross,_⟩ := repair_finite E S (fun e _ f _ hef => hE hef) a
  have hnew (e : ι) (he : (range b ∩ range (E e)).Nonempty) :
      (range a ∩ range (E e)).Nonempty := by
    by_cases heS : e∈S
    · exact (Finset.mem_filter.mp heS).2
    · have hcomp : ∀ f∈S, Compatible (E f) (E e) := by
        intro f hf
        exact hE (fun h => heS (h ▸ hf))
      exact he.mono (hcross (E e) hcomp)
  have hnear : ∀ x∈range b, ∃ y∈range a, dist x y≤B := by
    intro x hx
    rcases hsupp x hx with hxa|⟨e,he,hxe,y,hya,hye⟩
    · exact ⟨x,hxa,by simpa using hB⟩
    · exact ⟨y,hya,(Metric.dist_le_diam_of_mem (E e).compact_range.isBounded hxe hye).trans
        (hdiam e)⟩
  refine ⟨b,h₀,h₁,?_,?_,hnear,hnew,?_⟩
  · intro e
    by_cases he : e∈S
    · exact hconn e he
    · have hempty : b ⁻¹' range (E e)=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro t ht
        exact he (Finset.mem_filter.mpr ⟨Finset.mem_univ e,
          hnew e ⟨b t,mem_range_self t,ht⟩⟩)
      rw [hempty]
      exact ordConnected_empty
  · intro x hx
    rcases hsupp x hx with h|⟨e,_,he,_⟩
    · exact Or.inl h
    · exact Or.inr ⟨e,he⟩
  · apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro x hx y hy
    obtain ⟨x₀,hx₀,hxx₀⟩ := hnear x hx
    obtain ⟨y₀,hy₀,hyy₀⟩ := hnear y hy
    have hxy₀ := Metric.dist_le_diam_of_mem a.compact_range.isBounded hx₀ hy₀
    have htri := dist_triangle4 x x₀ y₀ y
    rw [dist_comm y₀ y] at htri
    linarith

noncomputable def incidentEdges {ι : Type*} [Fintype ι] (E : ι → Arc X) (a : Arc X) : Finset ι := by
  classical
  exact Finset.univ.filter (fun e => (range a ∩ range (E e)).Nonempty)

lemma original_incidence_count {ι : Type*} [Fintype ι] (E : ι → Arc X) (a : Arc X)
    {B : ℝ} (hB : 0<B) (ha : diam (range a)≤B) (M : ℕ)
    (hcount : ∀ x, intersectionCount E (ball x (2*B))≤M) :
    (incidentEdges E a).card≤M := by
  classical
  have hsub : (Finset.univ.filter (fun e => (range a ∩ range (E e)).Nonempty)) ⊆
      Finset.univ.filter (fun e => (range (E e) ∩ ball (a 0) (2*B)).Nonempty) := by
    intro e he
    obtain ⟨x,hxa,hxe⟩ := (Finset.mem_filter.mp he).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ e,x,hxe,?_⟩
    exact ((Metric.dist_le_diam_of_mem a.compact_range.isBounded hxa (mem_range_self 0)).trans ha).trans_lt
      (by linarith)
  have hc := hcount (a 0)
  rw [intersectionCount_eq_card] at hc
  exact (Finset.card_le_card hsub).trans hc

lemma breakpoints_local {ι : Type*} [Fintype ι] (E : ι → Arc X) (a b : Arc X) (M : ℕ)
    (hM : (incidentEdges E a).card≤M)
    (hconn : ∀ e, OrdConnected (b ⁻¹' range (E e)))
    (hnew : ∀ e, (range b ∩ range (E e)).Nonempty → (range a ∩ range (E e)).Nonempty) :
    ∃ P : Finset I, 0∈P ∧ 1∈P ∧ P.card≤2*M+2 ∧
      ∀ e, (b ⁻¹' range (E e))=∅ ∨ ∃ u∈P, ∃ v∈P, u≤v ∧ b ⁻¹' range (E e)=Icc u v := by
  classical
  let S := Finset.univ.filter (fun e => (range a ∩ range (E e)).Nonempty)
  obtain ⟨P,h₀,h₁,hcard,hP⟩ := finite_breakpoints E S b (fun e _ => hconn e)
  refine ⟨P,h₀,h₁,hcard.trans (by dsimp [S,incidentEdges] at *; omega),?_⟩
  intro e
  by_cases he : e∈S
  · exact hP e he
  · left
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact he (Finset.mem_filter.mpr ⟨Finset.mem_univ e,hnew e ⟨b t,mem_range_self t,ht⟩⟩)

lemma simultaneous_old_breakpoints {ι κ : Type*} (E : ι → Arc X) (A : κ → Arc X)
    (P : κ → Finset I) (p : ℕ) (hP : ∀ i, (P i).card≤p)
    (hunique : ∀ e i j, (range (A i) ∩ range (E e)).Nonempty →
      (range (A j) ∩ range (E e)).Nonempty → i=j) :
    ∃ Q : ι → Finset I, (∀ e, 0∈Q e ∧ 1∈Q e ∧ (Q e).card≤p+2) ∧
      (∀ i e t, E e t∈A i '' (P i : Set I) → t∈Q e) := by
  classical
  have hex (e : ι) : ∃ Q : Finset I, 0∈Q ∧ 1∈Q ∧ Q.card≤p+2 ∧
      ∀ i t, E e t∈A i '' (P i : Set I) → t∈Q := by
    by_cases hmeet : ∃ i, (range (A i) ∩ range (E e)).Nonempty
    · obtain ⟨i,hi⟩ := hmeet
      obtain ⟨Q,h₀,h₁,hcard,hmark⟩ := old_breakpoints (A i) (E e) (P i)
      refine ⟨Q,h₀,h₁,hcard.trans (Nat.add_le_add_right (hP i) 2),?_⟩
      intro j t ht
      have hji : j=i := hunique e j i ⟨E e t,image_subset_range _ _ ht,mem_range_self t⟩ hi
      subst j
      exact hmark t ht
    · refine ⟨{0,1},by simp,by simp,by simp,?_⟩
      intro i t ht
      exact (hmeet ⟨i,E e t,image_subset_range _ _ ht,mem_range_self t⟩).elim
  choose Q hQ using hex
  exact ⟨Q,fun e => ⟨(hQ e).1,(hQ e).2.1,(hQ e).2.2.1⟩,fun i e => (hQ e).2.2.2 i⟩

lemma count_ball_le_one {κ : Type*} [Fintype κ] (A : κ → Arc X) {B : ℝ}
    (hsep : ∀ i j, i≠j → ∀ x∈range (A i), ∀ y∈range (A j), 4*B<dist x y)
    (x : X) : intersectionCount A (ball x (2*B))≤1 := by
  classical
  rw [intersectionCount_eq_card]
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hne
  obtain ⟨y,hy,hry⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨z,hz,hrz⟩ := (Finset.mem_filter.mp hj).2
  have hfar := hsep i j hne y hy z hz
  have ht := dist_triangle y x z
  rw [dist_comm x z] at ht
  change dist y x<2*B at hry
  change dist z x<2*B at hrz
  linarith

lemma intersectionCount_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → Arc X) (e : κ ≃ ι) (S : Set X) :
    intersectionCount (E ∘ e) S=intersectionCount E S := by
  classical
  exact e.sum_comp (fun i => if (range (E i) ∩ S).Nonempty then (1:ℕ) else 0)

lemma support_reindex {ι κ : Type*} (E : ι → Arc X) (e : κ ≃ ι) :
    (⋃ j, range ((E ∘ e) j))=⋃ i, range (E i) := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨e j,hj⟩
  · rintro ⟨i,hi⟩
    exact ⟨e.symm i,by simpa using hi⟩

lemma vertex_reindex {ι κ : Type*} (E : ι → Arc X) (e : κ ≃ ι) (x : X) :
    Vertex (E ∘ e) x ↔ Vertex E x := by
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨e j,hj⟩
  · rintro ⟨i,hi⟩
    exact ⟨e.symm i,by simpa using hi⟩

def stageBound (M : ℕ) : ℕ := M*(2*M+4)^2+(2*M+2)^2

theorem separated_stage {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → Arc X) (A : κ → Arc X) {B : ℝ} (hB : 0<B) (M : ℕ)
    (hE : Pairwise (fun e f => Compatible (E e) (E f)))
    (hEd : ∀ e, diam (range (E e))≤B) (hAd : ∀ i, diam (range (A i))≤B)
    (hcount : ∀ x, intersectionCount E (ball x (2*B))≤M)
    (hsep : ∀ i j, i≠j → ∀ x∈range (A i), ∀ y∈range (A j), 4*B<dist x y) :
    ∃ n : ℕ, ∃ F : Fin n → Arc X,
      Pairwise (fun e f => Compatible (F e) (F f)) ∧
      (⋃ e, range (E e)) ⊆ (⋃ j, range (F j)) ∧
      (∀ x, Vertex E x → Vertex F x) ∧
      (∀ i, Vertex F (A i 0) ∧ Vertex F (A i 1)) ∧
      (∀ i, ∃ b : Arc X, b 0=A i 0 ∧ b 1=A i 1 ∧
        range b ⊆ (⋃ j, range (F j)) ∧ diam (range b)≤3*B) ∧
      (∀ j, diam (range (F j))≤B) ∧
      (∀ x, intersectionCount F (ball x (2*B))≤ stageBound M) ∧
      (⋃ j, range (F j)) ⊆ (⋃ e, range (E e)) ∪ (⋃ i, range (A i)) := by
  classical
  choose A' h₀ h₁ hconn hsupp hnear hnew hdiam using
    fun i => repair_local E hE (A i) hB.le hEd
  have hsep' (i j : κ) (hij : i≠j) :
      ∀ x∈range (A' i), ∀ y∈range (A' j), B<dist x y := by
    apply separated_of_near (A i) (A j) (A' i) (A' j) (hnear i) (hnear j)
    intro x hx y hy
    have hh := hsep i j hij x hx y hy
    linarith
  have hdisj : Pairwise (fun i j => Disjoint (range (A' i)) (range (A' j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    have hh := hsep' i j hij x hi x hj
    simp only [dist_self] at hh
    linarith
  have hunique (e : ι) (i j : κ) (hi : (range (A' i) ∩ range (E e)).Nonempty)
      (hj : (range (A' j) ∩ range (E e)).Nonempty) : i=j := by
    by_contra hij
    exact meets_at_most_one (A' i) (A' j) (E e) (hsep' i j hij) (hEd e) ⟨hi,hj⟩
  choose P hP₀ hP₁ hPcard hinterval using fun i => breakpoints_local E (A i) (A' i) M
    (original_incidence_count E (A i) hB (hAd i) M hcount) (hconn i) (hnew i)
  obtain ⟨Q,hQ,hmark⟩ := simultaneous_old_breakpoints E A' P (2*M+2) hPcard hunique
  have hQcard (e : ι) : (Q e).card≤2*M+4 := by have h := (hQ e).2.2; omega
  let R := RefinementIndex E A' P Q
  let F₀ : R → Arc X := refinementArc E A' P Q
  have hcomp : Pairwise (fun e f => Compatible (F₀ e) (F₀ f)) :=
    refinement_compatible E A' P Q hE hdisj hinterval hmark
  have hsource (i : κ) (z : segments (P i)) (hz : FreeSegment E A' P i z) :
      range (subdivArc (A' i) (P i) z) ⊆ range (A i) :=
    free_segment_original E (A i) (A' i) (P i) z (hinterval i) hz (hsupp i)
  have hcover : (⋃ e, range (E e)) ∪ (⋃ i, range (A' i))=⋃ j, range (F₀ j) :=
    refinement_cover E A' P Q hP₀ hP₁ (fun e => (hQ e).1) (fun e => (hQ e).2.1)
  have hdF (j : R) : diam (range (F₀ j))≤B := by
    rcases j with ⟨e,z⟩|⟨i,z⟩
    · exact (Metric.diam_mono (subdivArc_range_subset (E e) (Q e) z)
        (E e).compact_range.isBounded).trans (hEd e)
    · exact (Metric.diam_mono (hsource i z.val z.property)
        (A i).compact_range.isBounded).trans (hAd i)
  have hcF (x : X) : intersectionCount F₀ (ball x (2*B))≤ stageBound M := by
    have hc := refinement_local_count E A' A P Q hsource (2*M+2) (2*M+4) hPcard hQcard (ball x (2*B))
    have hm := hcount x
    have ha := count_ball_le_one A hsep x
    have ha' : intersectionCount A (ball x (2*B))*(2*M+2)^2 ≤ (2*M+2)^2 := by
      calc
        _ ≤ 1*(2*M+2)^2 := Nat.mul_le_mul_right _ ha
        _ = _ := one_mul _
    exact hc.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hm) ha')
  let e : Fin (Fintype.card R) ≃ R := (Fintype.equivFin R).symm
  let F : Fin (Fintype.card R) → Arc X := F₀ ∘ e
  have hsF : (⋃ j, range (F j))=⋃ j, range (F₀ j) := support_reindex F₀ e
  refine ⟨Fintype.card R,F,fun i j hij => hcomp (fun h => hij (e.injective h)),?_,?_,?_,?_,
    fun j => hdF (e j),?_,?_⟩
  · rw [hsF,← hcover]
    exact subset_union_left
  · intro x hx
    rw [vertex_reindex]
    obtain ⟨j,hj⟩ := hx
    rcases hj with hj|hj
    · rw [← hj]
      exact refinement_old_mark_vertex E A' P Q (fun e => (hQ e).1) (fun e => (hQ e).2.1)
        j (hQ j).1
    · rw [← hj]
      exact refinement_old_mark_vertex E A' P Q (fun e => (hQ e).1) (fun e => (hQ e).2.1)
        j (hQ j).2.1
  · intro i
    rw [vertex_reindex,vertex_reindex,← h₀ i,← h₁ i]
    exact ⟨refinement_new_mark_vertex E A' P Q hmark hP₀ hP₁
      (fun e => (hQ e).1) (fun e => (hQ e).2.1) i (hP₀ i),
      refinement_new_mark_vertex E A' P Q hmark hP₀ hP₁
      (fun e => (hQ e).1) (fun e => (hQ e).2.1) i (hP₁ i)⟩
  · intro i
    refine ⟨A' i,h₀ i,h₁ i,?_,?_⟩
    · rw [hsF,← hcover]
      exact (subset_iUnion (fun i => range (A' i)) i).trans subset_union_right
    · exact (hdiam i).trans (by linarith [hAd i])
  · intro x
    rw [intersectionCount_reindex]
    exact hcF x
  · rw [hsF]
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    rcases j with ⟨j,z⟩|⟨i,z⟩
    · exact Or.inl (mem_iUnion_of_mem j (subdivArc_range_subset (E j) (Q j) z hj))
    · exact Or.inr (mem_iUnion_of_mem i (hsource i z.val z.property hj))

end Arc
end CannonEmbeddedArc

namespace CannonEmbeddedArc
namespace Arc
open Set Metric

variable {X : Type*} [MetricSpace X]

def colorBound : ℕ → ℕ
  | 0 => 0
  | n+1 => stageBound (colorBound n)

theorem colored_stages {κ : Type*} [Fintype κ] (A : κ → Arc X) (color : κ → ℕ)
    {B : ℝ} (hB : 0<B) (hAd : ∀ i, diam (range (A i))≤B)
    (hsep : ∀ i j, i≠j → color i=color j →
      ∀ x∈range (A i), ∀ y∈range (A j), 4*B<dist x y) (N : ℕ) :
    ∃ n : ℕ, ∃ F : Fin n → Arc X,
      Pairwise (fun e f => Compatible (F e) (F f)) ∧
      (∀ i, color i<N → Vertex F (A i 0) ∧ Vertex F (A i 1)) ∧
      (∀ i, color i<N → ∃ b : Arc X, b 0=A i 0 ∧ b 1=A i 1 ∧
        range b ⊆ (⋃ j, range (F j)) ∧ diam (range b)≤3*B) ∧
      (∀ j, diam (range (F j))≤B) ∧
      (∀ x, intersectionCount F (ball x (2*B))≤ colorBound N) ∧
      (⋃ j, range (F j)) ⊆ (⋃ i, range (A i)) := by
  classical
  induction N with
  | zero =>
    refine ⟨0,Fin.elim0,?_,?_,?_,?_,?_,?_⟩
    · intro i; exact i.elim0
    · intro i hi; omega
    · intro i hi; omega
    · intro i; exact i.elim0
    · intro x; simp [intersectionCount,colorBound]
    · simp
  | succ N ih =>
    obtain ⟨k,E,hEc,hEv,hEj,hEd,hEt,hEs⟩ := ih
    let K := {i : κ // color i=N}
    let A₀ : K → Arc X := fun i => A i.val
    have hsep₀ (i j : K) (hne : i≠j) :
        ∀ x∈range (A₀ i), ∀ y∈range (A₀ j), 4*B<dist x y :=
      hsep i.val j.val (fun h => hne (Subtype.ext h)) (i.property.trans j.property.symm)
    obtain ⟨n,F,hFc,hFE,hFv,hFa,hFj,hFd,hFt,hFs⟩ :=
      separated_stage E A₀ hB (colorBound N) hEc hEd (fun i => hAd i.val) hEt hsep₀
    refine ⟨n,F,hFc,?_,?_,hFd,hFt,?_⟩
    · intro i hi
      by_cases h : color i<N
      · exact ⟨hFv _ (hEv i h).1,hFv _ (hEv i h).2⟩
      · exact hFa ⟨i,by omega⟩
    · intro i hi
      by_cases h : color i<N
      · obtain ⟨b,h₀,h₁,hs,hd⟩ := hEj i h
        exact ⟨b,h₀,h₁,hs.trans hFE,hd⟩
      · exact hFj ⟨i,by omega⟩
    · apply hFs.trans
      apply union_subset hEs
      intro x hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion_of_mem i.val hi

theorem colored_arc_graph {κ : Type*} [Fintype κ] (A : κ → Arc X) (N : ℕ)
    (color : κ → Fin N) {B : ℝ} (hB : 0<B) (hAd : ∀ i, diam (range (A i))≤B)
    (hsep : ∀ i j, i≠j → color i=color j →
      ∀ x∈range (A i), ∀ y∈range (A j), 4*B<dist x y) :
    ∃ n : ℕ, ∃ F : Fin n → Arc X,
      Pairwise (fun e f => Compatible (F e) (F f)) ∧
      (∀ i, Vertex F (A i 0) ∧ Vertex F (A i 1)) ∧
      (∀ i, ∃ b : Arc X, b 0=A i 0 ∧ b 1=A i 1 ∧
        range b ⊆ (⋃ j, range (F j)) ∧ diam (range b)≤3*B) ∧
      (∀ j, diam (range (F j))≤B) ∧
      (∀ x, intersectionCount F (ball x (2*B))≤ colorBound N) ∧
      (⋃ j, range (F j)) ⊆ (⋃ i, range (A i)) := by
  obtain ⟨n,F,hc,hv,hj,hd,ht,hs⟩ := colored_stages A (fun i => (color i).val) hB hAd
    (fun i j hij hc => hsep i j hij (Fin.ext hc)) N
  exact ⟨n,F,hc,fun i => hv i (color i).isLt,fun i => hj i (color i).isLt,hd,ht,hs⟩

end Arc
end CannonEmbeddedArc

namespace CannonRegularDisk
open Metric
open Set CannonEmbeddedArc

variable {X : Type*} [TopologicalSpace X]

theorem IsRegularDisk.exists_arc {U : Set X} (hU : IsRegularDisk U)
    {x y : X} (hx : x∈U) (hy : y∈U) (hxy : x≠y) :
    ∃ a : Arc X, a 0=x ∧ a 1=y ∧ range a ⊆ U := by
  obtain ⟨e,he,q,r,hr,rfl⟩ := hU
  obtain ⟨u,hu,rfl⟩ := hx
  obtain ⟨v,hv,rfl⟩ := hy
  have huv : u≠v := fun h => hxy (congrArg e h)
  refine ⟨Arc.mappedSegment e he.continuous he.injective u v huv,by simp,by simp,?_⟩
  exact Arc.mappedSegment_range e he.continuous he.injective u v huv (convex_ball q r) hu hv

end CannonRegularDisk

end
end
end
end
end
end

end OAI
