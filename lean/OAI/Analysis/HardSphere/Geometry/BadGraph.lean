import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.Lattice
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def badGraph (G : SimpleGraph V) (B : Finset V) : SimpleGraph V where
  Adj x y := x∈B ∧ y∈B ∧ G.Adj x y
  symm := ⟨by intro x y h; exact ⟨h.2.1,h.1,h.2.2.symm⟩⟩
  loopless := ⟨by intro x h; exact G.irrefl h.2.2⟩

def badComponent (G : SimpleGraph V) (B : Finset V) (x : V) : Finset V :=
  B.filter (fun y ↦ (badGraph G B).Reachable x y)

def badComponents (G : SimpleGraph V) (B : Finset V) : Finset (Finset V) :=
  B.image (badComponent G B)

lemma mem_badComponent (G : SimpleGraph V) (B : Finset V) (x y : V) :
    y∈badComponent G B x ↔ y∈B ∧ (badGraph G B).Reachable x y :=
  Finset.mem_filter

lemma mem_own_badComponent (G : SimpleGraph V) (B : Finset V) {x : V} (hx : x∈B) :
    x∈badComponent G B x := (mem_badComponent G B x x).mpr ⟨hx,.refl x⟩

lemma badComponent_subset (G : SimpleGraph V) (B : Finset V) (x : V) :
    badComponent G B x ⊆ B := Finset.filter_subset _ _

lemma badComponent_eq_of_reachable (G : SimpleGraph V) (B : Finset V) {x y : V}
    (h : (badGraph G B).Reachable x y) : badComponent G B x=badComponent G B y := by
  ext z
  simp only [mem_badComponent]
  exact ⟨fun ⟨hz,hxz⟩ ↦ ⟨hz,h.symm.trans hxz⟩,
    fun ⟨hz,hyz⟩ ↦ ⟨hz,h.trans hyz⟩⟩

lemma badComponents_disjoint (G : SimpleGraph V) (B : Finset V) :
    (↑(badComponents G B) : Set (Finset V)).PairwiseDisjoint id := by
  rw [Finset.pairwiseDisjoint_iff]
  rintro C hC D hD ⟨z,hz⟩
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hD
  obtain ⟨hzx,hzy⟩ := Finset.mem_inter.mp hz
  exact badComponent_eq_of_reachable G B
    (((mem_badComponent G B x z).mp hzx).2.trans
      ((mem_badComponent G B y z).mp hzy).2.symm)

lemma badComponents_subset (G : SimpleGraph V) (B : Finset V) {C : Finset V}
    (hC : C∈badComponents G B) : C⊆B := by
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hC
  exact badComponent_subset G B x

lemma badComponents_nonempty (G : SimpleGraph V) (B : Finset V) {C : Finset V}
    (hC : C∈badComponents G B) : C.Nonempty := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hC
  exact ⟨x,mem_own_badComponent G B hx⟩

def candidateSets (G : SimpleGraph V) : Finset (Finset V) :=
  Finset.univ.filter (fun F ↦ F.Nonempty ∧
    ∀ x∈F, ∀ y∈F, (badGraph G F).Reachable x y)

lemma reachable_inside_component (G : SimpleGraph V) (B : Finset V) {x y : V}
    (hy : (badGraph G B).Reachable x y) :
    (badGraph G (badComponent G B x)).Reachable x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hy ⊢
  induction hy with
  | refl => exact .refl
  | @tail y z hxy hyz ih =>
    apply ih.tail
    have hreach : (badGraph G B).Reachable x y :=
      (SimpleGraph.reachable_iff_reflTransGen _ _).mpr hxy
    refine ⟨(mem_badComponent G B x y).mpr ⟨hyz.1,hreach⟩,
      (mem_badComponent G B x z).mpr ⟨hyz.2.1,hreach.trans hyz.reachable⟩,hyz.2.2⟩

lemma badComponents_candidate (G : SimpleGraph V) (B : Finset V) :
    badComponents G B ⊆ candidateSets G := by
  intro C hC
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hC
  simp only [candidateSets, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨x,mem_own_badComponent G B hx⟩, ?_⟩
  intro y hy z hz
  have hxy := reachable_inside_component G B ((mem_badComponent G B x y).mp hy).2
  have hxz := reachable_inside_component G B ((mem_badComponent G B x z).mp hz).2
  exact hxy.symm.trans hxz

abbrev ExploreState (V : Type u) := Finset V × Finset V

def frontierHead (s : ExploreState V) (h : s.2.Nonempty) : V := h.choose

omit [Fintype V] [DecidableEq V] in
lemma frontierHead_mem (s : ExploreState V) (h : s.2.Nonempty) :
    frontierHead s h ∈ s.2 := h.choose_spec

def exploreNext (s : ExploreState V) (A : Finset V) : ExploreState V :=
  if h : s.2.Nonempty then
    let x := frontierHead s h
    (insert x s.1, (s.2 ∪ A) \ insert x s.1)
  else s

def exploreStep (G : SimpleGraph V) (F : Finset V) (s : ExploreState V) : ExploreState V :=
  if h : s.2.Nonempty then exploreNext s ((G.neighborFinset (frontierHead s h)) ∩ F)
  else s

def exploration (G : SimpleGraph V) (F : Finset V) (r : V) : ℕ → ExploreState V
  | 0 => (∅,{r})
  | n+1 => exploreStep G F (exploration G F r n)

def ExploreInvariant (G : SimpleGraph V) (F : Finset V) (r : V) (s : ExploreState V) : Prop :=
  s.1 ⊆ F ∧ s.2 ⊆ F ∧ Disjoint s.1 s.2 ∧ r∈s.1∪s.2 ∧
    ∀ x∈s.1, ∀ y∈F, G.Adj x y → y∈s.1∪s.2

omit [Fintype V] in
lemma invariant_initial (G : SimpleGraph V) (F : Finset V) {r : V} (hr : r∈F) :
    ExploreInvariant G F r (∅,{r}) := by
  simp [ExploreInvariant,hr]

lemma invariant_step (G : SimpleGraph V) (F : Finset V) (r : V) (s : ExploreState V)
    (hs : ExploreInvariant G F r s) : ExploreInvariant G F r (exploreStep G F s) := by
  rcases hs with ⟨h₁,h₂,hd,hr,hclosed⟩
  by_cases h : s.2.Nonempty
  · let x := frontierHead s h
    have hx : x∈s.2 := frontierHead_mem s h
    have hxF : x∈F := h₂ hx
    have hseen : s.1∪s.2 ⊆ (insert x s.1) ∪
        ((s.2 ∪ (G.neighborFinset x ∩ F)) \ insert x s.1) := by
      intro y hy
      by_cases hyp : y∈insert x s.1
      · exact Finset.mem_union_left _ hyp
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨Finset.mem_union_left _ (by
            rcases Finset.mem_union.mp hy with hy|hy
            · exact False.elim (hyp (Finset.mem_insert_of_mem hy))
            · exact hy),hyp⟩)
    simp only [exploreStep,dite_eq_left h,exploreNext]
    change ExploreInvariant G F r
      (insert x s.1, (s.2 ∪ (G.neighborFinset x ∩ F)) \ insert x s.1)
    refine ⟨Finset.insert_subset hxF h₁, ?_, (Finset.disjoint_left.mpr (fun _ hy hz ↦ (Finset.mem_sdiff.mp hz).2 hy)), hseen hr, ?_⟩
    · intro y hy
      rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hy).1 with hy|hy
      · exact h₂ hy
      · exact (Finset.mem_inter.mp hy).2
    · intro y hy z hz hyz
      rcases Finset.mem_insert.mp hy with rfl|hy
      · by_cases hzp : z∈insert x s.1
        · exact Finset.mem_union_left _ hzp
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
            ⟨Finset.mem_union_right _ (Finset.mem_inter.mpr
              ⟨(G.mem_neighborFinset x z).mpr hyz,hz⟩),hzp⟩)
      · exact hseen (hclosed y hy z hz hyz)
  · simpa only [exploreStep,dite_eq_right h] using
      (show ExploreInvariant G F r s from ⟨h₁,h₂,hd,hr,hclosed⟩)

lemma exploration_invariant (G : SimpleGraph V) (F : Finset V) {r : V} (hr : r∈F) (n : ℕ) :
    ExploreInvariant G F r (exploration G F r n) := by
  induction n with
  | zero => exact invariant_initial G F hr
  | succ n ih => exact invariant_step G F r _ ih

omit [Fintype V] in
lemma invariant_empty_frontier (G : SimpleGraph V) (F : Finset V) (r : V) (s : ExploreState V)
    (hs : ExploreInvariant G F r s)
    (hconn : ∀ y∈F, (badGraph G F).Reachable r y) (he : s.2=∅) : s.1=F := by
  apply Finset.Subset.antisymm hs.1
  intro y hy
  have hreach := hconn y hy
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => simpa only [he,Finset.union_empty] using hs.2.2.2.1
  | @tail y z _ hyz ih =>
      simpa only [he,Finset.union_empty] using hs.2.2.2.2 y (ih hyz.1) z hyz.2.1 hyz.2.2

lemma exploreStep_card (G : SimpleGraph V) (F : Finset V) (r : V) (s : ExploreState V)
    (hs : ExploreInvariant G F r s) (h : s.2.Nonempty) :
    (exploreStep G F s).1.card=s.1.card+1 := by
  have hx := frontierHead_mem s h
  have hn : frontierHead s h ∉ s.1 := fun hh ↦ Finset.disjoint_left.mp hs.2.2.1 hh hx
  simp only [exploreStep,dite_eq_left h,exploreNext]
  exact Finset.card_insert_of_notMem hn

lemma exploration_covers (G : SimpleGraph V) (F : Finset V) {r : V} (hr : r∈F)
    (hconn : ∀ y∈F, (badGraph G F).Reachable r y) :
    (exploration G F r F.card).1=F := by
  have hprogress (n : ℕ) : n≤(exploration G F r n).1.card ∨ (exploration G F r n).1=F := by
    induction n with
    | zero => exact Or.inl (Nat.zero_le _)
    | succ n ih =>
      have hs := exploration_invariant G F hr n
      by_cases h : (exploration G F r n).2.Nonempty
      · by_cases hc : (exploration G F r n).1=F
        · have hx := frontierHead_mem _ h
          have hp := hs.2.1 hx
          exact False.elim (Finset.disjoint_left.mp hs.2.2.1 (hc.ge hp) hx)
        · refine Or.inl ?_
          obtain hn|hn := ih
          · rw [exploration,exploreStep_card G F r _ hs h]
            omega
          · exact False.elim (hc hn)
      · apply Or.inr
        rw [exploration,exploreStep,dite_eq_right h]
        exact invariant_empty_frontier G F r _ hs hconn (Finset.not_nonempty_iff_eq_empty.mp h)
  rcases hprogress F.card with hc|hc
  · exact Finset.eq_of_subset_of_card_le (exploration_invariant G F hr F.card).1 hc
  · exact hc

def possibleSteps (G : SimpleGraph V) (s : ExploreState V) : Finset (ExploreState V) :=
  if h : s.2.Nonempty then
    (G.neighborFinset (frontierHead s h)).powerset.image (exploreNext s)
  else {s}

lemma exploreStep_mem_possible (G : SimpleGraph V) (F : Finset V) (s : ExploreState V) :
    exploreStep G F s ∈ possibleSteps G s := by
  by_cases h : s.2.Nonempty
  · simp only [exploreStep,possibleSteps,dite_eq_left h]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_powerset.mpr (Finset.inter_subset_left),rfl⟩
  · simp only [exploreStep,possibleSteps,dite_eq_right h,Finset.mem_singleton]

def possibleStates (G : SimpleGraph V) (r : V) : ℕ → Finset (ExploreState V)
  | 0 => {(∅,{r})}
  | n+1 => (possibleStates G r n).biUnion (possibleSteps G)

lemma exploration_mem_possible (G : SimpleGraph V) (F : Finset V) (r : V) (n : ℕ) :
    exploration G F r n ∈ possibleStates G r n := by
  induction n with
  | zero => simp only [exploration,possibleStates,Finset.mem_singleton]
  | succ n ih => exact Finset.mem_biUnion.mpr ⟨_,ih,exploreStep_mem_possible G F _⟩

lemma possibleSteps_card_le (G : SimpleGraph V) (Δ : ℕ)
    (hΔ : ∀ x, G.degree x≤Δ) (s : ExploreState V) :
    (possibleSteps G s).card ≤ 2^Δ := by
  by_cases h : s.2.Nonempty
  · simp only [possibleSteps,dite_eq_left h]
    calc
      _ ≤ (G.neighborFinset (frontierHead s h)).powerset.card := Finset.card_image_le
      _ = 2^(G.degree (frontierHead s h)) := by rw [Finset.card_powerset]; rfl
      _ ≤ 2^Δ := Nat.pow_le_pow_right (by omega) (hΔ _)
  · simp only [possibleSteps,dite_eq_right h,Finset.card_singleton]
    exact Nat.one_le_pow _ _ (by omega)

lemma possibleStates_card_le (G : SimpleGraph V) (Δ : ℕ)
    (hΔ : ∀ x, G.degree x≤Δ) (r : V) (n : ℕ) :
    (possibleStates G r n).card ≤ (2^Δ)^n := by
  induction n with
  | zero => simp only [possibleStates,Finset.card_singleton,pow_zero,le_refl]
  | succ n ih =>
    calc
      _ ≤ ∑ s∈possibleStates G r n, (possibleSteps G s).card := Finset.card_biUnion_le
      _ ≤ ∑ _s∈possibleStates G r n, 2^Δ :=
        Finset.sum_le_sum fun s _ ↦ possibleSteps_card_le G Δ hΔ s
      _ = (possibleStates G r n).card * 2^Δ := by simp
      _ ≤ (2^Δ)^n * 2^Δ := Nat.mul_le_mul_right _ ih
      _ = (2^Δ)^(n+1) := (pow_succ _ _).symm

def rootedAnimals (G : SimpleGraph V) (r : V) (m : ℕ) : Finset (Finset V) :=
  Finset.univ.filter (fun F ↦ r∈F ∧ F.card=m ∧ ∀ y∈F, (badGraph G F).Reachable r y)

lemma rootedAnimals_card_le (G : SimpleGraph V) (Δ : ℕ)
    (hΔ : ∀ x, G.degree x≤Δ) (r : V) (m : ℕ) :
    (rootedAnimals G r m).card ≤ (2^Δ)^m := by
  have hsub : rootedAnimals G r m ⊆ (possibleStates G r m).image Prod.fst := by
    intro F hF
    simp only [rootedAnimals,Finset.mem_filter,Finset.mem_univ,true_and] at hF
    rcases hF with ⟨hr,hm,hconn⟩
    refine Finset.mem_image.mpr ⟨exploration G F r m, exploration_mem_possible G F r m, ?_⟩
    rw [← hm]
    exact exploration_covers G F hr hconn
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans
    (possibleStates_card_le G Δ hΔ r m))

omit [Fintype V] [DecidableEq V] in
lemma badGraph_mono (G : SimpleGraph V) {S F : Finset V} (h : S⊆F) :
    badGraph G S ≤ badGraph G F := by
  intro x y hxy
  exact ⟨h hxy.1,h hxy.2.1,hxy.2.2⟩

omit [Fintype V] in
lemma internal_boundary (G : SimpleGraph V) (F S : Finset V) {r y : V}
    (hr : r∈S) (hy : y∉S) (hp : (badGraph G F).Reachable r y) :
    ∃ x∈S, ∃ z∈F, z∉S ∧ G.Adj x z := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hp
  induction hp with
  | refl => exact False.elim (hy hr)
  | @tail y z _ hyz ih =>
      by_cases h : y∈S
      · exact ⟨y,h,z,hyz.2.1,hy,hyz.2.2⟩
      · exact ih h

omit [Fintype V] in
lemma connected_insert (G : SimpleGraph V) (S : Finset V) (r : V)
    (hconn : ∀ y∈S, (badGraph G S).Reachable r y)
    {x z : V} (hx : x∈S) (hxz : G.Adj x z) :
    ∀ y∈insert z S, (badGraph G (insert z S)).Reachable r y := by
  have hmono := badGraph_mono G (Finset.subset_insert z S)
  intro y hy
  rcases Finset.mem_insert.mp hy with he|hy
  · subst y
    exact ((hconn x hx).mono hmono).trans
      (show (badGraph G (insert z S)).Adj x z from
        ⟨Finset.mem_insert_of_mem hx,Finset.mem_insert_self _ _,hxz⟩).reachable
  · exact (hconn y hy).mono hmono

lemma exists_rooted_subanimal (G : SimpleGraph V) (F : Finset V) {r : V}
    (hr : r∈F) (hconn : ∀ y∈F, (badGraph G F).Reachable r y)
    (m : ℕ) (hm : 1 ≤ m) (hmF : m ≤ F.card) :
    ∃ S⊆F, S∈rootedAnimals G r m := by
  have hex (k : ℕ) (hk : k+1≤F.card) :
      ∃ S⊆F, r∈S ∧ S.card=k+1 ∧ ∀ y∈S, (badGraph G S).Reachable r y := by
    induction k with
    | zero =>
      refine ⟨{r},Finset.singleton_subset_iff.mpr hr,Finset.mem_singleton_self _,by simp,?_⟩
      intro y hy
      have : y=r := Finset.mem_singleton.mp hy
      subst y
      exact .refl r
    | succ k ih =>
      obtain ⟨S,hSF,hrS,hcard,hSconn⟩ := ih (by omega)
      have hlt : S.card<F.card := by omega
      obtain ⟨y,hyF,hyS⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      obtain ⟨x,hx,z,hzF,hzS,hxz⟩ := internal_boundary G F S hrS hyS (hconn y hyF)
      refine ⟨insert z S,Finset.insert_subset hzF hSF,Finset.mem_insert_of_mem hrS,
        by rw [Finset.card_insert_of_notMem hzS,hcard],connected_insert G S r hSconn hx hxz⟩
  obtain ⟨S,hS,hrS,hc,hconnS⟩ := hex (m-1) (by omega)
  refine ⟨S,hS,?_⟩
  simp only [rootedAnimals,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨hrS,by omega,hconnS⟩

omit [Fintype V] in
lemma prod_ite_mem (A B : Finset V) (w : V → ℝ≥0∞) :
    (∏ x∈A, if x∈B then w x else 0) = if A⊆B then ∏ x∈A, w x else 0 := by
  by_cases h : A⊆B
  · simp only [ite_eq_left h]
    exact Finset.prod_congr rfl fun x hx ↦ ite_eq_left (h hx)
  · rw [ite_eq_right h]
    obtain ⟨x,hx,hxb⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hx (ite_eq_right hxb)

def JointBadLaw (μ : PMF (Finset V)) (p : ℝ≥0∞) : Prop :=
  ∀ A : Finset V, (∑' B, if A⊆B then μ B else 0) ≤ p^A.card

omit [Fintype V] in

lemma component_event_bound (μ : PMF (Finset V)) (p : ℝ≥0∞)
    (hbad : JointBadLaw μ p) (K : Finset V → Finset (Finset V))
    (hdisj : ∀ B, (↑(K B) : Set (Finset V)).PairwiseDisjoint id)
    (hsub : ∀ B F, F∈K B → F⊆B) (A : Finset (Finset V)) :
    (∑' B, if A⊆K B then μ B else 0) ≤ ∏ F∈A, p^F.card := by
  by_cases hex : ∃ B, A⊆K B
  · obtain ⟨B₀,hB₀⟩ := hex
    have hd : (↑A : Set (Finset V)).PairwiseDisjoint id :=
      by
      intro C hC D hD hCD
      exact hdisj B₀ (hB₀ hC) (hB₀ hD) hCD
    have hc : (A.biUnion id).card = ∑ F∈A, F.card := Finset.card_biUnion hd
    calc
      _ ≤ ∑' B, if A.biUnion id⊆B then μ B else 0 := by
        apply ENNReal.tsum_le_tsum
        intro B
        by_cases hB : A⊆K B
        · have hu : A.biUnion id⊆B := by
            intro x hx
            obtain ⟨F,hF,hxF⟩ := Finset.mem_biUnion.mp hx
            exact hsub B F (hB hF) hxF
          simp only [ite_eq_left hB,ite_eq_left hu]
          exact le_rfl
        · simp only [ite_eq_right hB]
          exact zero_le
      _ ≤ p^(A.biUnion id).card := hbad _
      _ = ∏ F∈A, p^F.card := by rw [hc,Finset.prod_pow_eq_pow_sum]
  · have hz : ∀ B, ¬ A⊆K B := by simpa only [not_exists] using hex
    simp only [ite_eq_right (hz _),tsum_zero]
    exact zero_le

theorem environment_product_bound (μ : PMF (Finset V)) (p : ℝ≥0∞)
    (hbad : JointBadLaw μ p) (K : Finset V → Finset (Finset V))
    (hdisj : ∀ B, (↑(K B) : Set (Finset V)).PairwiseDisjoint id)
    (hsub : ∀ B F, F∈K B → F⊆B) (C : Finset (Finset V))
    (hC : ∀ B, K B⊆C) (w : Finset V → ℝ≥0∞) :
    (∑' B, μ B * ∏ F∈K B, (1+w F)) ≤ ∏ F∈C, (1+p^F.card*w F) := by
  have hp (B : Finset V) : (∏ F∈K B, (1+w F)) =
      ∏ F∈C, (1+if F∈K B then w F else 0) := by
    calc
      _ = ∏ F∈K B, (1+if F∈K B then w F else 0) :=
        Finset.prod_congr rfl fun F hF ↦ by rw [ite_eq_left hF]
      _ = _ := Finset.prod_subset (hC B) (by
        intro F _ hF
        simp only [ite_eq_right hF,add_zero])
  simp_rw [hp,Finset.prod_one_add,Finset.mul_sum]
  rw [tsum_fintype,Finset.sum_comm]
  apply Finset.sum_le_sum
  intro A _
  rw [← tsum_fintype (L := .unconditional _) (fun B : Finset V ↦ μ B * ∏ i∈A, if i∈K B then w i else 0)]
  simp_rw [prod_ite_mem]
  have he : (∑' B, μ B * if A⊆K B then ∏ F∈A, w F else 0) =
      (∑' B, if A⊆K B then μ B else 0) * ∏ F∈A,w F := by
    rw [← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro B
    split_ifs <;> simp
  rw [he,Finset.prod_mul_distrib]
  exact mul_le_mul' (component_event_bound μ p hbad K hdisj hsub A) le_rfl

end HardSphere.Lattice
end

end OAI
