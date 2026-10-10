import OAI.Combinatorics.ListHadwiger.DistrictPaths

namespace OAI

namespace LinearListHadwiger
open SimpleGraph

namespace Density
variable {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def darts (S : Finset V) : Finset (V × V) :=
  (S ×ˢ S).filter (fun e => G.Adj e.1 e.2)

def neighbors (S : Finset V) (v : V) : Finset V := S.filter (G.Adj v)

@[simp] lemma mem_darts {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {S : Finset V} {e : V × V} :
    e ∈ darts G S ↔ e.1 ∈ S ∧ e.2 ∈ S ∧ G.Adj e.1 e.2 := by
  simp [darts, and_assoc]

@[simp] lemma mem_neighbors {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {S : Finset V} {v w : V} :
    w ∈ neighbors G S v ↔ w ∈ S ∧ G.Adj v w := by simp [neighbors]

lemma darts_mono {S T : Finset V} (h : S ⊆ T) : darts G S ⊆ darts G T := by
  intro e he
  obtain ⟨hx,hy,ha⟩ := (mem_darts G).mp he
  exact (mem_darts G).mpr ⟨h hx,h hy,ha⟩

lemma darts_card_le (S : Finset V) : (darts G S).card ≤ S.card * (S.card - 1) := by
  calc
    (darts G S).card ≤ S.offDiag.card := Finset.card_le_card (by
      intro e he
      obtain ⟨hx,hy,ha⟩ := (mem_darts G).mp he
      exact Finset.mem_offDiag.mpr ⟨hx,hy,ha.ne⟩)
    _ = _ := by simp [Finset.offDiag_card, Nat.mul_sub_left_distrib]

lemma darts_erase {S : Finset V} {v : V} (hv : v ∈ S) :
    (darts G S).card = (darts G (S.erase v)).card + 2 * (neighbors G S v).card := by
  let A := (neighbors G S v).image (fun w => (v,w))
  let B := (neighbors G S v).image (fun w => (w,v))
  have hA : A.card = (neighbors G S v).card :=
    Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)
  have hB : B.card = (neighbors G S v).card :=
    Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)
  have hDA : Disjoint (darts G (S.erase v)) A := by
    apply Finset.disjoint_left.mpr
    intro e he hA
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hA
    exact (Finset.mem_erase.mp ((mem_darts G).mp he).1).1 rfl
  have hDB : Disjoint (darts G (S.erase v)) B := by
    apply Finset.disjoint_left.mpr
    intro e he hB
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hB
    exact (Finset.mem_erase.mp ((mem_darts G).mp he).2.1).1 rfl
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨z,hz,heq⟩ := Finset.mem_image.mp hf
    have h : v = w := congrArg Prod.snd heq
    exact ((mem_neighbors G).mp hw).2.ne h
  have heq : darts G S = darts G (S.erase v) ∪ A ∪ B := by
    ext ⟨x,y⟩
    simp only [Finset.mem_union]
    constructor
    · intro h
      obtain ⟨hx,hy,ha⟩ := (mem_darts G).mp h
      by_cases hxv : x = v
      · subst x
        exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨y,(mem_neighbors G).mpr ⟨hy,ha⟩,rfl⟩))
      by_cases hyv : y = v
      · subst y
        exact Or.inr (Finset.mem_image.mpr ⟨x,(mem_neighbors G).mpr ⟨hx,ha.symm⟩,rfl⟩)
      exact Or.inl (Or.inl ((mem_darts G).mpr
        ⟨Finset.mem_erase.mpr ⟨hxv,hx⟩,Finset.mem_erase.mpr ⟨hyv,hy⟩,ha⟩))
    · rintro ((h | h) | h)
      · exact darts_mono G (Finset.erase_subset _ _) h
      · obtain ⟨w,hw,heq⟩ := Finset.mem_image.mp h
        rw [← heq]
        exact (mem_darts G).mpr ⟨hv,((mem_neighbors G).mp hw).1,((mem_neighbors G).mp hw).2⟩
      · obtain ⟨w,hw,heq⟩ := Finset.mem_image.mp h
        rw [← heq]
        exact (mem_darts G).mpr ⟨((mem_neighbors G).mp hw).1,hv,((mem_neighbors G).mp hw).2.symm⟩
  rw [heq,Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hDB,hAB⟩),
    Finset.card_union_of_disjoint hDA,hA,hB]
  omega

lemma darts_separator {S A Z B : Finset V} (h : SeparatorSplit G S A Z B) :
    (darts G S).card ≤ (darts G (A ∪ Z)).card + (darts G (B ∪ Z)).card := by
  apply (Finset.card_le_card (show darts G S ⊆ darts G (A ∪ Z) ∪ darts G (B ∪ Z) from ?_)).trans
    (Finset.card_union_le _ _)
  intro e he
  obtain ⟨hx,hy,ha⟩ := (mem_darts G).mp he
  rw [← h.union_eq] at hx hy
  simp only [Finset.mem_union] at hx hy ⊢
  rcases hx with (hx | hx) | hx <;> rcases hy with (hy | hy) | hy
  · exact Or.inl ((mem_darts G).mpr ⟨Finset.mem_union_left _ hx,Finset.mem_union_left _ hy,ha⟩)
  · exact Or.inl ((mem_darts G).mpr ⟨Finset.mem_union_left _ hx,Finset.mem_union_right _ hy,ha⟩)
  · exact (h.anticomplete _ hx _ hy ha).elim
  · exact Or.inl ((mem_darts G).mpr ⟨Finset.mem_union_right _ hx,Finset.mem_union_left _ hy,ha⟩)
  · exact Or.inl ((mem_darts G).mpr ⟨Finset.mem_union_right _ hx,Finset.mem_union_right _ hy,ha⟩)
  · exact Or.inr ((mem_darts G).mpr ⟨Finset.mem_union_right _ hx,Finset.mem_union_left _ hy,ha⟩)
  · exact (h.anticomplete _ hy _ hx ha.symm).elim
  · exact Or.inr ((mem_darts G).mpr ⟨Finset.mem_union_left _ hx,Finset.mem_union_right _ hy,ha⟩)
  · exact Or.inr ((mem_darts G).mpr ⟨Finset.mem_union_left _ hx,Finset.mem_union_left _ hy,ha⟩)

theorem connectivity_of_density (S : Finset V) {k : ℕ} (hk : 1 ≤ k)
    (hedges : 4*k*S.card < (darts G S).card) :
    ∃ T ⊆ S, KConnectedOn G T k := by
  classical
  have hbound := darts_card_le G S
  have hpos : 0 < S.card := by
    by_contra hn
    have hz : S.card = 0 := by omega
    simp only [hz, Nat.zero_mul] at hbound hedges
    omega
  have hlarge : 2*k ≤ S.card := by
    have hh : S.card - 1 ≤ S.card := Nat.sub_le _ _
    nlinarith
  let good := S.powerset.filter (fun T => 2*k ≤ T.card ∧ 4*k*(T.card-k) < (darts G T).card)
  have hSgood : S ∈ good := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _),hlarge,?_⟩
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) hedges
  obtain ⟨H,hHg,hmin⟩ := Finset.exists_min_image good Finset.card ⟨S,hSgood⟩
  obtain ⟨hHS,hHsize,hHedges⟩ : H ⊆ S ∧ 2*k ≤ H.card ∧
      4*k*(H.card-k) < (darts G H).card := by
    simpa only [good,Finset.mem_filter,Finset.mem_powerset,and_assoc] using hHg
  have hminimal (T : Finset V) (hTH : T ⊆ H) (hTk : 2*k ≤ T.card)
      (hcard : T.card < H.card) : (darts G T).card ≤ 4*k*(T.card-k) := by
    by_contra hn
    have hgood : T ∈ good := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (hTH.trans hHS),hTk,by omega⟩
    have := hmin T hgood
    omega
  have hHsize' : 2*k < H.card := by
    have hb := darts_card_le G H
    have hsub : H.card - 1 ≤ H.card := Nat.sub_le _ _
    by_contra hn
    have heq : H.card = 2*k := by omega
    have heq' : H.card - k = k := by omega
    rw [heq'] at hHedges
    nlinarith
  have hdegree (v : V) (hv : v ∈ H) : 2*k < (neighbors G H v).card := by
    have heq := Finset.card_erase_add_one hv
    have hd := darts_erase G hv
    have hb := hminimal (H.erase v) (Finset.erase_subset _ _) (by omega) (by omega)
    have hs : H.card-k = (H.erase v).card-k+1 := by omega
    rw [hs] at hHedges
    nlinarith
  refine ⟨H,hHS,?_⟩
  by_contra hn
  obtain ⟨A,Z,B,hZ,hsep⟩ := exists_separator G H (by omega) hn
  have hsub₁ : A ∪ Z ⊆ H := by rw [← hsep.union_eq]; exact Finset.subset_union_left
  have hsub₂ : B ∪ Z ⊆ H := by
    intro v hv
    rw [← hsep.union_eq]
    rcases Finset.mem_union.mp hv with hb | hz
    · exact Finset.mem_union_right _ hb
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hz)
  have hcard₁ : (A ∪ Z).card < H.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub₁,?_⟩
    intro heq
    obtain ⟨v,hv⟩ := hsep.right_nonempty
    have hvH : v ∈ H := by rw [← hsep.union_eq]; exact Finset.mem_union_right _ hv
    rw [←heq] at hvH
    rcases Finset.mem_union.mp hvH with ha | hz
    · exact Finset.disjoint_left.mp hsep.left_right ha hv
    · exact Finset.disjoint_left.mp hsep.sep_right hz hv
  have hcard₂ : (B ∪ Z).card < H.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub₂,?_⟩
    intro heq
    obtain ⟨v,hv⟩ := hsep.left_nonempty
    have hvH : v ∈ H := hsub₁ (Finset.mem_union_left _ hv)
    rw [←heq] at hvH
    rcases Finset.mem_union.mp hvH with hb | hz
    · exact Finset.disjoint_left.mp hsep.left_right hv hb
    · exact Finset.disjoint_left.mp hsep.left_sep hv hz
  have hsize₁ : 2*k ≤ (A ∪ Z).card := by
    obtain ⟨v,hv⟩ := hsep.left_nonempty
    have hd := hdegree v (hsub₁ (Finset.mem_union_left _ hv))
    have hb : (neighbors G H v).card ≤ (A ∪ Z).card := by
      apply Finset.card_le_card
      intro w hw
      obtain ⟨hwH,ha⟩ := (mem_neighbors G).mp hw
      rw [←hsep.union_eq] at hwH
      rcases Finset.mem_union.mp hwH with hw | hw
      · exact hw
      · exact (hsep.anticomplete _ hv _ hw ha).elim
    omega
  have hsize₂ : 2*k ≤ (B ∪ Z).card := by
    obtain ⟨v,hv⟩ := hsep.right_nonempty
    have hd := hdegree v (hsub₂ (Finset.mem_union_left _ hv))
    have hb : (neighbors G H v).card ≤ (B ∪ Z).card := by
      apply Finset.card_le_card
      intro w hw
      obtain ⟨hwH,ha⟩ := (mem_neighbors G).mp hw
      rw [←hsep.union_eq] at hwH
      rcases Finset.mem_union.mp hwH with hw | hw
      · rcases Finset.mem_union.mp hw with hw | hw
        · exact (hsep.anticomplete _ hw _ hv ha.symm).elim
        · exact Finset.mem_union_right _ hw
      · exact Finset.mem_union_left _ hw
    omega
  have hb₁ := hminimal (A ∪ Z) hsub₁ hsize₁ hcard₁
  have hb₂ := hminimal (B ∪ Z) hsub₂ hsize₂ hcard₂
  have hedge := darts_separator G hsep
  have hcards : (A ∪ Z).card + (B ∪ Z).card = H.card + Z.card := by
    rw [Finset.card_union_of_disjoint hsep.left_sep,
      Finset.card_union_of_disjoint hsep.sep_right.symm, ← hsep.union_eq,
      Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
        ⟨hsep.left_right,hsep.sep_right⟩),Finset.card_union_of_disjoint hsep.left_sep]
    omega
  have h1 : (A ∪ Z).card-k+k = (A ∪ Z).card := Nat.sub_add_cancel (by omega)
  have h2 : (B ∪ Z).card-k+k = (B ∪ Z).card := Nat.sub_add_cancel (by omega)
  have hH : H.card-k+k = H.card := Nat.sub_add_cancel (by omega)
  nlinarith

lemma darts_univ {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype V] : (darts G Finset.univ).card = 2 * G.edgeFinset.card := by
  simpa [darts] using G.two_mul_card_edgeFinset.symm

theorem edge_density_connectivity [Fintype V] {k : ℕ} (hk : 1 ≤ k)
    (he : 2*k*Fintype.card V < G.edgeFinset.card) :
    ∃ T : Finset V, KConnectedOn G T k := by
  obtain ⟨T,_,hT⟩ := connectivity_of_density G Finset.univ hk (by
    rw [darts_univ,Finset.card_univ]
    nlinarith)
  exact ⟨T,hT⟩

end Density

end LinearListHadwiger

end OAI
