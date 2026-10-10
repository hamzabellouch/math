import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.RootedCompletionMax

namespace OAI

section
noncomputable section
open scoped BigOperators
open Classical Filter

namespace SharpTerminalLeave

def rerootTemplate {k : ℕ} (T : RootedTemplate k) (J : Finset (Fin k)) : RootedTemplate k where
  edges := T.edges.filter (fun e => ¬ e ⊆ J)
  roots := J
  simple := fun e he => T.simple e (Finset.mem_filter.mp he).1
  independent := fun _e he => (Finset.mem_filter.mp he).2

lemma rerootTemplate_image_subset {k n : ℕ} (T : RootedTemplate k)
    (J : Finset (Fin k)) (φ : Fin k ↪ Fin n) :
    imageEdges (rerootTemplate T J) φ ⊆ imageEdges T φ := by
  exact Finset.image_subset_image (Finset.filter_subset _ _)

lemma rerootTemplate_remaining {k : ℕ} (T : RootedTemplate k)
    (J K : Finset (Fin k)) (hJK : J ⊆ K) :
    (rerootTemplate T J).edges.card-
      ((rerootTemplate T J).edges.filter (· ⊆ K)).card =
        T.edges.card-(T.edges.filter (· ⊆ K)).card := by
  rw [← Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
    ← Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
  congr 1
  ext e
  simp only [rerootTemplate,Finset.mem_sdiff,Finset.mem_filter]
  constructor
  · rintro ⟨⟨he,hJ⟩,hK⟩
    exact ⟨he,fun hk => hK ⟨⟨he,hJ⟩,hk.2⟩⟩
  · rintro ⟨he,hK⟩
    have hnK : ¬ e ⊆ K := fun hk => hK ⟨he,hk⟩
    exact ⟨⟨he,fun hj => hnK (hj.trans hJK)⟩,fun hk => hnK hk.2⟩

def RootedTwoBalanced {k : ℕ} (T : RootedTemplate k) : Prop :=
  ∀ J : Finset (Fin k), T.roots ⊆ J →
    (T.edges.filter (· ⊆ J)).card ≤ 2*(J.card-T.roots.card)

lemma balanced_overlap_scale {k n : ℕ} (T : RootedTemplate k)
    (hT : RootedTwoBalanced T) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (J : Finset (Fin k)) (hJ : T.roots ⊆ J) :
    ((n : ℝ)*p^2)^(J.card-T.roots.card) ≤
      (n : ℝ)^(J.card-T.roots.card)*p^(T.edges.filter (· ⊆ J)).card := by
  rw [mul_pow,← pow_mul]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one hp hp1 (hT J hJ)) (by positivity)

lemma balanced_completion_bound {k n : ℕ} (T : RootedTemplate k)
    (hT : RootedTwoBalanced T) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hD : 1 ≤ (n : ℝ)*p^2) (J : Finset (Fin k))
    (hJ : T.roots ⊆ J) (hJ' : T.roots.card < J.card) :
    (n : ℝ)^(k-J.card)*p^(T.edges.card-(T.edges.filter (· ⊆ J)).card) ≤
      rootedScaling T n p/((n : ℝ)*p^2) := by
  have hD0 : 0 < (n : ℝ)*p^2 := lt_of_lt_of_le zero_lt_one hD
  apply (le_div_iff₀ hD0).mpr
  rw [← rooted_completion_factorization T J hJ p]
  have hl : (n : ℝ)*p^2 ≤
      (n : ℝ)^(J.card-T.roots.card)*p^(T.edges.filter (· ⊆ J)).card := by
    apply le_trans _ (balanced_overlap_scale T hT hp.le hp1 J hJ)
    simpa only [pow_one] using (pow_le_pow_right₀ hD (show 1 ≤ J.card-T.roots.card by omega))
  exact (mul_le_mul_of_nonneg_left hl (by positivity)).trans_eq (mul_comm _ _)

theorem balanced_reroot_completion_bound {k n : ℕ} (T : RootedTemplate k)
    (hT : RootedTwoBalanced T) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hD : 1 ≤ (n : ℝ)*p^2) (J : Finset (Fin k))
    (hJ : T.roots ⊆ J) (hJ' : T.roots.card < J.card) :
    rootedCompletionMax (rerootTemplate T J) n p ≤ rootedScaling T n p/((n : ℝ)*p^2) := by
  have h1 : 1 ≤ rootedScaling T n p/((n : ℝ)*p^2) := by
    have hk : T.roots.card < (Finset.univ : Finset (Fin k)).card :=
      lt_of_lt_of_le hJ' (Finset.card_le_card (Finset.subset_univ J))
    simpa using balanced_completion_bound T hT hp hp1 hD Finset.univ (Finset.subset_univ _) hk
  apply Finset.sup'_le
  intro K _
  split_ifs with hK
  · change J ⊆ K at hK
    rw [rerootTemplate_remaining T J K hK]
    exact balanced_completion_bound T hT hp hp1 hD K (hJ.trans hK)
      (hJ'.trans_le (Finset.card_le_card hK))
  · exact h1

lemma fintype_sum_le_injection {α β : Type*} [Fintype α] [Fintype β]
    (e : α → β) (he : Function.Injective e) (f : α → ℝ) (g : β → ℝ)
    (hfg : ∀ a, f a ≤ g (e a)) (hg : ∀ b, 0 ≤ g b) :
    ∑ a, f a ≤ ∑ b, g b := by
  calc
    _ ≤ ∑ a, g (e a) := Finset.sum_le_sum (fun a _ => hfg a)
    _ = ∑ b ∈ Finset.univ.image e, g b := (Finset.sum_image (fun a _ b _ h => he h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun b _ _ => hg b)

abbrev RootedEdgePin {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (f : Finset (Fin k)) (e : Finset (Fin n)) :=
  {ξ : {v // v ∈ T.roots ∪ f} ↪ Fin n //
    (∀ r : {v // v ∈ T.roots}, ξ ⟨r.val,Finset.mem_union_left _ r.property⟩ = ψ r) ∧
    ∀ v : {v // v ∈ f}, ξ ⟨v.val,Finset.mem_union_right _ v.property⟩ ∈ e}

lemma rootedEdgePin_card {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (f : Finset (Fin k)) (e : Finset (Fin n)) :
    Fintype.card (RootedEdgePin T ψ f e) ≤ e.card^f.card := by
  let enc : RootedEdgePin T ψ f e → (f → e) := fun ξ v =>
    ⟨ξ.val ⟨v.val,Finset.mem_union_right _ v.property⟩,ξ.property.2 v⟩
  have hinj : Function.Injective enc := by
    intro ξ χ hh
    apply Subtype.ext
    apply DFunLike.ext
    intro v
    rcases Finset.mem_union.mp v.property with hv | hv
    · exact (ξ.property.1 ⟨v.val,hv⟩).trans (χ.property.1 ⟨v.val,hv⟩).symm
    · exact congrArg Subtype.val (congrFun hh ⟨v.val,hv⟩)
  simpa only [Fintype.card_fun,Fintype.card_coe] using Fintype.card_le_of_injective enc hinj

def rootedEdgeFiberEncoding {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (f : Finset (Fin k)) (e : Finset (Fin n))
    (φ : {φ : RootedInjection T ψ // f.map φ.val = e}) :
    Σ ξ : RootedEdgePin T ψ f e, RootedInjection (rerootTemplate T (T.roots ∪ f)) ξ.val := by
  let ξ : {v // v ∈ T.roots ∪ f} ↪ Fin n :=
    ⟨fun v => φ.val.val v,fun _ _ h => Subtype.ext (φ.val.val.injective h)⟩
  have hξ : (∀ r : {v // v ∈ T.roots}, ξ ⟨r.val,Finset.mem_union_left _ r.property⟩ = ψ r) ∧
      ∀ v : {v // v ∈ f}, ξ ⟨v.val,Finset.mem_union_right _ v.property⟩ ∈ e := by
    refine ⟨fun r => φ.val.property r,?_⟩
    intro v
    rw [← φ.property]
    exact Finset.mem_map.mpr ⟨v.val,v.property,rfl⟩
  exact ⟨⟨ξ,hξ⟩,φ.val.val,fun _ => rfl⟩

lemma rootedEdgeFiberEncoding_injective {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (f : Finset (Fin k)) (e : Finset (Fin n)) :
    Function.Injective (rootedEdgeFiberEncoding T ψ f e) := by
  intro φ χ hh
  have he := congrArg (fun z : Σ ξ : RootedEdgePin T ψ f e,
      RootedInjection (rerootTemplate T (T.roots ∪ f)) ξ.val => z.2.val) hh
  exact Subtype.ext (Subtype.ext he)

lemma intact_antitone_required {n : ℕ} {F J : Graph n} (hF : F ⊆ J) (G : Graph n) :
    intact J G ≤ intact F G := by
  unfold intact
  split_ifs with hJ hFG hFG
  · exact le_rfl
  · exact False.elim (hFG (hF.trans hJ))
  · norm_num
  · norm_num

lemma rooted_edge_fiber_load {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (f : Finset (Fin k)) (e : Finset (Fin n))
    (G : Graph n) (L : ℝ) (hL : 0 ≤ L)
    (hcounts : ∀ ξ : {v // v ∈ T.roots ∪ f} ↪ Fin n,
      rootedCount (rerootTemplate T (T.roots ∪ f)) ξ G ≤ L) :
    (∑ φ : {φ : RootedInjection T ψ // f.map φ.val = e}, intact (imageEdges T φ.val.val) G) ≤
      (e.card : ℝ)^f.card*L := by
  have hh := fintype_sum_le_injection (rootedEdgeFiberEncoding T ψ f e)
    (rootedEdgeFiberEncoding_injective T ψ f e)
    (fun φ => intact (imageEdges T φ.val.val) G)
    (fun z => intact (imageEdges (rerootTemplate T (T.roots ∪ f)) z.2.val) G)
    (fun φ => intact_antitone_required (rerootTemplate_image_subset T (T.roots ∪ f) φ.val.val) G)
    (fun a => intact_nonnegative _ _)
  apply hh.trans
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ _ξ : RootedEdgePin T ψ f e, L := Finset.sum_le_sum (fun ξ _ => hcounts ξ.val)
    _ = (Fintype.card (RootedEdgePin T ψ f e) : ℝ)*L := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast rootedEdgePin_card T ψ f e) hL

theorem rooted_copyEdgeLoad_from_reroots {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (G : Graph n) (e : Finset (Fin n))
    (he : e.card = 2) (L : ℝ) (hL : 0 ≤ L)
    (hcounts : ∀ f ∈ T.edges, ∀ ξ : {v // v ∈ T.roots ∪ f} ↪ Fin n,
      rootedCount (rerootTemplate T (T.roots ∪ f)) ξ G ≤ L) :
    copyEdgeLoad (fun φ : RootedInjection T ψ => imageEdges T φ.val) G e ≤
      4*(T.edges.card : ℝ)*L := by
  let A := {φ : RootedInjection T ψ // e ∈ imageEdges T φ.val}
  let B := Σ f : T.edges, {φ : RootedInjection T ψ // f.val.map φ.val = e}
  have hex (φ : A) : ∃ f ∈ T.edges, f.map φ.val.val = e := Finset.mem_image.mp φ.property
  let enc : A → B := fun φ =>
    ⟨⟨(hex φ).choose,(hex φ).choose_spec.1⟩,φ.val,(hex φ).choose_spec.2⟩
  have hinj : Function.Injective enc := by
    intro φ χ h
    exact Subtype.ext (congrArg (fun z : B => z.2.val) h)
  rw [copyEdgeLoad_eq_subfamily,copyCount]
  have hh := fintype_sum_le_injection enc hinj
    (fun φ : A => intact (imageEdges T φ.val.val) G)
    (fun z : B => intact (imageEdges T z.2.val.val) G)
    (fun _ => le_refl _) (fun _ => intact_nonnegative _ _)
  apply hh.trans
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ _f : T.edges, 4*L := by
      apply Finset.sum_le_sum
      intro f _
      have hh := rooted_edge_fiber_load T ψ f.val e G L hL (hcounts f.val f.property)
      simpa only [he,T.simple f.val f.property,Nat.cast_ofNat,show (2 : ℝ)^2 = 4 by norm_num] using hh
    _ = _ := by simp; ring

theorem balanced_rooted_load_bound {H k n : ℕ} (T : RootedTemplate k)
    (hk : k ≤ H) (hT : RootedTwoBalanced T)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (G : Graph n) (hG : G ⊆ completeGraph n)
    {p B : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hB : 0 ≤ B) (hD : 1 ≤ (n : ℝ)*p^2)
    (hupper : ∀ k ≤ H, ∀ U : RootedTemplate k, ∀ ξ : {v // v ∈ U.roots} ↪ Fin n,
      rootedCount U ξ G ≤ B*rootedCompletionMax U n p) :
    copyLoadSafe (fun φ : RootedInjection T ψ => imageEdges T φ.val)
      (4*(T.edges.card : ℝ)*B*rootedScaling T n p/((n : ℝ)*p^2)) G := by
  intro e he
  have hnonneg : 0 ≤ B*(rootedScaling T n p/((n : ℝ)*p^2)) := by
    unfold rootedScaling; positivity
  have hmain := rooted_copyEdgeLoad_from_reroots T ψ G e (mem_completeGraph.mp (hG he))
    (B*(rootedScaling T n p/((n : ℝ)*p^2))) hnonneg ?_
  · convert hmain using 1; ring
  intro f hf ξ
  have hproper : T.roots.card < (T.roots ∪ f).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_union_left,?_⟩
    intro hh
    exact T.independent f hf (hh ▸ Finset.subset_union_right)
  exact (hupper k hk (rerootTemplate T (T.roots ∪ f)) ξ).trans
    (mul_le_mul_of_nonneg_left (balanced_reroot_completion_bound T hT hp hp1 hD
      (T.roots ∪ f) Finset.subset_union_left hproper) hB)

end SharpTerminalLeave
end
end

end OAI
