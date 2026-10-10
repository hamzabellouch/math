import OAI.Combinatorics.CliqueFree.TriangleState

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

variable {U : Type v} [Fintype U]

lemma sum_injective_le {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (f : I → J) (hf : Function.Injective f) (g : J → ℝ) (hg : ∀ j, 0 ≤ g j) :
    (∑ i, g (f i)) ≤ ∑ j, g j := by
  classical
  calc
    _ = ∑ j ∈ univ.image f, g j := (sum_image (fun _ _ _ _ h ↦ hf h)).symm
    _ ≤ _ := sum_le_univ_sum_of_nonneg hg

/-- A weight-preserving, directed-edge-injective projection. -/
structure EdgeProjection (H : SimpleGraph U) (G : SimpleGraph V) (π : U → V) : Prop where
  map_adj : ∀ a b, H.Adj a b → G.Adj (π a) (π b)
  inj : ∀ a b c d, H.Adj a b → H.Adj c d → π a = π c → π b = π d → a = c ∧ b = d

namespace EdgeProjection
variable {H : SimpleGraph U} {G : SimpleGraph V} {π : U → V}

def edgeMap (h : EdgeProjection H G π) (e : EdgeState H) : EdgeState G :=
  ⟨(π e.src, π e.dst), h.map_adj _ _ e.adj⟩

omit [Fintype V] [Fintype U] in
lemma edgeMap_injective (h : EdgeProjection H G π) : Function.Injective h.edgeMap := by
  intro e f hef
  have heq := congrArg Subtype.val hef
  have hpair := h.inj e.src e.dst f.src f.dst e.adj f.adj
    (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  exact Subtype.ext (Prod.ext hpair.1 hpair.2)

omit [Fintype V] [Fintype U] in
lemma mass_image_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A : Finset U) :
    mass w (A.image π) ≤ mass (w ∘ π) A := by
  classical
  exact sum_image_le_of_nonneg (fun _ _ ↦ hw _)

lemma crossMass_edge_sum (H : SimpleGraph U) (w : U → ℝ) (A B : Finset U) :
    crossMass H w A B =
      ∑ e : EdgeState H, if e.src ∈ A ∧ e.dst ∈ B then w e.src * w e.dst else 0 := by
  classical
  rw [EdgeState.sum_eq (fun a b ↦ if a ∈ A ∧ b ∈ B then w a * w b else 0)]
  have heq : (∑ a, ∑ b ∈ neighbors H a, if a ∈ A ∧ b ∈ B then w a * w b else 0) =
      ∑ a, if a ∈ A then (∑ b, if b ∈ B then if H.Adj a b then w a * w b else 0 else 0) else 0 := by
    apply sum_congr rfl
    intro a _
    by_cases ha : a ∈ A
    · simp only [ha, true_and, ↓reduceIte, neighbors, sum_filter]
      apply sum_congr rfl
      intro b _
      by_cases hb : b ∈ B <;> simp [hb]
    · simp [ha]
  rw [heq]
  simp [crossMass]

lemma crossMass_le (h : EdgeProjection H G π) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (A B : Finset U) :
    crossMass H (w ∘ π) A B ≤ crossMass G w (A.image π) (B.image π) := by
  classical
  rw [crossMass_edge_sum, crossMass_edge_sum]
  calc
    _ ≤ ∑ e : EdgeState H,
        if (h.edgeMap e).src ∈ A.image π ∧ (h.edgeMap e).dst ∈ B.image π
          then w (h.edgeMap e).src * w (h.edgeMap e).dst else 0 := by
      apply sum_le_sum
      intro e _
      by_cases he : e.src ∈ A ∧ e.dst ∈ B
      · have hi : (h.edgeMap e).src ∈ A.image π ∧ (h.edgeMap e).dst ∈ B.image π :=
          ⟨mem_image.2 ⟨e.src, he.1, rfl⟩, mem_image.2 ⟨e.dst, he.2, rfl⟩⟩
        simp only [he, hi]
        exact le_rfl
      · simp only [he, ↓reduceIte]
        split_ifs
        · exact mul_nonneg (hw _) (hw _)
        · exact le_rfl
    _ ≤ _ := sum_injective_le h.edgeMap h.edgeMap_injective
      (fun e ↦ if e.src ∈ A.image π ∧ e.dst ∈ B.image π then w e.src * w e.dst else 0)
      (fun e ↦ by split_ifs; exact mul_nonneg (hw _) (hw _); exact le_rfl)

lemma crossBound (h : EdgeProjection H G π) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {C : ℝ} (hC : 0 ≤ C) (hc : CrossBound G w C) : CrossBound H (w ∘ π) C := by
  classical
  intro x hx A B hA hB
  have hAi := mass_image_le (π := π) hw A
  have hBi := mass_image_le (π := π) hw B
  exact (h.crossMass_le hw A B).trans ((hc x hx _ _ (hAi.trans hA) (hBi.trans hB)).trans
    (mul_le_mul_of_nonneg_left (growth_mono hx (mass_nonneg hw _) (mass_nonneg (fun u ↦ hw (π u)) _) hAi) hC))

lemma edgeMass_le (h : EdgeProjection H G π) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    edgeMass H (w ∘ π) ≤ edgeMass G w := by
  classical
  have hsum : (∑ e : EdgeState H, w (π e.src) * w (π e.dst)) ≤
      ∑ e : EdgeState G, w e.src * w e.dst :=
    sum_injective_le h.edgeMap h.edgeMap_injective (fun e ↦ w e.src * w e.dst)
      (fun e ↦ mul_nonneg (hw _) (hw _))
  unfold edgeMass
  rw [crossMass_edge_sum, crossMass_edge_sum]
  simpa only [mem_univ, true_and, ↓reduceIte, Function.comp_apply] using
    div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)

omit [Fintype V] in
lemma neighbor_injective (h : EdgeProjection H G π) (a : U) :
    Set.InjOn π (neighbors H a) := by
  intro b hb c hc heq
  exact (h.inj a b a c ((mem_neighbors _ _ _).1 hb) ((mem_neighbors _ _ _).1 hc) rfl heq).2

lemma neighborhood_image (h : EdgeProjection H G π) (a : U) :
    (neighbors H a).image π ⊆ neighbors G (π a) := by
  intro b hb
  obtain ⟨c, hc, rfl⟩ := mem_image.1 hb
  exact (mem_neighbors _ _ _).2 (h.map_adj _ _ ((mem_neighbors _ _ _).1 hc))

lemma neighborMass_le (h : EdgeProjection H G π) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (a : U) :
    neighborMass H (w ∘ π) a ≤ neighborMass G w (π a) := by
  classical
  calc
    _ = mass w ((neighbors H a).image π) := (sum_image (h.neighbor_injective a)).symm
    _ ≤ _ := mass_mono hw (h.neighborhood_image a)

end EdgeProjection

end CliqueFreeIndependence.WeightedGraph

end

end OAI
