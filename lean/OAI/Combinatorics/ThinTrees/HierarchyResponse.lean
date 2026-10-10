import OAI.Combinatorics.ThinTrees.ResponseBounds

namespace OAI

universe uE

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree
lemma finite_markov {E : Type uE} [DecidableEq E] (B : Finset E) (R : E → ℝ)
    (hR : ∀e ∈ B, 0 ≤ R e) {t a : ℝ} (ht : 0 < t)
    (havg : (B.card:ℝ)⁻¹*(∑e ∈ B, R e) ≤ a) :
    ((B.filter (fun e => t < R e)).card:ℝ) ≤ a/t*B.card := by
  classical
  by_cases hz : B=∅
  · simp [hz]
  have hc : (0:ℝ) < B.card := Nat.cast_pos.mpr (card_pos.mpr (nonempty_iff_ne_empty.mpr hz))
  have hs : (∑e ∈ B, R e) ≤ a*B.card := by
    rw [mul_comm,←div_eq_mul_inv] at havg
    exact (div_le_iff₀ hc).mp havg
  have hm : ((B.filter (fun e => t < R e)).card:ℝ)*t ≤ ∑e ∈ B, R e := by
    calc
      _ = ∑e ∈ B.filter (fun e => t < R e), t := by simp
      _ ≤ ∑e ∈ B.filter (fun e => t < R e), R e := sum_le_sum (fun e he => (mem_filter.mp he).2.le)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun e he _ => hR e he)
  have hh := (le_div_iff₀ ht).mpr (hm.trans hs)
  calc
    _ ≤ (a*(B.card:ℝ))/t := hh
    _ = _ := by ring

namespace MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
lemma parentBoundary_sub (H : Hierarchy n) (A : Finset (Fin n)) : H.parentBoundary G A ⊆ G.cut univ A := by
  intro e he
  exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp he).2⟩
lemma singleton_locally (v : Fin n) (q : ℝ) : G.EdgeConnectedReal {v} q := by
  intro S hS hS'
  have hlt := card_lt_card hS'
  simp only [card_singleton] at hlt
  have hp := card_pos.mpr hS
  omega
lemma chain_locally (P : PartitionChain n) (I : Finset ℕ) (H : Hierarchy n) (hH : H.nodes=P.nodes I)
    {q : ℝ} (hlocal : ∀i ∈ I, ∀A ∈ P.parts i, G.EdgeConnectedReal A q) : H.LocallyConnectedReal G q := by
  intro A hA
  rw [hH] at hA
  rcases P.mem_nodes.mp hA with ⟨i,hi,hA⟩ | ⟨v,rfl⟩
  · exact hlocal i hi A hA
  · exact G.singleton_locally v q

lemma shortcut_response {H : Hierarchy n} {q : ℕ} (hq : 0 < q) (hn : 0 < n)
    (hc : G.EdgeConnected 1) {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (hcut : ∀S : Finset (Fin n), S.Nonempty → S ≠ univ → qform D (cutIndicator S) ≤ (G.cut univ S).card)
    (havg : ∀A ∈ H.nodes, A ≠ univ → ((G.cut univ A).card:ℝ)/q ≤ (H.parentBoundary G A).card →
      ShortcutDual.boundaryAverage G.incidence (H.parentBoundary G) A D ≤ a) :
    ∃Y ∈ G.matrixDomain, ∀A ∈ H.nodes,
      (((univ.filter (fun e => t < G.resistance Y e)) ∩ H.parentBoundary G A).card:ℝ) ≤
      (a/t+1/(q:ℝ))*(G.cut univ A).card := by
  let Y := G.baseMatrix+D
  have hY : Y.PosDef := (G.baseMatrix_pd hn).add hD
  have hYm : Y ∈ G.matrixDomain := by
    refine ⟨le_add_of_nonneg_right (Matrix.nonneg_iff_posSemidef.mpr hD.posSemidef),?_⟩
    intro S hS hS'
    rw [qform_add,G.baseMatrix_cut]
    have h1 : (1:ℝ) ≤ (G.cut univ S).card := by exact_mod_cast hc S hS hS'
    have hcard : (S.card:ℝ) ≤ n := by exact_mod_cast (show S.card ≤ n by simpa using card_le_univ S)
    have hdiv := (div_le_one (Nat.cast_pos.mpr hn)).mpr hcard
    linarith [hcut S hS hS']
  have hRY (e : Fin m) : G.resistance Y e ≤ G.resistance D e := by
    apply G.resistance_antitone hY hD
    have hb := Matrix.nonneg_iff_posSemidef.mpr (G.baseMatrix_pd hn).posSemidef
    exact le_add_of_nonneg_left hb
  have hcoeff : 0 ≤ a/t := div_nonneg ha ht.le
  have hqR : (0:ℝ) < q := Nat.cast_pos.mpr hq
  refine ⟨Y,hYm,fun A hA => ?_⟩
  have hsub := G.parentBoundary_sub H A
  have hcard : ((H.parentBoundary G A).card:ℝ) ≤ (G.cut univ A).card := by exact_mod_cast card_le_card hsub
  have hbadsub : (univ.filter (fun e => t < G.resistance Y e)) ∩ H.parentBoundary G A ⊆
      (H.parentBoundary G A).filter (fun e => t < G.resistance D e) := by
    intro e he
    obtain ⟨hb,heA⟩ := mem_inter.mp he
    exact mem_filter.mpr ⟨heA,(mem_filter.mp hb).2.trans_le (hRY e)⟩
  by_cases hroot : A=univ
  · subst A
    have he : G.cut univ univ=∅ := by ext e; simp [cut]
    have ho : H.parentBoundary G univ=∅ := subset_empty.mp (he ▸ hsub)
    simp [ho,he]
  by_cases hmark : ((G.cut univ A).card:ℝ)/q ≤ (H.parentBoundary G A).card
  · have hm := finite_markov (H.parentBoundary G A) (G.resistance D) (fun e _ => G.resistance_nonneg hD e)
      ht (havg A hA hroot hmark)
    calc
      _ ≤ (((H.parentBoundary G A).filter (fun e => t < G.resistance D e)).card:ℝ) := by exact_mod_cast card_le_card hbadsub
      _ ≤ a/t*(H.parentBoundary G A).card := hm
      _ ≤ a/t*(G.cut univ A).card := mul_le_mul_of_nonneg_left hcard hcoeff
      _ ≤ _ := by
        have hnon : 0 ≤ 1/(q:ℝ)*(G.cut univ A).card := by positivity
        nlinarith
  · have hb : (((univ.filter (fun e => t < G.resistance Y e)) ∩ H.parentBoundary G A).card:ℝ) ≤
        (H.parentBoundary G A).card := by exact_mod_cast card_le_card (inter_subset_right)
    have hm := (lt_of_not_ge hmark).le
    have hnon : 0 ≤ a/t*(G.cut univ A).card := mul_nonneg hcoeff (Nat.cast_nonneg _)
    calc
      _ ≤ ((H.parentBoundary G A).card:ℝ) := hb
      _ ≤ ((G.cut univ A).card:ℝ)/q := hm
      _ ≤ _ := by nlinarith [show ((G.cut univ A).card:ℝ)/q=(1/(q:ℝ))*(G.cut univ A).card by ring]

end MultiGraph
end StrongThinTree

end
end

end OAI
