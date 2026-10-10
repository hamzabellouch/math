import Mathlib
import OAI.Combinatorics.IndependentSets.Model
import OAI.Combinatorics.IndependentSets.Reduction.SamplerParameters

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators

namespace Graph

noncomputable def ofSimple {W : Type} [Fintype W] [Nonempty W] (H : SimpleGraph W) : Graph where
  vertices := Fintype.card W
  nonempty := Fintype.card_pos
  adj u v := decide (H.Adj ((Fintype.equivFin W).symm u) ((Fintype.equivFin W).symm v))
  symm u v := by simp only [decide_eq_decide]; exact H.adj_comm _ _
  loopless u := by simp

theorem ofSimple_colorable {W : Type} [Fintype W] [Nonempty W] (H : SimpleGraph W)
    (h : ∃ color : W → Fin 3, ∀ u v, H.Adj u v → color u ≠ color v) :
    (ofSimple H).ThreeColorable := by
  obtain ⟨color,hcolor⟩ := h
  refine ⟨fun u => color ((Fintype.equivFin W).symm u),?_⟩
  intro u v h
  exact hcolor _ _ (of_decide_eq_true h)

theorem ofSimple_independent {W : Type} [Fintype W] [Nonempty W] (H : SimpleGraph W)
    (A : Finset (Fin (ofSimple H).vertices)) (hA : (ofSimple H).Independent A) :
    H.IsIndepSet (A.image (Fintype.equivFin W).symm : Set W) := by
  intro u hu v hv hne hadj
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
  have hne' : a ≠ b := fun h => hne (congrArg _ h)
  have hh := hA a ha b hb hne'
  have ht : (ofSimple H).adj a b = true := by exact decide_eq_true hadj
  exact Bool.false_ne_true (hh.symm.trans ht)

lemma exists_max_independent (G : Graph) :
    ∃ A : Finset (Fin G.vertices), G.Independent A ∧ G.independenceNumber = A.card := by
  let all := ((Finset.univ : Finset (Fin G.vertices)).powerset.filter G.Independent)
  have hne : all.Nonempty := by
    refine ⟨∅,?_⟩
    simp [all, Independent]
  obtain ⟨A,hA,he⟩ := Finset.exists_mem_eq_sup all hne Finset.card
  exact ⟨A,(Finset.mem_filter.mp hA).2,he⟩

theorem ofSimple_alpha {W : Type} [Fintype W] [Nonempty W] (H : SimpleGraph W)
    {δ : ℝ} (h : ∀ A : Finset W, H.IsIndepSet (A : Set W) →
      (A.card : ℝ) / Fintype.card W < δ) :
    ((ofSimple H).independenceNumber : ℝ) < δ * (ofSimple H).vertices := by
  obtain ⟨A,hA,he⟩ := (ofSimple H).exists_max_independent
  have hh := h (A.image (Fintype.equivFin W).symm) (ofSimple_independent H A hA)
  have hc : (A.image (Fintype.equivFin W).symm).card = A.card := by
    apply Finset.card_image_iff.mpr
    exact (Fintype.equivFin W).symm.injective.injOn
  rw [hc] at hh
  rw [he]
  exact (div_lt_iff₀ (Nat.cast_pos.mpr Fintype.card_pos)).mp hh

def clique (q : ℕ) (hq : 0 < q) : Graph where
  vertices := q
  nonempty := hq
  adj u v := decide (u ≠ v)
  symm u v := by simp [ne_comm]
  loopless u := by simp

lemma clique_alpha_le (q : ℕ) (hq : 0 < q) : (clique q hq).independenceNumber ≤ 1 := by
  obtain ⟨A,hA,he⟩ := (clique q hq).exists_max_independent
  rw [he]
  apply Finset.card_le_one.mpr
  intro u hu v hv
  by_contra hne
  have hh := hA u hu v hv hne
  let : DecidableEq (Fin q) := instDecidableEqFin q
  have hh' : decide (u ≠ v) = false := hh
  exact (of_decide_eq_false hh') hne

lemma clique_sound (q : ℕ) (hq : 0 < q) {δ : ℝ} (hδq : 1 < δ*q) :
    ((clique q hq).independenceNumber : ℝ) < δ*(clique q hq).vertices :=
  lt_of_le_of_lt (by exact_mod_cast clique_alpha_le q hq) hδq

end Graph

namespace SamplerParameters

def CliqueTest (p : SamplerParameters) {U V L R C : Type} [Fintype L] [Fintype R]
    (lc : LabelCoverData U V L R C) : Prop :=
  ∃ x : GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=p.n)) (p.m*2^p.k),
    pathDistance (layeredSystem lc p.n).linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1/8)

noncomputable def output (p : SamplerParameters) (q : ℕ) (hq : 0 < q)
    {U V L R C : Type} [Fintype L] [Fintype R] [Fintype C] [Nonempty C]
    (lc : LabelCoverData U V L R C) : Graph :=
  if p.CliqueTest lc then Graph.clique q hq else Graph.ofSimple (p.graph lc)

lemma output_complete (p : SamplerParameters) (q : ℕ) (hq : 0 < q)
    {U V L R C : Type} [Fintype L] [Fintype R] [Fintype C] [Nonempty C]
    (lc : LabelCoverData U V L R C) (ℓ : U → L) (ρ : V → R) (h : lc.Satisfied ℓ ρ) :
    (p.output q hq lc).ThreeColorable := by
  obtain ⟨hn,hcol⟩ := p.completeness lc ℓ ρ h
  have ht : ¬p.CliqueTest lc := by
    rintro ⟨x,hx⟩
    exact hn x hx
  rw [output,ite_eq_right ht]
  exact Graph.ofSimple_colorable _ hcol

lemma output_size (p : SamplerParameters) (q : ℕ) (hq : 0 < q)
    {U V L R C : Type} [Fintype L] [Fintype R] [Fintype C] [Nonempty C]
    (lc : LabelCoverData U V L R C) :
    (p.output q hq lc).vertices ≤ max q (Fintype.card C ^ p.n * (p.law L R).denominator) := by
  unfold output
  split
  · exact le_max_left _ _
  · change Fintype.card (p.Vertices L R C) ≤ _
    rw [RationalLaw.card_vertices]
    exact le_max_right _ _

end SamplerParameters

theorem finite_graph_reduction {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : SamplerParameters, ∃ σ : ℚ, ∃ q : ℕ, ∃ hq : 0 < q,
    0 < σ ∧ σ < 1 ∧
    ∀ (U V L R C : Type) [Fintype L] [Fintype R] [Fintype C]
      [Nonempty L] [Nonempty R] [Nonempty C] (lc : LabelCoverData U V L R C),
    ((∃ ℓ ρ, lc.Satisfied ℓ ρ) → (p.output q hq lc).ThreeColorable) ∧
    (lc.Sound (σ:ℝ) → ((p.output q hq lc).independenceNumber : ℝ) <
      δ*(p.output q hq lc).vertices) := by
  obtain ⟨p,σ,hσ,hσ1,H⟩ := finite_source_soundness hδ
  obtain ⟨q,hq⟩ := exists_nat_gt (max (1:ℝ) (1/δ))
  have hq0 : 0 < q := by exact_mod_cast lt_trans (by norm_num : (0:ℝ) < 1) ((le_max_left _ _).trans_lt hq)
  have hδq : 1 < δ*(q:ℝ) := by
    have hh := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hq)
    nlinarith
  refine ⟨p,σ,q,hq0,hσ,hσ1,?_⟩
  intro U V L R C _ _ _ _ _ _ lc
  constructor
  · rintro ⟨ℓ,ρ,h⟩
    exact p.output_complete q hq0 lc ℓ ρ h
  · intro hs
    by_cases ht : p.CliqueTest lc
    · rw [SamplerParameters.output,ite_eq_left ht]
      exact Graph.clique_sound q hq0 hδq
    · rw [SamplerParameters.output,ite_eq_right ht]
      apply Graph.ofSimple_alpha
      apply H U V L R C lc hs
      intro x hx
      exact ht ⟨x,hx⟩

end LargeIndependentSets

end OAI
