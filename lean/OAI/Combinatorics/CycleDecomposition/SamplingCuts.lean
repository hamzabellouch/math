import OAI.Combinatorics.CycleDecomposition.Sampling

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7

section
namespace ErdosGallai.Sampling
open Finset MeasureTheory ProbabilityTheory Real
open scoped symmDiff
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

noncomputable def cutColor (e : V × V) : ℕ :=
  (Fintype.equivFin V e.1).val + (Fintype.equivFin V e.2).val

lemma cutColor_lt {V : Type cycleUniverse2} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (e : V × V) : cutColor e < 2 * Fintype.card V := by
  have h₁ := (Fintype.equivFin V e.1).isLt
  have h₂ := (Fintype.equivFin V e.2).isLt
  dsimp [cutColor]
  omega

lemma same_cutColor_blocks_disjoint (A B : Finset V) (hAB : Disjoint A B)
    {e f : V × V} (he₁ : e.1 ∈ A) (he₂ : e.2 ∈ B)
    (hf₁ : f.1 ∈ A) (hf₂ : f.2 ∈ B) (hc : cutColor e = cutColor f) (hef : e ≠ f) :
    Disjoint ({e.1, e.2} : Finset V) {f.1, f.2} := by
  have h₁ : e.1 ≠ f.1 := by
    intro h
    have ht : e.2 = f.2 := (Fintype.equivFin V).injective (Fin.ext (by
      dsimp [cutColor] at hc
      rw [h] at hc
      omega))
    exact hef (Prod.ext h ht)
  have h₂ : e.2 ≠ f.2 := by
    intro h
    have ht : e.1 = f.1 := (Fintype.equivFin V).injective (Fin.ext (by
      dsimp [cutColor] at hc
      rw [h] at hc
      omega))
    exact hef (Prod.ext ht h)
  have h₃ : e.1 ≠ f.2 := fun h => Finset.disjoint_left.mp hAB he₁ (h ▸ hf₂)
  have h₄ : e.2 ≠ f.1 := fun h => Finset.disjoint_left.mp hAB hf₁ (h ▸ he₂)
  simp [Finset.disjoint_left, h₁, h₂, h₃, h₄]

lemma blockIndicator_sum_card (E : Finset (V × V)) (ω : V → Bool) :
    (∑ e ∈ E, blockIndicator ({e.1, e.2} : Finset V) ω) =
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) := by
  classical
  simp only [blockIndicator, Set.indicator_apply, Set.mem_ofPred_eq,
    Finset.insert_subset_iff, Finset.singleton_subset_iff]
  exact Finset.sum_boole _ _

lemma sampled_matching_lower_tail (p : unitInterval) (A B : Finset V) (hAB : Disjoint A B)
    (E : Finset (V × V)) (hE : ∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ B)
    (c : ℕ) (hc : ∀ e ∈ E, cutColor e = c) :
    (sampleMeasure V p).real {ω |
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) ≤
        (p : ℝ) ^ 2 * E.card / 2} ≤ exp (-(p : ℝ) ^ 2 * E.card / 8) := by
  classical
  let S : E → Finset V := fun e => {e.val.1, e.val.2}
  have hS : Pairwise fun e f : E => Disjoint (S e) (S f) := by
    intro e f hef
    exact same_cutColor_blocks_disjoint A B hAB (hE e e.property).1 (hE e e.property).2
      (hE f f.property).1 (hE f f.property).2 ((hc e e.property).trans (hc f f.property).symm)
      (fun h => hef (Subtype.ext h))
  have hd : ∀ e : E, (S e).card = 2 := by
    intro e
    apply Finset.card_pair
    intro h
    exact Finset.disjoint_left.mp hAB (hE e e.property).1 (h ▸ (hE e e.property).2)
  have ht := sample_blocks_lower_tail p S hS 2 hd Finset.univ
  have heq (ω : V → Bool) : (∑ e : E, blockIndicator (S e) ω) =
      (∑ e ∈ E, blockIndicator ({e.1, e.2} : Finset V) ω) := by
    exact Finset.sum_attach E (fun e => blockIndicator ({e.1, e.2} : Finset V) ω)
  simp_rw [heq, blockIndicator_sum_card] at ht
  simpa using ht

lemma sum_cutColor_class_card (E : Finset (V × V)) :
    (∑ i ∈ Finset.range (2 * Fintype.card V), (E.filter (fun e => cutColor e = i)).card) =
      E.card := by
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  apply Finset.filter_true_of_mem
  intro e _
  exact Finset.mem_range.mpr (cutColor_lt e)

theorem sampled_bipartite_cut_lower_tail (p : unitInterval)
    (hr : 0 < Fintype.card V) (A B : Finset V) (hAB : Disjoint A B)
    (E : Finset (V × V)) (hE : ∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ B) :
    (sampleMeasure V p).real {ω |
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) <
        (p : ℝ) ^ 2 * E.card / 4} ≤
      2 * (Fintype.card V : ℝ) * exp (-(p : ℝ) ^ 2 * E.card / (32 * Fintype.card V)) := by
  classical
  let r : ℝ := Fintype.card V
  have hrR : 0 < r := by
    change 0 < (Fintype.card V : ℝ)
    exact_mod_cast hr
  let colors := Finset.range (2 * Fintype.card V)
  let C (i : ℕ) := E.filter (fun e => cutColor e = i)
  let m (i : ℕ) : ℝ := (C i).card
  let L := colors.filter (fun i => (E.card : ℝ) / (4 * r) ≤ m i)
  let retained (i : ℕ) (ω : V → Bool) : ℝ :=
    ((C i |>.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ)
  have hsum : ∑ i ∈ colors, m i = (E.card : ℝ) := by
    dsimp [colors, m, C]
    exact_mod_cast sum_cutColor_class_card E
  have hretain (ω : V → Bool) : ∑ i ∈ colors, retained i ω =
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) := by
    have ht := sum_cutColor_class_card
      (E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω))
    simpa only [retained, C, colors, Finset.filter_filter, and_comm, Nat.cast_sum] using
      (show (∑ i ∈ Finset.range (2 * Fintype.card V),
        (((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).filter
          (fun e => cutColor e = i)).card : ℝ)) = _ by exact_mod_cast ht)
  have hlarge : (E.card : ℝ) / 2 ≤ ∑ i ∈ L, m i := by
    have hb : ∑ i ∈ colors, m i ≤
        ∑ i ∈ colors, ((if i ∈ L then m i else 0) + (E.card : ℝ) / (4 * r)) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hiL : i ∈ L
      · simp only [hiL, ↓reduceIte]
        have : 0 ≤ (E.card : ℝ) / (4 * r) := by positivity
        linarith
      · have hiM : m i < (E.card : ℝ) / (4 * r) := by
          simpa only [L, Finset.mem_filter, hi, true_and, not_le] using hiL
        simp only [hiL, ↓reduceIte, zero_add]
        exact hiM.le
    rw [hsum, Finset.sum_add_distrib, Finset.sum_ite_mem] at hb
    have hsub : colors ∩ L = L := Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
    rw [hsub] at hb
    have hconst : ∑ _i ∈ colors, (E.card : ℝ) / (4 * r) = (E.card : ℝ) / 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, colors, Finset.card_range, Nat.cast_mul,
        Nat.cast_ofNat]
      dsimp [r] at *
      field_simp
      ; ring
    rw [hconst] at hb
    linarith
  let Bad (i : ℕ) : Set (V → Bool) :=
    {ω | retained i ω ≤ (p : ℝ) ^ 2 * m i / 2}
  have hcover : {ω |
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) <
        (p : ℝ) ^ 2 * E.card / 4} ⊆ ⋃ i ∈ L, Bad i := by
    intro ω hfail
    by_contra hnot
    have hiok : ∀ i ∈ L, (p : ℝ) ^ 2 * m i / 2 ≤ retained i ω := by
      intro i hi
      have hn : ω ∉ Bad i := fun h => hnot (Set.mem_iUnion.mpr ⟨i,
        Set.mem_iUnion.mpr ⟨hi, h⟩⟩)
      exact (lt_of_not_ge hn).le
    have hs₁ : (p : ℝ) ^ 2 / 2 * (∑ i ∈ L, m i) ≤ ∑ i ∈ L, retained i ω := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ = (p : ℝ) ^ 2 * m i / 2 := by ring
        _ ≤ retained i ω := hiok i hi
    have hs₂ : (∑ i ∈ L, retained i ω) ≤ ∑ i ∈ colors, retained i ω :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => Nat.cast_nonneg _)
    rw [hretain] at hs₂
    have hs₃ := mul_le_mul_of_nonneg_left hlarge (by positivity : 0 ≤ (p : ℝ) ^ 2 / 2)
    change ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) <
      (p : ℝ) ^ 2 * E.card / 4 at hfail
    nlinarith
  have hbad (i : ℕ) (hi : i ∈ L) : (sampleMeasure V p).real (Bad i) ≤
      exp (-(p : ℝ) ^ 2 * E.card / (32 * r)) := by
    have ht := sampled_matching_lower_tail p A B hAB (C i)
      (fun e he => hE e (Finset.mem_filter.mp he).1) i
      (fun e he => (Finset.mem_filter.mp he).2)
    have hm : (E.card : ℝ) / (4 * r) ≤ m i := (Finset.mem_filter.mp hi).2
    have he : -(p : ℝ) ^ 2 * m i / 8 ≤ -(p : ℝ) ^ 2 * E.card / (32 * r) := by
      have ht := mul_le_mul_of_nonpos_left hm (neg_nonpos.mpr (sq_nonneg (p : ℝ)))
      calc
        _ ≤ (-(p : ℝ) ^ 2 * ((E.card : ℝ) / (4 * r))) / 8 := by linarith
        _ = _ := by ring
    exact ht.trans (exp_le_exp.mpr he)
  calc
    _ ≤ (sampleMeasure V p).real (⋃ i ∈ L, Bad i) := measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ i ∈ L, (sampleMeasure V p).real (Bad i) := measureReal_biUnion_finset_le L Bad
    _ ≤ ∑ i ∈ L, exp (-(p : ℝ) ^ 2 * E.card / (32 * r)) := Finset.sum_le_sum hbad
    _ = (L.card : ℝ) * exp (-(p : ℝ) ^ 2 * E.card / (32 * r)) := by simp
    _ ≤ 2 * r * exp (-(p : ℝ) ^ 2 * E.card / (32 * r)) := by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      have ht := Finset.card_le_card (Finset.filter_subset (fun i => (E.card : ℝ) / (4 * r) ≤ m i) colors)
      have ht' : L.card ≤ 2 * Fintype.card V := by
        simpa only [colors, Finset.card_range] using ht
      change (L.card : ℝ) ≤ 2 * (Fintype.card V : ℝ)
      exact_mod_cast ht'

def neighborsIn (P : SimpleGraph V) [DecidableRel P.Adj] (v : V) (A : Finset V) :=
  A.filter (P.Adj v)

lemma card_interedges_eq_sum_neighborsIn {V : Type cycleUniverse3} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    (A B : Finset V) : (P.interedges A B).card = ∑ v ∈ A, (neighborsIn P v B).card := by
  simp only [SimpleGraph.interedges, Rel.interedges, neighborsIn, Finset.card_filter]
  rw [Finset.sum_product]

lemma neighborsIn_partition_card {V : Type cycleUniverse4} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    (v : V) (A W : Finset V) (hAW : A ⊆ W) :
    (neighborsIn P v W).card = (neighborsIn P v A).card + (neighborsIn P v (W \ A)).card := by
  have hu : neighborsIn P v W = neighborsIn P v A ∪ neighborsIn P v (W \ A) := by
    ext x; simp only [neighborsIn, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · intro ⟨hx, ha⟩
      by_cases hxA : x ∈ A
      · exact Or.inl ⟨hxA, ha⟩
      · exact Or.inr ⟨⟨hx, hxA⟩, ha⟩
    · rintro (⟨hx, ha⟩ | ⟨⟨hx, _⟩, ha⟩)
      · exact ⟨hAW hx, ha⟩
      · exact ⟨hx, ha⟩
  rw [hu, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2 (Finset.mem_filter.mp hx).1

lemma interedges_sym2_injective {V : Type cycleUniverse5} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    (A B : Finset V) (hAB : Disjoint A B) :
    Set.InjOn (fun e : V × V => s(e.1, e.2)) (P.interedges A B : Set (V × V)) := by
  intro e he f hf hef
  rcases Sym2.mk_eq_mk_iff.mp hef with h | h
  · exact h
  · exact False.elim <| Finset.disjoint_left.mp hAB (P.mem_interedges_iff.mp he).1
      ((congrArg Prod.fst h).symm ▸ (P.mem_interedges_iff.mp hf).2.1)

lemma cut_perturbation_card (P : SimpleGraph V) [DecidableRel P.Adj]
    (W A T : Finset V) (_hAW : A ⊆ W) (_hTW : T ⊆ W) :
    (P.interedges T (W \ T)).card ≤ (P.interedges A (W \ A)).card +
      Fintype.card V * (A ∆ T).card := by
  classical
  let f := fun e : V × V => s(e.1, e.2)
  let E := (P.interedges A (W \ A)).image f
  let D := (((A ∆ T) ×ˢ (Finset.univ : Finset V)).image f)
  have hinj := interedges_sym2_injective P T (W \ T) (Finset.disjoint_left.mpr (by
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 hx))
  have hsub : (P.interedges T (W \ T)).image f ⊆ E ∪ D := by
    intro e he
    obtain ⟨⟨x,y⟩, hxy, rfl⟩ := Finset.mem_image.mp he
    rcases P.mem_interedges_iff.mp hxy with ⟨hxT, hyWT, hxy⟩
    obtain ⟨hyW, hyT⟩ := Finset.mem_sdiff.mp hyWT
    by_cases hxA : x ∈ A
    · by_cases hyA : y ∈ A
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨(y,x), Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
        · exact Finset.mem_symmDiff.mpr (Or.inl ⟨hyA, hyT⟩)
        · exact Sym2.eq_swap
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨(x,y), P.mem_interedges_iff.mpr
          ⟨hxA, Finset.mem_sdiff.mpr ⟨hyW, hyA⟩, hxy⟩, rfl⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(x,y), Finset.mem_product.mpr
        ⟨Finset.mem_symmDiff.mpr (Or.inr ⟨hxT, hxA⟩), Finset.mem_univ _⟩, rfl⟩
  calc
    _ = ((P.interedges T (W \ T)).image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (E ∪ D).card := Finset.card_le_card hsub
    _ ≤ E.card + D.card := Finset.card_union_le _ _
    _ ≤ (P.interedges A (W \ A)).card + (((A ∆ T) ×ˢ (Finset.univ : Finset V))).card :=
      Nat.add_le_add (Finset.card_image_le) Finset.card_image_le
    _ = _ := by simp [mul_comm]

lemma card_le_add_symmDiff {V : Type cycleUniverse6} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (A T : Finset V) : A.card ≤ T.card + (A ∆ T).card := by
  have hs : A ⊆ T ∪ (A ∆ T) := by
    intro x hx
    by_cases hxT : x ∈ T
    · exact Finset.mem_union_left _ hxT
    · exact Finset.mem_union_right _ (Finset.mem_symmDiff.mpr (Or.inl ⟨hx,hxT⟩))
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

lemma sdiff_card_le_add_symmDiff {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (W A T : Finset V) :
    (W \ A).card ≤ (W \ T).card + (A ∆ T).card := by
  have hs : W \ A ⊆ (W \ T) ∪ (A ∆ T) := by
    intro x hx
    obtain ⟨hxW,hxA⟩ := Finset.mem_sdiff.mp hx
    by_cases hxT : x ∈ T
    · exact Finset.mem_union_right _ (Finset.mem_symmDiff.mpr (Or.inr ⟨hxT,hxA⟩))
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxW,hxT⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

lemma cut_card_lower_of_neighbors (P : SimpleGraph V) [DecidableRel P.Adj]
    (A B Q : Finset V) (hQA : Q ⊆ A) (c : ℝ)
    (hc : ∀ v ∈ Q, c ≤ (neighborsIn P v B).card) :
    c * Q.card ≤ ((P.interedges A B).card : ℝ) := by
  rw [card_interedges_eq_sum_neighborsIn, Nat.cast_sum]
  calc
    _ = ∑ v ∈ Q, c := by simp [mul_comm]
    _ ≤ ∑ v ∈ Q, ((neighborsIn P v B).card : ℝ) := Finset.sum_le_sum hc
    _ ≤ ∑ v ∈ A, ((neighborsIn P v B).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hQA (fun _ _ _ => Nat.cast_nonneg _)

lemma bad_sampled_cut_size_and_exceptional (P : SimpleGraph V) [DecidableRel P.Adj]
    (W A : Finset V) (hAW : A ⊆ W) (_ha : 0 < (A.card : ℝ))
    {p h τ : ℝ} (hp : 0 < p) (hh : 0 < h) (hτ : τ < p*h/4)
    (hdeg : ∀ v, p*h/2 ≤ ((neighborsIn P v W).card : ℝ))
    (hbad : ((P.interedges A (W \ A)).card : ℝ) < τ * A.card) :
    p*h/4 < (A.card : ℝ) ∧
      ((A \ A.filter (fun v => p*h/4 ≤ ((neighborsIn P v A).card : ℝ))).card : ℝ) ≤
        4*τ*A.card/(p*h) := by
  have hpart (v : V) : ((neighborsIn P v W).card : ℝ) =
      ((neighborsIn P v A).card : ℝ) + ((neighborsIn P v (W \ A)).card : ℝ) := by
    exact_mod_cast neighborsIn_partition_card P v A W hAW
  constructor
  · by_contra hn
    have ha' : (A.card : ℝ) ≤ p*h/4 := le_of_not_gt hn
    have hlo : p*h/4 * A.card ≤ ((P.interedges A (W \ A)).card : ℝ) := by
      apply cut_card_lower_of_neighbors P A (W \ A) A (Finset.Subset.refl _) (p*h/4)
      intro v _
      have hc : ((neighborsIn P v A).card : ℝ) ≤ A.card := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset (P.Adj v) A)
      have hd := hdeg v
      have he := hpart v
      linarith
    nlinarith
  · let Q := A \ A.filter (fun v => p*h/4 ≤ ((neighborsIn P v A).card : ℝ))
    have hl : p*h/4 * Q.card ≤ ((P.interedges A (W \ A)).card : ℝ) := by
      apply cut_card_lower_of_neighbors P A (W \ A) Q Finset.sdiff_subset (p*h/4)
      intro v hv
      obtain ⟨hvA,hvG⟩ := Finset.mem_sdiff.mp hv
      have hn : ((neighborsIn P v A).card : ℝ) < p*h/4 := by
        simpa only [Finset.mem_filter, hvA, true_and, not_le] using hvG
      have hd := hdeg v
      have he := hpart v
      linarith
    change (Q.card : ℝ) ≤ _
    apply (le_div_iff₀ (mul_pos hp hh)).mpr
    nlinarith

def neighborhoodUnion (P : SimpleGraph V) [DecidableRel P.Adj] (S : Finset V) : Finset V :=
  S.biUnion (fun v => neighborsIn P v Finset.univ)

lemma neighborhoodUnion_leakage (P : SimpleGraph V) [DecidableRel P.Adj]
    (S W A : Finset V) :
    (((neighborhoodUnion P S ∩ W) \ A).card : ℝ) ≤
      ∑ v ∈ S, ((neighborsIn P v (W \ A)).card : ℝ) := by
  have heq : (neighborhoodUnion P S ∩ W) \ A =
      S.biUnion (fun v => neighborsIn P v (W \ A)) := by
    ext x
    simp only [neighborhoodUnion, neighborsIn, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    aesop
  rw [heq]
  exact_mod_cast Finset.card_biUnion_le

lemma hitting_neighborhoodUnion (P : SimpleGraph V) [DecidableRel P.Adj]
    (good S A : Finset V) (hhit : ∀ v ∈ good, ¬Disjoint (neighborsIn P v A) S) :
    good ⊆ neighborhoodUnion P S := by
  intro v hv
  obtain ⟨x,hxK,hxS⟩ := Finset.not_disjoint_iff.mp (hhit v hv)
  apply Finset.mem_biUnion.mpr
  refine ⟨x,hxS,?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, P.adj_symm (Finset.mem_filter.mp hxK).2⟩

theorem exists_approximating_witness (P : SimpleGraph V) [DecidableRel P.Adj]
    (W A : Finset V) (hAW : A ⊆ W) (ha : 0 < (A.card : ℝ))
    {p h τ M : ℝ} (hp : 0 < p) (hh : 0 < h) (hτ0 : 0 < τ)
    (hτ : τ < p*h/4) (hM : 0 < M) (hMh : M ≤ h)
    (hmiss : (Fintype.card V : ℝ) * exp (-p*M/4) < 1/2)
    (hdeg : ∀ v, p*h/2 ≤ ((neighborsIn P v W).card : ℝ))
    (hbad : ((P.interedges A (W \ A)).card : ℝ) < τ * A.card) :
    p*h/4 < (A.card : ℝ) ∧ ∃ S : Finset V, S ⊆ A ∧
      (S.card : ℝ) ≤ 4 * A.card * M / h ∧
      ((A ∆ (neighborhoodUnion P S ∩ W)).card : ℝ) ≤
        (4*τ/(p*h) + 4*τ*M/h) * A.card := by
  classical
  obtain ⟨hlarge, hexc⟩ := bad_sampled_cut_size_and_exceptional P W A hAW ha hp hh hτ hdeg hbad
  refine ⟨hlarge, ?_⟩
  let good := A.filter (fun v => p*h/4 ≤ ((neighborsIn P v A).card : ℝ))
  let w : V → ℝ := fun v => ((neighborsIn P v (W \ A)).card : ℝ)
  let q : unitInterval := ⟨M/h, div_nonneg hM.le hh.le, (div_le_one hh).mpr hMh⟩
  have hq : 0 < (q : ℝ) := div_pos hM hh
  have hm : (good.card : ℝ) * exp (-(q : ℝ) * (p*h/4)) < 1/2 := by
    have heq : -(q : ℝ) * (p*h/4) = -p*M/4 := by
      dsimp [q]
      field_simp [hh.ne']
    rw [heq]
    have hg : (good.card : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ good
    exact (mul_le_mul_of_nonneg_right hg (exp_pos _).le).trans_lt hmiss
  have hsum : ∑ v ∈ A, w v ≤ τ * A.card := by
    dsimp [w]
    rw [← Nat.cast_sum, ← card_interedges_eq_sum_neighborsIn]
    exact hbad.le
  obtain ⟨S,hSA,hSc,hSw,hSh⟩ := exists_small_weighted_hitting_set A
    (Finset.card_pos.mp (by exact_mod_cast ha)) good (fun v => neighborsIn P v A)
    (fun v _ => Finset.filter_subset _ _) w (fun _ _ => Nat.cast_nonneg _)
    (mul_pos hτ0 ha) hsum
    (fun v hv => (Finset.mem_filter.mp hv).2) q hq hm
  refine ⟨S,hSA,?_,?_⟩
  · convert hSc using 1 ; dsimp [q] ; ring
  · let T := neighborhoodUnion P S ∩ W
    have hgood : good ⊆ neighborhoodUnion P S := hitting_neighborhoodUnion P good S A hSh
    have hsub : A ∆ T ⊆ (A \ good) ∪ (T \ A) := by
      intro v hv
      rcases Finset.mem_symmDiff.mp hv with ⟨hvA,hvT⟩ | ⟨hvT,hvA⟩
      · apply Finset.mem_union_left
        apply Finset.mem_sdiff.mpr
        refine ⟨hvA,?_⟩
        intro hvG
        exact hvT (Finset.mem_inter.mpr ⟨hgood hvG, hAW hvA⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hvT,hvA⟩)
    have hδ : ((A ∆ T).card : ℝ) ≤ ((A \ good).card : ℝ) + ((T \ A).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hleak : ((T \ A).card : ℝ) ≤ 4*(q : ℝ)*(τ*A.card) :=
      (neighborhoodUnion_leakage P S W A).trans hSw
    change ((A ∆ T).card : ℝ) ≤ _
    change ((A \ good).card : ℝ) ≤ _ at hexc
    calc
      _ ≤ 4*τ*A.card/(p*h) + 4*(q : ℝ)*(τ*A.card) := add_le_add hexc hleak |>.trans' hδ
      _ = _ := by dsimp [q]; ring

def CutExpansion (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ) : Prop :=
  ∀ U : Finset V, h * min (U.card : ℝ) (Uᶜ.card : ℝ) ≤
    ((P.interedges U Uᶜ).card : ℝ)

def CutExpansionOn (P : SimpleGraph V) [DecidableRel P.Adj] (W : Finset V) (h : ℝ) : Prop :=
  ∀ A : Finset V, A ⊆ W → h * min (A.card : ℝ) ((W \ A).card : ℝ) ≤
    ((P.interedges A (W \ A)).card : ℝ)

theorem cutExpansionOn_of_witnesses (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) {p h τ M : ℝ} (hp : 0 < p) (hh : 0 < h) (hτ0 : 0 < τ)
    (hτ : τ < p*h/4) (hM : 0 < M) (hMh : M ≤ h)
    (hmiss : (Fintype.card V : ℝ) * exp (-p*M/4) < 1/2)
    (hε : 4*τ/(p*h) + 4*τ*M/h ≤ 1/2)
    (hperturb : τ + Fintype.card V * (4*τ/(p*h) + 4*τ*M/h) ≤ p^2*h/8)
    (hexp : CutExpansion P h)
    (hdeg : ∀ v, p*h/2 ≤ ((neighborsIn P v W).card : ℝ))
    (hwitness : ∀ S : Finset V, (S.card : ℝ) ≤ 4*Fintype.card V*M/h →
      let U := neighborhoodUnion P S
      p*h/8 ≤ min (U.card : ℝ) (Uᶜ.card : ℝ) →
      (p^2/4) * ((P.interedges U Uᶜ).card : ℝ) ≤
        ((P.interedges (U ∩ W) (W \ (U ∩ W))).card : ℝ)) :
    CutExpansionOn P W τ := by
  classical
  have hsmall (A : Finset V) (hAW : A ⊆ W)
      (hsize : (A.card : ℝ) ≤ (W \ A).card) :
      τ * A.card ≤ ((P.interedges A (W \ A)).card : ℝ) := by
    by_contra hn
    have hbad := lt_of_not_ge hn
    have ha : 0 < (A.card : ℝ) := by
      by_contra hn
      have hz : (A.card : ℝ) = 0 := (le_of_not_gt hn).antisymm (Nat.cast_nonneg _)
      rw [hz, mul_zero] at hbad
      exact (Nat.cast_nonneg _).not_gt hbad
    obtain ⟨hlarge,S,hSA,hSc,hδ⟩ := exists_approximating_witness P W A hAW ha
      hp hh hτ0 hτ hM hMh hmiss hdeg hbad
    let U := neighborhoodUnion P S
    let T := U ∩ W
    let δ : ℝ := (A ∆ T).card
    have hδ' : δ ≤ (A.card : ℝ)/2 := by
      have ht := mul_le_mul_of_nonneg_right hε ha.le
      dsimp [δ,T,U]
      linarith
    have hmin : (A.card : ℝ)/2 ≤ min (U.card : ℝ) (Uᶜ.card : ℝ) := by
      apply le_min
      · have ht : (A.card : ℝ) ≤ (T.card : ℝ) + δ := by
          dsimp [δ]
          exact_mod_cast card_le_add_symmDiff A T
        have hTU : (T.card : ℝ) ≤ U.card := by
          exact_mod_cast Finset.card_le_card (Finset.inter_subset_left : T ⊆ U)
        linarith
      · have ht : ((W \ A).card : ℝ) ≤ ((W \ T).card : ℝ) + δ := by
          dsimp [δ]
          exact_mod_cast sdiff_card_le_add_symmDiff W A T
        have hs : W \ T ⊆ Uᶜ := by
          intro v hv
          obtain ⟨hvW,hvT⟩ := Finset.mem_sdiff.mp hv
          apply Finset.mem_compl.mpr
          intro hvU
          exact hvT (Finset.mem_inter.mpr ⟨hvU,hvW⟩)
        have hh' : ((W \ T).card : ℝ) ≤ Uᶜ.card := by exact_mod_cast Finset.card_le_card hs
        linarith
    have hsbound : (S.card : ℝ) ≤ 4*Fintype.card V*M/h := by
      apply hSc.trans
      have hac : (A.card : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ A
      gcongr
    have hw := hwitness S hsbound (by dsimp [U] at hmin; linarith)
    have he := hexp U
    have hlo : p^2*h*A.card/8 ≤ ((P.interedges T (W \ T)).card : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hmin hh.le
      have ht := mul_le_mul_of_nonneg_left (hm.trans he) (by positivity : 0 ≤ p^2/4)
      change p^2/4 * ((P.interedges U Uᶜ).card : ℝ) ≤ _ at hw
      nlinarith
    have hupper : ((P.interedges T (W \ T)).card : ℝ) ≤
        ((P.interedges A (W \ A)).card : ℝ) + Fintype.card V * δ := by
      dsimp [δ]
      exact_mod_cast cut_perturbation_card P W A T hAW Finset.inter_subset_right
    have hd := mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ (Fintype.card V : ℝ))
    have hp' := mul_le_mul_of_nonneg_right hperturb ha.le
    change (Fintype.card V : ℝ) * δ ≤ _ at hd
    nlinarith
  intro A hAW
  by_cases hs : (A.card : ℝ) ≤ (W \ A).card
  · rw [min_eq_left hs]
    exact hsmall A hAW hs
  · have hs' : ((W \ A).card : ℝ) ≤ A.card := (lt_of_not_ge hs).le
    rw [min_eq_right hs']
    have heq : W \ (W \ A) = A := Finset.sdiff_sdiff_eq_self hAW
    have ht := hsmall (W \ A) Finset.sdiff_subset (by simpa only [heq] using hs')
    rw [heq] at ht
    let : Std.Symm P.Adj := P.symm
    have hcomm : (P.interedges (W \ A) A).card = (P.interedges A (W \ A)).card :=
      Rel.card_interedges_comm (W \ A) A
    rwa [hcomm] at ht

lemma cutExpansion_minDegree (P : SimpleGraph V) [DecidableRel P.Adj]
    {h : ℝ} (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V) (v : V) :
    h ≤ ((neighborsIn P v Finset.univ).card : ℝ) := by
  have ht := hexp {v}
  have hc : (1 : ℝ) ≤ ((({v} : Finset V)ᶜ).card : ℝ) := by
    have : 1 ≤ (({v} : Finset V)ᶜ).card := by
      rw [Finset.card_compl, Finset.card_singleton]
      omega
    exact_mod_cast this
  simp only [Finset.card_singleton, Nat.cast_one, min_eq_left hc, mul_one] at ht
  rw [card_interedges_eq_sum_neighborsIn, Finset.sum_singleton] at ht
  have heq : neighborsIn P v ({v} : Finset V)ᶜ = neighborsIn P v Finset.univ := by
    ext x
    simp only [neighborsIn, Finset.mem_filter, Finset.mem_compl, Finset.mem_singleton,
      Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨fun he => P.irrefl (he ▸ h), h⟩⟩
  rwa [heq] at ht

lemma sample_neighbors_lower_tail (P : SimpleGraph V) [DecidableRel P.Adj]
    (p : unitInterval) {h : ℝ} (hdeg : ∀ v, h ≤ ((neighborsIn P v Finset.univ).card : ℝ))
    (v : V) :
    (sampleMeasure V p).real {ω | ((neighborsIn P v (sampleVertices ω)).card : ℝ) < (p : ℝ)*h/2} ≤
      exp (-(p : ℝ)*h/8) := by
  have heq (ω : V → Bool) : neighborsIn P v (sampleVertices ω) =
      neighborsIn P v Finset.univ ∩ sampleVertices ω := by
    ext x; simp [neighborsIn, and_comm]
  simp_rw [heq]
  have hs : {ω | (((neighborsIn P v Finset.univ) ∩ sampleVertices ω).card : ℝ) < (p : ℝ)*h/2} ⊆
      {ω | (((neighborsIn P v Finset.univ) ∩ sampleVertices ω).card : ℝ) ≤
        (p : ℝ)*(neighborsIn P v Finset.univ).card/2} := by
    intro ω hω
    change (((neighborsIn P v Finset.univ) ∩ sampleVertices ω).card : ℝ) < (p : ℝ)*h/2 at hω
    exact hω.le.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hdeg v) p.property.1) (by norm_num))
  have he : -(p : ℝ)*(neighborsIn P v Finset.univ).card/8 ≤ -(p : ℝ)*h/8 := by
    have ht := mul_le_mul_of_nonneg_left (hdeg v) p.property.1
    linarith
  exact (measureReal_mono hs (measure_ne_top _ _)).trans
    ((sample_card_lower_tail p _).trans (exp_le_exp.mpr he))

lemma card_small_subsets_le (s : ℕ) (hr : 0 < Fintype.card V) :
    (((Finset.univ : Finset V).powerset).filter (fun S => S.card ≤ s)).card ≤
      (s+1) * Fintype.card V ^ s := by
  classical
  have heq : (((Finset.univ : Finset V).powerset).filter (fun S => S.card ≤ s)) =
      (Finset.range (s+1)).biUnion (fun t => (Finset.univ : Finset V).powersetCard t) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
      Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
    exact ⟨fun h => ⟨S.card, by omega, rfl⟩,
      fun ⟨t,ht,he⟩ => by omega⟩
  rw [heq]
  calc
    _ ≤ ∑ t ∈ Finset.range (s+1), ((Finset.univ : Finset V).powersetCard t).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ t ∈ Finset.range (s+1), Fintype.card V ^ s := by
      apply Finset.sum_le_sum
      intro t ht
      rw [Finset.card_powersetCard, Finset.card_univ]
      exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_right hr (by simpa using ht))
    _ = _ := by simp [mul_comm]

def witnessFamily (P : SimpleGraph V) [DecidableRel P.Adj] (s : ℕ) : Finset (Finset V) :=
  ((((Finset.univ : Finset V).powerset).filter (fun S => S.card ≤ s))).image (neighborhoodUnion P)

lemma card_witnessFamily_le (P : SimpleGraph V) [DecidableRel P.Adj]
    (s : ℕ) (hr : 0 < Fintype.card V) :
    (witnessFamily P s).card ≤ (s+1) * Fintype.card V ^ s :=
  Finset.card_image_le.trans (card_small_subsets_le s hr)

lemma sampled_witness_cut_lower_tail (P : SimpleGraph V) [DecidableRel P.Adj]
    (p : unitInterval) {h : ℝ} (hh : 0 ≤ h) (hexp : CutExpansion P h)
    (hr : 0 < Fintype.card V) (U : Finset V)
    (hU : (p : ℝ)*h/8 ≤ min (U.card : ℝ) (Uᶜ.card : ℝ)) :
    (sampleMeasure V p).real {ω |
      ((P.interedges (U ∩ sampleVertices ω) (sampleVertices ω \ (U ∩ sampleVertices ω))).card : ℝ) <
        (p : ℝ)^2/4 * (P.interedges U Uᶜ).card} ≤
      2 * (Fintype.card V : ℝ) * exp (-(p : ℝ)^3*h^2/(256*Fintype.card V)) := by
  have hAB : Disjoint U Uᶜ := Finset.disjoint_left.mpr (fun _ hx hy => (Finset.mem_compl.mp hy) hx)
  have heq (ω : V → Bool) :
      P.interedges (U ∩ sampleVertices ω) (sampleVertices ω \ (U ∩ sampleVertices ω)) =
        (P.interedges U Uᶜ).filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω) := by
    ext ⟨x,y⟩
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_filter, Finset.mem_compl]
    aesop
  have ht := sampled_bipartite_cut_lower_tail p hr U Uᶜ hAB (P.interedges U Uᶜ)
    (fun e he => ⟨(P.mem_interedges_iff.mp he).1, (P.mem_interedges_iff.mp he).2.1⟩)
  have hl : (p : ℝ)*h^2/8 ≤ ((P.interedges U Uᶜ).card : ℝ) := by
    have ht := mul_le_mul_of_nonneg_left hU hh
    have hu := hexp U
    nlinarith
  have he : -(p : ℝ)^2 * (P.interedges U Uᶜ).card/(32*Fintype.card V) ≤
      -(p : ℝ)^3*h^2/(256*Fintype.card V) := by
    have hrR : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hr
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hs := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (p : ℝ)^2)
    nlinarith
  simp_rw [heq]
  have hc : (p : ℝ)^2/4 * (P.interedges U Uᶜ).card = (p : ℝ)^2 * (P.interedges U Uᶜ).card/4 := by ring
  rw [hc]
  exact ht.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr he) (by positivity))

def SampleGood (P : SimpleGraph V) [DecidableRel P.Adj] (p h τ : ℝ) (ω : V → Bool) : Prop :=
  ((sampleVertices ω).card : ℝ) ≤ 2*p*Fintype.card V ∧
    (∀ v, p*h/2 ≤ ((neighborsIn P v (sampleVertices ω)).card : ℝ)) ∧
    CutExpansionOn P (sampleVertices ω) τ

theorem vertex_sampling_failure_bound (P : SimpleGraph V) [DecidableRel P.Adj]
    (p : unitInterval) {h τ M : ℝ} (hp : 0 < (p : ℝ)) (hh : 0 < h) (hτ0 : 0 < τ)
    (hτ : τ < (p : ℝ)*h/4) (hM : 0 < M) (hMh : M ≤ h)
    (hr : 2 ≤ Fintype.card V)
    (hmiss : (Fintype.card V : ℝ) * exp (-(p : ℝ)*M/4) < 1/2)
    (hε : 4*τ/((p : ℝ)*h) + 4*τ*M/h ≤ 1/2)
    (hperturb : τ + Fintype.card V * (4*τ/((p : ℝ)*h) + 4*τ*M/h) ≤ (p : ℝ)^2*h/8)
    (hexp : CutExpansion P h) :
    (sampleMeasure V p).real {ω | ¬SampleGood P (p : ℝ) h τ ω} ≤
      exp (-(p : ℝ)*Fintype.card V/3) +
      Fintype.card V * exp (-(p : ℝ)*h/8) +
      2*Fintype.card V * ((⌈4*Fintype.card V*M/h⌉₊+1 : ℕ) : ℝ) *
        (Fintype.card V : ℝ)^⌈4*Fintype.card V*M/h⌉₊ *
        exp (-(p : ℝ)^3*h^2/(256*Fintype.card V)) := by
  classical
  let μ := sampleMeasure V p
  let s := ⌈4*(Fintype.card V : ℝ)*M/h⌉₊
  let large := (witnessFamily P s).filter
    (fun U => (p : ℝ)*h/8 ≤ min (U.card : ℝ) (Uᶜ.card : ℝ))
  let B₀ : Set (V → Bool) := {ω | 2*(p : ℝ)*Fintype.card V < ((sampleVertices ω).card : ℝ)}
  let B₁ (v : V) : Set (V → Bool) :=
    {ω | ((neighborsIn P v (sampleVertices ω)).card : ℝ) < (p : ℝ)*h/2}
  let B₂ (U : Finset V) : Set (V → Bool) := {ω |
    ((P.interedges (U ∩ sampleVertices ω) (sampleVertices ω \ (U ∩ sampleVertices ω))).card : ℝ) <
      (p : ℝ)^2/4 * (P.interedges U Uᶜ).card}
  have h₀ : μ.real B₀ ≤ exp (-(p : ℝ)*Fintype.card V/3) := by
    have hs : B₀ ⊆ {ω | 2*(p : ℝ)*Fintype.card V ≤ ((sampleVertices ω).card : ℝ)} := by
      intro ω hω
      change 2*(p : ℝ)*Fintype.card V < ((sampleVertices ω).card : ℝ) at hω
      exact hω.le
    have ht := sample_card_upper_tail p (Finset.univ : Finset V)
    simp only [Finset.card_univ, Finset.univ_inter] at ht
    exact (measureReal_mono hs (measure_ne_top _ _)).trans ht
  have h₁ : μ.real (⋃ v ∈ (Finset.univ : Finset V), B₁ v) ≤
      Fintype.card V * exp (-(p : ℝ)*h/8) := by
    calc
      _ ≤ ∑ v : V, μ.real (B₁ v) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _v : V, exp (-(p : ℝ)*h/8) := Finset.sum_le_sum (fun v _ =>
        sample_neighbors_lower_tail P p (cutExpansion_minDegree P hexp hr) v)
      _ = _ := by simp
  have h₂ : μ.real (⋃ U ∈ large, B₂ U) ≤
      2*Fintype.card V * ((s+1 : ℕ) : ℝ) * (Fintype.card V : ℝ)^s *
        exp (-(p : ℝ)^3*h^2/(256*Fintype.card V)) := by
    calc
      _ ≤ ∑ U ∈ large, μ.real (B₂ U) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _U ∈ large, 2*(Fintype.card V : ℝ)*exp (-(p : ℝ)^3*h^2/(256*Fintype.card V)) := by
        apply Finset.sum_le_sum
        intro U hU
        exact sampled_witness_cut_lower_tail P p hh.le hexp (by omega) U (Finset.mem_filter.mp hU).2
      _ = (large.card : ℝ) * (2*Fintype.card V * exp (-(p : ℝ)^3*h^2/(256*Fintype.card V))) := by simp
      _ ≤ (((s+1 : ℕ) : ℝ) * (Fintype.card V : ℝ)^s) *
          (2*Fintype.card V * exp (-(p : ℝ)^3*h^2/(256*Fintype.card V))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have ht : large.card ≤ (s+1)*Fintype.card V^s :=
          (Finset.card_le_card (Finset.filter_subset _ _)).trans
            (card_witnessFamily_le P s (by omega))
        exact_mod_cast ht
      _ = _ := by ring
  have hcover : {ω | ¬SampleGood P (p : ℝ) h τ ω} ⊆
      (B₀ ∪ (⋃ v ∈ (Finset.univ : Finset V), B₁ v)) ∪ (⋃ U ∈ large, B₂ U) := by
    intro ω hω
    by_contra hn
    have hn₀ : ω ∉ B₀ := fun h => hn (Or.inl (Or.inl h))
    have hn₁ (v : V) : ω ∉ B₁ v := fun h => hn (Or.inl (Or.inr
      (Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨Finset.mem_univ _, h⟩⟩)))
    have hn₂ (U : Finset V) (hU : U ∈ large) : ω ∉ B₂ U := fun h => hn (Or.inr
      (Set.mem_iUnion.mpr ⟨U, Set.mem_iUnion.mpr ⟨hU,h⟩⟩))
    apply hω
    have hd (v : V) : (p : ℝ)*h/2 ≤ ((neighborsIn P v (sampleVertices ω)).card : ℝ) :=
      le_of_not_gt (hn₁ v)
    refine ⟨le_of_not_gt hn₀, hd, ?_⟩
    apply cutExpansionOn_of_witnesses P (sampleVertices ω) hp hh hτ0 hτ hM hMh
      hmiss hε hperturb hexp hd
    intro S hS
    dsimp only
    intro hU
    let U := neighborhoodUnion P S
    have hSc : S.card ≤ s := by
      have ht := hS.trans (Nat.le_ceil (4*(Fintype.card V : ℝ)*M/h))
      dsimp [s]
      exact_mod_cast ht
    have hmem : U ∈ large := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, hU⟩
      apply Finset.mem_image.mpr
      exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hSc⟩, rfl⟩
    exact le_of_not_gt (hn₂ U hmem)
  calc
    _ ≤ μ.real ((B₀ ∪ (⋃ v ∈ (Finset.univ : Finset V), B₁ v)) ∪ (⋃ U ∈ large, B₂ U)) :=
      measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ μ.real (B₀ ∪ (⋃ v ∈ (Finset.univ : Finset V), B₁ v)) + μ.real (⋃ U ∈ large, B₂ U) :=
      measureReal_union_le _ _
    _ ≤ μ.real B₀ + μ.real (⋃ v ∈ (Finset.univ : Finset V), B₁ v) + μ.real (⋃ U ∈ large, B₂ U) :=
      add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add h₀ h₁) h₂

end ErdosGallai.Sampling

end

end OAI
