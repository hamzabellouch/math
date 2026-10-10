import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Selection.GreedyPivots

namespace OAI

namespace SiegelZeros

open scoped BigOperators
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped BigOperators
open scoped BigOperators
namespace WeightedTorusJets

def weightedJetIndices (H B : ℕ) : Finset (Fin 3 → ℕ) :=
  (Fintype.piFinset (fun _ : Fin 3 => Finset.range (B + 1))).filter
    (fun α => α 0 + H * α 1 + H * α 2 ≤ B)

theorem mem_weightedJetIndices_iff {H B : ℕ} (hH : 0 < H) (α : Fin 3 → ℕ) :
    α ∈ weightedJetIndices H B ↔ α 0 + H * α 1 + H * α 2 ≤ B := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    have h1 : α 1 ≤ H * α 1 := Nat.le_mul_of_pos_left _ hH
    have h2 : α 2 ≤ H * α 2 := Nat.le_mul_of_pos_left _ hH
    fin_cases i
    · change α 0 < B + 1
      omega
    · change α 1 < B + 1
      omega
    · change α 2 < B + 1
      omega



theorem extendFiniteFamily_injOn_range {α : Type*} {n : ℕ} (f : Fin n → α)
    (hf : Function.Injective f) (fallback : α) :
    Set.InjOn (extendFiniteFamily f fallback) (Finset.range n : Set ℕ) := by
  intro i hi j hj hij
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  have heq : f ⟨i, hi'⟩ = f ⟨j, hj'⟩ := by
    simpa [extendFiniteFamily, hi', hj'] using hij
  exact congrArg Fin.val (hf heq)

noncomputable def finiteGreedyPivots (K : Type*) [DivisionRing K]
    {α V : Type*} [AddCommGroup V] [Module K V] (s : Finset α) (R : α → V)
    (e : Fin s.card ≃ s) (fallback : α) : Finset α := by
  classical
  let a := extendFiniteFamily (fun i => (e i : α)) fallback
  exact (greedyPivots K (R ∘ a) s.card).image a

theorem finiteGreedyPivots_spec {K α V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (s : Finset α) (R : α → V)
    (e : Fin s.card ≃ s) (fallback : α)
    (hspan : Submodule.span K (R '' (s : Set α)) = ⊤) :
    finiteGreedyPivots K s R e fallback ⊆ s ∧
      (finiteGreedyPivots K s R e fallback).card = Module.finrank K V ∧
      LinearIndepOn K R (finiteGreedyPivots K s R e fallback : Set α) ∧
      Submodule.span K (R '' (finiteGreedyPivots K s R e fallback : Set α)) = ⊤ := by
  classical
  let a := extendFiniteFamily (fun i => (e i : α)) fallback
  let v := R ∘ a
  let I := greedyPivots K v s.card
  have hI : I ⊆ Finset.range s.card := greedyPivots_subset_range v s.card
  have hainj : Set.InjOn a (Finset.range s.card : Set ℕ) :=
    extendFiniteFamily_injOn_range _ (Subtype.val_injective.comp e.injective) fallback
  have haimage : a '' (Finset.range s.card : Set ℕ) = (s : Set α) := by
    rw [show a = extendFiniteFamily (fun i => (e i : α)) fallback from rfl,
      image_extendFiniteFamily_range]
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩
  have hvimage : v '' (Finset.range s.card : Set ℕ) = R '' (s : Set α) := by
    rw [show v = R ∘ a from rfl, Set.image_comp, haimage]
  have hvspan : Submodule.span K (v '' (Finset.range s.card : Set ℕ)) = ⊤ := by
    rw [hvimage, hspan]
  change I.image a ⊆ s ∧ (I.image a).card = _ ∧
    LinearIndepOn K R (I.image a : Set α) ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    change a i ∈ (s : Set α)
    rw [← haimage]
    exact Set.mem_image_of_mem a (hI hi)
  · rw [Finset.card_image_of_injOn (hainj.mono hI)]
    exact card_greedyPivots_of_span_eq_top v s.card hvspan
  · rw [Finset.coe_image]
    exact LinearIndepOn.image_of_comp a R (greedyPivots_linearIndepOn v s.card)
  · change Submodule.span K (R '' (I.image a : Set α)) = ⊤
    rw [Finset.coe_image, ← Set.image_comp]
    exact (span_greedyPivots v s.card).trans hvspan

theorem finiteGreedyPivots_weighted_bounds {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (s : Finset (Fin 3 → ℕ)) (R : (Fin 3 → ℕ) → V)
    (e : Fin s.card ≃ s) (H N : ℕ) (hH : 0 < H) (hHN : H ≤ N)
    (hN : 18818 ≤ N) (hdim : Module.finrank K V = N ^ 4)
    (hspan : Submodule.span K (R '' (s : Set (Fin 3 → ℕ))) = ⊤)
    (hw : ∀ a ∈ s, (a 0 : ℝ) + (H : ℝ) * a 1 + (H : ℝ) * a 2 ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) :
    let P := finiteGreedyPivots K s R e 0
    P.card = N ^ 4 ∧ LinearIndepOn K R (P : Set (Fin 3 → ℕ)) ∧
      (N : ℝ) ^ 4 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) /
        (4 * 97 ^ 2) ≤ ∑ a ∈ P, (a 0 : ℝ) ∧
      (∑ a ∈ P, ((a 1 : ℝ) + a 2)) ≤
        192 * (N : ℝ) ^ 4 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) := by
  dsimp only
  obtain ⟨hsub, hcard, hlin, _⟩ := finiteGreedyPivots_spec s R e 0 hspan
  have hcard' := hcard.trans hdim
  exact ⟨hcard', hlin, weighted_pivot_bounds _ H N hH hHN hN hcard'
    (fun a ha => hw a (hsub ha))⟩

theorem row_space_finrank {K : Type*} [DivisionRing K] (N : ℕ) :
    Module.finrank K ((Fin 4 → Fin N) → K) = N ^ 4 := by
  simp

theorem finiteGreedyPivots_sum {K α V β : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [AddCommMonoid β]
    (s : Finset α) (R : α → V) (e : Fin s.card ≃ s) (fallback : α) (f : α → β) :
    let a := extendFiniteFamily (fun i => (e i : α)) fallback
    ∑ x ∈ finiteGreedyPivots K s R e fallback, f x =
      ∑ i ∈ greedyPivots K (R ∘ a) s.card, f (a i) := by
  classical
  dsimp only [finiteGreedyPivots]
  apply Finset.sum_image
  have hinj := extendFiniteFamily_injOn_range (fun i => (e i : α))
    (Subtype.val_injective.comp e.injective) fallback
  exact hinj.mono (greedyPivots_subset_range _ _)

theorem sum_embedding_eq_sum_of_range {β : Type*} [AddCommMonoid β]
    (I : Finset ℕ) (m : ℕ) (e : Fin m ↪ ℕ) (he : Set.range e = (I : Set ℕ))
    (f : ℕ → β) : (∑ i : Fin m, f (e i)) = ∑ i ∈ I, f i := by
  apply Finset.sum_bij (fun i _ => e i)
  · intro i _
    change e i ∈ (I : Set ℕ)
    rw [← he]
    exact Set.mem_range_self i
  · intro i _ j _ hij
    exact e.injective hij
  · intro j hj
    have hj' : j ∈ Set.range e := he ▸ hj
    obtain ⟨i, rfl⟩ := hj'
    exact ⟨i, Finset.mem_univ i, rfl⟩
  · intro i _
    rfl

theorem weightedJetIndices_real_weight {H : ℕ} (hH : 0 < H) {W : ℝ}
    (hW : 0 ≤ W) {a : Fin 3 → ℕ} (ha : a ∈ weightedJetIndices H ⌊W⌋₊) :
    (a 0 : ℝ) + (H : ℝ) * a 1 + (H : ℝ) * a 2 ≤ W := by
  have hnat := (mem_weightedJetIndices_iff hH a).mp ha
  have hreal : (a 0 : ℝ) + (H : ℝ) * a 1 + (H : ℝ) * a 2 ≤ (⌊W⌋₊ : ℝ) := by
    exact_mod_cast hnat
  exact hreal.trans (Nat.floor_le hW)



theorem mem_weightedJetIndices_of_rectangle {H : ℕ} {U : ℝ} (hH : 0 < H)
    (a : Fin 3 → ℕ)
    (ha₀ : (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * U)
    (ha₁ : (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U)
    (ha₂ : (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U) :
    a ∈ weightedJetIndices H ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * U⌋₊ := by
  apply (mem_weightedJetIndices_iff hH a).mpr
  apply Nat.le_floor
  push_cast
  exact pivot_weight_of_rectangle (by exact_mod_cast hH) (a 0) (a 1) (a 2) ha₀ ha₁ ha₂

theorem span_cutoff_eq_top_of_rectangle {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] {H : ℕ} {U : ℝ} (hH : 0 < H)
    (R : (Fin 3 → ℕ) → V)
    (hspan : Submodule.span K (R '' {a : Fin 3 → ℕ |
      (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * U ∧
      (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U ∧
      (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U}) = ⊤) :
    Submodule.span K (R '' (weightedJetIndices H
      ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * U⌋₊ : Set (Fin 3 → ℕ))) = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  apply Set.image_mono
  intro a ha
  exact mem_weightedJetIndices_of_rectangle hH a ha.1 ha.2.1 ha.2.2



theorem rectangle_span_yields_sorted_greedy_pivots {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (R : (Fin 3 → ℕ) → V)
    (H N : ℕ) (hH : 0 < H) (hHN : H ≤ N) (hN : 18818 ≤ N)
    (hdim : Module.finrank K V = N ^ 4)
    (hspan : Submodule.span K (R '' {a : Fin 3 → ℕ |
      (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)}) = ⊤) :
    let s := weightedJetIndices H
      ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)⌋₊
    ∃ e : Fin s.card ≃ s,
      Monotone (fun i => (e i).1 0 + H * (e i).1 1 + H * (e i).1 2) ∧
      let P := finiteGreedyPivots K s R e 0
      P.card = N ^ 4 ∧ LinearIndepOn K R (P : Set (Fin 3 → ℕ)) ∧
      (N : ℝ) ^ 4 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) /
        (4 * 97 ^ 2) ≤ ∑ a ∈ P, (a 0 : ℝ) ∧
      (∑ a ∈ P, ((a 1 : ℝ) + a 2)) ≤
        192 * (N : ℝ) ^ 4 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) := by
  dsimp only
  obtain ⟨e, he⟩ := exists_weight_sorted_enumeration
    (weightedJetIndices H ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)⌋₊)
    (fun a => a 0 + H * a 1 + H * a 2)
  refine ⟨e, he, ?_⟩
  apply finiteGreedyPivots_weighted_bounds _ R e H N hH hHN hN hdim
    (span_cutoff_eq_top_of_rectangle hH R hspan)
  intro a ha
  exact weightedJetIndices_real_weight hH (by positivity) ha

end WeightedTorusJets

open Module
open scoped BigOperators

namespace WeightedTorusJets

theorem det_ne_zero_of_linearIndepOn_rows
    {K ι n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (s : Finset ι) (R : ι → n → K) (e : n ≃ s)
    (hlin : LinearIndepOn K R (s : Set ι)) :
    Matrix.det (fun i j => R (e i) j) ≠ 0 := by
  classical
  have hrows : LinearIndependent K (fun i j => R (e i) j) :=
    hlin.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero

theorem span_rows_eq_top_of_detects
    {K ι n : Type*} [Field K] [Fintype n]
    (s : Finset ι) (R : ι → n → K)
    (hdetect : ∀ c : n → K, c ≠ 0 → ∃ a ∈ s, ∑ j, R a j * c j ≠ 0) :
    Submodule.span K (R '' (s : Set ι)) = ⊤ := by
  classical
  apply (Submodule.map_eq_top_iff (e := dotProductEquiv K n)).mp
  rw [Submodule.map_span]
  apply Submodule.span_eq_top_of_ne_zero
  intro c hc
  obtain ⟨a, ha, hsum⟩ := hdetect c hc
  exact ⟨dotProductEquiv K n (R a),
    Set.mem_image_of_mem _ (Set.mem_image_of_mem R ha), hsum⟩

theorem detects_of_field_embedding
    {K L ι n : Type*} [Field K] [Field L] [Fintype n]
    (s : Finset ι) (R : ι → n → K) (f : K →+* L)
    (hdetect : ∀ c : n → L, c ≠ 0 → ∃ a ∈ s, ∑ j, f (R a j) * c j ≠ 0) :
    ∀ c : n → K, c ≠ 0 → ∃ a ∈ s, ∑ j, R a j * c j ≠ 0 := by
  intro c hc
  have hfc : (fun j => f (c j)) ≠ 0 := by
    intro heq
    apply hc
    funext j
    apply f.injective
    simpa only [Pi.zero_apply, map_zero] using congr_fun heq j
  obtain ⟨a, ha, hsum⟩ := hdetect (fun j => f (c j)) hfc
  refine ⟨a, ha, fun heq => hsum ?_⟩
  simpa only [map_sum, map_mul, map_zero] using congr_arg f heq


theorem finite_weighted_greedy_package {K α : Type*} [Field K] {M : ℕ}
    (s : Finset α) (R : α → Fin M → K) (e : Fin s.card ≃ s) (fallback : α)
    (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (hsort : Monotone (fun i => w (e i)))
    (hspan : Submodule.span K (R '' (s : Set α)) = ⊤) :
    let a := extendFiniteFamily (fun i => (e i : α)) fallback
    let v := R ∘ a
    let wt := extendFiniteFamily (fun i => w (e i)) B
    let P := finiteGreedyPivots K s R e fallback
    ∃ (g : Fin M ↪o ℕ) (p : Fin M ↪ α),
      Set.range g = (greedyPivots K v s.card : Set ℕ) ∧
      (∀ i, p i = a (g i)) ∧ Set.range p = (P : Set α) ∧
      Monotone wt ∧ Monotone (fun i => w (p i)) ∧
      (∀ i, g i < s.card) ∧
      (∀ r < s.card, wt r = w (a r)) ∧
      (∀ i, v (g i) = R (p i) ∧ wt (g i) = w (p i) ∧ w (p i) ≤ B) ∧
      (∀ b, w b ≤ B → ∃ r < s.card, a r = b ∧ wt r = w b ∧ v r = R b) ∧
      Matrix.det (fun i j => R (p i) j) ≠ 0 ∧ P.card = M ∧
      (∀ (β : Type) [AddCommMonoid β] (F : α → β),
        (∑ i, F (p i)) = ∑ b ∈ P, F b) := by
  classical
  dsimp only
  let a := extendFiniteFamily (fun i => (e i : α)) fallback
  let v := R ∘ a
  let G := greedyPivots K v s.card
  have haimage : a '' (Finset.range s.card : Set ℕ) = (s : Set α) := by
    rw [show a = extendFiniteFamily (fun i => (e i : α)) fallback from rfl,
      image_extendFiniteFamily_range]
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩
  have hvspan : Submodule.span K (v '' (Finset.range s.card : Set ℕ)) = ⊤ := by
    rw [show v = R ∘ a from rfl, Set.image_comp, haimage, hspan]
  have hcard : G.card = M := by
    simpa [G] using card_greedyPivots_of_span_eq_top v s.card hvspan
  let g := G.orderEmbOfFin hcard
  have hg : Set.range g = (G : Set ℕ) := G.range_orderEmbOfFin hcard
  have hgT : ∀ i, g i < s.card := fun i =>
    Finset.mem_range.mp (greedyPivots_subset_range v s.card
      (G.orderEmbOfFin_mem hcard i))
  have hainj : Set.InjOn a (Finset.range s.card : Set ℕ) :=
    extendFiniteFamily_injOn_range _ (Subtype.val_injective.comp e.injective) fallback
  let p : Fin M ↪ α := ⟨a ∘ g, fun i j hij => g.injective
    (hainj (Finset.mem_range.mpr (hgT i)) (Finset.mem_range.mpr (hgT j)) hij)⟩
  have hpe : ∀ i, p i = (e ⟨g i, hgT i⟩ : α) := by
    intro i
    change a (g i) = _
    simp only [a, extendFiniteFamily, dite_eq_left (hgT i)]
  have hpbound : ∀ i, w (p i) ≤ B := by
    intro i
    rw [hpe i]
    exact (hs _).mp (e ⟨g i, hgT i⟩).property
  have hpmono : Monotone (fun i => w (p i)) := by
    intro i j hij
    change w (p i) ≤ w (p j)
    rw [hpe i, hpe j]
    exact hsort (show (⟨g i, hgT i⟩ : Fin s.card) ≤ ⟨g j, hgT j⟩ from g.monotone hij)
  refine ⟨g, p, hg, fun _ => rfl, ?_, ?_, hpmono, hgT, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Set.range (a ∘ g) = ((greedyPivots K v s.card).image a : Set α)
    rw [Set.range_comp, hg, Finset.coe_image]
  · exact monotone_extendFiniteFamily _ _ hsort (fun i => (hs _).mp (e i).property)
  · intro r hr
    simp [extendFiniteFamily, hr]
  · intro i
    refine ⟨rfl, ?_, hpbound i⟩
    rw [hpe i]
    simp only [extendFiniteFamily, dite_eq_left (hgT i)]
  · intro b hb
    let r : Fin s.card := e.symm ⟨b, (hs b).mpr hb⟩
    refine ⟨r, r.isLt, ?_, ?_, ?_⟩
    · simp [extendFiniteFamily, r.isLt, r]
    · simp [extendFiniteFamily, r.isLt, r]
    · simp [extendFiniteFamily, r.isLt, r]
  · exact det_ne_zero_of_linearIndepOn_rows G v (G.orderIsoOfFin hcard).toEquiv
      (greedyPivots_linearIndepOn v s.card)
  · simpa using (finiteGreedyPivots_spec s R e fallback hspan).2.1
  · intro β _ F
    rw [finiteGreedyPivots_sum]
    exact sum_embedding_eq_sum_of_range G M g.toEmbedding hg (F ∘ a)



theorem rectangle_greedy_selection_package {K : Type*} [Field K] (H N : ℕ)
    (R : (Fin 3 → ℕ) → Fin (N ^ 4) → K)
    (hH : 0 < H) (hHN : H ≤ N) (hN : 18818 ≤ N)
    (hspan : Submodule.span K (R '' {b : Fin 3 → ℕ |
      (b 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (b 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (b 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)}) = ⊤) :
    let w := fun b : Fin 3 → ℕ => b 0 + H * b 1 + H * b 2
    let B := ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)⌋₊
    let s := weightedJetIndices H B
    ∃ e : Fin s.card ≃ s,
      Monotone (fun i => w (e i)) ∧
      let a := extendFiniteFamily (fun i => (e i : Fin 3 → ℕ)) 0
      let v := R ∘ a
      let wt := extendFiniteFamily (fun i => w (e i)) B
      let P := finiteGreedyPivots K s R e 0
      ∃ (g : Fin (N ^ 4) ↪o ℕ) (p : Fin (N ^ 4) ↪ (Fin 3 → ℕ)),
        Set.range g = (greedyPivots K v s.card : Set ℕ) ∧
        (∀ i, p i = a (g i)) ∧ Set.range p = (P : Set (Fin 3 → ℕ)) ∧
        Monotone wt ∧ Monotone (fun i => w (p i)) ∧
        (∀ i, g i < s.card) ∧ (∀ r < s.card, wt r = w (a r)) ∧
        (∀ i, v (g i) = R (p i) ∧ wt (g i) = w (p i) ∧ w (p i) ≤ B) ∧
        (∀ b, w b ≤ B → ∃ r < s.card, a r = b ∧ wt r = w b ∧ v r = R b) ∧
        Matrix.det (fun i j => R (p i) j) ≠ 0 ∧ P.card = N ^ 4 ∧
        (∀ (β : Type) [AddCommMonoid β] (F : (Fin 3 → ℕ) → β),
          (∑ i, F (p i)) = ∑ b ∈ P, F b) ∧
        (N : ℝ) ^ 4 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) /
          (4 * 97 ^ 2) ≤ ∑ i, ((p i) 0 : ℝ) ∧
        (∑ i, (((p i) 1 : ℝ) + (p i) 2)) ≤
          192 * (N : ℝ) ^ 4 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) := by
  classical
  dsimp only
  let w := fun b : Fin 3 → ℕ => b 0 + H * b 1 + H * b 2
  let B := ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)⌋₊
  let s := weightedJetIndices H B
  obtain ⟨e, he⟩ := exists_weight_sorted_enumeration s w
  have hcut : Submodule.span K (R '' (s : Set (Fin 3 → ℕ))) = ⊤ :=
    span_cutoff_eq_top_of_rectangle hH R hspan
  obtain ⟨g, p, hg, hpa, hp, hwt, hpmono, hgT, hprefix, hrows, hcover,
      hdet, hcard, hsum⟩ := finite_weighted_greedy_package s R e 0 w B
        (mem_weightedJetIndices_iff hH) he hcut
  have hbounds := finiteGreedyPivots_weighted_bounds s R e H N hH hHN hN
    (by simp) hcut (fun b hb => weightedJetIndices_real_weight hH (by positivity) hb)
  refine ⟨e, he, g, p, hg, hpa, hp, hwt, hpmono, hgT, hprefix, hrows, hcover,
    hdet, hcard, hsum, ?_, ?_⟩
  · have h := hbounds.2.2.1
    rw [← hsum ℝ (fun b => (b 0 : ℝ))] at h
    exact h
  · have h := hbounds.2.2.2
    rw [← hsum ℝ (fun b => (b 1 : ℝ) + b 2)] at h
    exact h

open Submodule
variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

theorem greedyPivots_filter_lt (v : ℕ → V) (n r : ℕ) (hrn : r ≤ n) :
    (greedyPivots K v n).filter (fun j => j < r) = greedyPivots K v r := by
  classical
  ext j
  simp only [Finset.mem_filter, mem_greedyPivots_iff]
  constructor
  · rintro ⟨⟨_, hind⟩, hjr⟩
    exact ⟨hjr, hind⟩
  · rintro ⟨hjr, hind⟩
    exact ⟨⟨hjr.trans_le hrn, hind⟩, hjr⟩

theorem span_greedyPivots_eq_span_earlier_rows {ι : Type*} [LinearOrder ι]
    (v : ℕ → V) (n : ℕ) (e : ι ↪o ℕ)
    (he : Set.range e = (greedyPivots K v n : Set ℕ)) (i : ι) :
    span K (v '' (greedyPivots K v (e i) : Set ℕ)) =
      span K ((v ∘ e) '' {j | j < i}) := by
  have hei : e i ∈ greedyPivots K v n := by
    change e i ∈ (greedyPivots K v n : Set ℕ)
    rw [← he]
    exact Set.mem_range_self i
  have hein : e i ≤ n :=
    (Finset.mem_range.mp (greedyPivots_subset_range v n hei)).le
  rw [← greedyPivots_filter_lt v n (e i) hein]
  congr 1
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨hr, hri⟩ := Finset.mem_filter.mp hr
    have hrange : r ∈ Set.range e := by rwa [he]
    obtain ⟨j, rfl⟩ := hrange
    exact ⟨j, e.lt_iff_lt.mp hri, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨e j, Finset.mem_filter.mpr ⟨?_, e.strictMono hj⟩, rfl⟩
    change e j ∈ (greedyPivots K v n : Set ℕ)
    rw [← he]
    exact Set.mem_range_self j

theorem smaller_weight_mem_span_earlier_retained_rows {ι : Type*} [LinearOrder ι]
    (v : ℕ → V) (w : ℕ → ℕ) (hw : Monotone w) (n : ℕ) (e : ι ↪o ℕ)
    (he : Set.range e = (greedyPivots K v n : Set ℕ))
    (rows : ι → V) (hrows : rows = v ∘ e) (i : ι) (r : ℕ)
    (hr : w r < w (e i)) :
    v r ∈ span K (rows '' {j | j < i}) := by
  rw [hrows, ← span_greedyPivots_eq_span_earlier_rows v n e he i]
  exact smaller_weight_row_mem_span_greedyPivots v w hw hr

end WeightedTorusJets

namespace WeightedTorusJets

theorem jet_weight_ball_span_eq_top {K : Type*} [Field K] {M : ℕ}
    (θ y z : Fin M → K) (hθ : Function.Injective θ) (H : ℕ) (hH : 0 < H) :
    Submodule.span K
      ((fun α : Fin 3 → ℕ => fun j => θ j ^ α 0 * y j ^ α 1 * z j ^ α 2) ''
        (weightedJetIndices H (M - 1) : Set (Fin 3 → ℕ))) = ⊤ := by
  classical
  let V : Matrix (Fin M) (Fin M) K := (Matrix.vandermonde θ).transpose
  have hdet : V.det ≠ 0 := by
    simpa only [V, Matrix.det_transpose] using
      (Matrix.det_vandermonde_ne_zero_iff.mpr hθ)
  have hspan : Submodule.span K (Set.range V) = ⊤ :=
    (Matrix.linearIndependent_rows_of_det_ne_zero hdet).span_eq_top_of_card_eq_finrank'
      (by simp)
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro _ ⟨k, rfl⟩
  refine ⟨![k.val, 0, 0], ?_, ?_⟩
  · apply (mem_weightedJetIndices_iff hH _).mpr
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Nat.mul_zero, Nat.add_zero]
    omega
  · funext j
    simp [V, Matrix.vandermonde_apply]

end WeightedTorusJets


end SiegelZeros

end OAI
