import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Characters.BiquadraticArithmeticFull
import OAI.NumberTheory.SiegelZeros.Selection.WeightedJetIndices

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
open Module
open scoped BigOperators
namespace WeightedTorusJets

theorem exists_first_greedy_jet_rows {K : Type*} [Field K] {M : ℕ}
    (θ y z : Fin M → K) (hθ : Function.Injective θ) (H : ℕ) (hH : 0 < H) :
    let s := weightedJetIndices H (M - 1)
    let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
    let R := fun α : Fin 3 → ℕ => fun j => θ j ^ α 0 * y j ^ α 1 * z j ^ α 2
    ∃ e : Fin s.card ≃ s, Monotone (fun i => w (e i)) ∧
      let β := extendFiniteFamily (fun i => (e i : Fin 3 → ℕ)) 0
      ∃ (g : Fin M ↪o ℕ) (α : Fin M ↪ (Fin 3 → ℕ)),
        Set.range g = (greedyPivots K (R ∘ β) s.card : Set ℕ) ∧
        (∀ i, α i = β (g i)) ∧
        Set.range α = (finiteGreedyPivots K s R e 0 : Set (Fin 3 → ℕ)) ∧
        Monotone (fun i => w (α i)) ∧ (∀ i, w (α i) ≤ M - 1) ∧
        (∀ i a b c, a + H * b + H * c < w (α i) →
          (fun j => θ j ^ a * y j ^ b * z j ^ c) ∈
            Submodule.span K ((R ∘ α) '' {j | j < i})) ∧
        Matrix.det (fun i j => R (α i) j) ≠ 0 := by
  classical
  dsimp only
  let s := weightedJetIndices H (M - 1)
  let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
  let R := fun α : Fin 3 → ℕ => fun j => θ j ^ α 0 * y j ^ α 1 * z j ^ α 2
  obtain ⟨e, he⟩ := exists_weight_sorted_enumeration s w
  have hs : ∀ α, α ∈ s ↔ w α ≤ M - 1 := mem_weightedJetIndices_iff hH
  obtain ⟨g, α, hg, hα, hrange, hmono, hαmono, hlt, hprefix,
    hselected, hcoverage, hdet, hcard, hsum⟩ :=
    finite_weighted_greedy_package s R e 0 w (M - 1) hs he
      (jet_weight_ball_span_eq_top θ y z hθ H hH)
  refine ⟨e, he, g, α, hg, hα, hrange, hαmono,
    fun i => (hselected i).2.2, ?_, hdet⟩
  intro i a b c hweight
  have habc : w ![a, b, c] ≤ M - 1 :=
    Nat.le_trans (Nat.le_of_lt hweight) (hselected i).2.2
  obtain ⟨r, _, _, hwr, hvr⟩ := hcoverage ![a, b, c] habc
  have hrows : R ∘ α = (R ∘ extendFiniteFamily (fun i => (e i : Fin 3 → ℕ)) 0) ∘ g := by
    funext j
    exact (hselected j).1.symm
  have hstrict : (extendFiniteFamily (fun j => w (e j)) (M - 1)) r <
      (extendFiniteFamily (fun j => w (e j)) (M - 1)) (g i) := by
    rw [hwr, (hselected i).2.1]
    exact hweight
  have hmem := smaller_weight_mem_span_earlier_retained_rows _ _ hmono s.card g hg
    (R ∘ α) hrows i r hstrict
  rw [hvr] at hmem
  simpa only [R, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons] using hmem

end WeightedTorusJets

open scoped BigOperators
open Module

namespace WeightedTorusJets

theorem basis_nat_sum_injective {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℚ V] (b : Basis ι ℚ V) :
    Function.Injective (fun n : ι → ℕ => ∑ i, (n i : ℚ) • b i) := by
  intro n m h
  funext i
  have hi := congrArg (fun v => b.repr v i) h
  simp only [Basis.repr_sum_self] at hi
  exact_mod_cast hi

theorem basis_nat_sum_mul_injective {ι K : Type*} [Fintype ι]
    [CommRing K] [Algebra ℚ K] (b : Basis ι ℚ K) :
    Function.Injective (fun n : ι → ℕ => ∑ i, (n i : K) * b i) := by
  have h : (fun n : ι → ℕ => ∑ i, (n i : ℚ) • b i) =
      (fun n : ι → ℕ => ∑ i, (n i : K) * b i) := by
    funext n
    simp [Algebra.smul_def]
  rw [← h]
  exact basis_nat_sum_injective b

theorem basis_fin_sum_mul_injective {ι K : Type*} [Fintype ι]
    [CommRing K] [Algebra ℚ K] (b : Basis ι ℚ K) (N : ℕ) :
    Function.Injective (fun n : ι → Fin N => ∑ i, ((n i : ℕ) : K) * b i) := by
  intro n m h
  have hcoords := basis_nat_sum_mul_injective b h
  funext i
  exact Fin.ext (congrFun hcoords i)



theorem exists_first_greedy_jet_rows_of_sorted_enumeration {K : Type*} [Field K] {M : ℕ}
    (θ y z : Fin M → K) (hθ : Function.Injective θ) (H : ℕ) (hH : 0 < H) :
    let s := weightedJetIndices H (M - 1)
    let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
    let R := fun α : Fin 3 → ℕ => fun j => θ j ^ α 0 * y j ^ α 1 * z j ^ α 2
    ∀ e : Fin s.card ≃ s, Monotone (fun i => w (e i)) →
      let β := extendFiniteFamily (fun i => (e i : Fin 3 → ℕ)) 0
      ∃ (g : Fin M ↪o ℕ) (α : Fin M ↪ (Fin 3 → ℕ)),
        Set.range g = (greedyPivots K (R ∘ β) s.card : Set ℕ) ∧
        (∀ i, α i = β (g i)) ∧
        Set.range α = (finiteGreedyPivots K s R e 0 : Set (Fin 3 → ℕ)) ∧
        Monotone (fun i => w (α i)) ∧ (∀ i, w (α i) ≤ M - 1) ∧
        (∀ i a b c, a + H * b + H * c < w (α i) →
          (fun j => θ j ^ a * y j ^ b * z j ^ c) ∈
            Submodule.span K ((R ∘ α) '' {j | j < i})) ∧
        Matrix.det (fun i j => R (α i) j) ≠ 0 := by
  classical
  dsimp only
  let s := weightedJetIndices H (M - 1)
  let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
  let R := fun α : Fin 3 → ℕ => fun j => θ j ^ α 0 * y j ^ α 1 * z j ^ α 2
  intro e he
  have hs : ∀ α, α ∈ s ↔ w α ≤ M - 1 := mem_weightedJetIndices_iff hH
  obtain ⟨g, α, hg, hα, hrange, hmono, hαmono, hlt, hprefix,
    hselected, hcoverage, hdet, hcard, hsum⟩ :=
    finite_weighted_greedy_package s R e 0 w (M - 1) hs he
      (jet_weight_ball_span_eq_top θ y z hθ H hH)
  refine ⟨g, α, hg, hα, hrange, hαmono,
    fun i => (hselected i).2.2, ?_, hdet⟩
  intro i a b c hweight
  have habc : w ![a, b, c] ≤ M - 1 :=
    Nat.le_trans (Nat.le_of_lt hweight) (hselected i).2.2
  obtain ⟨r, _, _, hwr, hvr⟩ := hcoverage ![a, b, c] habc
  have hrows : R ∘ α = (R ∘ extendFiniteFamily (fun i => (e i : Fin 3 → ℕ)) 0) ∘ g := by
    funext j
    exact (hselected j).1.symm
  have hstrict : (extendFiniteFamily (fun j => w (e j)) (M - 1)) r <
      (extendFiniteFamily (fun j => w (e j)) (M - 1)) (g i) := by
    rw [hwr, (hselected i).2.1]
    exact hweight
  have hmem := smaller_weight_mem_span_earlier_retained_rows _ _ hmono s.card g hg
    (R ∘ α) hrows i r hstrict
  rw [hvr] at hmem
  simpa only [R, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons] using hmem



open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

theorem source_character_fixed_greedy_determinant_divisibility_of_field_ne (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)) :
    ∃ (d : ℤ) (a b : (CyclotomicField (8 * q) ℚ)), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : (CyclotomicField (8 * q) ℚ)) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ N H : ℕ, 0 < H →
            ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
              let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) *
                ![1, a', b', a' * b'] i
              let R := fun α : Fin 3 → ℕ => fun j =>
                θ j ^ α 0 * σ (θ j) ^ α 1 * (σ * τ) (θ j) ^ α 2
              let s := weightedJetIndices H (N ^ 4 - 1)
              let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
              ∀ e : Fin s.card ≃ s, Monotone (fun i => w (e i)) →
                let β := extendFiniteFamily (fun i => (e i : Fin 3 → ℕ)) 0
                ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)),
                  Set.range g = (greedyPivots B (R ∘ β) s.card : Set ℕ) ∧
                  (∀ i, α i = β (g i)) ∧
                  Set.range α = (finiteGreedyPivots B s R e 0 : Set (Fin 3 → ℕ)) ∧
                  Monotone (fun i => w (α i)) ∧ (∀ i, w (α i) ≤ N ^ 4 - 1) ∧
                  ∃ Δ : 𝓞 B, (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧
                    Δ ≠ 0 ∧
                    ∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                      Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ (∑ i, α i 0 / p) := by
  classical
  obtain ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hFrob⟩ :=
    source_biquadratic_arithmetic_canonical_of_field_ne q χ hreal hprim hne hfield
  refine ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  intro N H hH n
  dsimp only
  intro e he
  let L := CyclotomicField (8 * q) ℚ
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i
  have hθ : Function.Injective θ := by
    have hinj := (basis_fin_sum_mul_injective v N).comp n.injective
    simpa only [Function.comp_def, hv, θ, a', b'] using hinj
  obtain ⟨g, α, hg, hα, hrange, hmono, hweight, hspan, hdet⟩ :=
    exists_first_greedy_jet_rows_of_sorted_enumeration
      θ (σ ∘ θ) ((σ * τ) ∘ θ) hθ H hH e he
  refine ⟨g, α, hg, hα, hrange, hmono, hweight, ?_⟩
  have ha' : a' ^ 2 = (d : B) := by
    apply Subtype.ext
    exact ha
  have hb' : b' ^ 2 = (2 : B) := by
    apply Subtype.ext
    exact hb
  obtain ⟨Δ, hΔ, hneΔ, hdiv⟩ := exists_integral_jet_determinant_divisible
    σ.toRingHom τ.toRingHom ha' hb' (fun j i => (n j i : ℕ)) α H hspan hdet
  refine ⟨Δ, hΔ, hneΔ, ?_⟩
  intro p hp hHp hpq hχp
  exact hdiv p hHp (frobenius_action_choice_quotient σ τ p (hFrob p hp hpq hχp))

end WeightedTorusJets

namespace WeightedTorusJets

theorem greedyPivots_congr_prefix {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (v v' : ℕ → V) (n : ℕ)
    (h : ∀ i < n, v i = v' i) : greedyPivots K v n = greedyPivots K v' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      classical
      have hprevious := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
      have hlast := h n (Nat.lt_succ_self n)
      have himage : v '' (greedyPivots K v' n : Set ℕ) =
          v' '' (greedyPivots K v' n : Set ℕ) := by
        apply Set.image_congr
        intro i hi
        exact h i (Nat.lt_succ_of_lt
          (Finset.mem_range.mp (greedyPivots_subset_range v' n hi)))
      simp only [greedyPivots, hprevious, hlast, himage]



theorem weight_sorted_equiv_mem_iff_lt_card {α : Type*}
    (s : Finset α) (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (e : ℕ ≃ α) (he : Monotone (fun i => w (e i))) (i : ℕ) :
    e i ∈ s ↔ i < s.card := by
  classical
  let t := s.map e.symm.toEmbedding
  have htmem : ∀ j, j ∈ t ↔ e j ∈ s := fun j => Finset.mem_map_equiv
  have htcard : t.card = s.card := Finset.card_map _
  have hsub : t ⊆ Finset.range s.card := by
    intro j hj
    have hlow : Finset.range (j + 1) ⊆ t := by
      intro k hk
      apply (htmem k).mpr
      apply (hs _).mpr
      exact (he (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).trans
        ((hs _).mp ((htmem j).mp hj))
    have hcard := Finset.card_le_card hlow
    rw [Finset.card_range, htcard] at hcard
    exact Finset.mem_range.mpr (Nat.lt_of_succ_le hcard)
  have ht : t = Finset.range s.card :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range, htcard])
  rw [← htmem, ht, Finset.mem_range]

noncomputable def restrictWeightSortedEquiv {α : Type*}
    (s : Finset α) (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (e : ℕ ≃ α) (he : Monotone (fun i => w (e i))) : Fin s.card ≃ s where
  toFun i := ⟨e i, (weight_sorted_equiv_mem_iff_lt_card s w B hs e he i).mpr i.isLt⟩
  invFun a := ⟨e.symm a, (weight_sorted_equiv_mem_iff_lt_card s w B hs e he (e.symm a)).mp
    (by rw [e.apply_symm_apply]; exact a.property)⟩
  left_inv i := Fin.ext (e.symm_apply_apply i)
  right_inv a := Subtype.ext (e.apply_symm_apply a)

theorem restrictWeightSortedEquiv_apply {α : Type*}
    (s : Finset α) (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (e : ℕ ≃ α) (he : Monotone (fun i => w (e i))) (i : Fin s.card) :
    (restrictWeightSortedEquiv s w B hs e he i : α) = e i := rfl

theorem restrictWeightSortedEquiv_monotone {α : Type*}
    (s : Finset α) (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (e : ℕ ≃ α) (he : Monotone (fun i => w (e i))) :
    Monotone (fun i => w (restrictWeightSortedEquiv s w B hs e he i)) := by
  intro i j hij
  exact he hij

theorem extend_restrictWeightSortedEquiv_eq {α : Type*}
    (s : Finset α) (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (e : ℕ ≃ α) (he : Monotone (fun i => w (e i))) (fallback : α)
    (i : ℕ) (hi : i < s.card) :
    extendFiniteFamily (fun j => (restrictWeightSortedEquiv s w B hs e he j : α))
      fallback i = e i := by
  simp only [extendFiniteFamily, dite_eq_left hi, restrictWeightSortedEquiv_apply]

theorem greedyPivots_restrictWeightSortedEquiv {K V α : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V]
    (s : Finset α) (R : α → V) (w : α → ℕ) (B : ℕ)
    (hs : ∀ a, a ∈ s ↔ w a ≤ B) (e : ℕ ≃ α)
    (he : Monotone (fun i => w (e i))) (fallback : α) :
    greedyPivots K
      (R ∘ extendFiniteFamily
        (fun j => (restrictWeightSortedEquiv s w B hs e he j : α)) fallback) s.card =
      greedyPivots K (R ∘ e) s.card := by
  apply greedyPivots_congr_prefix
  intro i hi
  exact congrArg R (extend_restrictWeightSortedEquiv_eq s w B hs e he fallback i hi)



theorem weight_sorted_equiv_image_range {α : Type*}
    (s : Finset α) (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (e : ℕ ≃ α) (he : Monotone (fun i => w (e i))) :
    e '' (Finset.range s.card : Set ℕ) = (s : Set α) := by
  ext a
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact (weight_sorted_equiv_mem_iff_lt_card s w B hs e he i).mpr
      (Finset.mem_range.mp hi)
  · intro ha
    refine ⟨e.symm a, ?_, e.apply_symm_apply a⟩
    apply Finset.mem_range.mpr
    apply (weight_sorted_equiv_mem_iff_lt_card s w B hs e he (e.symm a)).mp
    simpa using ha

theorem span_global_weight_cutoff_eq_top {K V α : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V]
    (s : Finset α) (R : α → V) (w : α → ℕ) (B : ℕ)
    (hs : ∀ a, a ∈ s ↔ w a ≤ B) (e : ℕ ≃ α)
    (he : Monotone (fun i => w (e i)))
    (hspan : Submodule.span K (R '' (s : Set α)) = ⊤) :
    Submodule.span K ((R ∘ e) '' (Finset.range s.card : Set ℕ)) = ⊤ := by
  rw [Set.image_comp, weight_sorted_equiv_image_range s w B hs e he]
  exact hspan

theorem greedyPivots_global_weight_cutoff {K V α : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V]
    (s : Finset α) (R : α → V) (w : α → ℕ) (B : ℕ)
    (hs : ∀ a, a ∈ s ↔ w a ≤ B) (e : ℕ ≃ α)
    (he : Monotone (fun i => w (e i)))
    (hspan : Submodule.span K (R '' (s : Set α)) = ⊤)
    (m : ℕ) (hm : s.card ≤ m) :
    greedyPivots K (R ∘ e) m = greedyPivots K (R ∘ e) s.card := by
  exact (greedyPivots_eq_of_span_eq_top (R ∘ e) hm
    (span_global_weight_cutoff_eq_top s R w B hs e he hspan)).symm



open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

theorem source_character_global_greedy_determinant_divisibility (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)) :
    ∃ (d : ℤ) (a b : (CyclotomicField (8 * q) ℚ)), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : (CyclotomicField (8 * q) ℚ)) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ N H : ℕ, 0 < H →
            ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
              let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) *
                ![1, a', b', a' * b'] i
              let R := fun α : Fin 3 → ℕ => fun j =>
                θ j ^ α 0 * σ (θ j) ^ α 1 * (σ * τ) (θ j) ^ α 2
              let s := weightedJetIndices H (N ^ 4 - 1)
              let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
              ∀ e : ℕ ≃ (Fin 3 → ℕ), Monotone (fun i => w (e i)) →
                ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)),
                  Set.range g = (greedyPivots B (R ∘ e) s.card : Set ℕ) ∧
                  (∀ i, α i = e (g i)) ∧
                  Set.range α = ((greedyPivots B (R ∘ e) s.card).image e : Set (Fin 3 → ℕ)) ∧
                  Monotone (fun i => w (α i)) ∧ (∀ i, w (α i) ≤ N ^ 4 - 1) ∧
                  (∀ t : ℕ, s.card ≤ t →
                    Set.range g = (greedyPivots B (R ∘ e) t : Set ℕ)) ∧
                  ∃ Δ : 𝓞 B, (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧
                    Δ ≠ 0 ∧
                    ∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                      Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ (∑ i, α i 0 / p) := by
  classical
  obtain ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hsource⟩ :=
    source_character_fixed_greedy_determinant_divisibility_of_field_ne
      q χ hreal hprim hne hfield
  refine ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  intro N H hH n
  dsimp only
  intro e he
  let L := CyclotomicField (8 * q) ℚ
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i
  let R := fun α : Fin 3 → ℕ => fun j =>
    θ j ^ α 0 * σ (θ j) ^ α 1 * (σ * τ) (θ j) ^ α 2
  let s := weightedJetIndices H (N ^ 4 - 1)
  let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
  have hs : ∀ α, α ∈ s ↔ w α ≤ N ^ 4 - 1 := mem_weightedJetIndices_iff hH
  let e₀ := restrictWeightSortedEquiv s w (N ^ 4 - 1) hs e he
  have he₀ : Monotone (fun i => w (e₀ i)) :=
    restrictWeightSortedEquiv_monotone s w (N ^ 4 - 1) hs e he
  obtain ⟨g, α, hg, hα, _, hmono, hweight, Δ, hΔ, hneΔ, hdiv⟩ :=
    hsource N H hH n e₀ he₀
  have hgGlobal : Set.range g = (greedyPivots B (R ∘ e) s.card : Set ℕ) :=
    hg.trans (congrArg (fun t : Finset ℕ => (t : Set ℕ))
      (greedyPivots_restrictWeightSortedEquiv s R w (N ^ 4 - 1) hs e he 0))
  have hαGlobal : ∀ i, α i = e (g i) := by
    intro i
    have hi : g i ∈ greedyPivots B (R ∘ e) s.card := by
      change g i ∈ (greedyPivots B (R ∘ e) s.card : Set ℕ)
      rw [← hgGlobal]
      exact Set.mem_range_self i
    have hiT := Finset.mem_range.mp (greedyPivots_subset_range (R ∘ e) s.card hi)
    exact (hα i).trans
      (extend_restrictWeightSortedEquiv_eq s w (N ^ 4 - 1) hs e he 0 (g i) hiT)
  have hθ : Function.Injective θ := by
    have hinj := (basis_fin_sum_mul_injective v N).comp n.injective
    simpa only [Function.comp_def, hv, θ, a', b'] using hinj
  have hball : Submodule.span B (R '' (s : Set (Fin 3 → ℕ))) = ⊤ :=
    jet_weight_ball_span_eq_top θ (σ ∘ θ) ((σ * τ) ∘ θ) hθ H hH
  have hspan : Submodule.span B ((R ∘ e) '' (Finset.range s.card : Set ℕ)) = ⊤ :=
    span_global_weight_cutoff_eq_top s R w (N ^ 4 - 1) hs e he hball
  refine ⟨g, α, hgGlobal, hαGlobal, ?_, hmono, hweight, ?_, Δ, hΔ, hneΔ, hdiv⟩
  · rw [show (α : Fin (N ^ 4) → Fin 3 → ℕ) = e ∘ g from funext hαGlobal,
      Set.range_comp, hgGlobal, Finset.coe_image]
  · intro t ht
    exact hgGlobal.trans (congrArg (fun u : Finset ℕ => (u : Set ℕ))
      (greedyPivots_eq_of_span_eq_top (R ∘ e) ht hspan))

end WeightedTorusJets

open scoped BigOperators
open InnerProductSpace

namespace SiegelJets

theorem norm_det_le_prod_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin n))‖ := by
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 (A i)
  let e := EuclideanSpace.basisFun (Fin n) ℂ
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := by
    simp
  let b := gramSchmidtOrthonormalBasis hdim v
  have hchange : e.toBasis.det v = e.toBasis.det b * b.toBasis.det v := by
    have h := congrArg (fun f : (EuclideanSpace ℂ (Fin n)) [⋀^Fin n]→ₗ[ℂ] ℂ => f v)
      (e.toBasis.det.eq_smul_basis_det b.toBasis)
    simpa using h
  have hnorm : ‖e.toBasis.det v‖ = ‖b.toBasis.det v‖ := by
    rw [hchange, norm_mul, e.det_to_matrix_orthonormalBasis b, one_mul]
  have hdet : e.toBasis.det v = A.det := by
    rw [Module.Basis.det_apply, ← Matrix.det_transpose A]
    congr
  rw [← hdet, hnorm]
  change ‖b.toBasis.det v‖ ≤ ∏ i, ‖v i‖
  rw [show b.toBasis.det v = ∏ i, inner ℂ (b i) (v i) from
    gramSchmidtOrthonormalBasis_det hdim v, norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => by
    simpa using norm_inner_le_norm (b i) (v i)

theorem norm_det_le_of_entry_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ i j, ‖A i j‖ ≤ B ^ d i) :
    ‖A.det‖ ≤ (Real.sqrt n) ^ n * B ^ (∑ i, d i) := by
  have hrow (i : Fin n) :
      ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin n))‖ ≤
        Real.sqrt n * B ^ d i := by
    rw [EuclideanSpace.norm_eq]
    calc
      Real.sqrt (∑ j, ‖A i j‖ ^ 2) ≤ Real.sqrt (∑ _ : Fin n, (B ^ d i) ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hA i j) 2
      _ = Real.sqrt n * B ^ d i := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (pow_nonneg hB _)]
  calc
    ‖A.det‖ ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin n))‖ :=
      norm_det_le_prod_norm A
    _ ≤ ∏ i, (Real.sqrt n * B ^ d i) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hrow i)
    _ = (Real.sqrt n) ^ n * B ^ (∑ i, d i) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      simp

theorem log_norm_det_le_of_entry_bound {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hdet : A.det ≠ 0)
    (d : Fin n → ℕ) {B : ℝ} (hB : 0 < B)
    (hA : ∀ i j, ‖A i j‖ ≤ B ^ d i) :
    Real.log ‖A.det‖ ≤ (n : ℝ) / 2 * Real.log n + (∑ i, d i : ℕ) * Real.log B := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  calc
    Real.log ‖A.det‖ ≤ Real.log ((Real.sqrt n) ^ n * B ^ (∑ i, d i)) :=
      Real.log_le_log (norm_pos_iff.mpr hdet) (norm_det_le_of_entry_bound A d hB.le hA)
    _ = (n : ℝ) / 2 * Real.log n + (∑ i, d i : ℕ) * Real.log B := by
      rw [Real.log_mul (pow_ne_zero _ (Real.sqrt_pos.mpr hn').ne')
        (pow_ne_zero _ hB.ne'), Real.log_pow, Real.log_pow,
        Real.log_sqrt hn'.le]
      ring

theorem log_norm_det_archimedean {m N q : ℕ} (hm : 0 < m) (hN : 0 < N) (hq : 0 < q)
    (A : Matrix (Fin m) (Fin m) ℂ) (hdet : A.det ≠ 0)
    (d : Fin m → ℕ)
    (hA : ∀ i j, ‖A i j‖ ≤ (8 * N * Real.sqrt q) ^ d i) :
    Real.log ‖A.det‖ ≤ (m : ℝ) / 2 * Real.log m +
      (∑ i, d i : ℕ) * (Real.log N + 1 / 2 * Real.log q + Real.log 8) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hB : (0 : ℝ) < 8 * N * Real.sqrt q := by positivity
  have hlog : Real.log (8 * N * Real.sqrt q) =
      Real.log N + 1 / 2 * Real.log q + Real.log 8 := by
    rw [Real.log_mul (mul_pos (by norm_num) hN').ne' (Real.sqrt_pos.mpr hq').ne',
      Real.log_mul (by norm_num) hN'.ne', Real.log_sqrt hq'.le]
    ring
  simpa only [hlog] using log_norm_det_le_of_entry_bound hm A hdet d hB hA

theorem log_norm_map_det_archimedean {K : Type*} [Field K] {m N q : ℕ}
    (hm : 0 < m) (hN : 0 < N) (hq : 0 < q)
    (ν : K →+* ℂ) (A : Matrix (Fin m) (Fin m) K) (hdet : A.det ≠ 0)
    (d : Fin m → ℕ)
    (hA : ∀ i j, ‖ν (A i j)‖ ≤ (8 * N * Real.sqrt q) ^ d i) :
    Real.log ‖ν A.det‖ ≤ (m : ℝ) / 2 * Real.log m +
      (∑ i, d i : ℕ) * (Real.log N + 1 / 2 * Real.log q + Real.log 8) := by
  have hmapped : (ν.mapMatrix A).det ≠ 0 := by
    rw [← RingHom.map_det]
    exact (map_ne_zero ν).mpr hdet
  simpa only [← RingHom.map_det] using
    log_norm_det_archimedean hm hN hq (ν.mapMatrix A) hmapped d hA

end SiegelJets


end SiegelZeros

end OAI
