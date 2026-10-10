import OAI.NumberTheory.Ostmann.QuadraticSieveGaussNorm
import OAI.NumberTheory.Ostmann.QuadraticSieveNormReciprocity
import OAI.NumberTheory.Ostmann.SharpSieve

namespace OAI

namespace Ostmann.QuadraticSieve

noncomputable def unitResidues (q : ℕ) : Finset (Fin q) := by
  classical
  exact Finset.univ.filter (fun r => Nat.Coprime r.val q)

theorem gauss_times_character_sum {q : ℕ} [NeZero q] (hq : Odd q) (hsq : Squarefree q)
    (N : ℕ) (a : ℕ → ℂ) :
    gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar *
        (∑ n ∈ Finset.range N, a n * (jacobiSym (n : ℤ) q : ℂ)) =
      ∑ r : Fin q, (jacobiSym (r.val : ℤ) q : ℂ) *
        circleTrigPoly N a (((r.val : ℝ) / q : ℝ) : UnitAddCircle) := by
  simp only [circleTrigPoly, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hg := finite_jacobi_gauss_transform hq hsq (n : ℤ)
  calc
    gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar *
        (a n * (jacobiSym (n : ℤ) q : ℂ)) =
        a n * ((jacobiSym (n : ℤ) q : ℂ) *
          gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar) := by ring
    _ = a n * (∑ r : Fin q, (jacobiSym (r.val : ℤ) q : ℂ) *
          fourier (n : ℤ) (((r.val : ℝ) / q : ℝ) : UnitAddCircle)) := by rw [hg]
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r hr; ring

theorem gauss_times_character_sum_units {q : ℕ} [NeZero q] (hq : Odd q) (hsq : Squarefree q)
    (N : ℕ) (a : ℕ → ℂ) :
    gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar *
        (∑ n ∈ Finset.range N, a n * (jacobiSym (n : ℤ) q : ℂ)) =
      ∑ r ∈ unitResidues q, (jacobiSym (r.val : ℤ) q : ℂ) *
        circleTrigPoly N a (((r.val : ℝ) / q : ℝ) : UnitAddCircle) := by
  classical
  rw [gauss_times_character_sum hq hsq]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro r hr hnot
  have hcop : ¬Nat.Coprime r.val q := by simpa [unitResidues] using hnot
  have hz : jacobiSym (r.val : ℤ) q = 0 := jacobiSym.eq_zero_iff_not_coprime.mpr
    (by simpa only [Int.gcd_natCast_natCast, Nat.coprime_iff_gcd_eq_one] using hcop)
  simp [hz]

theorem character_sum_sq_le_unit_frequencies {q : ℕ} [NeZero q]
    (hq : Odd q) (hsq : Squarefree q) (N : ℕ) (a : ℕ → ℂ) :
    ‖∑ n ∈ Finset.range N, a n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2 ≤
      ∑ r ∈ unitResidues q, ‖trigPoly N a ((r.val : ℝ) / q)‖ ^ 2 := by
  classical
  let P : Fin q → ℂ := fun r => circleTrigPoly N a (((r.val : ℝ) / q : ℝ) : UnitAddCircle)
  have hn : ‖∑ r ∈ unitResidues q, (jacobiSym (r.val : ℤ) q : ℂ) * P r‖ ≤
      ∑ r ∈ unitResidues q, ‖P r‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro r hr
    rcases jacobiSym.trichotomy (r.val : ℤ) q with h | h | h <;> simp [h]
  have hcauchy : (∑ r ∈ unitResidues q, ‖P r‖) ^ 2 ≤
      ((unitResidues q).card : ℝ) * ∑ r ∈ unitResidues q, ‖P r‖ ^ 2 := by
    simpa [mul_comm] using Finset.sum_mul_sq_le_sq_mul_sq (unitResidues q)
      (fun r => ‖P r‖) (fun _ => (1 : ℝ))
  have hcard : ((unitResidues q).card : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (show (unitResidues q).card ≤ q from
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp))
  have h := (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcauchy
  have h' := h.trans (mul_le_mul_of_nonneg_right hcard
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  rw [← gauss_times_character_sum_units hq hsq N a, norm_mul, mul_pow,
    quadratic_gauss_norm_sq hq hsq] at h'
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_neZero q
  have hout := (mul_le_mul_iff_right₀ hqpos).mp h'
  simpa only [P, circleTrigPoly_coe] using hout

theorem sum_unit_frequencies_le_reduced (U N : ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ oddSquarefreeUpTo U, ∑ r ∈ unitResidues q,
      ‖trigPoly N a ((r.val : ℝ) / q)‖ ^ 2) ≤
      ∑ f : SharpSieve.ReducedFrequency U, ‖trigPoly N a f.value‖ ^ 2 := by
  classical
  let I := (q : oddSquarefreeUpTo U) × unitResidues (q : ℕ)
  let F : I → SharpSieve.ReducedFrequency U := fun x =>
    ⟨((x.1 : ℕ), x.2.val.val), by
      have hq := mem_oddSquarefreeUpTo.mp x.1.property
      exact ⟨hq.1, hq.2.1, x.2.val.isLt, (Finset.mem_filter.mp x.2.property).2⟩⟩
  have hF : Function.Injective F := by
    intro x y h
    rcases x with ⟨⟨q, hq⟩, ⟨⟨r, hr⟩, hc⟩⟩
    rcases y with ⟨⟨q', hq'⟩, ⟨⟨r', hr'⟩, hc'⟩⟩
    have heq : (q, r) = (q', r') := congrArg Subtype.val h
    have hqeq := congrArg Prod.fst heq
    have hreq := congrArg Prod.snd heq
    dsimp at hqeq hreq
    subst q'
    subst r'
    rfl
  let G : SharpSieve.ReducedFrequency U → ℝ := fun f => ‖trigPoly N a f.value‖ ^ 2
  have hsum : (∑ i : I, G (F i)) ≤ ∑ f : SharpSieve.ReducedFrequency U, G f := by
    rw [← Finset.sum_image (fun x _ y _ h => hF h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)
  have heq : (∑ i : I, G (F i)) =
      ∑ q ∈ oddSquarefreeUpTo U, ∑ r ∈ unitResidues q,
        ‖trigPoly N a ((r.val : ℝ) / q)‖ ^ 2 := by
    simp only [I, G, F, Fintype.sum_sigma,
      SharpSieve.ReducedFrequency.value, SharpSieve.ReducedFrequency.numerator,
      SharpSieve.ReducedFrequency.denominator]
    rw [← Finset.sum_coe_sort (oddSquarefreeUpTo U)
      (fun q => ∑ r ∈ unitResidues q, ‖trigPoly N a ((r.val : ℝ) / q)‖ ^ 2)]
    apply Finset.sum_congr rfl
    intro q hq
    exact Finset.sum_coe_sort (unitResidues (q : ℕ))
      (fun r => ‖trigPoly N a ((r.val : ℝ) / (q : ℕ))‖ ^ 2)
  rw [← heq]
  exact hsum

theorem initial_character_sieve (U N : ℕ) (a : ℕ → ℂ) (hU : 0 < U) :
    (∑ q ∈ oddSquarefreeUpTo U,
      ‖∑ n ∈ Finset.range N, a n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2) ≤
        32 * ((N : ℝ) + (U : ℝ) ^ 2) * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  calc
    _ ≤ ∑ q ∈ oddSquarefreeUpTo U, ∑ r ∈ unitResidues q,
        ‖trigPoly N a ((r.val : ℝ) / q)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      have h := mem_oddSquarefreeUpTo.mp hq
      let : NeZero q := ⟨by omega⟩
      exact character_sum_sq_le_unit_frequencies h.2.2.1 h.2.2.2 N a
    _ ≤ ∑ f : SharpSieve.ReducedFrequency U, ‖trigPoly N a f.value‖ ^ 2 :=
      sum_unit_frequencies_le_reduced U N a
    _ ≤ _ := sum_trigPoly_sq_reducedFrequency_le N U a hU

end Ostmann.QuadraticSieve

end OAI
