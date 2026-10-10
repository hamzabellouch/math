import OAI.Combinatorics.BinaryEdit.FiniteSeparation
import OAI.Combinatorics.BinaryEdit.FiniteWordL1Mean
import OAI.Combinatorics.BinaryEdit.ParameterImage
import OAI.Combinatorics.BinaryEdit.FiniteAlphabet
import OAI.Combinatorics.BinaryEdit.FiniteFamilyTransfer
import OAI.Combinatorics.BinaryEdit.PrimeSupply
import OAI.Combinatorics.BinaryEdit.EditDeficit

namespace OAI

noncomputable section
namespace TreeEdit.BinaryLower

open FiniteTree
open scoped BigOperators

/-- A finite-alphabet family with distortion constant `1/34`, constructed
from finite coordinate groups and their word images. -/
theorem exists_finite_source_family :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∃ Γ : Type, ∃ inst : Fintype Γ,
        1 ≤ @Fintype.card Γ inst ∧ @Fintype.card Γ inst ≤ finiteSourceLength k ∧
        ∃ W : Finset (Word Γ (finiteSourceLength k)), 2 ≤ W.card ∧
          c₀ * ((k : ℝ) / 4) ^ k ≤
            c1 {x : Word Γ (finiteSourceLength k) // x ∈ W}
              (fun x y => (ed x.val.val y.val.val : ℝ)) := by
  classical
  obtain ⟨K, hK⟩ := PrimeSupply.finite_tree_odd_prime_family
  refine ⟨1 / 34, by norm_num, K, ?_⟩
  intro k hk
  obtain ⟨hk2, primes, hprimes⟩ := hK k hk
  let p : Fin k → Fin (20 * k) → ℕ := fun q i => primes (q, i)
  have hpprime : ∀ q i, Nat.Prime (p q i) := fun q i => (hprimes (q, i)).1
  have hppos : ∀ q i, 0 < p q i := fun q i => (hpprime q i).pos
  have hplarge : ∀ q i, k ^ 4 ≤ p q i := fun q i => (hprimes (q, i)).2.2.1
  have hpupper : ∀ q i, p q i ≤ k ^ 5 := fun q i => (hprimes (q, i)).2.2.2
  have hpinj : Function.Injective (fun z : Fin k × Fin (20 * k) => p z.1 z.2) :=
    primes.injective
  let i₀ : Fin (20 * k) := ⟨0, by omega⟩
  let Γ := Symbol (wordPeriods p)
  let A := State (wordPeriods p)
  let : Finite Γ := finite_wordSymbol p hppos
  let : Fintype Γ := Fintype.ofFinite Γ
  let : Finite A := finite_wordState p hppos
  let : Fintype A := Fintype.ofFinite A
  have hΓ := FiniteAlphabet.prime_product_alphabet_bounds hk2 p hppos hpupper
  change Finite Γ ∧ 1 ≤ Nat.card Γ ∧ Nat.card Γ ≤ finiteSourceLength k at hΓ
  have hΓ1 : 1 ≤ Fintype.card Γ := by simpa only [Nat.card_eq_fintype_card] using hΓ.2.1
  have hΓM : Fintype.card Γ ≤ finiteSourceLength k := by
    simpa only [Nat.card_eq_fintype_card] using hΓ.2.2
  let G : A → Word Γ (finiteSourceLength k) := rootWord p i₀ (k ^ (20 * k))
  let z : A := wordW p i₀ []
  have hMnat : 0 < finiteSourceLength k := by
    unfold finiteSourceLength
    positivity
  have hM : (0 : ℝ) < finiteSourceLength k := by exact_mod_cast hMnat
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsep : ∀ x : A, (finiteSourceLength k : ℝ) / (4 : ℝ) ^ k ≤
      (ed (G x).val (G (x + z)).val : ℝ) := by
    intro x
    have hd := finiteWord_root_deficit hk2 p i₀ hpinj hpprime hplarge x
    have he := deficit_le_editDistance
      (finiteWord_length p i₀ (k ^ (20 * k)) k [] x)
      (finiteWord_length p i₀ (k ^ (20 * k)) k [] (x + z))
    exact hd.trans (Nat.cast_le.mpr he)
  have hmean : ∀ F : A → RealL1,
      (∀ x y, ‖F x - F y‖ ≤ (ed (G x).val (G y).val : ℝ)) →
      (∑ x : A, ‖F (x + z) - F x‖) / Fintype.card A ≤
        34 * (finiteSourceLength k : ℝ) / (k : ℝ) ^ k := by
    intro F hF
    have h := finiteWord_root_mean_bound34 p i₀ hk2 hppos hpupper F hF
    simpa only [Fintype.expect_eq_sum_div_card, finiteSourceLength, Nat.cast_pow] using h
  obtain ⟨W, _, hW, hdist⟩ := ParameterImage.exists_word_image_lower_of_root_bound
    G z ((finiteSourceLength k : ℝ) / (4 : ℝ) ^ k)
    (34 * (finiteSourceLength k : ℝ) / (k : ℝ) ^ k)
    (by positivity) (by positivity) hsep hmean
  refine ⟨Γ, inferInstance, hΓ1, hΓM, W, hW, ?_⟩
  have hratio : (finiteSourceLength k : ℝ) / (4 : ℝ) ^ k /
      (34 * (finiteSourceLength k : ℝ) / (k : ℝ) ^ k) =
        (1 / 34 : ℝ) * ((k : ℝ) / 4) ^ k := by
    rw [div_pow]
    field_simp
  rw [hratio] at hdist
  exact hdist

end TreeEdit.BinaryLower

end

end OAI
