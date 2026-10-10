import Mathlib.Algebra.BigOperators.Associated
import OAI.NumberTheory.Ostmann.Construction.TransferCopiedSupport

namespace OAI

/-! # Deriving all phase support conditions from the actual transfer ranges -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem prime_product_factors_large {I : Type*} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, (p i).Prime) (V : ℕ) (hV : ∀ i, V < p i)
    (q : ℕ) (hq : q.Prime) (hdiv : q ∣ ∏ i, p i) : V < q := by
  obtain ⟨i, _, hi⟩ := (hq.prime.dvd_finsetProd_iff p).mp hdiv
  have he : q = p i := ((Nat.dvd_prime (hp i)).mp hi).resolve_left hq.ne_one
  rw [he]
  exact hV i

/-- The integer extension keeps its inherited unit conditions. The signed
substitution then supplies every support hypothesis of the phase identity. -/
theorem transfer_copied_support_of_ranges {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ)
    [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]
    (M B K V : ℕ) (v w s : ℤ) (hMpos : 0 < M) (hs : s ≠ 0)
    (hrel : v * (∏ h, R h) - w * (∏ h, L h) = s * M)
    (hv : v.natAbs ≤ B) (hw : w.natAbs ≤ B)
    (hLbound : (∏ h, L h) ≤ K) (hRbound : (∏ h, R h) ≤ K)
    (hscale : 2 * B * K ≤ V * M)
    (hL : Pairwise (fun h k => (L h).Coprime (L k)))
    (hR : Pairwise (fun h k => (R h).Coprime (R k)))
    (hU : Pairwise (fun y z => (U y).Coprime (U z)))
    (hLU : (∏ h, L h).Coprime (∏ y, U y)) (hRU : (∏ h, R h).Coprime (∏ y, U y))
    (hML : M.Coprime (∏ h, L h)) (hMR : M.Coprime (∏ h, R h)) (hMU : M.Coprime (∏ y, U y))
    (hlargeL : ∀ h, V < L h) (hlargeR : ∀ h, V < R h) (hlargeU : ∀ y, V < U y) :
    s.natAbs ≤ V ∧
      Pairwise (fun i j => (transferredLabels L R U i).Coprime (transferredLabels L R U j)) ∧
      (∀ i, M.Coprime (transferredLabels L R U i)) ∧
      (∀ i, IsUnit (s : ZMod (transferredLabels L R U i))) := by
  have hsV := transferred_frequency_bound M (∏ h, L h) (∏ h, R h) B K V s v w
    hMpos hv hw hLbound hRbound hscale hrel
  have hLR : (∏ h, L h).Coprime (∏ h, R h) :=
    transferred_products_coprime _ _ v w s M hs hrel
      (fun q hq hd _ => hsV.trans_lt (prime_product_factors_large L
        (fun h => Fact.out) V hlargeL q hq hd))
      (common_prime_pivot_unit M _ _ hML.symm)
  exact ⟨hsV, transferredLabels_pairwise L R U hL hR hU hLR hLU hRU,
    transferredLabels_pivot_coprime L R U M hML hMR hMU,
    transferredLabels_frequency_unit L R U s hs
      (fun h => hsV.trans_lt (hlargeL h)) (fun h => hsV.trans_lt (hlargeR h))
      (fun y => hsV.trans_lt (hlargeU y))⟩

/-- The full phase identity with support derived from the original ranges. -/
theorem transfer_complete_phase_of_ranges {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ)
    [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]
    (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νL νR : H → ℂ) (νYL νYR : Y → ℂ) (M : ℕ) (v w s : ℤ)
    (hrel : v * (∏ h, R h) - w * (∏ h, L h) = s * M)
    (B K V : ℕ) (hMpos : 0 < M) (hs : s ≠ 0)
    (hv : v.natAbs ≤ B) (hw : w.natAbs ≤ B)
    (hLbound : (∏ h, L h) ≤ K) (hRbound : (∏ h, R h) ≤ K)
    (hscale : 2 * B * K ≤ V * M)
    (hL : Pairwise (fun h k => (L h).Coprime (L k)))
    (hR : Pairwise (fun h k => (R h).Coprime (R k)))
    (hU : Pairwise (fun y z => (U y).Coprime (U z)))
    (hLU : (∏ h, L h).Coprime (∏ y, U y)) (hRU : (∏ h, R h).Coprime (∏ y, U y))
    (hML : M.Coprime (∏ h, L h)) (hMR : M.Coprime (∏ h, R h)) (hMU : M.Coprime (∏ y, U y))
    (hlargeL : ∀ h, V < L h) (hlargeR : ∀ h, V < R h) (hlargeU : ∀ y, V < U y)
    (hb : ∀ y, b (some (.inr y)) (some (.inr y)) = 0) :
    retainedPrimePhase L U t χH χY b νL νYL M v *
      conj (retainedPrimePhase R U t χH χY b νR νYR M w) =
    ∏ i, transferredAdditiveRow L R U t s i *
      transferredCharacterFactor L R U χH χY b νL νR νYL νYR v w s i := by
  obtain ⟨_, hc, hM, hsu⟩ := transfer_copied_support_of_ranges L R U M B K V v w s
    hMpos hs hrel hv hw hLbound hRbound hscale hL hR hU hLU hRU hML hMR hMU
    hlargeL hlargeR hlargeU
  exact transfer_complete_phase L R U t χH χY b νL νR νYL νYR M v w s hrel hc hM hsu hb

end Ostmann

end OAI
