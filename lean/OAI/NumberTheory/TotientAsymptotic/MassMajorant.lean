import OAI.NumberTheory.TotientAsymptotic.RemainderSplit
import OAI.NumberTheory.TotientAsymptotic.CofactorMass

namespace OAI

/-! Summing over witnesses is an upper bound, including repeated tail primes. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma sum_image_nonneg_le {α β : Type*} (s : Finset α) (f : α → β) (w : β → ℝ)
    (hw : ∀ b, 0 ≤ w b) : (∑ b ∈ s.image f, w b) ≤ ∑ a ∈ s, w (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.image_insert, Finset.sum_insert ha]
    by_cases hfa : f a ∈ s.image f
    · rw [Finset.insert_eq_of_mem hfa]
      exact ih.trans (le_add_of_nonneg_left (hw _))
    · rw [Finset.sum_insert hfa]
      exact add_le_add le_rfl ih

def basicRemainderFinset (x : ℝ) (H : ℕ) : Finset (RemainderDatum (L x H)) :=
  (basicRemainders_finite x H).toFinset

@[simp] lemma mem_basicRemainderFinset {x : ℝ} {H : ℕ} {η : RemainderDatum (L x H)} :
    η ∈ basicRemainderFinset x H ↔ IsBasicRemainder x H η := by
  simp [basicRemainderFinset]

lemma prefixDataFinset_eq_image (x : ℝ) (H : ℕ) :
    prefixDataFinset x H = (basicRemainderFinset x H).image (prefixOfRemainder x H) := by
  classical
  ext ζ
  simp only [mem_prefixDataFinset, Finset.mem_image, mem_basicRemainderFinset,
    isPrefixDatum_iff]

lemma prod_fin_shifted {M : Type*} [CommMonoid M] (N : ℕ) (f : ℕ → M) :
    (∏ i : Fin N, f (i.val+1)) = ∏ r ∈ Finset.Icc 1 N, f r := by
  apply Finset.prod_bij (fun i _ => i.val+1)
  · intro i _
    exact Finset.mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩
  · intro i _ j _ hij
    apply Fin.ext
    omega
  · intro r hr
    have := Finset.mem_Icc.mp hr
    exact ⟨⟨r-1, by omega⟩, Finset.mem_univ _, by simp; omega⟩
  · intro i _
    rfl

lemma prod_Icc_split_at {M : Type*} [CommMonoid M] {i R L : ℕ}
    (hi : i ≤ R) (hR : R ≤ L) (f : ℕ → M) :
    (∏ r ∈ Finset.Icc (i+1) L, f r) =
      (∏ r ∈ Finset.Icc (i+1) R, f r) * ∏ r ∈ Finset.Icc (R+1) L, f r := by
  have he : Finset.Icc (i+1) L = Finset.Icc (i+1) R ∪ Finset.Icc (R+1) L := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  rw [he, Finset.prod_union]
  apply Finset.disjoint_left.mpr
  intro r hr hs
  have := Finset.mem_Icc.mp hr
  have := Finset.mem_Icc.mp hs
  omega

def remainderReciprocalWeight {x : ℝ} {H : ℕ} (η : RemainderDatum (L x H)) : ℝ :=
  (η.cofactor.totient : ℝ)⁻¹ * reciprocalShiftWeight η.primes

lemma prefix_reciprocal_majorant {x : ℝ} {H : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hPH : P H ≤ H) :
    1 / (((remainderTail x H η).totient : ℝ)*
      ∏ i : Fin (R x H), (remainderPrime η (i.val+1)-1 : ℕ)) ≤ remainderReciprocalWeight η := by
  have hRL : R x H ≤ L x H := by unfold R L; omega
  have htail := reciprocal_totient_prime_product (Finset.Icc (R x H+1) (L x H))
    (remainderPrime η) η.cofactor hη.1 (fun r hr =>
      (hη.2.1 r (Finset.mem_Icc.mpr
        ⟨by have := (Finset.mem_Icc.mp hr).1; omega, (Finset.mem_Icc.mp hr).2⟩)).1)
  have hp : ∀ r ∈ Finset.Icc 1 (L x H), 1 ≤ remainderPrime η r :=
    fun r hr => (hη.2.1 r hr).1.one_lt.le
  have hprod : (∏ i : Fin (L x H), (η.primes i-1 : ℕ)) =
      (∏ i : Fin (R x H), (remainderPrime η (i.val+1)-1 : ℕ))*
        ∏ r ∈ Finset.Icc (R x H+1) (L x H), (remainderPrime η r-1 : ℕ) := by
    have he : (∏ i : Fin (L x H), (η.primes i-1 : ℕ)) =
        ∏ i : Fin (L x H), (remainderPrime η (i.val+1)-1 : ℕ) := by
      apply Finset.prod_congr rfl
      intro i _
      simp [remainderPrime, i.isLt]
    rw [he, prod_fin_shifted (L x H) (fun r => (remainderPrime η r-1 : ℕ)),
      prod_Icc_split_at (Nat.zero_le _) hRL,
      prod_fin_shifted (R x H) (fun r => (remainderPrime η r-1 : ℕ))]
  have hcast (r : ℕ) (hr : r ∈ Finset.Icc (R x H+1) (L x H)) :
      ((remainderPrime η r-1 : ℕ) : ℝ) = (remainderPrime η r : ℝ)-1 := by
    rw [Nat.cast_sub (hp r (Finset.mem_Icc.mpr
      ⟨by have := (Finset.mem_Icc.mp hr).1; omega, (Finset.mem_Icc.mp hr).2⟩)), Nat.cast_one]
  have he : (∏ r ∈ Finset.Icc (R x H+1) (L x H), (remainderPrime η r-1 : ℝ)⁻¹) =
      ∏ r ∈ Finset.Icc (R x H+1) (L x H), ((remainderPrime η r-1 : ℕ) : ℝ)⁻¹ := by
    apply Finset.prod_congr rfl
    intro r hr
    rw [hcast r hr]
  rw [he, Finset.prod_inv_distrib, ← Nat.cast_prod] at htail
  change ((remainderTail x H η).totient : ℝ)⁻¹ ≤ _ at htail
  have hh := mul_le_mul_of_nonneg_right htail
    (show 0 ≤ (((∏ i : Fin (R x H), (remainderPrime η (i.val+1)-1 : ℕ)) : ℕ) : ℝ)⁻¹ by positivity)
  unfold remainderReciprocalWeight reciprocalShiftWeight
  rw [hprod, Nat.cast_mul, mul_inv]
  simpa only [one_div, mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh

/-- The finite prefix mass is bounded by a sum over complete witnesses with
the reciprocal totient of the small cofactor separated out. -/
theorem mass_le_remainder_sum {x : ℝ} {H : ℕ} (hPH : P H ≤ H)
    (f : ℝ → ℝ) (hf : ∀ r, f r ≤ 1) :
    M x H f ≤ ∑ η ∈ basicRemainderFinset x H, remainderReciprocalWeight η := by
  apply (mass_mono x H hf).trans
  rw [mass_eq_sum_prefixData, prefixDataFinset_eq_image]
  apply (sum_image_nonneg_le _ _
    (fun ζ : PrefixDatum (R x H) => 1/((ζ.d : ℝ)*∏ i, (ζ.primes i-1 : ℕ)))
    (fun _ => by positivity)).trans
  apply Finset.sum_le_sum
  intro η hη
  exact prefix_reciprocal_majorant (mem_basicRemainderFinset.mp hη) hPH

def fullPrimeTuples (x : ℝ) (H : ℕ) : Finset (Fin (L x H) → ℕ) :=
  (basicRemainderFinset x H).image RemainderDatum.primes

/-- The entire cost of the discrete cofactor separates from the reciprocal
prime sum. The latter still retains all the basic simplex restrictions. -/
theorem mass_le_cofactor_sum_mul_prime_sum {x : ℝ} {H : ℕ}
    (hPH : P H < H) (hHm : H ≤ m x) (hs : theta x ∈ Set.Ico (0 : ℝ) 1)
    (f : ℝ → ℝ) (hf : ∀ r, f r ≤ 1) :
    M x H f ≤ (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
      ∑ p ∈ fullPrimeTuples x H, reciprocalShiftWeight p := by
  classical
  apply (mass_le_remainder_sum hPH.le f hf).trans
  let F : RemainderDatum (L x H) → ℕ × (Fin (L x H) → ℕ) := fun η => (η.cofactor, η.primes)
  have hinj : Function.Injective F := by
    intro η ξ h
    cases η
    cases ξ
    simpa only [F, Prod.mk.injEq, RemainderDatum.mk.injEq, and_comm] using h
  have hsum : (∑ η ∈ basicRemainderFinset x H, remainderReciprocalWeight η) =
      ∑ z ∈ (basicRemainderFinset x H).image F, (z.1.totient : ℝ)⁻¹*reciprocalShiftWeight z.2 := by
    rw [Finset.sum_image]
    · rfl
    · intro η _ ξ _ h
      exact hinj h
  rw [hsum]
  have hsubset : (basicRemainderFinset x H).image F ⊆
      Finset.Icc 1 (tailCofactorBound H) ×ˢ fullPrimeTuples x H := by
    intro z hz
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hz
    have hb := witness_cofactor_bound hs
      (extractTail_isWitness (mem_basicRemainderFinset.mp hη) hPH hHm)
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hb, Finset.mem_image.mpr ⟨η, hη, rfl⟩⟩
  calc
    _ ≤ ∑ z ∈ Finset.Icc 1 (tailCofactorBound H) ×ˢ fullPrimeTuples x H,
        (z.1.totient : ℝ)⁻¹*reciprocalShiftWeight z.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro z _ _
      exact mul_nonneg (by positivity) (reciprocalShiftWeight_nonneg z.2)
    _ = _ := by rw [Finset.sum_product]; simp only [← Finset.mul_sum, ← Finset.sum_mul]

end TotientAsymptotic

end

end OAI
