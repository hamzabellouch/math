import OAI.NumberTheory.TotientAsymptotic.TupleMassBound
import OAI.NumberTheory.TotientAsymptotic.PrefixSize
import OAI.NumberTheory.TotientAsymptotic.MassMajorant
import OAI.NumberTheory.TotientAsymptotic.WitnessCollision

namespace OAI

/-! Counting any specified family of full basic witnesses, with their cofactors. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma restricted_remainder_weight {x : ℝ} {H : ℕ}
    (hPH : P H < H) (hHm : H ≤ m x) (hs : theta x ∈ Set.Ico (0 : ℝ) 1)
    (S : Finset (RemainderDatum (L x H))) (hS : ∀ η ∈ S, IsBasicRemainder x H η) :
    (∑ η ∈ S, remainderReciprocalWeight η) ≤
      (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
        ∑ p ∈ S.image RemainderDatum.primes, reciprocalShiftWeight p := by
  let F : RemainderDatum (L x H) → ℕ × (Fin (L x H) → ℕ) := fun η => (η.cofactor,η.primes)
  have hinj : Function.Injective F := by
    intro η ξ h
    cases η
    cases ξ
    simpa only [F,Prod.mk.injEq,RemainderDatum.mk.injEq,and_comm] using h
  have he : (∑ η ∈ S, remainderReciprocalWeight η) =
      ∑ z ∈ S.image F, (z.1.totient : ℝ)⁻¹*reciprocalShiftWeight z.2 := by
    rw [Finset.sum_image]
    · rfl
    · intro η _ ξ _ hh
      exact hinj hh
  rw [he]
  have hsub : S.image F ⊆ Finset.Icc 1 (tailCofactorBound H) ×ˢ S.image RemainderDatum.primes := by
    intro z hz
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (witness_cofactor_bound hs
      (extractTail_isWitness (hS η hη) hPH hHm)),Finset.mem_image.mpr ⟨η,hη,rfl⟩⟩
  calc
    _ ≤ ∑ z ∈ Finset.Icc 1 (tailCofactorBound H) ×ˢ S.image RemainderDatum.primes,
        (z.1.totient : ℝ)⁻¹*reciprocalShiftWeight z.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun z _ _ => mul_nonneg (by positivity) (reciprocalShiftWeight_nonneg z.2))
    _ = _ := by rw [Finset.sum_product]; simp only [← Finset.mul_sum,← Finset.sum_mul]

def witnessHeadSet {x : ℝ} {H : ℕ} (t : ℝ) (η : RemainderDatum (L x H)) : Finset ℕ :=
  (Finset.range (⌊t⌋₊+2)).filter (fun p => IsBasicTuple x H t (witnessTuple p η))

def witnessFamily {x : ℝ} {H : ℕ} (t : ℝ) (S : Finset (RemainderDatum (L x H))) :
    Finset (RemainderDatum (L x H) × ℕ) :=
  (S ×ˢ Finset.range (⌊t⌋₊+2)).filter (fun q => IsBasicTuple x H t (witnessTuple q.2 q.1))

lemma witnessFamily_card {x : ℝ} {H : ℕ} (t : ℝ) (S : Finset (RemainderDatum (L x H))) :
    (witnessFamily t S).card = ∑ η ∈ S, (witnessHeadSet t η).card := by
  simp only [witnessFamily,witnessHeadSet,Finset.card_eq_sum_ones,Finset.sum_filter,
    Finset.sum_product]

theorem restricted_witness_count : ∀ᶠ x : ℝ in atTop, ∀ H : ℕ, P H ≤ H →
    ∀ t : ℝ, t ≤ x → ∀ S : Finset (RemainderDatum (L x H)),
    (∀ η ∈ S, IsBasicRemainder x H η) →
    ((witnessFamily t S).card : ℝ) ≤
      (10*x/Real.log x)*(∑ η ∈ S, remainderReciprocalWeight η) := by
  filter_upwards [largest_prime_count_upper,eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro H hPH t ht S hS
  rw [witnessFamily_card,Nat.cast_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro η hη
  let ζ := prefixOfRemainder x H η
  have hz : IsPrefixDatum x H ζ := (isPrefixDatum_iff x H ζ).mpr ⟨η,hS η hη,rfl⟩
  let D := ζ.d*∏ i, (ζ.primes i-1)
  have hD : 0 < D := basic_prefix_denominator_pos hPH hz
  have hh := hx D hD (witnessHeadSet t η) (by
    intro p hp
    have hb := (Finset.mem_filter.mp hp).2
    refine ⟨hb.1,hb.2.1,?_⟩
    have hv := hb.2.2.2
    change (tupleValue (TotientTuple.mk p ζ) : ℝ) ≤ t at hv
    rw [tupleValue_eq_head] at hv
    exact hv.trans ht)
  have hw := prefix_reciprocal_majorant (hS η hη) hPH
  change 1/((ζ.d : ℝ)*∏ i, (ζ.primes i-1 : ℕ)) ≤ remainderReciprocalWeight η at hw
  have hcoef : 0 ≤ 10*x/Real.log x := by
    exact div_nonneg (mul_nonneg (by norm_num) (zero_lt_one.trans hx1).le) (Real.log_pos hx1).le
  apply hh.trans
  calc
    _ = (10*x/Real.log x)*(1/((ζ.d : ℝ)*∏ i, (ζ.primes i-1 : ℕ))) := by
      dsimp [D]
      push_cast
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hw hcoef

end TotientAsymptotic

end

end OAI
