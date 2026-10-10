import OAI.NumberTheory.TotientAsymptotic.RestrictedWitnessCount

namespace OAI

/-! A direct weighted count including the head prime, used only for the
zero-index squarefree exclusion. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def fullWitnessPrimes {x : ℝ} {H : ℕ} (q : RemainderDatum (L x H) × ℕ) :
    Fin (L x H+1) → ℕ := Fin.cons q.2 q.1.primes

lemma fullWitnessWeight_eq {x : ℝ} {H : ℕ} (q : RemainderDatum (L x H) × ℕ) :
    (q.1.cofactor.totient : ℝ)⁻¹*reciprocalShiftWeight (fullWitnessPrimes q) =
      ((q.2-1 : ℕ) : ℝ)⁻¹*remainderReciprocalWeight q.1 := by
  simp only [reciprocalShiftWeight,fullWitnessPrimes,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,
    remainderReciprocalWeight,Nat.cast_mul,mul_inv]
  ring

lemma full_witness_count_le {x t : ℝ} {H : ℕ} (hPH : P H ≤ H) (ht : t ≤ x)
    (S : Finset (RemainderDatum (L x H) × ℕ))
    (hS : ∀ q ∈ S, IsBasicRemainder x H q.1 ∧ IsBasicTuple x H t (witnessTuple q.2 q.1)) :
    (S.card : ℝ) ≤ x*∑ q ∈ S, (q.1.cofactor.totient : ℝ)⁻¹*reciprocalShiftWeight (fullWitnessPrimes q) := by
  classical
  rw [Finset.mul_sum]
  calc
    _ = ∑ _q ∈ S, (1 : ℝ) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hη,hτ⟩ := hS q hq
      let D := (prefixOfRemainder x H q.1).d*∏ i, ((prefixOfRemainder x H q.1).primes i-1)
      have hpre := (isPrefixDatum_iff x H (prefixOfRemainder x H q.1)).mpr ⟨q.1,hη,rfl⟩
      have hD : 0 < D := basic_prefix_denominator_pos hPH hpre
      have hp : 0 < q.2-1 := Nat.sub_pos_of_lt hτ.1.one_lt
      have hv : (((q.2-1)*D : ℕ) : ℝ) ≤ x := by
        have hh := hτ.2.2.2.trans ht
        simpa only [witnessTuple,tupleValue_eq_head,D] using hh
      have hvpos : (0 : ℝ) < ((q.2-1)*D : ℕ) := by exact_mod_cast Nat.mul_pos hp hD
      have hx : 0 ≤ x := hvpos.le.trans hv
      have hu : 1 ≤ x/(((q.2-1)*D : ℕ) : ℝ) := (one_le_div hvpos).mpr hv
      have hw : 1/(D : ℝ) ≤ remainderReciprocalWeight q.1 := by
        simpa only [D,prefixOfRemainder,Nat.cast_mul,Nat.cast_prod] using prefix_reciprocal_majorant hη hPH
      rw [fullWitnessWeight_eq]
      apply hu.trans
      have hh := mul_le_mul_of_nonneg_left hw (show 0 ≤ ((q.2-1 : ℕ) : ℝ)⁻¹ by positivity)
      have hh' := mul_le_mul_of_nonneg_left hh hx
      simpa only [Nat.cast_mul,div_eq_mul_inv,mul_inv,one_mul,mul_assoc] using hh'

lemma full_witness_weight_le {x : ℝ} {H : ℕ} (hPH : P H < H) (hHm : H ≤ m x)
    (hs : theta x ∈ Set.Ico (0 : ℝ) 1)
    (S : Finset (RemainderDatum (L x H) × ℕ))
    (hS : ∀ q ∈ S, IsBasicRemainder x H q.1) :
    (∑ q ∈ S, (q.1.cofactor.totient : ℝ)⁻¹*reciprocalShiftWeight (fullWitnessPrimes q)) ≤
      (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
        ∑ p ∈ S.image fullWitnessPrimes, reciprocalShiftWeight p := by
  classical
  let F := fun q : RemainderDatum (L x H) × ℕ => (q.1.cofactor,fullWitnessPrimes q)
  have hF : Function.Injective F := by
    rintro ⟨η,p⟩ ⟨ξ,q⟩ he
    have hc := congrArg Prod.fst he
    have hv := congrArg Prod.snd he
    have hpq := congrFun hv 0
    have het : η.primes=ξ.primes := by
      funext i
      exact congrFun hv i.succ
    simp only [F,fullWitnessPrimes,Fin.cons_zero] at hc hpq
    have heq : η=ξ := by cases η; cases ξ; simp_all
    exact Prod.ext heq hpq
  have he : (∑ q ∈ S, (q.1.cofactor.totient : ℝ)⁻¹*reciprocalShiftWeight (fullWitnessPrimes q)) =
      ∑ z ∈ S.image F, (z.1.totient : ℝ)⁻¹*reciprocalShiftWeight z.2 := by
    rw [Finset.sum_image (fun q _ r _ h => hF h)]
  rw [he]
  have hsub : S.image F ⊆ Finset.Icc 1 (tailCofactorBound H) ×ˢ S.image fullWitnessPrimes := by
    intro z hz
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (witness_cofactor_bound hs
      (extractTail_isWitness (hS q hq) hPH hHm)),Finset.mem_image.mpr ⟨q,hq,rfl⟩⟩
  calc
    _ ≤ ∑ z ∈ Finset.Icc 1 (tailCofactorBound H) ×ˢ S.image fullWitnessPrimes,
        (z.1.totient : ℝ)⁻¹*reciprocalShiftWeight z.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun z _ _ => mul_nonneg (by positivity) (reciprocalShiftWeight_nonneg z.2))
    _ = _ := by rw [Finset.sum_product]; simp only [← Finset.mul_sum,← Finset.sum_mul]

end TotientAsymptotic

end

end OAI
