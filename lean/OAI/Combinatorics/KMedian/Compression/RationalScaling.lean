import Mathlib

namespace OAI

namespace MetricKMedian.RationalScaling
open Finset
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

def denominator (q : Ω → ℚ) : ℤ := ∏ i, (q i).den

def numerator (q : Ω → ℚ) (i : Ω) : ℤ :=
  (q i).num * ∏ j ∈ univ.erase i, ((q j).den:ℤ)

omit [DecidableEq Ω] in
theorem denominator_pos (q : Ω → ℚ) : 0 < denominator q := by
  apply prod_pos
  intro i _
  exact_mod_cast (q i).den_pos

theorem numerator_cast (q : Ω → ℚ) (i : Ω) :
    (numerator q i:ℚ)=q i*(denominator q:ℚ) := by
  have he : (q i).den*(∏ j ∈ univ.erase i, ((q j).den:ℤ))=denominator q :=
    mul_prod_erase univ (fun j => ((q j).den:ℤ)) (mem_univ i)
  rw [← he]
  simp only [numerator,Int.cast_mul]
  push_cast
  rw [← mul_assoc,(q i).mul_den_eq_num]

omit [DecidableEq Ω] in
theorem denominator_bound (q : Ω → ℚ) (L : ℕ)
    (hq : ∀ i, ((q i).den:ℤ) ≤ 2^L) :
    denominator q ≤ (2:ℤ)^(L*Fintype.card Ω) := by
  calc
    _ ≤ ∏ _i : Ω, (2:ℤ)^L := prod_le_prod₀ (fun index _ => by positivity) (fun index _ => hq index)
    _ = _ := by simp only [prod_const,card_univ,← pow_mul]

theorem numerator_bound (q : Ω → ℚ) (L : ℕ)
    (hqnum : ∀ i, |(q i).num| ≤ (2:ℤ)^L)
    (hqden : ∀ i, ((q i).den:ℤ) ≤ (2:ℤ)^L) (i : Ω) :
    |numerator q i| ≤ (2:ℤ)^(L*(Fintype.card Ω+1)) := by
  have hprod0 : 0 ≤ ∏ j ∈ univ.erase i, ((q j).den:ℤ) :=
    prod_nonneg (fun _ _ => by positivity)
  have hp : (∏ j ∈ univ.erase i, ((q j).den:ℤ)) ≤ (2:ℤ)^(L*Fintype.card Ω) := by
    calc
      _ ≤ ∏ _j ∈ univ.erase i, (2:ℤ)^L :=
        prod_le_prod₀ (fun _ _ => by positivity) (fun index _ => hqden index)
      _ = (2:ℤ)^(L*(univ.erase i).card) := by rw [prod_const,pow_mul]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left L (card_erase_le.trans_eq (card_univ)))
  rw [numerator,abs_mul,abs_of_nonneg hprod0]
  calc
    _ ≤ (2:ℤ)^L * (2:ℤ)^(L*Fintype.card Ω) :=
      mul_le_mul (hqnum i) hp hprod0 (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; ring

end MetricKMedian.RationalScaling

end OAI
