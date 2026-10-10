import OAI.NumberTheory.TotientAsymptotic.FiniteDyadicHarmonic
import Mathlib.Analysis.PSeries

namespace OAI

/-! Elementary reciprocal mass of divisible prime shifts and square tails. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def shiftDivisiblePrimes (N d : ℕ) : Finset ℕ :=
  (Nat.primesLE N).filter (fun p => d ∣ p-1)

lemma shifted_divisor_mass (N : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ p ∈ shiftDivisiblePrimes N d, ((p-1 : ℕ) : ℝ)⁻¹) ≤
      (1+Real.log N)/(d : ℝ) := by
  let Q := shiftDivisiblePrimes N d
  let f : ℕ → ℕ := fun p => (p-1)/d
  have hp (p : ℕ) (h : p ∈ Q) : p.Prime ∧ p ≤ N ∧ d ∣ p-1 := by
    obtain ⟨hN,hd⟩ := Finset.mem_filter.mp h
    obtain ⟨hN,hp⟩ := Nat.mem_primesLE.mp hN
    exact ⟨hp,hN,hd⟩
  have he (p : ℕ) (h : p ∈ Q) : d*f p=p-1 := Nat.mul_div_cancel' (hp p h).2.2
  have hi : Set.InjOn f (↑Q : Set ℕ) := by
    intro p hP q hQ h
    have h1 := he p hP
    have h2 := he q hQ
    have hp2 := (hp p hP).1.two_le
    have hq2 := (hp q hQ).1.two_le
    change f p=f q at h
    rw [h] at h1
    omega
  have hsub : Q.image f ⊆ Finset.Icc 1 N := by
    intro k hk
    obtain ⟨p,hpQ,rfl⟩ := Finset.mem_image.mp hk
    have h := hp p hpQ
    refine Finset.mem_Icc.mpr ⟨?_,(Nat.div_le_self _ _).trans ((Nat.sub_le p 1).trans h.2.1)⟩
    have hh := he p hpQ
    have h2 := h.1.two_le
    by_contra hn
    have hz : f p=0 := by omega
    rw [hz,mul_zero] at hh
    omega
  calc
    _ = (d : ℝ)⁻¹*∑ k ∈ Q.image f, (k : ℝ)⁻¹ := by
      rw [Finset.sum_image hi,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hpQ
      have hh : (d : ℝ)*(f p : ℝ)=((p-1 : ℕ) : ℝ) := by exact_mod_cast he p hpQ
      rw [← hh,mul_inv]
    _ ≤ (d : ℝ)⁻¹*∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)) (by positivity)
    _ = (d : ℝ)⁻¹*(harmonic N : ℝ) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    _ ≤ _ := by
      simpa only [div_eq_mul_inv,mul_comm] using
        mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by positivity : 0 ≤ (d : ℝ)⁻¹)

lemma inverse_square_tail (Q : Finset ℕ) {z : ℝ} (hz : 1 ≤ z)
    (hQ : ∀ q ∈ Q, z < (q : ℝ)) :
    (∑ q ∈ Q, ((q : ℝ)^2)⁻¹) ≤ 2/z := by
  let k := ⌊z⌋₊
  let N := Q.sup id+1
  have hsub : Q ⊆ Finset.Ioo k N := by
    intro q hq
    refine Finset.mem_Ioo.mpr ⟨?_,?_⟩
    · have hh : (k : ℝ) ≤ z := Nat.floor_le (by linarith)
      have hqz := hQ q hq
      exact_mod_cast (show (k : ℝ) < q by linarith)
    · have hh : q ≤ Q.sup id := Finset.le_sup (f := id) hq
      dsimp [N]
      omega
  have hk : z < (k : ℝ)+1 := Nat.lt_floor_add_one z
  have hk0 : 0 < (k : ℝ)+1 := by positivity
  calc
    _ ≤ ∑ q ∈ Finset.Ioo k N, ((q : ℝ)^2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ ≤ 2/((k : ℝ)+1) := sum_Ioo_inv_sq_le k N
    _ ≤ 2/z := div_le_div_of_nonneg_left (by norm_num) (by linarith) hk.le

end TotientAsymptotic

end

end OAI
