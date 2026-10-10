import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.WLOG
import OAI.NumberTheory.Jacobsthal.Conclusions.Targets

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.JacobsthalFinite

theorem exists_offset_one (M : ℕ) (hM : 0 < M) (a : ℤ) :
    ∃ r : ℕ, r < M ∧ (M : ℤ) ∣ a + r - 1 := by
  let z : ℤ := (1 - a) % M
  have hMz : (0 : ℤ) < M := by exact_mod_cast hM
  have hz0 : 0 ≤ z := Int.emod_nonneg _ (ne_of_gt hMz)
  have hzM : z < M := Int.emod_lt_of_pos _ hMz
  refine ⟨z.toNat, ?_, ?_⟩
  · exact_mod_cast (show (z.toNat : ℤ) < M by simpa only [Int.toNat_of_nonneg hz0] using hzM)
  · refine ⟨-((1 - a) / M), ?_⟩
    rw [Int.toNat_of_nonneg hz0]
    dsimp [z]
    rw [Int.emod_def]
    ring

theorem prime_not_dvd_of_dvd_step {p M : ℕ} (hp : p.Prime)
    (hpM : p ∣ M) {b : ℤ} (hb : (M : ℤ) ∣ b - 1) :
    ¬ (p : ℤ) ∣ b := by
  intro hpb
  have hd : (p : ℤ) ∣ b - 1 :=
    (Int.natCast_dvd_natCast.mpr hpM).trans hb
  have hone : (p : ℤ) ∣ 1 := by
    have := dvd_sub hpb hd
    simpa using this
  exact hp.ne_one (Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hone))

theorem progression_prime_hit_unique {k p M : ℕ} (hp : p.Prime)
    (hkp : k < p) (hpM : ¬ p ∣ M) (b : ℤ)
    {j l : ℕ} (hj : j ≤ k) (hl : l ≤ k)
    (hpj : (p : ℤ) ∣ b + M * j) (hpl : (p : ℤ) ∣ b + M * l) :
    j = l := by
  wlog hjl : j ≤ l generalizing j l
  · exact (this hl hj hpl hpj (by omega)).symm
  have hd : (p : ℤ) ∣ (M * (l - j) : ℕ) := by
    have hd' : (p : ℤ) ∣ (b + M * l) - (b + M * j) := dvd_sub hpl hpj
    have heq : ((M * (l - j) : ℕ) : ℤ) = (b + M * l) - (b + M * j) := by
      push_cast [Nat.cast_sub hjl]; ring
    rw [heq]
    exact hd'
  have hdiff : p ∣ l - j :=
    (hp.dvd_mul.mp (Int.natCast_dvd_natCast.mp hd)).resolve_left hpM
  have hlt : l - j < p := lt_of_le_of_lt (Nat.sub_le l j) (lt_of_le_of_lt hl hkp)
  have hz := Nat.eq_zero_of_dvd_of_lt hdiff hlt
  omega

theorem exists_coprime_progression (k n : ℕ) (hn : 0 < n)
    (hcard : n.primeFactors.card ≤ k) (b : ℤ)
    (hb : ((k + 1).factorial : ℤ) ∣ b - 1) :
    ∃ j : ℕ, j ≤ k ∧ (b + (k + 1).factorial * j).natAbs.Coprime n := by
  classical
  by_contra hnone
  have hbad : ∀ j : ℕ, j ∈ Finset.range (k + 1) →
      ∃ p : ℕ, p ∈ n.primeFactors ∧
        (p : ℤ) ∣ b + (k + 1).factorial * j := by
    intro j hj
    have hnc : ¬ (b + (k + 1).factorial * j).natAbs.Coprime n := by
      intro hc
      exact hnone ⟨j, Nat.le_of_lt_succ (Finset.mem_range.mp hj), hc⟩
    obtain ⟨p, hp, hpd, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpn, ne_of_gt hn⟩,
      Int.natCast_dvd.mpr hpd⟩
  choose f hfmem hfdvd using hbad
  let F : ℕ → ℕ := fun j => if hj : j ∈ Finset.range (k + 1) then f j hj else 0
  have hFmem : ∀ j ∈ Finset.range (k + 1), F j ∈ n.primeFactors := by
    intro j hj
    simpa only [F, dite_eq_left hj] using hfmem j hj
  have hFdvd : ∀ j ∈ Finset.range (k + 1),
      (F j : ℤ) ∣ b + (k + 1).factorial * j := by
    intro j hj
    simpa only [F, dite_eq_left hj] using hfdvd j hj
  have hinj : Set.InjOn F (Finset.range (k + 1) : Set ℕ) := by
    intro j hj l hl heq
    have hp := (Nat.mem_primeFactors.mp (hFmem j hj)).1
    have hpj := hFdvd j hj
    have hpl := hFdvd l hl
    rw [← heq] at hpl
    have hpM : ¬ F j ∣ (k + 1).factorial := by
      intro hpM
      have hbase : (F j : ℤ) ∣ b := by
        have hmul : (F j : ℤ) ∣ (k + 1).factorial * j :=
          dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hpM) _
        simpa using dvd_sub hpj hmul
      exact prime_not_dvd_of_dvd_step hp hpM hb hbase
    have hlarge : k < F j := by
      have := not_le.mp (fun hle => hpM (Nat.dvd_factorial hp.pos hle))
      omega
    exact progression_prime_hit_unique hp hlarge hpM b
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      (Nat.le_of_lt_succ (Finset.mem_range.mp hl)) hpj hpl
  have hcount := Finset.card_le_card_of_injOn F hFmem hinj
  simp only [Finset.card_range] at hcount
  omega

theorem factorial_isJacobsthalBound (k : ℕ) :
    Targets.IsJacobsthalBound k ((k + 1) * (k + 1).factorial) := by
  intro n hn hcard a
  obtain ⟨r, hr, hres⟩ := exists_offset_one (k + 1).factorial (Nat.factorial_pos _) a
  obtain ⟨j, hj, hcop⟩ := exists_coprime_progression k n hn hcard (a + r) hres
  refine ⟨r + (k + 1).factorial * j, ?_, ?_⟩
  · have hmul := Nat.mul_le_mul_left (k + 1).factorial hj
    nlinarith
  · simpa only [Nat.cast_add, Nat.cast_mul, add_assoc] using hcop

theorem exists_isJacobsthalBound (k : ℕ) :
    ∃ m : ℕ, Targets.IsJacobsthalBound k m :=
  ⟨(k + 1) * (k + 1).factorial, factorial_isJacobsthalBound k⟩

theorem quadratic_of_eventually_quadratic
    (hlarge : ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 0 < k →
      ∃ m : ℕ, Targets.IsJacobsthalBound k m ∧ (m : ℝ) ≤ C * (k : ℝ) ^ 2) :
    Targets.JacobsthalQuadratic := by
  obtain ⟨C, hC, K, hK⟩ := hlarge
  let D : ℝ := max C (((K + 1) * (K + 1).factorial : ℕ) : ℝ)
  have hCD : C ≤ D := le_max_left _ _
  have hD : 0 < D := lt_of_lt_of_le hC hCD
  refine ⟨D, hD, ?_⟩
  intro k hk
  by_cases hKk : K ≤ k
  · obtain ⟨m, hm, hbound⟩ := hK k hKk hk
    exact ⟨m, hm, hbound.trans (mul_le_mul_of_nonneg_right hCD (sq_nonneg _))⟩
  · refine ⟨(k + 1) * (k + 1).factorial, factorial_isJacobsthalBound k, ?_⟩
    have hsmall : k + 1 ≤ K + 1 := by omega
    have hfac : (k + 1) * (k + 1).factorial ≤ (K + 1) * (K + 1).factorial :=
      Nat.mul_le_mul hsmall (Nat.factorial_le hsmall)
    have hfacR : (((k + 1) * (k + 1).factorial : ℕ) : ℝ) ≤
        (((K + 1) * (K + 1).factorial : ℕ) : ℝ) := by exact_mod_cast hfac
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    calc
      (((k + 1) * (k + 1).factorial : ℕ) : ℝ) ≤
          (((K + 1) * (K + 1).factorial : ℕ) : ℝ) := hfacR
      _ ≤ D := le_max_right _ _
      _ ≤ D * (k : ℝ) ^ 2 := by nlinarith

theorem quadratic_iff_eventually_quadratic :
    Targets.JacobsthalQuadratic ↔
      ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 0 < k →
        ∃ m : ℕ, Targets.IsJacobsthalBound k m ∧ (m : ℝ) ≤ C * (k : ℝ) ^ 2 := by
  constructor
  · rintro ⟨C, hC, hbound⟩
    exact ⟨C, hC, 0, fun k _ hk => hbound k hk⟩
  · exact quadratic_of_eventually_quadratic

end NumberTheoryLean.JacobsthalFinite

end

end Erdos970

end OAI
