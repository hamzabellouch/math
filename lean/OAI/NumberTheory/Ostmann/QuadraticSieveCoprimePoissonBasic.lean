import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparation
import OAI.NumberTheory.Ostmann.QuadraticSievePoissonDilation

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory Set
open scoped SchwartzMap FourierTransform ArithmeticFunction.Moebius

theorem integer_coprime_indicator_moebius (k : ℕ) (hk : k ≠ 0) (n : ℤ) :
    (if Nat.Coprime n.natAbs k then (1 : ℂ) else 0) =
      ∑ d ∈ k.divisors, if (d : ℤ) ∣ n then (μ d : ℂ) else 0 := by
  classical
  rw [← Finset.sum_filter]
  have heq : k.divisors.filter (fun d : ℕ => (d : ℤ) ∣ n) = (k.gcd n.natAbs).divisors := by
    ext d
    simp [Nat.mem_divisors, Int.natCast_dvd, Nat.dvd_gcd_iff, hk,
      Nat.gcd_ne_zero_left hk]
  rw [heq, sum_moebius_divisors_complex]
  simp only [Nat.coprime_comm, Nat.Coprime]

theorem tsum_integer_multiples (f : ℤ → ℂ) (d : ℕ) (hd : d ≠ 0) :
    (∑' n : ℤ, if (d : ℤ) ∣ n then f n else 0) = ∑' m : ℤ, f ((d : ℤ) * m) := by
  classical
  have hdi : (d : ℤ) ≠ 0 := by exact_mod_cast hd
  have hinj : Function.Injective (fun m : ℤ => (d : ℤ) * m) :=
    fun x y h => mul_left_cancel₀ hdi h
  have h := hinj.tsum_eq (f := fun n : ℤ => if (d : ℤ) ∣ n then f n else 0) (by
    intro n hn
    by_cases hdn : (d : ℤ) ∣ n
    · obtain ⟨m, hm⟩ := hdn
      exact ⟨m, hm.symm⟩
    · simp [Function.mem_support, hdn] at hn)
  simpa only [dvd_mul_right, ite_true] using h.symm

theorem coprime_tsum_moebius (f : ℤ → ℂ) (hf : Summable f) (k : ℕ) (hk : k ≠ 0) :
    (∑' n : ℤ, if Nat.Coprime n.natAbs k then f n else 0) =
      ∑ d ∈ k.divisors, (μ d : ℂ) * (∑' m : ℤ, f ((d : ℤ) * m)) := by
  classical
  have hd (d : ℕ) : Summable (fun n : ℤ => if (d : ℤ) ∣ n then f n else 0) :=
    (hf.indicator {n : ℤ | (d : ℤ) ∣ n}).congr (fun n => by simp [Set.indicator_apply])
  calc
    _ = ∑' n : ℤ, ∑ d ∈ k.divisors,
        (μ d : ℂ) * (if (d : ℤ) ∣ n then f n else 0) := by
      apply tsum_congr
      intro n
      calc
        _ = (if Nat.Coprime n.natAbs k then (1 : ℂ) else 0) * f n := by
          split_ifs <;> simp
        _ = _ := by
          rw [integer_coprime_indicator_moebius k hk n, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro d hd
          split_ifs <;> simp
    _ = ∑ d ∈ k.divisors, ∑' n : ℤ,
        (μ d : ℂ) * (if (d : ℤ) ∣ n then f n else 0) :=
      Summable.tsum_finsetSum (fun d _ => (hd d).mul_left (μ d : ℂ))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hdv
      rw [tsum_mul_left, tsum_integer_multiples f d (Nat.pos_of_mem_divisors hdv).ne']

theorem schwartz_summable_scaled_lattice (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    Summable (fun n : ℤ => ψ ((n : ℝ) / X)) := by
  simpa only [dilatedSchwartz_apply, div_eq_mul_inv, mul_comm] using
    schwartz_summable_int (dilatedSchwartz X⁻¹ (inv_ne_zero hX.ne') ψ)

theorem tsum_lattice_multiples (ψ : ℝ → ℂ) (X : ℝ) (d : ℕ) (hd : d ≠ 0) :
    (∑' n : ℤ, if (d : ℤ) ∣ n then ψ ((n : ℝ) / X) else 0) =
      ∑' m : ℤ, ψ ((d : ℝ) * m / X) := by
  classical
  have hdi : (d : ℤ) ≠ 0 := by exact_mod_cast hd
  have hinj : Function.Injective (fun m : ℤ => (d : ℤ) * m) :=
    fun x y h => mul_left_cancel₀ hdi h
  have h := hinj.tsum_eq
    (f := fun n : ℤ => if (d : ℤ) ∣ n then ψ ((n : ℝ) / X) else 0) (by
      intro n hn
      by_cases hdn : (d : ℤ) ∣ n
      · obtain ⟨m, hm⟩ := hdn
        exact ⟨m, hm.symm⟩
      · simp [Function.mem_support, hdn] at hn)
  simpa only [dvd_mul_right, ite_true, Int.cast_mul, Int.cast_natCast] using h.symm

theorem coprime_lattice_moebius (ψ : 𝓢(ℝ, ℂ)) (k : ℕ) (hk : k ≠ 0)
    (X : ℝ) (hX : 0 < X) :
    (∑' n : ℤ, if Nat.Coprime n.natAbs k then ψ ((n : ℝ) / X) else 0) =
      ∑ d ∈ k.divisors, (μ d : ℂ) * (∑' m : ℤ, ψ ((d : ℝ) * m / X)) := by
  classical
  have hs := schwartz_summable_scaled_lattice ψ X hX
  have hd (d : ℕ) : Summable (fun n : ℤ => if (d : ℤ) ∣ n then ψ ((n : ℝ) / X) else 0) := by
    exact (hs.indicator {n : ℤ | (d : ℤ) ∣ n}).congr (fun n => by simp [Set.indicator_apply])
  calc
    _ = ∑' n : ℤ, ∑ d ∈ k.divisors,
        (μ d : ℂ) * (if (d : ℤ) ∣ n then ψ ((n : ℝ) / X) else 0) := by
      apply tsum_congr
      intro n
      calc
        _ = (if Nat.Coprime n.natAbs k then (1 : ℂ) else 0) * ψ ((n : ℝ) / X) := by
          split_ifs <;> simp
        _ = _ := by
          rw [integer_coprime_indicator_moebius k hk n, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro d hd
          split_ifs <;> simp
    _ = ∑ d ∈ k.divisors, ∑' n : ℤ,
        (μ d : ℂ) * (if (d : ℤ) ∣ n then ψ ((n : ℝ) / X) else 0) :=
      Summable.tsum_finsetSum (fun d _ => (hd d).mul_left (μ d : ℂ))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hdv
      rw [tsum_mul_left, tsum_lattice_multiples ψ X d (Nat.pos_of_mem_divisors hdv).ne']

theorem schwartz_poisson_scaled (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' n : ℤ, ψ ((n : ℝ) / X)) =
      (X : ℂ) * (∑' l : ℤ, 𝓕 ψ ((l : ℝ) * X)) := by
  have h := periodic_weighted_poisson_scaled 1 X hX (fun _ => (1 : ℂ)) ψ
  simpa only [Fin.sum_univ_one, Fin.val_zero, Nat.cast_zero, Nat.cast_one, div_one,
    one_mul, zero_div, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one,
    tsum_mul_left] using h

end Ostmann.QuadraticSieve

end OAI
