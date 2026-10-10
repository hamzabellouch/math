import Mathlib.Algebra.MvPolynomial.Monad
import OAI.NumberTheory.Ostmann.Construction.HistoryResidueGate
import OAI.NumberTheory.Ostmann.Arithmetic.SampledPrimeCoincidence

namespace OAI

/-! # Removing reconstructed-pivot coprimalities to actual prime slots -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def zeroHistoryVariable {σ : Type*} (i : σ) :
    MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial σ ℤ :=
  MvPolynomial.bind₁ (fun j => if j = i then 0 else MvPolynomial.X j)

theorem zeroHistoryVariable_absent {σ : Type*} (i : σ) (P : MvPolynomial σ ℤ) :
    i ∉ (zeroHistoryVariable i P).vars := by
  intro h
  obtain ⟨j, _, hj⟩ := MvPolynomial.mem_vars_bind₁ _ P h
  by_cases hji : j = i <;> simp_all

theorem zeroHistoryVariable_eval {σ : Type*} (i : σ) (P : MvPolynomial σ ℤ) (x : σ → ℤ) :
    MvPolynomial.eval₂Hom (RingHom.id ℤ) x (zeroHistoryVariable i P) =
      MvPolynomial.eval₂Hom (RingHom.id ℤ) (Function.update x i 0) P := by
  rw [zeroHistoryVariable, MvPolynomial.hom_bind₁, MvPolynomial.eval₂Hom_comp_C]
  congr 1
  congr 1
  funext j
  by_cases hji : j = i <;> simp [hji, Function.update]

theorem zeroHistoryVariable_degree {σ : Type*} (i : σ) (P : MvPolynomial σ ℤ) :
    (zeroHistoryVariable i P).totalDegree ≤ P.totalDegree := by
  let v : σ → MvPolynomial σ ℤ := fun j => if j = i then 0 else MvPolynomial.X j
  have hv (j : σ) : (v j).totalDegree ≤ 1 := by
    dsimp only [v]
    split_ifs <;> simp
  have hs : zeroHistoryVariable i P =
      ∑ d ∈ P.support, zeroHistoryVariable i (MvPolynomial.monomial d (P.coeff d)) := by
    rw [← map_sum]
    exact congrArg (zeroHistoryVariable i) P.as_sum
  rw [hs]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  have hp : (d.prod fun j k => v j ^ k).totalDegree ≤ d.sum (fun _ k => k) := by
    change (∏ j ∈ d.support, v j ^ d j).totalDegree ≤ ∑ j ∈ d.support, d j
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    apply Finset.sum_le_sum
    intro j _
    exact ((MvPolynomial.totalDegree_pow _ _).trans
      (Nat.mul_le_mul_left (d j) (hv j))).trans_eq (Nat.mul_one _)
  simp only [zeroHistoryVariable, MvPolynomial.bind₁_monomial]
  change (MvPolynomial.C (P.coeff d) * d.prod (fun j k => v j ^ k)).totalDegree ≤ _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa only [MvPolynomial.totalDegree_C, zero_add] using hp.trans (MvPolynomial.le_totalDegree hd))

/-- Divisibility by the sampled prime is unchanged on setting that variable
to zero in the cleared numerator. -/
theorem zeroHistoryVariable_dvd_iff {σ : Type*} (i : σ) (P : MvPolynomial σ ℤ)
    (x : σ → ℤ) (p : ℕ) (hxi : x i = p) :
    p ∣ (MvPolynomial.eval₂Hom (RingHom.id ℤ) x P).natAbs ↔
      p ∣ (MvPolynomial.eval₂Hom (RingHom.id ℤ) x (zeroHistoryVariable i P)).natAbs := by
  rw [← Int.natCast_dvd, ← Int.natCast_dvd, zeroHistoryVariable_eval]
  apply Int.ModEq.dvd_iff
  apply integerPolynomial_eval_modEq
  intro j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self, hxi]
    exact Int.modEq_zero_iff_dvd.mpr (dvd_refl _)
  · simp [Function.update, hji]

theorem zeroHistoryVariable_identically_bad {σ : Type*} (i : σ) (P : MvPolynomial σ ℤ)
    (hP : zeroHistoryVariable i P = 0) (x : σ → ℤ) (p : ℕ) (hxi : x i = p) :
    p ∣ (MvPolynomial.eval₂Hom (RingHom.id ℤ) x P).natAbs := by
  rw [zeroHistoryVariable_dvd_iff i P x p hxi, hP, map_zero, Int.natAbs_zero]
  exact dvd_zero p

theorem reconstructed_prime_coprimality_error {A : Type*} [Fintype A] [Nonempty A]
    {n : ℕ} (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (P : MvPolynomial (Fin (n + 1)) ℤ) (i : Fin (n + 1))
    (hP : zeroHistoryVariable i P ≠ 0)
    (μ : Fin (n + 1) → A → ℝ) (hμ : ∀ j a, 0 ≤ μ j a) (hmass : ∀ j, ∑ a, μ j a = 1)
    (α β V H : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V) (hH : 1 ≤ H)
    (hmax : ∀ j a, μ j a ≤ α) (hpmax : ∀ a, μ i a ≤ β)
    (hsize : ∀ a, V ≤ Real.log (prime a : ℝ))
    (hvalue : ∀ x, |(integerTestValue (fun a => (prime a : ℤ)) (zeroHistoryVariable i P) x : ℝ)| ≤ H) :
    (∑ x, productPrior μ x *
      if prime (x i) ∣ (integerTestValue (fun a => (prime a : ℤ)) P x).natAbs then 1 else 0) ≤
      (P.totalDegree : ℝ) * α + (Real.log H / V) * β := by
  have hinj : Function.Injective (fun a => (prime a : ℤ)) := by
    intro a b h
    exact hpInj (Int.natCast_inj.mp h)
  have he (x : Fin (n + 1) → A) :
      prime (x i) ∣ (integerTestValue (fun a => (prime a : ℤ)) P x).natAbs ↔
        prime (x i) ∣ (integerTestValue (fun a => (prime a : ℤ)) (zeroHistoryVariable i P) x).natAbs :=
    zeroHistoryVariable_dvd_iff i P (fun j => (prime (x j) : ℤ)) (prime (x i)) rfl
  simp_rw [he]
  apply (sampled_coordinate_prime_coincidence_le (fun a => (prime a : ℤ)) hinj prime hpInj hprime
    (zeroHistoryVariable i P) hP i (zeroHistoryVariable_absent i P)
    μ hμ hmass α β V H hα hβ hV hH hmax hpmax (fun a _ => hsize a) hvalue).trans
  have hd : ((zeroHistoryVariable i P).totalDegree : ℝ) ≤ P.totalDegree := by
    exact_mod_cast zeroHistoryVariable_degree i P
  exact add_le_add (mul_le_mul_of_nonneg_right hd hα) le_rfl

end Ostmann

end OAI
