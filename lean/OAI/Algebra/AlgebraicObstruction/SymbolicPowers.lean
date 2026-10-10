import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.PositiveCoefficients
import OAI.Algebra.AlgebraicObstruction.TaylorEvaluation

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
variable {A : Type*} [CommRing A] [IsNoetherianRing A]

theorem primary_symbolic_cofinal (I : Ideal A) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ x : A,
      (∀ (p : Ideal A), p.IsPrime → I ≤ p →
        ∃ s : A, s ∉ p ∧ s*x ∈ p^N) → x ∈ I := by
  classical
  obtain ⟨S,hS,hprimary⟩ := Submodule.isLasker (R := A) (M := A) I
  have hb : ∀ Q : Ideal A, ∃ n : ℕ, Q.radical^n ≤ Q :=
    fun Q ↦ Q.exists_radical_pow_le_of_fg Q.radical.fg_of_isNoetherianRing
  choose n hn using hb
  refine ⟨S.sup n + 1, by omega, ?_⟩
  intro x hx
  rw [← hS]
  apply Submodule.mem_finsetInf.mpr
  intro Q hQ
  have hp : (Ideal.radical Q).IsPrime := Ideal.isPrime_radical (hprimary hQ)
  have hIQ : I ≤ Q := by
    rw [← hS]
    exact Finset.inf_le hQ
  obtain ⟨s,hs,hsx⟩ := hx (Ideal.radical Q) hp (hIQ.trans Ideal.le_radical)
  have hN : n Q ≤ S.sup n + 1 := (Finset.le_sup hQ).trans (Nat.le_succ _)
  have hmem : s*x ∈ Q := hn Q ((Ideal.pow_le_pow_right hN) hsx)
  exact ((Ideal.isPrimary_iff.mp (hprimary hQ)).2 (by simpa [mul_comm] using hmem)).resolve_right hs

theorem primary_symbolic_cofinal_power (K : Ideal A) (m : ℕ) (_hm : 1 ≤ m) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ x : A,
      (∀ (p : Ideal A), p.IsPrime → K ≤ p →
        ∃ s : A, s ∉ p ∧ s*x ∈ p^N) → x ∈ K^m := by
  obtain ⟨N,hN,h⟩ := primary_symbolic_cofinal (K^m)
  refine ⟨N,hN,?_⟩
  intro x hx
  apply h x
  intro p hp hK
  have hKp : K ≤ p := by
    intro a ha
    have ham : a^m ∈ p := hK (Ideal.pow_mem_pow ha m)
    exact hp.mem_of_pow_mem m ham
  exact hx p hp hKp

omit [IsNoetherianRing A] in
theorem symbolic_denominator_iff (p : Ideal A) [p.IsPrime] (N : ℕ) (x : A) :
    algebraMap A (Localization.AtPrime p) x ∈
        (p.map (algebraMap A (Localization.AtPrime p)))^N ↔
      ∃ s : A, s ∉ p ∧ s*x ∈ p^N := by
  rw [← Ideal.map_pow,
    IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl]
  rfl

end BoundaryOnly.FormalObstruction.AlgebraicReplacement

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
variable {K A α : Type*} [Field K] [PerfectField K] [CommRing A] [IsNoetherianRing A]
  [Algebra K A] [Algebra (MvPolynomial α K) A] [IsScalarTower K (MvPolynomial α K) A]
  [Algebra.EssFiniteType K A] [Algebra.FormallyEtale (MvPolynomial α K) A]

theorem taylor_kernel_cofinal (J : Ideal A) (m : ℕ) (hm : 1 ≤ m) :
    ∃ q : ℕ, ∃ hq : 1 ≤ q,
      RingHom.ker (TaylorShift.taylor (K := K) (α := α) J.radical q hq) ≤ J^m := by
  obtain ⟨q,hq,h⟩ := primary_symbolic_cofinal_power J m hm
  refine ⟨q,hq,?_⟩
  intro a ha
  apply h a
  intro p hp hJp
  let := hp
  have hIp : J.radical ≤ p := hp.radical_le_iff.mpr hJp
  exact SymbolicTaylor.kernel_le_symbolic J.radical p hIp q hq a ha

end BoundaryOnly.FormalObstruction.AlgebraicReplacement

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget
variable {A B α : Type*} [CommRing A] [CommRing B]

theorem lift_of_coefficients (f : A →+* B) (q : ℕ) (x : Ring B α q)
    (h : ∀ e, e.degree < q → ∃ a : A, f a = coefficient q e x) :
    ∃ y : Ring A α q, map f q y = x := by
  classical
  let p := representative q x
  let c : (α →₀ ℕ) → A := fun e ↦ if he : e.degree < q then (h e he).choose else 0
  have hc (e : α →₀ ℕ) (he : e.degree < q) : f (c e) = coefficient q e x := by
    dsimp only [c]
    rw [dite_eq_left he]
    exact (h e he).choose_spec
  let r : MvPolynomial α A := ∑ e ∈ p.support, MvPolynomial.monomial e (c e)
  refine ⟨mk A α q r,?_⟩
  apply coefficient_ext
  intro e he
  rw [coefficient_map f q e he,coefficient_mk q e he]
  have hr : r.coeff e = if e ∈ p.support then c e else 0 := by
    simp only [r,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
    simp
  rw [hr]
  split_ifs with hm
  · exact hc e he
  · rw [map_zero]
    have hp : p.coeff e = 0 := not_not.mp (fun hn ↦ hm (MvPolynomial.mem_support_iff.mpr hn))
    have hx := coefficient_mk q e he p
    rw [mk_representative] at hx
    exact (hx.trans hp).symm

lemma coefficient_zero_eq_reduction (q : ℕ) (hq : 1 ≤ q) (x : Ring A α q) :
    coefficient q 0 x = reduction A α q hq x := by
  obtain ⟨p,rfl⟩ := mk_surjective q x
  rw [coefficient_mk q 0 (by simp only [map_zero]; omega),reduction_mk]
  rfl

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget

namespace BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart
open BoundaryOnly.FormalObstruction.AlgebraicReplacement
variable {K α : Type} [Field K] [CharZero K] [Finite α]

theorem primitive_approximation_from_constant_reduction (E : AffineEtaleChart K α)
    (L : Ideal E.LocalRing)
    (b : AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing)
    (hconstant : ∃ a₀ : E.LocalRing ⧸ L.radical,
      TaylorTarget.quotientCoefficient
        (S := AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing) L.radical a₀ =
      Ideal.Quotient.mk (L.radical.map (algebraMap E.LocalRing
        (AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing))) b)
    (hjets : ∀ i : α, ∀ q : ℕ, 1 ≤ q → ∃ a : E.LocalRing,
      E.completionDeriv i b - AdicCompletion.of _ _ a ∈
        (L.map (algebraMap E.LocalRing
          (AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing)))^q)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ a : E.LocalRing, b - AdicCompletion.of _ _ a ∈
      (L^m).map (algebraMap E.LocalRing
        (AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing)) := by
  have : Algebra.EssFiniteType K E.LocalRing :=
    Algebra.EssFiniteType.comp K (MvPolynomial α K) E.LocalRing
  obtain ⟨q,hq,hcofinal⟩ := taylor_kernel_cofinal (K := K) (α := α) L m hm
  let I := L.radical
  let J := IsLocalRing.maximalIdeal E.LocalRing
  let B := AdicCompletion J E.LocalRing
  let F := TaylorShift.fullTaylor (K := K) (α := α) I J (q+1) (by omega) b
  have hcoeff : ∀ e, e.degree < q+1 → ∃ a : E.LocalRing ⧸ I,
      TaylorTarget.quotientCoefficient (S := B) I a =
        TaylorTarget.coefficient (q+1) e F := by
    intro e he
    by_cases he0 : e = 0
    · subst e
      obtain ⟨a₀,ha₀⟩ := hconstant
      refine ⟨a₀,?_⟩
      rw [TaylorTarget.coefficient_zero_eq_reduction (q+1) (by omega)]
      exact ha₀.trans (E.reduction_fullTaylor I (q+1) (by omega) b).symm
    · exact E.fullTaylor_positive_coefficients I L Ideal.le_radical q hq b
        (fun i ↦ hjets i q hq) e he he0
  obtain ⟨x,hx⟩ := TaylorTarget.lift_of_coefficients
    (TaylorTarget.quotientCoefficient (S := B) I) (q+1) F hcoeff
  obtain ⟨a,ha,hba⟩ := E.taylor_primitive_tuple I (q+1) (by omega) b x hx.symm
  refine ⟨a,?_⟩
  apply Ideal.map_mono (show RingHom.ker
    (TaylorShift.taylor (K := K) (α := α) I (q+1) (by omega)) ≤ L^m from ?_) hba
  intro c hc
  apply hcofinal
  change TaylorShift.taylor (K := K) (α := α) I q hq c = 0
  rw [← TaylorShift.lower_taylor (K := K) (α := α) I q hq c]
  change TaylorTarget.lower q (TaylorShift.taylor (K := K) (α := α) I (q+1) _ c) = 0
  rw [hc,map_zero]

end BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart

end

end OAI
