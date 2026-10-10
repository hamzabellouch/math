import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Trace.Defs
import Mathlib.Tactic

namespace OAI

noncomputable section

namespace PiExponent

open scoped LaurentSeries Matrix

theorem laurent_derivative_residue_eq_zero {K : Type*} [Field K]
    (f : K⸨X⸩) : (LaurentSeries.derivative K f).coeff (-1) = 0 := by
  simp [LaurentSeries.derivative]

theorem laurent_derivative_ne_simple_pole {K : Type*} [Field K]
    (f : K⸨X⸩) {c : K} (hc : c ≠ 0) :
    LaurentSeries.derivative K f ≠ HahnSeries.single (-1) c := by
  intro h
  have hr := congrArg (fun z : K⸨X⸩ => z.coeff (-1)) h
  exact hc (by simpa [laurent_derivative_residue_eq_zero] using hr.symm)

open Polynomial

theorem polynomial_logarithmic_equation_impossible {K : Type*} [Field K] [CharZero K]
    (P Q : K[X]) (hQ : Q ≠ 0) (hcop : IsCoprime P Q) {c : K} (hc : c ≠ 0) :
    X * (derivative P * Q - P * derivative Q) ≠ C c * Q ^ 2 := by
  intro heq
  obtain ⟨U, hfactor, hU⟩ := Q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hQ 0
  simp only [map_zero, sub_zero] at hfactor hU
  have hU0 : U.coeff 0 ≠ 0 := fun h => hU (X_dvd_iff.mpr h)
  cases hn : Q.rootMultiplicity 0 with
  | zero =>
      have hQ0 : Q.coeff 0 ≠ 0 := by
        rw [hfactor, hn]
        simpa using hU0
      have hconst := congrArg (fun f : K[X] => f.coeff 0) heq
      have hz : c * (Q.coeff 0) ^ 2 = 0 := by simpa [pow_two] using hconst.symm
      exact (mul_ne_zero hc (pow_ne_zero _ hQ0)) hz
  | succ n =>
      have hQfactor : Q = X ^ (n + 1) * U := by simpa [hn] using hfactor
      have hQ0 : Q.coeff 0 = 0 := by simp [hQfactor]
      have hP0 : P.coeff 0 ≠ 0 := by
        intro hp
        obtain ⟨A, B, hab⟩ := hcop
        have hconst := congrArg (fun f : K[X] => f.coeff 0) hab
        simp [hp, hQ0] at hconst
      have hcancel :
          X * derivative P * U - P * (C (n + 1 : K) * U + X * derivative U) =
            C c * X ^ (n + 1) * U ^ 2 := by
        apply mul_left_cancel₀ (pow_ne_zero (n + 1) (X_ne_zero (R := K)))
        calc
          X ^ (n + 1) *
              (X * derivative P * U - P * (C (n + 1 : K) * U + X * derivative U)) =
              X * (derivative P * Q - P * derivative Q) := by
                rw [hQfactor, derivative_mul, derivative_X_pow_succ]
                ring
          _ = C c * Q ^ 2 := heq
          _ = X ^ (n + 1) * (C c * X ^ (n + 1) * U ^ 2) := by rw [hQfactor]; ring
      have hconst := congrArg (fun f : K[X] => f.coeff 0) hcancel
      have hz : P.coeff 0 * ((n + 1 : K) * U.coeff 0) = 0 := by
        simpa using hconst
      exact (mul_ne_zero hP0 (mul_ne_zero (Nat.cast_add_one_ne_zero n) hU0)) hz

theorem ratFunc_derivation_polynomial {K : Type*} [Field K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hDX : D RatFunc.X = 1) (p : K[X]) :
    D (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (derivative p) := by
  simpa [RatFunc.aeval_X_left_eq_algebraMap, hDX] using D.comp_aeval_eq RatFunc.X p

theorem ratFunc_derivation_ne_simple_pole {K : Type*} [Field K] [CharZero K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hDX : D RatFunc.X = 1) (r : RatFunc K) {c : K} (hc : c ≠ 0) :
    D r ≠ RatFunc.C c / RatFunc.X := by
  intro heq
  have hquot := D.leibniz_div (algebraMap K[X] (RatFunc K) r.num)
    (algebraMap K[X] (RatFunc K) r.denom)
  rw [RatFunc.num_div_denom, ratFunc_derivation_polynomial D hDX,
    ratFunc_derivation_polynomial D hDX] at hquot
  have hder : D r =
      algebraMap K[X] (RatFunc K) (derivative r.num * r.denom - r.num * derivative r.denom) /
        (algebraMap K[X] (RatFunc K) r.denom) ^ 2 := by
    rw [hquot]
    simp only [smul_eq_mul, map_sub, map_mul, div_eq_mul_inv, inv_pow]
    ring
  have hden : algebraMap K[X] (RatFunc K) r.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero r.denom_ne_zero
  have hx : (RatFunc.X : RatFunc K) ≠ 0 := by
    rw [← RatFunc.algebraMap_X]
    exact RatFunc.algebraMap_ne_zero X_ne_zero
  have hcross := (div_eq_div_iff (pow_ne_zero 2 hden) hx).mp (hder.symm.trans heq)
  apply polynomial_logarithmic_equation_impossible r.num r.denom r.denom_ne_zero
    r.isCoprime_num_denom hc
  apply RatFunc.algebraMap_injective K
  simpa only [map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, mul_comm] using hcross

theorem derivation_intermediate_smul
    {k F E : Type*} [Field k] [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    (d : Derivation k F F) (D : Derivation k E E)
    (hcompat : ∀ a : F, D (algebraMap F E a) = algebraMap F E (d a))
    (a : F) (z : E) : D (a • z) = d a • z + a • D z := by
  rw [Algebra.smul_def, D.leibniz, hcompat]
  simp only [smul_eq_mul, Algebra.smul_def]
  ring

theorem derivation_basis_coordinates
    {k F E ι : Type*} [Field k] [Field F] [Field E] [Fintype ι]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    (d : Derivation k F F) (D : Derivation k E E)
    (hcompat : ∀ a : F, D (algebraMap F E a) = algebraMap F E (d a))
    (b : Module.Basis ι F E) (z : E) (i : ι) :
    b.repr (D z) i = d (b.repr z i) +
      ∑ j, b.repr z j * b.repr (D (b j)) i := by
  classical
  conv_lhs => rw [← b.sum_repr z]
  simp only [map_sum, derivation_intermediate_smul d D hcompat, map_add,
    map_smul, Finset.sum_add_distrib, Finsupp.coe_add, Pi.add_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  simp [Finsupp.single_apply, eq_comm]

theorem derivation_trace_of_basis
    {k F E ι : Type*} [Field k] [Field F] [Field E] [Fintype ι]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    (d : Derivation k F F) (D : Derivation k E E)
    (hcompat : ∀ a : F, D (algebraMap F E a) = algebraMap F E (d a))
    (b : Module.Basis ι F E) (x : E) :
    d (Algebra.trace F E x) = Algebra.trace F E (D x) := by
  classical
  let M := Algebra.leftMulMatrix b x
  let N : Matrix ι ι F := fun i j => b.repr (D (b j)) i
  have hentry (i j : ι) :
      Algebra.leftMulMatrix b (D x) i j + (M * N) i j =
        d (M i j) + (N * M) i j := by
    have hMN : (M * N) i j = ∑ t, M i t * N t j := rfl
    have hNM : (N * M) i j = ∑ t, N i t * M t j := rfl
    have hz := derivation_basis_coordinates d D hcompat b (x * b j) i
    have hm := congrFun (Algebra.leftMulMatrix_mulVec_repr b x (D (b j))) i
    have hl : b.repr (D (x * b j)) i =
        Algebra.leftMulMatrix b (D x) i j + (M * N) i j := by
      rw [hMN, D.leibniz]
      simp only [smul_eq_mul, map_add, Finsupp.add_apply]
      rw [← hm]
      simp only [M, N, Algebra.leftMulMatrix_eq_repr_mul,
        Matrix.mulVec, dotProduct, mul_comm, add_comm]
    rw [hl] at hz
    simpa only [hNM, M, N, Algebra.leftMulMatrix_eq_repr_mul, mul_comm] using hz
  have hs := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hentry i i)
  have ht : Matrix.trace (Algebra.leftMulMatrix b (D x)) + Matrix.trace (M * N) =
      d (Matrix.trace M) + Matrix.trace (N * M) := by
    simpa only [Matrix.trace, Matrix.diag_apply, Finset.sum_add_distrib, map_sum] using hs
  rw [Matrix.trace_mul_comm M N] at ht
  have ht' := add_right_cancel ht
  simpa only [Algebra.trace_eq_matrix_trace b, M] using ht'.symm

theorem finite_extension_derivation_ne_simple_pole
    {K E : Type*} [Field K] [CharZero K] [Field E]
    [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    [FiniteDimensional (RatFunc K) E]
    (d : Derivation K (RatFunc K) (RatFunc K)) (D : Derivation K E E)
    (hdX : d RatFunc.X = 1)
    (hcompat : ∀ a : RatFunc K,
      D (algebraMap (RatFunc K) E a) = algebraMap (RatFunc K) E (d a))
    (x : E) {c : K} (hc : c ≠ 0) :
    D x ≠ algebraMap (RatFunc K) E (RatFunc.C c / RatFunc.X) := by
  intro hx
  have ht := derivation_trace_of_basis d D hcompat
    (Module.finBasis (RatFunc K) E) x
  rw [hx, Algebra.trace_algebraMap] at ht
  have hdegree : (Module.finrank (RatFunc K) E : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := RatFunc K) (M := E)))
  apply ratFunc_derivation_ne_simple_pole d hdX (Algebra.trace (RatFunc K) E x)
    (mul_ne_zero hdegree hc)
  calc
    d (Algebra.trace (RatFunc K) E x) =
        Module.finrank (RatFunc K) E • (RatFunc.C c / RatFunc.X) := ht
    _ = RatFunc.C ((Module.finrank (RatFunc K) E : K) * c) / RatFunc.X := by
      simp only [map_mul, map_natCast, nsmul_eq_mul, mul_div_assoc]

end PiExponent

end

end OAI
