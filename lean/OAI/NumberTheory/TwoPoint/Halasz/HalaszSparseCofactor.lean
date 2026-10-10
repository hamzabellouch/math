import OAI.NumberTheory.TwoPoint.Halasz.HalaszIntegerKernel
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparseCofactor

namespace OAI

/-! The proved integer kernel attached to actual reciprocal-count cofactors. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszSparseKernelError (M T : ℝ) : ℝ :=
  (440/Real.pi)*Real.sqrt (2*T) +
    (512/(M*(2*Real.pi)^2))*halaszIntegerSquareMass

lemma halasz_triangle_dyadic_member (M : ℝ) (hM : 0 < M) (n : ℕ)
    (hn : n ∈ Ioc ⌊M⌋₊ ⌊2*M⌋₊) :
    n ∈ halaszTriangleSupport M ∧ 1 ≤ halaszTriangleWeight M n := by
  have hlow : M < n := (Nat.floor_lt hM.le).mp (mem_Ioc.mp hn).1
  have hu : (n:ℝ) ≤ 2*M :=
    (Nat.cast_le.mpr (mem_Ioc.mp hn).2).trans (Nat.floor_le (by positivity))
  refine ⟨?_,halasz_triangle_weight_dyadic M n hM ⟨hlow.le,hu⟩⟩
  apply mem_range.mpr
  change n < ⌈5*M/2⌉₊+1
  apply Nat.lt_succ_of_le
  exact_mod_cast (show (n:ℝ) ≤ (⌈5*M/2⌉₊:ℝ) from
    (hu.trans (by linarith)).trans (Nat.le_ceil (5*M/2)))

lemma halasz_integer_kernel_on_samples (M T : ℝ) (hM : 0 < M) (_hT : 0 ≤ T)
    (S : Finset ℝ) (hS : ∀ t ∈ S, |t| ≤ T) :
    ∀ t ∈ S, ∀ s ∈ S,
      ‖mrtExponentialPolynomial (halaszTriangleSupport M)
        (fun n => (halaszTriangleWeight M n:ℂ)) (fun n => -Real.log n) (t-s)‖ ≤
      (18600*M)/(1+(t-s)^2)+halaszSparseKernelError M T := by
  intro t ht s hs
  apply (halasz_integer_kernel M (t-s) hM).trans
  have hts : |t-s| ≤ 2*T := by
    have hh := abs_sub t s
    linarith [hS t ht,hS s hs]
  have hroot := Real.sqrt_le_sqrt hts
  dsimp [halaszSparseKernelError]
  rw [← add_assoc]
  gcongr

/-- An unconditional sparse mean square for the literal cofactor window. -/
theorem halasz_sparse_cofactor_energy (P : Finset ℕ) (F : ℕ → ℂ)
    (hF : OneBounded F) (N : ℕ) {a : ℝ} (ha : 1 ≤ a)
    (hx : 2 ≤ (N:ℝ)/a) {T : ℝ} (hT : 0 ≤ T)
    (S : Finset ℝ) (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) :
    (∑ t ∈ S, ‖mrtCofactorPolynomial P F N a t‖^2) ≤
      (148800*((N:ℝ)/a)+(S.card:ℝ)*halaszSparseKernelError ((N:ℝ)/a) T)*(2*a/N) := by
  have hM : 0 < (N:ℝ)/a := lt_of_lt_of_le (by norm_num) hx
  have he : (2*N:ℝ)/a = 2*((N:ℝ)/a) := by ring
  have hmem (n : ℕ) (hn : n ∈ Ioc ⌊(N:ℝ)/a⌋₊ ⌊(2*N:ℝ)/a⌋₊) :=
    halasz_triangle_dyadic_member ((N:ℝ)/a) hM n (by rwa [he] at hn)
  have h := mrt_sparse_cofactor_energy P F hF N ha hx
    (halaszTriangleSupport ((N:ℝ)/a)) (fun n hn => (hmem n hn).1)
    (fun n => halaszTriangleWeight ((N:ℝ)/a) n) (fun n _ => halasz_triangle_weight_nonneg _ n)
    (fun n hn => (hmem n hn).2) S hsep
    (by positivity : 0 ≤ 18600*((N:ℝ)/a))
    (by
      dsimp [halaszSparseKernelError]
      exact add_nonneg (by positivity) (mul_nonneg (by positivity) halasz_integer_square_mass_nonneg))
    (halasz_integer_kernel_on_samples ((N:ℝ)/a) T hM hT S hS)
  convert h using 1
  ring

end TwoPointCorrelations

end OAI
