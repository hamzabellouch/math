import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.SpectralPowers

namespace OAI

/-! Hermitian trace representatives and spanning by reflections. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open PolynomialPEPS.PinnedEntropy

open scoped MatrixOrder
namespace PolynomialPEPS.Subvolume.HermitianFunctional
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem map_star_of_real (l : Matrix ι ι ℂ →ₗ[ℂ] ℂ)
    (h : ∀ H : Matrix ι ι ℂ, H.IsHermitian → (l H).im = 0)
    (A : Matrix ι ι ℂ) : l (star A) = star (l A) := by
  have hplus : (A+star A).IsHermitian := by
    change star (A+star A) = A+star A
    simp [add_comm]
  have hminus : (Complex.I • (A-star A)).IsHermitian := by
    change star (Complex.I • (A-star A)) = Complex.I • (A-star A)
    simp [star_sub,star_smul,RCLike.star_def,smul_sub,neg_smul]
    abel
  have hp := h (A+star A) hplus
  have hm := h (Complex.I • (A-star A)) hminus
  simp only [map_add,Complex.add_im] at hp
  simp only [map_smul,map_sub,smul_eq_mul,Complex.mul_im,Complex.I_re,
    Complex.I_im,zero_mul,one_mul,zero_add,Complex.sub_re] at hm
  apply Complex.ext
  · simpa [RCLike.star_def] using (sub_eq_zero.mp hm).symm
  · simp only [RCLike.star_def,Complex.conj_im]
    linarith

def representative (l : Matrix ι ι ℂ →ₗ[ℂ] ℂ) : Matrix ι ι ℂ :=
  fun i j => l (Matrix.single j i 1)

theorem apply_eq_trace (l : Matrix ι ι ℂ →ₗ[ℂ] ℂ) (A : Matrix ι ι ℂ) :
    l A = (representative l * A).trace := by
  rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum,Matrix.mul_sum,Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← show A i j • Matrix.single i j (1 : ℂ) = Matrix.single i j (A i j) from by
    simp [Matrix.smul_single], map_smul]
  simp [representative,smul_eq_mul,mul_comm,Matrix.trace_mul_single]

theorem isHermitian_of_trace_real (B : Matrix ι ι ℂ)
    (h : ∀ H : Matrix ι ι ℂ, H.IsHermitian → (B*H).trace.im=0) : B.IsHermitian := by
  let l : Matrix ι ι ℂ →ₗ[ℂ] ℂ :=
    (Matrix.traceLinearMap ι ℂ ℂ).comp (LinearMap.mulLeft ℂ B)
  have hs := map_star_of_real l h
  apply Matrix.IsHermitian.ext
  intro i j
  have hij := hs (Matrix.single i j 1)
  simpa [l,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_single,
    Matrix.trace_mul_single] using hij.symm

theorem commuting_transition (F B : Matrix ι ι ℂ) (hF : F.PosSemidef)
    (hFB : (F*B).IsHermitian) (hBF : (B*F).IsHermitian) : Commute F B := by
  have h1 : star B * F = F*B := by
    simpa only [star_mul,hF.isHermitian.star_eq] using hFB.star_eq
  have h2 : F * star B = B*F := by
    simpa only [star_mul,hF.isHermitian.star_eq] using hBF.star_eq
  have hc : Commute (F*F) B := by
    change (F*F)*B = B*(F*F)
    calc
      (F*F)*B = F*(F*B) := mul_assoc _ _ _
      _ = F*(star B*F) := by rw [h1]
      _ = (F*star B)*F := (mul_assoc _ _ _).symm
      _ = B*(F*F) := by rw [h2,mul_assoc]
  have hroot := hc.cfcₙ_nnreal NNReal.sqrt
  change Commute (CFC.sqrt (F*F)) B at hroot
  simpa only [CFC.sqrt_mul_self F hF.nonneg] using hroot

theorem moment_commute (l : Matrix ι ι ℂ →ₗ[ℂ] ℂ) (F : Matrix ι ι ℂ)
    (hF : F.PosSemidef)
    (hleft : ∀ H : Matrix ι ι ℂ, H.IsHermitian → (l (H*F)).im=0)
    (hright : ∀ H : Matrix ι ι ℂ, H.IsHermitian → (l (F*H)).im=0)
    (A : Matrix ι ι ℂ) : l (A*F) = l (F*A) := by
  let B := representative l
  have hFB : (F*B).IsHermitian := isHermitian_of_trace_real _ (fun H hH => by
    have hb := hleft H hH
    rw [apply_eq_trace] at hb
    change (F*B*H).trace.im = 0
    rw [← Matrix.trace_mul_cycle B H F,mul_assoc]
    exact hb)
  have hBF : (B*F).IsHermitian := isHermitian_of_trace_real _ (fun H hH => by
    have hb := hright H hH
    rw [apply_eq_trace] at hb
    simpa [B,mul_assoc] using hb)
  have hc := commuting_transition F B hF hFB hBF
  rw [apply_eq_trace,apply_eq_trace]
  change (B*(A*F)).trace = (B*(F*A)).trace
  calc
    (B*(A*F)).trace = (F*B*A).trace := by rw [← mul_assoc,Matrix.trace_mul_cycle]
    _ = (B*(F*A)).trace := by rw [hc.eq,mul_assoc]

end PolynomialPEPS.Subvolume.HermitianFunctional

namespace PolynomialPEPS.Subvolume.ReflectionSpan
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open PolynomialPEPS.Subvolume.SpectralCurve
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def reflection (U : unitary (Matrix ι ι ℂ)) (i : ι) : unitary (Matrix ι ι ℂ) :=
  ⟨spectralHom U (fun j => if j=i then -1 else 1), by
    let d : ι → ℂ := fun j => if j=i then -1 else 1
    have hd : star d = d := by
      ext j
      by_cases h : j=i <;> simp [d,h]
    have hsq : d*d = 1 := by
      ext j
      by_cases h : j=i <;> simp [d,h]
    change star (spectralHom U d)*spectralHom U d = 1 ∧
      spectralHom U d*star (spectralHom U d) = 1
    constructor <;> rw [← map_star,hd,← map_mul,hsq,map_one]⟩

theorem reflection_star (U : unitary (Matrix ι ι ℂ)) (i : ι) :
    star (reflection U i : Matrix ι ι ℂ) = (reflection U i : Matrix ι ι ℂ) := by
  change star (spectralHom U _) = spectralHom U _
  rw [← map_star]
  congr 1
  ext j
  by_cases h : j=i <;> simp [h]

theorem reflection_eq (U : unitary (Matrix ι ι ℂ)) (i : ι) :
    (reflection U i : Matrix ι ι ℂ) =
      1-(2:ℂ) • spectralHom U (Pi.single i 1) := by
  have hd : (fun j : ι => if j=i then (-1 : ℂ) else 1) =
      1-(2:ℂ) • Pi.single i 1 := by
    ext j
    by_cases h : j=i <;> norm_num [Pi.single_apply,h]
  change spectralHom U _ = _
  rw [hd,map_sub,map_smul,map_one]

theorem zero_of_hermitian_tests (l : Matrix ι ι ℂ →ₗ[ℂ] ℂ)
    (h : ∀ H : Matrix ι ι ℂ, H.IsHermitian → l H = 0)
    (A : Matrix ι ι ℂ) : l A = 0 := by
  have hplus : (A+star A).IsHermitian := by
    change star (A+star A) = A+star A
    simp [add_comm]
  have hminus : (Complex.I • (A-star A)).IsHermitian := by
    change star (Complex.I • (A-star A)) = Complex.I • (A-star A)
    simp [star_sub,star_smul,RCLike.star_def,smul_sub,neg_smul]
    abel
  have hp := h (A+star A) hplus
  have hm := h (Complex.I • (A-star A)) hminus
  simp only [map_add] at hp
  have hm' : l A = l (star A) := by
    apply sub_eq_zero.mp
    simpa [map_smul,map_sub,smul_eq_mul] using hm
  rw [← hm'] at hp
  have hz : (2:ℂ)*l A = 0 := by simpa [two_mul] using hp
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem zero_of_reflection_tests (l : Matrix ι ι ℂ →ₗ[ℂ] ℂ)
    (h : ∀ W : unitary (Matrix ι ι ℂ), star (W : Matrix ι ι ℂ)=W → l W = 0)
    (A : Matrix ι ι ℂ) : l A = 0 := by
  have h1 : l 1 = 0 := h 1 (by simp)
  have hP (U : unitary (Matrix ι ι ℂ)) (i : ι) :
      l (spectralHom U (Pi.single i 1)) = 0 := by
    have hs := h (reflection U i) (reflection_star U i)
    rw [reflection_eq,map_sub,map_smul,h1] at hs
    simpa [smul_eq_mul] using hs
  apply zero_of_hermitian_tests l ?_ A
  intro H hH
  let U := hH.eigenvectorUnitary
  have hdiag : (fun j => (hH.eigenvalues j : ℂ)) =
      ∑ i, (hH.eigenvalues i : ℂ) • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply,Finset.sum_apply,Pi.smul_apply]
  have hrep : H = spectralHom U (fun j => (hH.eigenvalues j : ℂ)) := hH.spectral_theorem
  rw [hrep,hdiag,map_sum,map_sum]
  simp only [map_smul,hP,smul_zero,Finset.sum_const_zero]

end PolynomialPEPS.Subvolume.ReflectionSpan

end

end OAI
