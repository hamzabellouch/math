import Mathlib
import OAI.Analysis.LaughlinFock.RowTraces

namespace OAI

/-! Three Traces. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology

 
def sourceRowP {Q t : ℕ} (hQ : 8 ≤ Q) (b : RowEntry t) : PairLabel Q :=
  ⟨rowP b, by have := (rowEntry_bounds b).1; omega⟩

def sourceRowI {Q t : ℕ} (hQ : 8 ≤ Q) (b : RowEntry t) : Orbital Q :=
  ⟨rowI b, by have := (rowEntry_bounds b).2.2.1; omega⟩

def sourceRowJ {Q t : ℕ} (hQ : 8 ≤ Q) (b : RowEntry t) : Orbital Q :=
  ⟨rowJ b, by have := (rowEntry_bounds b).2.1; omega⟩

def sourceRowT {Q t : ℕ} (hQ : 8 ≤ Q) (ht : t ≤ 7) : PairLabel Q :=
  ⟨t, by omega⟩

 
def sourceRowThreeKernel {Q t : ℕ} (hQ : 8 ≤ Q) (ht : t ≤ 7)
    (ℓ : ℝ) (a : RowEntry t → ℝ) :
    Matrix (PairLabel Q × Orbital Q) (PairLabel Q × Orbital Q) ℂ :=
  rowThreePrewedge Q (sourceRowT hQ ht) ℓ (sourceRowP hQ) (sourceRowI hQ) (sourceRowJ hQ) a

theorem sourceRowThreeKernel_lift {Q t : ℕ} (hQ : 8 ≤ Q) (ht : t ≤ 7)
    (ℓ : ℝ) (a : RowEntry t → ℝ) :
    exteriorLift Q 3 (threeWedgeMatrix Q * sourceRowThreeKernel hQ ht ℓ a *
      (threeWedgeMatrix Q)ᴴ) =
      rowThreeBody Q t ℓ rowP (sourceRowI hQ) (sourceRowJ hQ) a :=
  rowThreePrewedge_lift Q (sourceRowT hQ ht) ℓ (sourceRowP hQ) (sourceRowI hQ) (sourceRowJ hQ) a

 
def sphericalRowAmplitude (Q z t T : ℕ) (a : RowEntry t → ℝ) : ℝ :=
  ∑ b : RowEntry t, if rowP b+rowJ b=T then
    a b*sphericalThreeCoefficient Q z T (rowP b) else 0

 
theorem coupledVector_eq_sphericalThree (Q z k p j : ℕ) :
    coupledVector (2*Q-2) Q z k p j =
      if p+j=z+k then sphericalThreeCoefficient Q z (z+k) p else 0 := by
  simp [coupledVector, sphericalThreeCoefficient]

 

theorem sourceRowThreeKernel_diagonal {Q t : ℕ} (hQ : 8 ≤ Q) (ht : t ≤ 7)
    (ℓ : ℝ) (a : RowEntry t → ℝ) (z k : ℕ) :
    star (threeCoupledColumn Q z k) ⬝ᵥ
      (sourceRowThreeKernel hQ ht ℓ a *ᵥ threeCoupledColumn Q z k) =
      ((2*ℓ*sphericalThreeCoefficient Q z (z+k) t * sphericalRowAmplitude Q z t (z+k) a +
        (sphericalRowAmplitude Q z t (z+k) a)^2 : ℝ) : ℂ) := by
  classical
  rw [sourceRowThreeKernel]
  unfold threeCoupledColumn
  rw [rowThreePrewedge_bilinear]
  have hi (b : RowEntry t) : t+rowI b=rowP b+rowJ b := (rowEntry_bounds b).2.2.2
  have hh (b c : RowEntry t) : sourceRowI hQ b=sourceRowI hQ c ↔ rowI b=rowI c := by
    exact Fin.ext_iff
  simp only [sourceRowT, sourceRowP, sourceRowJ, sourceRowI, coupledVector_eq_sphericalThree, hi]
  apply congrArg (fun x : ℝ => (x : ℂ))
  apply congrArg₂ (· + ·)
  · unfold sphericalRowAmplitude
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> ring
  · unfold sphericalRowAmplitude
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    have he : (⟨rowI b, by have := (rowEntry_bounds b).2.2.1; omega⟩ : Orbital Q) =
        (⟨rowI c, by have := (rowEntry_bounds c).2.2.1; omega⟩ : Orbital Q) ↔
        rowP b+rowJ b=rowP c+rowJ c := by
      rw [Fin.mk.injEq, rowI_eq_iff]
    simp only [he]
    split_ifs <;> ring_nf
    omega

 
theorem sphericalRowAmplitude_zero {Q z t T : ℕ} (a : RowEntry t → ℝ)
    (h : T < t ∨ 15 < T) : sphericalRowAmplitude Q z t T a = 0 := by
  apply Finset.sum_eq_zero
  intro b _
  rw [ite_eq_right]
  have hb := rowEntry_bounds b
  omega

 
def rowThreeLevelTrace (Q z t : ℕ) (ℓ : ℝ) (a : RowEntry t → ℝ) (T : ℕ) : ℝ :=
  if z ≤ T ∧ t ≤ T then
    2*ℓ*sphericalThreeCoefficient Q z T t*sphericalRowAmplitude Q z t T a +
      (sphericalRowAmplitude Q z t T a)^2
  else 0

theorem rowThreeLevelTrace_lower_zero (Q z t : ℕ) (ℓ : ℝ) (a : RowEntry t → ℝ)
    (T : ℕ) (hT : T < z) : rowThreeLevelTrace Q z t ℓ a T = 0 := by
  simp [rowThreeLevelTrace, Nat.not_le.mpr hT]

theorem rowThreeLevelTrace_upper_zero (Q z t : ℕ) (ℓ : ℝ) (a : RowEntry t → ℝ)
    (T : ℕ) (hT : 15 < T) : rowThreeLevelTrace Q z t ℓ a T = 0 := by
  simp [rowThreeLevelTrace, sphericalRowAmplitude_zero a (Or.inr hT)]

theorem sourceRowThreeKernel_diagonal_level {Q t : ℕ} (hQ : 8 ≤ Q) (ht : t ≤ 7)
    (ℓ : ℝ) (a : RowEntry t → ℝ) (z k : ℕ) :
    star (threeCoupledColumn Q z k) ⬝ᵥ
      (sourceRowThreeKernel hQ ht ℓ a *ᵥ threeCoupledColumn Q z k) =
      (rowThreeLevelTrace Q z t ℓ a (z+k) : ℂ) := by
  rw [sourceRowThreeKernel_diagonal]
  unfold rowThreeLevelTrace
  split_ifs with h
  · rfl
  · have ht' : z+k < t := by omega
    rw [sphericalRowAmplitude_zero a (Or.inl ht')]
    simp

 

theorem sum_shifted_of_support {K L z : ℕ} (hKL : L ≤ z+K) (f : ℕ → ℝ)
    (hlo : ∀ T, T < z → f T=0) (hhi : ∀ T, L ≤ T → f T=0) :
    (∑ k ∈ Finset.range K, f (z+k)) = ∑ T ∈ Finset.range L, f T := by
  have hl : ∑ T ∈ Finset.range z, f T = 0 := by
    exact Finset.sum_eq_zero fun T hT => hlo T (Finset.mem_range.mp hT)
  have hu : (∑ T ∈ Finset.range L, f T) = ∑ T ∈ Finset.range (z+K), f T := by
    apply Finset.sum_subset (Finset.range_mono hKL)
    intro T _ hT
    exact hhi T (by simpa using hT)
  rw [hu, Finset.sum_range_add, hl, zero_add]

 

theorem sourceRowThreeKernel_spinTrace {Q t z : ℕ} (hQ : 16 ≤ Q) (ht : t ≤ 7)
    (hz : z ≤ Q) (ℓ : ℝ) (a : RowEntry t → ℝ) :
    (∑ k : Fin (2*Q-2+Q-2*z+1), star (threeCoupledColumn Q z k.val) ⬝ᵥ
      (sourceRowThreeKernel (by omega : 8 ≤ Q) ht ℓ a *ᵥ threeCoupledColumn Q z k.val)) =
      (rowThreeTrace Q z t ℓ a : ℂ) := by
  simp only [sourceRowThreeKernel_diagonal_level]
  rw [← Complex.ofReal_sum]
  apply congrArg (fun x : ℝ => (x : ℂ))
  rw [Fin.sum_univ_eq_sum_range
    (fun k => rowThreeLevelTrace Q z t ℓ a (z+k)) (2*Q-2+Q-2*z+1)]
  exact sum_shifted_of_support (by omega : 16 ≤ z+(2*Q-2+Q-2*z+1))
    (rowThreeLevelTrace Q z t ℓ a)
    (rowThreeLevelTrace_lower_zero Q z t ℓ a)
    (fun T hT => rowThreeLevelTrace_upper_zero Q z t ℓ a T (by omega))

 

theorem threeSpinProjection_kernel_trace {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (M : Matrix (PairLabel Q × Orbital Q) (PairLabel Q × Orbital Q) ℂ) :
    (threeSpinProjection Q z * M).trace =
      ∑ k : Fin (2*Q-2+Q-2*z+1), star (threeCoupledColumn Q z k.val) ⬝ᵥ
        (M *ᵥ threeCoupledColumn Q z k.val) := by
  classical
  have hz' : z < min (2*Q-2) Q+1 := by omega
  let r : Fin (min (2*Q-2) Q+1) := ⟨z,hz'⟩
  unfold threeSpinProjection
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, ite_mul, one_mul, zero_mul]
  rw [Fintype.sum_sigma, Finset.sum_eq_single r]
  · simp only [r, ite_true]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, threeCouplingMatrix,
      dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  · intro a _ ha
    have han : a.val ≠ z := by
      intro h
      exact ha (Fin.ext h)
    simp [han]
  · simp

 

theorem sourceRowThreeKernel_projectionTrace {Q t z : ℕ} (hQ : 16 ≤ Q)
    (ht : t ≤ 7) (hz : z ≤ Q) (ℓ : ℝ) (a : RowEntry t → ℝ) :
    (threeSpinProjection Q z * sourceRowThreeKernel (by omega : 8 ≤ Q) ht ℓ a).trace =
      (rowThreeTrace Q z t ℓ a : ℂ) := by
  rw [threeSpinProjection_kernel_trace (by omega) hz,
    sourceRowThreeKernel_spinTrace hQ ht hz]

 

theorem rowThreeTrace_above_support {Q z t : ℕ} (hz : 15 < z)
    (ℓ : ℝ) (a : RowEntry t → ℝ) : rowThreeTrace Q z t ℓ a = 0 := by
  apply Finset.sum_eq_zero
  intro T hT
  have hT' := Finset.mem_range.mp hT
  simp only [show ¬ (z ≤ T ∧ t ≤ T) by omega, ite_false]

end LaughlinFock
end

end OAI
