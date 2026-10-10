import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.Outside
import OAI.Combinatorics.ThinTrees.Normalization.Realization
import OAI.Combinatorics.ThinTrees.Signing.RealMatrixBridge

namespace OAI

/-! Rational signing. -/

section

namespace AlgorithmicThinTrees.RationalSigning
open Matrix Finset CurrentKS
open RealMatrixBridge
open scoped MatrixOrder ComplexOrder
variable {d m : ℕ}

def entry (q : ℚ) : RationalEntry := ⟨q.num,q.den,q.den_pos⟩

lemma entry_value (q : ℚ) : (entry q).value=q := by
  exact q.num_div_den

def input (v : Fin m → Fin d → ℚ) : CurrentKS.Input where
  d := d
  N := m
  entries e i j := (entry (v e i*v e j),entry 0)

def selected (v : Fin m → Fin d → ℚ) : Finset (Fin m) :=
  univ.filter (fun e => (CurrentKS.RationalInput.signing (input v)).getD e.val false)

def realVec (v : Fin m → Fin d → ℚ) : Fin m → Fin d → ℝ := fun e i => (v e i:ℝ)

noncomputable def outer (v : Fin m → Fin d → ℚ) (e : Fin m) :=
  vecMulVec (realVec v e) (realVec v e)

lemma input_matrix (v : Fin m → Fin d → ℚ) (e : Fin m) :
    (input v).matrix e=complexMatrix (outer v e) := by
  change (fun i j => CurrentKS.toComplex (entry (v e i*v e j),entry 0)) =
    complexMatrix (outer v e)
  ext i j
  apply Complex.ext <;>
    simp [CurrentKS.toComplex,entry_value,outer,realVec,complexMatrix,vecMulVec_apply]

lemma complex_outer (u : Fin d → ℝ) :
    complexMatrix (vecMulVec u u)=vecMulVec (fun i => (u i:ℂ)) (star (fun i => (u i:ℂ))) := by
  ext i j
  simp [complexMatrix,vecMulVec_apply]

lemma input_admissible (v : Fin m → Fin d → ℚ) : CurrentKS.Admissible (input v) := by
  intro e
  change Fin m at e
  rw [input_matrix,outer,complex_outer]
  exact ⟨(posSemidef_vecMulVec_self_star _).isHermitian,rank_vecMulVec_le _ _⟩

lemma outer_psd (v : Fin m → Fin d → ℚ) (e : Fin m) : (outer v e).PosSemidef := by
  simpa only [outer,star_trivial] using posSemidef_vecMulVec_self_star (realVec v e)

lemma outer_square (v : Fin m → Fin d → ℚ) (e : Fin m) :
    outer v e*outer v e=(realVec v e ⬝ᵥ realVec v e) • outer v e := by
  rw [outer,vecMulVec_mul_vecMulVec]
  ext i j
  simp only [vecMulVec_apply,Pi.smul_apply,Matrix.smul_apply,smul_eq_mul]
  ring

lemma complexMatrix_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin d) (Fin d) ℝ) :
    complexMatrix (∑e∈s, A e)=∑e∈s, complexMatrix (A e) := by
  ext i j
  simp only [complexMatrix,map_apply,Matrix.sum_apply,Complex.ofReal_sum]

lemma variance_eq (v : Fin m → Fin d → ℚ) :
    variance (input v)=complexMatrix (∑e, (realVec v e ⬝ᵥ realVec v e) • outer v e) := by
  have hm (e : Fin m) := input_matrix v e
  dsimp only [input] at hm
  simp only [variance,input]
  simp only [hm]
  change (∑e : Fin m, complexMatrix (outer v e)*complexMatrix (outer v e)) = _
  simp only [←complexMatrix_mul,outer_square,complexMatrix_sum]

lemma scalar_order {A B : Matrix (Fin d) (Fin d) ℝ} (h : A ≤ B) {c : ℝ} (hc : 0 ≤ c) :
    c • A ≤ c • B := by
  rw [Matrix.le_iff,←smul_sub]
  exact (Matrix.le_iff.mp h).smul hc

lemma variance_bound (v : Fin m → Fin d → ℚ) {δ c : ℝ} (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hcov : (∑e, outer v e) ≤ c • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hnorm : ∀e, realVec v e ⬝ᵥ realVec v e ≤ δ) :
    opNorm (variance (input v)) ≤ c*δ := by
  rw [variance_eq]
  have hp : (∑e, (realVec v e ⬝ᵥ realVec v e) • outer v e).PosSemidef := by
    refine Matrix.posSemidef_sum _ ?_
    intro e _
    exact (outer_psd v e).smul (by unfold dotProduct;exact sum_nonneg (fun e _ => mul_self_nonneg _))
  apply norm_le_of_psd_bound hp (mul_nonneg hc hδ)
  have hle : (∑e, (realVec v e ⬝ᵥ realVec v e) • outer v e) ≤ δ • (∑e, outer v e) := by
    rw [smul_sum]
    apply sum_le_sum
    intro e _
    rw [Matrix.le_iff,←sub_smul]
    exact (outer_psd v e).smul (sub_nonneg.mpr (hnorm e))
  exact hle.trans ((scalar_order hcov hδ).trans_eq (by rw [smul_smul,mul_comm δ c]))

lemma signed_eq (v : Fin m → Fin d → ℚ) (bits : List Bool) :
    CurrentKS.signedSum (input v) bits=complexMatrix
      (∑e, CurrentKS.signValue (bits.getD e.val false) • outer v e) := by
  have hm (e : Fin m) := input_matrix v e
  dsimp only [input] at hm
  simp only [signedSum,input]
  simp only [hm,complexMatrix_sum,complexMatrix_smul]
  rfl

lemma half_identity (v : Fin m → Fin d → ℚ) :
    (∑e∈selected v, outer v e)-(1/2:ℝ) • (∑e,outer v e)=
      (1/2:ℝ) • (∑e, CurrentKS.signValue
        ((CurrentKS.RationalInput.signing (input v)).getD e.val false) • outer v e) := by
  rw [selected,sum_filter,smul_sum,smul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro e _
  cases (CurrentKS.RationalInput.signing (input v)).getD e.val false <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,signValue,smul_smul] <;> module

theorem half_bounds (v : Fin m → Fin d → ℚ) {δ c : ℝ} (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hcov : (∑e,outer v e) ≤ c • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hnorm : ∀e, realVec v e ⬝ᵥ realVec v e ≤ δ) :
    let D := (∑e∈selected v,outer v e)-(1/2:ℝ) • (∑e,outer v e)
    (-(20*Real.sqrt (c*δ))) • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ D ∧
      D ≤ (20*Real.sqrt (c*δ)) • 1 := by
  let bits := CurrentKS.RationalInput.signing (input v)
  have hsign := (CurrentKS.RationalInput.signing_good (input v) (input_admissible v)).2
  have hvar := variance_bound v hδ hc hcov hnorm
  have hnorm' : opNorm (complexMatrix (∑e,CurrentKS.signValue (bits.getD e.val false) • outer v e)) ≤
      40*Real.sqrt (c*δ) := by
    rw [←signed_eq]
    exact hsign.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvar) (by norm_num))
  have hH : (∑e,CurrentKS.signValue (bits.getD e.val false) • outer v e).IsHermitian := by
    change (∑e,CurrentKS.signValue (bits.getD e.val false) • outer v e)ᴴ = _
    rw [conjTranspose_sum]
    apply sum_congr rfl
    intro e _
    exact (outer_psd v e).isHermitian.smul (isSelfAdjoint_iff.mpr (star_trivial _))
  obtain ⟨hl,hu⟩ := bounds_of_norm_le hH hnorm'
  dsimp only
  rw [half_identity]
  have hhalf : (0:ℝ) ≤ 1/2 := by norm_num
  constructor
  · convert scalar_order hl hhalf using 1
    rw [smul_smul]
    congr 1
    ring
  · convert scalar_order hu hhalf using 1
    rw [smul_smul]
    congr 1
    ring

end AlgorithmicThinTrees.RationalSigning
end

end OAI
