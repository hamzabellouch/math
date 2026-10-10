import Mathlib
import OAI.Analysis.LaughlinFock.CopyNormalization

namespace OAI

/-! Bessel Comparison. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

 
abbrev CopyLabel (D : ℕ) := {r : Fin (D+1) // Odd r.val}

 
abbrev FourUncoupled (Q : ℕ) := Fin (2*Q-2+1) × IncreasingPair Q

 
abbrev FourHighestShell (Q D : ℕ) :=
  {b : FourUncoupled Q // b.1.val+b.2.val.1.val+b.2.val.2.val=D}

 
theorem sum_subtype_support {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (P : ι → Prop) [DecidablePred P] (f : ι → M)
    (hf : ∀ i, ¬P i → f i=0) : (∑ i : {i // P i}, f i.val) = ∑ i, f i := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp) f, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · rfl
  · exact (hf i h).symm

 

def highestCopyMatrix (Q D : ℕ) : Matrix (CopyLabel D) (FourHighestShell Q D) ℂ :=
  fun r b => sphericalCopyCoefficient Q D D r.val.val
    b.val.1.val b.val.2.val.1.val b.val.2.val.2.val

 

theorem highestCopyMatrix_gram {Q D : ℕ} (hD : D ≤ Q) :
    highestCopyMatrix Q D * (highestCopyMatrix Q D)ᴴ = 1 := by
  classical
  ext r s
  have h := sphericalCopyCoefficient_highest_gram hD
    (Nat.le_of_lt_succ r.val.isLt) (Nat.le_of_lt_succ s.val.isLt) r.property s.property
  have he : (r.val.val=s.val.val) ↔ r=s := by
    constructor
    · intro h
      exact Subtype.ext (Fin.ext h)
    · rintro rfl
      rfl
  simp only [he] at h
  rw [← sum_subtype_support
    (fun b : FourUncoupled Q => b.1.val+b.2.val.1.val+b.2.val.2.val=D)
    (fun b => sphericalCopyCoefficient Q D D r.val.val b.1.val b.2.val.1.val b.2.val.2.val *
      sphericalCopyCoefficient Q D D s.val.val b.1.val b.2.val.1.val b.2.val.2.val)] at h
  · have hc := congrArg (fun t : ℝ => (t : ℂ)) h
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, highestCopyMatrix,
      Complex.star_def, Complex.conj_ofReal, Complex.ofReal_sum, Complex.ofReal_mul,
      Matrix.one_apply, apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using hc
  · intro b hb
    simp [sphericalCopyCoefficient, hb]

 
def shellFourAnnihilator (Q D : ℕ) (b : FourHighestShell Q D) : FockMatrix Q :=
  annihilator Q b.val.2.val.2 * annihilator Q b.val.2.val.1 * pairAnnihilator Q b.val.1.val

 

def highestFourAnnihilator (Q D : ℕ) (r : CopyLabel D) : FockMatrix Q :=
  ∑ b : FourHighestShell Q D, highestCopyMatrix Q D r b • shellFourAnnihilator Q D b

 

theorem highestFourAnnihilator_bessel {Q D : ℕ} (hD : D ≤ Q)
    (ψ : Occupation Q → ℂ) :
    (∑ r : CopyLabel D, ∑ A, ‖(highestFourAnnihilator Q D r *ᵥ ψ) A‖^2) ≤
      ∑ b : FourHighestShell Q D, ∑ A, ‖(shellFourAnnihilator Q D b *ᵥ ψ) A‖^2 := by
  have h := row_isometry_contracts_family (highestCopyMatrix Q D) (highestCopyMatrix_gram hD)
    (fun b A => (shellFourAnnihilator Q D b *ᵥ ψ) A)
  simpa only [highestFourAnnihilator, Matrix.sum_mulVec, Matrix.smul_mulVec,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

 

theorem highestFourAnnihilator_pair_bound {Q D : ℕ} (hD : D ≤ Q)
    (ψ : Occupation Q → ℂ) :
    (∑ r : CopyLabel D, ∑ A, ‖(highestFourAnnihilator Q D r *ᵥ ψ) A‖^2) ≤
      ∑ b : FourHighestShell Q D, ∑ A,
        ‖(pairAnnihilator Q b.val.1.val *ᵥ ψ) A‖^2 := by
  refine (highestFourAnnihilator_bessel hD ψ).trans ?_
  exact Finset.sum_le_sum fun b _ =>
    twoAnnihilators_contract Q b.val.2.val.1 b.val.2.val.2 _ ψ

 

def fourHighestShellEquiv {Q D : ℕ} (hQ : 1 ≤ Q) (hD : D ≤ Q) :
    FourHighestShell Q D ≃ ((n : Fin (D+1)) × Fin ((n.val+1)/2)) where
  toFun b := ⟨⟨b.val.2.val.1.val+b.val.2.val.2.val, by have := b.property; omega⟩,
    ⟨b.val.2.val.1.val, by
      change b.val.2.val.1.val < (b.val.2.val.1.val+b.val.2.val.2.val+1)/2
      have hlt : b.val.2.val.1.val < b.val.2.val.2.val := b.val.2.property
      omega⟩⟩
  invFun c := by
    let n := c.1.val
    let j := c.2.val
    have hn := c.1.isLt
    have hj := c.2.isLt
    refine ⟨(⟨D-n, by dsimp [n] at *; omega⟩,
      ⟨(⟨j, by dsimp [n,j] at *; omega⟩,
        ⟨n-j, by dsimp [n,j] at *; omega⟩), ?_⟩), ?_⟩
    · change j < n-j
      dsimp [n,j] at *
      omega
    · change D-n+j+(n-j)=D
      dsimp [n,j] at *
      omega
  left_inv b := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      dsimp
      have := b.property
      omega
    · apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        rfl
      · apply Fin.ext
        dsimp
        omega
  right_inv c := by
    rcases c with ⟨n,j⟩
    apply Sigma.ext
    · apply Fin.ext
      dsimp
      have := j.isLt
      omega
    · apply (Fin.heq_ext_iff ?_).mpr
      · rfl
      · dsimp
        have := j.isLt
        omega

theorem fourHighestShell_card_sum {Q D : ℕ} (hQ : 1 ≤ Q) (hD : D ≤ Q) :
    Fintype.card (FourHighestShell Q D) = ∑ n ∈ Finset.range (D+1), (n+1)/2 := by
  rw [Fintype.card_congr (fourHighestShellEquiv hQ hD)]
  simp only [Fintype.card_sigma, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun n => (n+1)/2) (D+1)

 
theorem shell_count_formula (D : ℕ) :
    (∑ n ∈ Finset.range (D+1), (n+1)/2) = (D+1)^2/4 := by
  induction D using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more D ih _ =>
    rw [show D+2+1 = (D+1)+1+1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have he : (D+2)/2 + (D+3)/2 = D+2 := by omega
    have hh : (D+3)^2 = (D+1)^2 + (D+2)*4 := by ring
    rw [show D+1+1 = D+2 by omega, show D+1+1+1 = D+3 by omega,
      add_assoc, he, hh, Nat.add_mul_div_right]
    norm_num

theorem fourHighestShell_card {Q D : ℕ} (hQ : 1 ≤ Q) (hD : D ≤ Q) :
    Fintype.card (FourHighestShell Q D) = (D+1)^2/4 := by
  rw [fourHighestShell_card_sum hQ hD, shell_count_formula]

 

theorem fourHighestShell_count {Q : ℕ} (hQ : 23 ≤ Q) :
    (∑ D ∈ Finset.Icc 1 23, Fintype.card (FourHighestShell Q D)) = 1222 := by
  calc
    _ = ∑ D ∈ Finset.Icc 1 23, (D+1)^2/4 := by
      apply Finset.sum_congr rfl
      intro D hD
      exact fourHighestShell_card (by omega) (by have := (Finset.mem_Icc.mp hD).2; omega)
    _ = 1222 := by norm_num [Finset.sum_Icc_succ_top]

end LaughlinFock
end

end OAI
