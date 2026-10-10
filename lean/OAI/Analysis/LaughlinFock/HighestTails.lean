import Mathlib
import OAI.Analysis.LaughlinFock.BesselComparison
import OAI.Analysis.LaughlinFock.CreationRows
import OAI.Analysis.LaughlinFock.ThreeSpectrum

namespace OAI

/-! Highest Tails. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

 
theorem sum_gram_comparison {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (A : α → Matrix ι ι ℂ) (B : β → Matrix ι ι ℂ)
    (h : ∀ ψ : ι → ℂ, (∑ a, ∑ i, ‖(A a *ᵥ ψ) i‖^2) ≤
      ∑ b, ∑ i, ‖(B b *ᵥ ψ) i‖^2) :
    ((∑ b, (B b)ᴴ * B b) - ∑ a, (A a)ᴴ * A a).PosSemidef := by
  classical
  have hA : (∑ a, (A a)ᴴ * A a).IsHermitian :=
    (Matrix.posSemidef_sum _ fun a _ => Matrix.posSemidef_conjTranspose_mul_self _).isHermitian
  have hB : (∑ b, (B b)ᴴ * B b).IsHermitian :=
    (Matrix.posSemidef_sum _ fun b _ => Matrix.posSemidef_conjTranspose_mul_self _).isHermitian
  have hH := hB.sub hA
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro ψ
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hH.im_star_dotProduct_mulVec_self ψ).symm⟩
  simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.sum_mulVec, dotProduct_sum,
    gram_quadratic_form, star_dotProduct_self, Complex.sub_re,
    Complex.re_sum, Complex.ofReal_re]
  exact sub_nonneg.mpr (h ψ)

 

theorem highestFourAnnihilator_pair_posSemidef {Q D : ℕ} (hD : D ≤ Q) :
    ((∑ b : FourHighestShell Q D,
      (pairAnnihilator Q b.val.1.val)ᴴ * pairAnnihilator Q b.val.1.val) -
      ∑ r : CopyLabel D, (highestFourAnnihilator Q D r)ᴴ * highestFourAnnihilator Q D r).PosSemidef :=
  sum_gram_comparison _ _ (highestFourAnnihilator_pair_bound hD)

 

theorem unit_vector_contracts_family {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s : ι → ℝ) (hs : ∑ i, s i ^ 2 = 1) (x : ι → κ → ℂ) :
    (∑ k, ‖∑ i, (s i : ℂ) * x i k‖^2) ≤ ∑ i, ∑ k, ‖x i k‖^2 := by
  classical
  let S : Matrix Unit ι ℂ := fun _ i => s i
  have hS : S * Sᴴ = 1 := by
    ext u v
    have hu : u=() := by cases u; rfl
    have hv : v=() := by cases v; rfl
    subst u v
    have hc := congrArg (fun t : ℝ => (t : ℂ)) hs
    change (∑ i, (s i : ℂ) * star (s i : ℂ)) = 1
    simpa only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_sum,
      Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_mul, pow_two] using hc
  have h := row_isometry_contracts_family S hS x
  simpa only [S, Fintype.sum_unique] using h

 

def highestThreeAnnihilator (Q z : ℕ) (hz : z ≤ Q) : FockMatrix Q :=
  ∑ p : Fin (z+1), (highestCoefficient (2*Q-2) Q z p.val : ℂ) •
    (annihilator Q ⟨z-p.val, by omega⟩ * pairAnnihilator Q p.val)

 

theorem highestThreeAnnihilator_bound {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (ψ : Occupation Q → ℂ) :
    (∑ A, ‖(highestThreeAnnihilator Q z hz *ᵥ ψ) A‖^2) ≤
      ∑ p : Fin (z+1), ∑ A, ‖(pairAnnihilator Q p.val *ᵥ ψ) A‖^2 := by
  have hn : ∑ p : Fin (z+1), highestCoefficient (2*Q-2) Q z p.val ^ 2 = 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun p => highestCoefficient (2*Q-2) Q z p ^ 2) (z+1)]
    exact highestCoefficient_norm (by omega)
  have h := unit_vector_contracts_family _ hn
    (fun p A => ((annihilator Q ⟨z-p.val, by omega⟩ * pairAnnihilator Q p.val) *ᵥ ψ) A)
  calc
    _ ≤ ∑ p : Fin (z+1), ∑ A,
        ‖((annihilator Q ⟨z-p.val, by omega⟩ * pairAnnihilator Q p.val) *ᵥ ψ) A‖^2 := by
      simpa only [highestThreeAnnihilator, Matrix.sum_mulVec, Matrix.smul_mulVec,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p _
      simpa only [Matrix.mulVec_mulVec] using
        annihilator_contracts Q ⟨z-p.val, by omega⟩ (pairAnnihilator Q p.val *ᵥ ψ)

 

theorem highestThreeAnnihilator_pair_posSemidef {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    ((∑ p : Fin (z+1), (pairAnnihilator Q p.val)ᴴ * pairAnnihilator Q p.val) -
      (highestThreeAnnihilator Q z hz)ᴴ * highestThreeAnnihilator Q z hz).PosSemidef := by
  have h : ∀ ψ : Occupation Q → ℂ,
      (∑ _ : Unit, ∑ A, ‖(highestThreeAnnihilator Q z hz *ᵥ ψ) A‖^2) ≤
        ∑ p : Fin (z+1), ∑ A, ‖(pairAnnihilator Q p.val *ᵥ ψ) A‖^2 := by
    simpa only [Fintype.sum_unique] using highestThreeAnnihilator_bound hQ hz
  simpa only [Fintype.sum_unique] using
    sum_gram_comparison (fun _ : Unit => highestThreeAnnihilator Q z hz)
      (fun p : Fin (z+1) => pairAnnihilator Q p.val) h

 

theorem wedgeAnnihilator_mulVec {ι : Type*} [Fintype ι] (Q k : ℕ)
    (W : Matrix (SectorOccupation Q k) ι ℂ) (s : ι → ℂ) :
    wedgeAnnihilator Q k (W *ᵥ s) =
      ∑ i, star (s i) • wedgeAnnihilator Q k (fun A => W A i) := by
  classical
  simp only [wedgeAnnihilator, Matrix.mulVec, dotProduct, star_sum, star_mul,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

 

theorem threeWedgeMatrix_annihilator_column (Q : ℕ) (pj : PairLabel Q × Orbital Q) :
    wedgeAnnihilator Q 3 (fun A => threeWedgeMatrix Q A pj) =
      annihilator Q pj.2 * pairAnnihilator Q pj.1.val := by
  apply wedgeAnnihilator_annihilatorVector
  exact orbitalPair_mem Q pj.1.val pj.2

 

theorem highestThreeAnnihilator_eq_wedge {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    highestThreeAnnihilator Q z hz =
      wedgeAnnihilator Q 3 (threeWedgeMatrix Q *ᵥ threeCoupledColumn Q z 0) := by
  classical
  rw [wedgeAnnihilator_mulVec]
  simp_rw [threeWedgeMatrix_annihilator_column]
  let e : Fin (z+1) → PairLabel Q × Orbital Q :=
    fun p => (⟨p.val, by have := p.isLt; omega⟩, ⟨z-p.val, by omega⟩)
  have he : Function.Injective e := by
    intro p q h
    exact Fin.ext (congrArg (fun b => b.1.val) h)
  unfold highestThreeAnnihilator
  apply Fintype.sum_of_injective e he
  · intro pj hpj
    have hn : pj.1.val+pj.2.val ≠ z := by
      intro h
      apply hpj
      refine ⟨⟨pj.1.val, by omega⟩, ?_⟩
      apply Prod.ext
      · apply Fin.ext
        rfl
      · apply Fin.ext
        dsimp [e]
        omega
    simp [threeCoupledColumn, coupledVector, hn]
  · intro p
    have hp : p.val+(z-p.val) = z := by have := p.isLt; omega
    simp only [e, threeCoupledColumn, coupledVector, Nat.add_zero, ite_eq_left hp,
      coupledCoefficient, Complex.star_def, Complex.conj_ofReal]

 

theorem threeSpinProjection_trace {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    (threeSpinProjection Q z).trace = ((3*Q-1-2*z : ℕ) : ℂ) := by
  classical
  have hz' : z < min (2*Q-2) Q+1 := by omega
  let r : Fin (min (2*Q-2) Q+1) := ⟨z,hz'⟩
  unfold threeSpinProjection
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, threeCouplingMatrix_gram Q (by omega),
    Matrix.one_mul, Matrix.trace_diagonal]
  change (∑ c : CoupledIndex (2*Q-2) Q, if c.1.val=z then (1:ℂ) else 0) = _
  rw [Fintype.sum_sigma]
  have hs : (∑ a : Fin (min (2*Q-2) Q + 1),
      ∑ _ : Fin (2*Q-2+Q-2*a.val+1), if a.val=z then (1:ℂ) else 0) =
      ((2*Q-2+Q-2*z+1 : ℕ) : ℂ) := by
    rw [Finset.sum_eq_single r]
    · simp [r]
    · intro a _ ha
      have han : a.val ≠ z := by
        intro h
        apply ha
        exact Fin.ext h
      simp [han]
    · simp
  rw [hs]
  congr 1
  omega

end LaughlinFock
end

end OAI
