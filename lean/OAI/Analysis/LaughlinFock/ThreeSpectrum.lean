import Mathlib
import OAI.Analysis.LaughlinFock.CopyNormalization
import OAI.Analysis.LaughlinFock.ExchangeSpectrum
import OAI.Analysis.LaughlinFock.ThreeGram

namespace OAI

/-! Three Spectrum. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

 

theorem pairSwapCompression_apply (Q : ℕ) (f : GridVector) (p j : ℕ) :
    pairSwapCompression Q f p j =
      ∑ r ∈ Finset.range (2*Q-2+1), ∑ k ∈ Finset.range (Q+1),
        (∑ i ∈ Finset.range (Q+1),
          coupledVector Q Q 1 p i k * coupledVector Q Q 1 r i j) * f r k := by
  simp only [pairSwapCompression, LinearMap.comp_apply, pairTensorProject,
    pairTensorEmbed, swap23, LinearMap.coe_mk, AddHom.coe_mk, gridInner,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.range (Q+1)) (t := Finset.range (2*Q-2+1))]
  rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

 
theorem pairSwapCompression_apply_fin (Q : ℕ) (hQ : 1 ≤ Q)
    (f : GridVector) (p j : ℕ) :
    pairSwapCompression Q f p j =
      ∑ r : PairLabel Q, ∑ k : Orbital Q,
        (∑ i : Orbital Q,
          coupledVector Q Q 1 p i.val k.val * coupledVector Q Q 1 r.val i.val j) * f r.val k.val := by
  rw [pairSwapCompression_apply]
  symm
  calc
    _ = ∑ r : PairLabel Q, ∑ k ∈ Finset.range (Q+1),
        (∑ i ∈ Finset.range (Q+1),
          coupledVector Q Q 1 p i k * coupledVector Q Q 1 r.val i j) * f r.val k := by
      apply Finset.sum_congr rfl
      intro r _
      calc
        _ = ∑ k : Orbital Q, (∑ i ∈ Finset.range (Q+1),
            coupledVector Q Q 1 p i k.val * coupledVector Q Q 1 r.val i j) * f r.val k.val := by
          apply Finset.sum_congr rfl
          intro k _
          congr 1
          exact Fin.sum_univ_eq_sum_range
            (fun i => coupledVector Q Q 1 p i k.val * coupledVector Q Q 1 r.val i j) (Q+1)
        _ = _ := Fin.sum_univ_eq_sum_range
          (fun k => (∑ i ∈ Finset.range (Q+1),
            coupledVector Q Q 1 p i k * coupledVector Q Q 1 r.val i j) * f r.val k) (Q+1)
    _ = _ := by
      rw [show 2*Q-2+1 = 2*Q-1 by omega]
      exact Fin.sum_univ_eq_sum_range
        (fun r => ∑ k ∈ Finset.range (Q+1), (∑ i ∈ Finset.range (Q+1),
          coupledVector Q Q 1 p i k * coupledVector Q Q 1 r i j) * f r k) (2*Q-1)

 

theorem threeWedgeMatrix_gram_mulVec_grid (Q : ℕ) (hQ : 1 ≤ Q)
    (f : GridVector) (pj : PairLabel Q × Orbital Q) :
    (((threeWedgeMatrix Q)ᴴ * threeWedgeMatrix Q) *ᵥ
      (fun rk => (f rk.1.val rk.2.val : ℂ))) pj =
        (f pj.1.val pj.2.val : ℂ) - 2 *
          (pairSwapCompression Q f pj.1.val pj.2.val : ℂ) := by
  classical
  have hc (p : PairLabel Q) (j i : Orbital Q) :
      (pairCoefficient Q p.val j i : ℂ) =
        -(Real.sqrt 2 : ℂ) * (coupledVector Q Q 1 p.val i.val j.val : ℂ) := by
    rw [pairCoefficient_antisymm, pairCoefficient_eq_coupled hQ (by have := p.isLt; omega)]
    push_cast
    ring
  have htwo : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num)
  have hex (rk : PairLabel Q × Orbital Q) :
      (∑ i : Orbital Q, (pairCoefficient Q pj.1.val rk.2 i : ℂ) *
          (pairCoefficient Q rk.1.val pj.2 i : ℂ)) =
        2 * (∑ i : Orbital Q, (coupledVector Q Q 1 pj.1.val i.val rk.2.val : ℂ) *
          (coupledVector Q Q 1 rk.1.val i.val pj.2.val : ℂ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hc, hc]
    calc
      _ = ((Real.sqrt 2 : ℂ)*(Real.sqrt 2 : ℂ)) *
          ((coupledVector Q Q 1 pj.1.val i.val rk.2.val : ℂ) *
           (coupledVector Q Q 1 rk.1.val i.val pj.2.val : ℂ)) := by ring
      _ = _ := by rw [htwo]
  simp only [Matrix.mulVec, dotProduct, threeWedgeMatrix_gram_apply Q hQ, hex,
    sub_mul, Finset.sum_sub_distrib]
  rw [show (∑ rk : PairLabel Q × Orbital Q,
      (if pj=rk then (1:ℂ) else 0) * (f rk.1.val rk.2.val : ℂ)) = f pj.1.val pj.2.val by simp]
  congr 1
  rw [pairSwapCompression_apply_fin Q hQ, Fintype.sum_prod_type]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

 
def threeCoupledColumn (Q z k : ℕ) : PairLabel Q × Orbital Q → ℂ :=
  fun pj => coupledVector (2*Q-2) Q z k pj.1.val pj.2.val

 

theorem threeWedgeMatrix_gram_eigenvector {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) (k : ℕ) :
    ((threeWedgeMatrix Q)ᴴ * threeWedgeMatrix Q) *ᵥ threeCoupledColumn Q z k =
      (1 + gramShift Q z : ℂ) • threeCoupledColumn Q z k := by
  funext pj
  unfold threeCoupledColumn
  rw [threeWedgeMatrix_gram_mulVec_grid Q (by omega),
    pairSwapCompression_eigenvector hQ hz]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

 

theorem coupledVector_resolution (n m : ℕ)
    (pq rs : Fin (n+1) × Fin (m+1)) :
    (∑ c : CoupledIndex n m,
      coupledVector n m c.1.val c.2.val pq.1.val pq.2.val *
        coupledVector n m c.1.val c.2.val rs.1.val rs.2.val) =
      if pq=rs then 1 else 0 := by
  classical
  simpa only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul, coupledBasis_apply, coupledEuclidean, gridEuclidean,
    PiLp.single_apply, eq_comm] using
      (coupledBasis n m).sum_inner_mul_inner
        (EuclideanSpace.single pq 1) (EuclideanSpace.single rs 1)

 

def threeCouplingMatrix (Q : ℕ) :
    Matrix (PairLabel Q × Orbital Q) (CoupledIndex (2*Q-2) Q) ℂ :=
  fun pj c => threeCoupledColumn Q c.1.val c.2.val pj

 
theorem threeCouplingMatrix_gram (Q : ℕ) (hQ : 1 ≤ Q) :
    (threeCouplingMatrix Q)ᴴ * threeCouplingMatrix Q = 1 := by
  classical
  ext c d
  have hc := coupledIndex_bounds c
  have hd := coupledIndex_bounds d
  have h := coupledVector_gram hc.1 hc.2.1 hd.1 hd.2.1 hc.2.2 hd.2.2
  rw [gridInner_eq_fin_sum] at h
  rw [show 2*Q-2+1 = 2*Q-1 by omega] at h
  have he : (c.1.val=d.1.val ∧ c.2.val=d.2.val) ↔ c=d := by
    constructor
    · intro ⟨hz, hk⟩
      rcases c with ⟨z, k⟩
      rcases d with ⟨r, l⟩
      have hr : z=r := Fin.ext hz
      subst r
      have hl : k=l := Fin.ext hk
      subst l
      rfl
    · rintro rfl
      exact ⟨rfl, rfl⟩
  simp only [he] at h
  have h' := congrArg (fun t : ℝ => (t : ℂ)) h
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    threeCouplingMatrix, threeCoupledColumn, Complex.star_def, Complex.conj_ofReal,
    Fintype.sum_prod_type, Matrix.one_apply, Complex.ofReal_sum,
    Complex.ofReal_mul, apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using h'

 

theorem threeCouplingMatrix_complete (Q : ℕ) (hQ : 1 ≤ Q) :
    threeCouplingMatrix Q * (threeCouplingMatrix Q)ᴴ = 1 := by
  classical
  ext pj rk
  have hdim : 2*Q-1 = 2*Q-2+1 := by omega
  let pq : Fin (2*Q-2+1) × Fin (Q+1) := (Fin.cast hdim pj.1, pj.2)
  let rs : Fin (2*Q-2+1) × Fin (Q+1) := (Fin.cast hdim rk.1, rk.2)
  have h := congrArg (fun t : ℝ => (t : ℂ)) (coupledVector_resolution (2*Q-2) Q pq rs)
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    threeCouplingMatrix, threeCoupledColumn, Complex.star_def, Complex.conj_ofReal,
    Matrix.one_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    pq, rs, Fin.val_cast, Prod.mk.injEq, Fin.cast_inj, ← Prod.ext_iff,
    apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using h

 
theorem threeWedgeMatrix_gram_diagonal (Q : ℕ) (hQ : 2 ≤ Q) :
    (threeWedgeMatrix Q)ᴴ * threeWedgeMatrix Q - 1 =
      threeCouplingMatrix Q *
        Matrix.diagonal (fun c : CoupledIndex (2*Q-2) Q => (gramShift Q c.1.val : ℂ)) *
          (threeCouplingMatrix Q)ᴴ := by
  classical
  have he : ((threeWedgeMatrix Q)ᴴ * threeWedgeMatrix Q) * threeCouplingMatrix Q =
      threeCouplingMatrix Q * Matrix.diagonal
        (fun c : CoupledIndex (2*Q-2) Q => (1+gramShift Q c.1.val : ℂ)) := by
    ext pj c
    rw [Matrix.mul_diagonal]
    change (((threeWedgeMatrix Q)ᴴ * threeWedgeMatrix Q) *ᵥ
      threeCoupledColumn Q c.1.val c.2.val) pj =
        threeCoupledColumn Q c.1.val c.2.val pj * (1+gramShift Q c.1.val : ℂ)
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using
      congrArg (fun v => v pj)
        (threeWedgeMatrix_gram_eigenvector hQ (coupledIndex_bounds c).2.1 c.2.val)
  have he' := congrArg (fun M => M * (threeCouplingMatrix Q)ᴴ) he
  rw [Matrix.mul_assoc, threeCouplingMatrix_complete Q (by omega), Matrix.mul_one] at he'
  rw [he']
  have hsum : Matrix.diagonal (fun c : CoupledIndex (2*Q-2) Q => (1+gramShift Q c.1.val : ℂ)) =
      1 + Matrix.diagonal (fun c : CoupledIndex (2*Q-2) Q => (gramShift Q c.1.val : ℂ)) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_add]
  rw [hsum, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    threeCouplingMatrix_complete Q (by omega)]
  abel

 

def threeSpinProjection (Q z : ℕ) : Matrix (PairLabel Q × Orbital Q) (PairLabel Q × Orbital Q) ℂ :=
  threeCouplingMatrix Q * Matrix.diagonal
    (fun c : CoupledIndex (2*Q-2) Q => if c.1.val=z then (1:ℂ) else 0) * (threeCouplingMatrix Q)ᴴ

 
theorem threeSpinProjection_posSemidef (Q z : ℕ) : (threeSpinProjection Q z).PosSemidef := by
  classical
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro c
  split_ifs <;> norm_num

 
theorem threeSpinProjection_mul (Q z w : ℕ) (hQ : 1 ≤ Q) :
    threeSpinProjection Q z * threeSpinProjection Q w =
      if z=w then threeSpinProjection Q z else 0 := by
  classical
  unfold threeSpinProjection
  have hd : Matrix.diagonal (fun c : CoupledIndex (2*Q-2) Q => if c.1.val=z then (1:ℂ) else 0) *
      Matrix.diagonal (fun c : CoupledIndex (2*Q-2) Q => if c.1.val=w then (1:ℂ) else 0) =
        if z=w then Matrix.diagonal (fun c : CoupledIndex (2*Q-2) Q => if c.1.val=z then (1:ℂ) else 0) else 0 := by
    rw [Matrix.diagonal_mul_diagonal]
    split_ifs with hzw
    · subst w
      congr 1
      funext c
      split_ifs <;> norm_num
    · ext c d
      rw [Matrix.diagonal_apply]
      split_ifs <;> simp_all
  calc
    _ = threeCouplingMatrix Q *
        (Matrix.diagonal (fun c : CoupledIndex (2*Q-2) Q => if c.1.val=z then (1:ℂ) else 0) *
          ((threeCouplingMatrix Q)ᴴ * threeCouplingMatrix Q) *
            Matrix.diagonal (fun c : CoupledIndex (2*Q-2) Q => if c.1.val=w then (1:ℂ) else 0)) *
              (threeCouplingMatrix Q)ᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [threeCouplingMatrix_gram Q hQ, Matrix.mul_one, hd]
      split_ifs <;> simp

 

theorem threeWedgeMatrix_gram_spectral (Q : ℕ) (hQ : 2 ≤ Q) :
    (threeWedgeMatrix Q)ᴴ * threeWedgeMatrix Q - 1 =
      ∑ z ∈ Finset.range (Q+1), (gramShift Q z : ℂ) • threeSpinProjection Q z := by
  classical
  rw [threeWedgeMatrix_gram_diagonal Q hQ]
  have hd : Matrix.diagonal (fun c : CoupledIndex (2*Q-2) Q => (gramShift Q c.1.val : ℂ)) =
      ∑ z ∈ Finset.range (Q+1), (gramShift Q z : ℂ) •
        Matrix.diagonal (fun c : CoupledIndex (2*Q-2) Q => if c.1.val=z then (1:ℂ) else 0) := by
    ext c d
    simp only [Matrix.diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases h : c=d
    · subst d
      simp only [ite_true, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr (by have := coupledIndex_bounds c; omega))]
    · simp [h]
  rw [hd]
  simp only [threeSpinProjection, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

end LaughlinFock
end

end OAI
