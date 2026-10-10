import Mathlib
import OAI.Analysis.LaughlinFock.FermionOperators
import OAI.Analysis.LaughlinFock.SphereScaling

namespace OAI

/-! Local Energy. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
open Filter Topology
theorem coefficientPairAnnihilator_smul (L : ℕ) (r : ℂ)
    (a : Orbital L → Orbital L → ℂ) :
    coefficientPairAnnihilator L (fun i j => r * a i j) =
      r • coefficientPairAnnihilator L a := by
  classical
  unfold coefficientPairAnnihilator
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [smul_smul]

 
def localPairAnnihilator (L Q p : ℕ) : FockMatrix L :=
  coefficientPairAnnihilator L
    (fun i j => (sphericalPairCoefficient Q p i.val j.val : ℂ))

 
def limitPairAnnihilator (L p : ℕ) : FockMatrix L :=
  coefficientPairAnnihilator L (fun i j => (limitPairCoefficient p i.val j.val : ℂ))

def localDelta (L Q : ℕ) : FockMatrix L :=
  occupationDiagonal L (fun j => (modeScale Q j.val : ℂ))

def localDeltaInv (L Q : ℕ) : FockMatrix L :=
  occupationDiagonalInv L (fun j => (modeScale Q j.val : ℂ))

theorem localDelta_factor_ne_zero {L Q : ℕ} (hQ : 0 < Q) (hL : L ≤ Q)
    (j : Orbital L) : (modeScale Q j.val : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (modeScale_pos hQ (j.is_le.trans hL))

theorem localDelta_inv_mul {L Q : ℕ} (hQ : 0 < Q) (hL : L ≤ Q) :
    localDeltaInv L Q * localDelta L Q = 1 :=
  occupationDiagonal_inv_mul L _ (localDelta_factor_ne_zero hQ hL)

theorem localDelta_mul_inv {L Q : ℕ} (hQ : 0 < Q) (hL : L ≤ Q) :
    localDelta L Q * localDeltaInv L Q = 1 :=
  occupationDiagonal_mul_inv L _ (localDelta_factor_ne_zero hQ hL)

 
theorem localPair_conjugation {L Q p : ℕ} (hQ : 0 < Q) (hL : L ≤ Q)
    (hp : p ≤ 2*Q-2) :
    localPairAnnihilator L Q p = (pairScale Q p : ℂ) •
      (localDeltaInv L Q * limitPairAnnihilator L p * localDelta L Q) := by
  change localPairAnnihilator L Q p = (pairScale Q p : ℂ) •
    diagonalConjugate L (fun j => (modeScale Q j.val : ℂ)) (limitPairAnnihilator L p)
  rw [limitPairAnnihilator, diagonalConjugate_pair L _
    (localDelta_factor_ne_zero hQ hL), ← coefficientPairAnnihilator_smul]
  unfold localPairAnnihilator
  congr 1
  funext i j
  rw [sphericalPairCoefficient_factorization hQ hp]
  push_cast
  ring

 
theorem localFour_conjugation {L Q p : ℕ} (hQ : 0 < Q) (hL : L ≤ Q)
    (hp : p ≤ 2*Q-2) (j k : Orbital L) :
    annihilator L k * annihilator L j * localPairAnnihilator L Q p =
      ((pairScale Q p : ℂ) / ((modeScale Q j.val : ℂ) * modeScale Q k.val)) •
        (localDeltaInv L Q *
          (annihilator L k * annihilator L j * limitPairAnnihilator L p) *
          localDelta L Q) := by
  let d : Orbital L → ℂ := fun j => modeScale Q j.val
  have hd : ∀ j, d j ≠ 0 := localDelta_factor_ne_zero hQ hL
  change _ = ((pairScale Q p : ℂ) / (d j * d k)) •
    diagonalConjugate L d (annihilator L k * annihilator L j * limitPairAnnihilator L p)
  rw [diagonalConjugate_mul L d hd, diagonalConjugate_mul L d hd,
    diagonalConjugate_annihilator L d hd, diagonalConjugate_annihilator L d hd]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [localPair_conjugation hQ hL hp, Matrix.mul_smul]
  congr 1
  field_simp [hd j, hd k]

 

theorem localDelta_tendsto (L : ℕ) :
    Tendsto (fun Q : ℕ => localDelta L Q) atTop (𝓝 1) := by
  classical
  apply tendsto_pi_nhds.mpr
  intro A
  apply tendsto_pi_nhds.mpr
  intro B
  dsimp only [localDelta, occupationDiagonal]
  by_cases h : A=B
  · subst B
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    have ht := tendsto_finsetProd A (fun j _ =>
      Complex.continuous_ofReal.continuousAt.tendsto.comp (modeScale_tendsto j.val))
    simpa using ht
  · simp only [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    exact tendsto_const_nhds

theorem localDeltaInv_tendsto (L : ℕ) :
    Tendsto (fun Q : ℕ => localDeltaInv L Q) atTop (𝓝 1) := by
  classical
  apply tendsto_pi_nhds.mpr
  intro A
  apply tendsto_pi_nhds.mpr
  intro B
  dsimp only [localDeltaInv, occupationDiagonalInv]
  by_cases h : A=B
  · subst B
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    have ht : Tendsto (fun Q : ℕ => ∏ j ∈ A, (modeScale Q j.val : ℂ)) atTop (𝓝 1) := by
      have ht := tendsto_finsetProd A (fun j _ =>
        Complex.continuous_ofReal.continuousAt.tendsto.comp (modeScale_tendsto j.val))
      simpa using ht
    simpa only [inv_one] using ht.inv₀ (by norm_num : (1:ℂ) ≠ 0)
  · simp only [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    exact tendsto_const_nhds

theorem localDelta_posSemidef (L Q : ℕ) : (localDelta L Q).PosSemidef := by
  classical
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro A
  rw [← Complex.ofReal_prod]
  exact_mod_cast Finset.prod_nonneg (fun j (_ : j ∈ A) => modeScale_nonneg Q j.val)

theorem localDelta_le_identity {L Q : ℕ} (hQ : 0 < Q) :
    (1-localDelta L Q).PosSemidef := by
  classical
  rw [localDelta, occupationDiagonal, ← Matrix.diagonal_one, Matrix.diagonal_sub]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro A
  rw [← Complex.ofReal_one, ← Complex.ofReal_prod, ← Complex.ofReal_sub]
  exact_mod_cast sub_nonneg.mpr (Finset.prod_le_one₀
    (fun j (_ : j ∈ A) => modeScale_nonneg Q j.val) (fun j _ => modeScale_le_one hQ j.val))

theorem localDelta_contraction {L Q : ℕ} (hQ : 0 < Q) :
    (1 - (localDelta L Q)ᴴ * localDelta L Q).PosSemidef := by
  classical
  rw [(localDelta_posSemidef L Q).isHermitian.eq]
  rw [localDelta, occupationDiagonal, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one, Matrix.diagonal_sub]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro A
  rw [← Complex.ofReal_one, ← Complex.ofReal_prod, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub]
  have h0 := Finset.prod_nonneg (fun j (_ : j ∈ A) => modeScale_nonneg Q j.val)
  have h1 := Finset.prod_le_one₀ (fun j (_ : j ∈ A) => modeScale_nonneg Q j.val)
    (fun j _ => modeScale_le_one hQ j.val)
  have hs : (∏ j ∈ A, modeScale Q j.val) * (∏ j ∈ A, modeScale Q j.val) ≤ (1:ℝ) := by
    simpa only [mul_one] using mul_self_le_mul_self h0 h1
  exact_mod_cast sub_nonneg.mpr hs

 
theorem gram_bound_of_scaled_contraction {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (D : Matrix ι ι ℂ) (B C : Matrix ι κ ℂ) (r : ℝ)
    (hD : (1 - Dᴴ * D).PosSemidef) (hr : 1 ≤ r)
    (hDB : D * B = (r:ℂ) • C) : (Bᴴ * B - Cᴴ * C).PosSemidef := by
  classical
  have hgram : Bᴴ * (Dᴴ * D) * B = (r:ℂ)^2 • (Cᴴ * C) := by
    calc
      _ = (D * B)ᴴ * (D * B) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by
        rw [hDB]
        simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
          Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two]
  have hs : (0:ℝ) ≤ r^2-1 := by nlinarith
  have hs' : (0:ℂ) ≤ (r:ℂ)^2-1 := by exact_mod_cast hs
  have h := (hD.conjTranspose_mul_mul_same B).add
    ((Matrix.posSemidef_conjTranspose_mul_self C).smul hs')
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hgram] at h
  convert h using 1
  simp only [sub_smul, one_smul]
  abel

 
def localHamiltonian (L P Q : ℕ) : FockMatrix L :=
  ∑ p ∈ Finset.range P, (localPairAnnihilator L Q p)ᴴ * localPairAnnihilator L Q p

def limitHamiltonian (L P : ℕ) : FockMatrix L :=
  ∑ p ∈ Finset.range P, (limitPairAnnihilator L p)ᴴ * limitPairAnnihilator L p

theorem localPair_energy_transfer {L Q p : ℕ} (hQ : 0 < Q) (hL : L ≤ Q)
    (hp : p ≤ 2*Q-2) :
    ((localPairAnnihilator L Q p)ᴴ * localPairAnnihilator L Q p -
      localDelta L Q * ((limitPairAnnihilator L p)ᴴ * limitPairAnnihilator L p) *
        localDelta L Q).PosSemidef := by
  classical
  have hDB : localDelta L Q * localPairAnnihilator L Q p =
      (pairScale Q p : ℂ) • (limitPairAnnihilator L p * localDelta L Q) := by
    rw [localPair_conjugation hQ hL hp, Matrix.mul_smul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, localDelta_mul_inv hQ hL,
      Matrix.one_mul]
  have h := gram_bound_of_scaled_contraction (localDelta L Q)
    (localPairAnnihilator L Q p) (limitPairAnnihilator L p * localDelta L Q)
    (pairScale Q p) (localDelta_contraction hQ) (pairScale_one_le hQ hp) hDB
  simpa only [Matrix.conjTranspose_mul, (localDelta_posSemidef L Q).isHermitian.eq,
    Matrix.mul_assoc] using h

 
theorem localHamiltonian_energy_transfer {L P Q : ℕ} (hQ : 0 < Q) (hL : L ≤ Q)
    (hP : P ≤ 2*Q-1) :
    (localHamiltonian L P Q -
      localDelta L Q * limitHamiltonian L P * localDelta L Q).PosSemidef := by
  classical
  unfold localHamiltonian limitHamiltonian
  rw [Matrix.mul_sum, Matrix.sum_mul, ← Finset.sum_sub_distrib]
  apply Matrix.posSemidef_sum
  intro p hp
  exact localPair_energy_transfer hQ hL (by have := Finset.mem_range.mp hp; omega)

 
theorem star_dotProduct_self {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    star x ⬝ᵥ x = ((∑ i, ‖x i‖^2 : ℝ) : ℂ) := by
  simp [dotProduct, RCLike.star_def, RCLike.conj_mul, ← Complex.ofReal_pow,
    Complex.ofReal_sum]

theorem row_isometry_gram_complement {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (S : Matrix ι κ ℂ) (hS : S * Sᴴ = 1) :
    (1 - Sᴴ * S).PosSemidef := by
  have hsq : (Sᴴ * S) * (Sᴴ * S) = Sᴴ * S := by
    calc
      _ = Sᴴ * (S * Sᴴ) * S := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hS, Matrix.mul_one]
  have heq : (1-Sᴴ*S)ᴴ * (1-Sᴴ*S) = 1-Sᴴ*S := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      (Matrix.isHermitian_conjTranspose_mul_self S).eq]
    calc
      _ = 1 - Sᴴ*S - Sᴴ*S + (Sᴴ*S)*(Sᴴ*S) := by noncomm_ring
      _ = _ := by rw [hsq]; abel
  rw [← heq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

 
theorem row_isometry_contracts {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (S : Matrix ι κ ℂ) (hS : S * Sᴴ = 1)
    (x : κ → ℂ) :
    (∑ i, ‖(S *ᵥ x) i‖^2) ≤ ∑ j, ‖x j‖^2 := by
  have h := Complex.re_le_re ((row_isometry_gram_complement S hS).dotProduct_mulVec_nonneg x)
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, gram_quadratic_form,
    star_dotProduct_self, star_dotProduct_self, Complex.sub_re] at h
  simpa only [Complex.ofReal_re, Complex.zero_re, sub_nonneg] using h

 

theorem row_isometry_contracts_family {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [Fintype α] [DecidableEq ι] [DecidableEq κ]
    (S : Matrix ι κ ℂ) (hS : S * Sᴴ = 1) (x : κ → α → ℂ) :
    (∑ i, ∑ a, ‖(∑ j, S i j * x j a)‖^2) ≤ ∑ j, ∑ a, ‖x j a‖^2 := by
  rw [Finset.sum_comm, Finset.sum_comm (f := fun j a => ‖x j a‖^2)]
  exact Finset.sum_le_sum fun a _ => row_isometry_contracts S hS (fun j => x j a)

 
theorem twoAnnihilators_contract (L : ℕ) (j k : Orbital L) (B : FockMatrix L)
    (ψ : Occupation L → ℂ) :
    (∑ A, ‖((annihilator L k * annihilator L j * B) *ᵥ ψ) A‖^2) ≤
      ∑ A, ‖(B *ᵥ ψ) A‖^2 := by
  have hk := annihilator_contracts L k (annihilator L j *ᵥ (B *ᵥ ψ))
  have hj := annihilator_contracts L j (B *ᵥ ψ)
  simpa only [← Matrix.mulVec_mulVec] using hk.trans hj

theorem limitHamiltonian_quadratic_form (L P : ℕ) (ψ : Occupation L → ℂ) :
    (star ψ ⬝ᵥ (limitHamiltonian L P *ᵥ ψ)).re =
      ∑ p ∈ Finset.range P, ∑ A, ‖(limitPairAnnihilator L p *ᵥ ψ) A‖^2 := by
  classical
  simp only [limitHamiltonian, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum,
    gram_quadratic_form, star_dotProduct_self, Complex.ofReal_re]

 

theorem finite_annihilator_family_bound {β : Type*} [Fintype β]
    (L P : ℕ) (p : β → ℕ) (j k : β → Orbital L) (hp : ∀ b, p b < P)
    (ψ : Occupation L → ℂ) :
    (∑ b, ∑ A,
      ‖((annihilator L (k b) * annihilator L (j b) * limitPairAnnihilator L (p b)) *ᵥ ψ) A‖^2)
    ≤ (Fintype.card β : ℝ) * (star ψ ⬝ᵥ (limitHamiltonian L P *ᵥ ψ)).re := by
  classical
  rw [limitHamiltonian_quadratic_form]
  calc
    _ ≤ ∑ b : β, ∑ q ∈ Finset.range P, ∑ A, ‖(limitPairAnnihilator L q *ᵥ ψ) A‖^2 := by
      apply Finset.sum_le_sum
      intro b _
      refine (twoAnnihilators_contract L (j b) (k b) _ ψ).trans ?_
      exact Finset.single_le_sum
        (f := fun q => ∑ A : Occupation L, ‖(limitPairAnnihilator L q *ᵥ ψ) A‖^2)
        (fun q _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        (Finset.mem_range.mpr (hp b))
    _ = _ := by simp

 

def entryNormBound {ι κ : Type*} [Fintype ι] [Fintype κ] (R : Matrix ι κ ℂ) : ℝ :=
  ∑ i, ∑ j, ‖R i j‖

theorem entryNormBound_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : Matrix ι κ ℂ) : 0 ≤ entryNormBound R :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

theorem entryNormBound_quadratic_form {ι : Type*} [Fintype ι]
    (R : Matrix ι ι ℂ) (x : ι → ℂ) :
    |(star x ⬝ᵥ (R *ᵥ x)).re| ≤ entryNormBound R * ∑ i, ‖x i‖^2 := by
  classical
  have hp (i j : ι) : ‖x i‖ * ‖x j‖ ≤ ∑ k, ‖x k‖^2 := by
    have hi := Finset.single_le_sum (f := fun k : ι => ‖x k‖^2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    have hj := Finset.single_le_sum (f := fun k : ι => ‖x k‖^2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    nlinarith [sq_nonneg (‖x i‖-‖x j‖)]
  refine (Complex.abs_re_le_norm _).trans ?_
  calc
    ‖star x ⬝ᵥ (R *ᵥ x)‖ = ‖∑ i, ∑ j, star (x i) * (R i j * x j)‖ := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, ‖R i j‖ * ∑ k, ‖x k‖^2 := by
      apply norm_sum_le_of_le
      intro i _
      apply norm_sum_le_of_le
      intro j _
      calc
        _ = ‖R i j‖ * (‖x i‖ * ‖x j‖) := by simp only [norm_mul, norm_star]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hp i j) (norm_nonneg _)
    _ = _ := by simp only [entryNormBound, Finset.sum_mul]

 

theorem entryNormBound_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℂ) (hR : R.IsHermitian) :
    (R + entryNormBound R • 1).PosSemidef := by
  have hH : (R + entryNormBound R • 1).IsHermitian :=
    hR.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro x
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hH.im_star_dotProduct_mulVec_self x).symm⟩
  have h := (abs_le.mp (entryNormBound_quadratic_form R x)).1
  simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, star_dotProduct_self, Complex.add_re, Complex.smul_re,
    Complex.ofReal_re, smul_eq_mul]
  linarith

open Filter Topology

theorem entryNormBound_tendsto_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    {R : ℕ → Matrix ι κ ℂ} (hR : Tendsto R atTop (𝓝 0)) :
    Tendsto (fun Q => entryNormBound (R Q)) atTop (𝓝 0) := by
  have ht : ∀ i j, Tendsto (fun Q => ‖R Q i j‖) atTop (𝓝 0) := by
    intro i j
    simpa only [Matrix.zero_apply, norm_zero] using
      ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hR i) j).norm)
  have h := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ => ht i j))
  simpa only [entryNormBound, Finset.sum_const_zero] using h

 

theorem relative_compression_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix κ ι ℂ) (D : Matrix ι ι ℂ)
    (hD : D.IsHermitian) (M R : Matrix κ κ ℂ) (hR : R.IsHermitian)
    (Hstar HQ : Matrix ι ι ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hLimit : (Aᴴ * M * A).PosSemidef)
    (hMajorant : (C • Hstar - Aᴴ * A).PosSemidef)
    (hEnergy : (HQ - D * Hstar * D).PosSemidef) :
    (D * (Aᴴ * (M + R) * A) * D +
      (C * entryNormBound R) • HQ).PosSemidef := by
  have h1 := (entryNormBound_lower_bound R hR).conjTranspose_mul_mul_same (A * D)
  have h2 := hLimit.conjTranspose_mul_mul_same D
  have h3 := (hMajorant.conjTranspose_mul_mul_same D).smul (entryNormBound_nonneg R)
  have h4 := hEnergy.smul (mul_nonneg hC (entryNormBound_nonneg R))
  convert ((h1.add h2).add h3).add h4 using 1
  simp only [Matrix.conjTranspose_mul, hD.eq, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.mul_assoc, smul_sub, smul_smul]
  rw [mul_comm (entryNormBound R) C]
  abel
end LaughlinFock
end

end OAI
