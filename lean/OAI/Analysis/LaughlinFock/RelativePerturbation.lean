import Mathlib
import OAI.Analysis.LaughlinFock.LocalEnergy

namespace OAI

/-! Relative Perturbation. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
open Filter Topology
open Filter Topology
open scoped Kronecker

 
def stackFamily {β ι κ : Type*} (A : β → Matrix ι κ ℂ) : Matrix (β × ι) κ ℂ :=
  fun b j => A b.1 b.2 j

@[simp]
theorem stackFamily_mulVec {β ι κ : Type*} [Fintype κ]
    (A : β → Matrix ι κ ℂ) (x : κ → ℂ) (b : β) (i : ι) :
    (stackFamily A *ᵥ x) (b,i) = (A b *ᵥ x) i := rfl

theorem stackFamily_gram {β ι κ : Type*} [Fintype β] [Fintype ι]
    (A : β → Matrix ι κ ℂ) : (stackFamily A)ᴴ * stackFamily A = ∑ b, (A b)ᴴ * A b := by
  ext i j
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    stackFamily, Matrix.sum_apply]

 
theorem stackFamily_kronecker {β ι κ : Type*} [Fintype β] [Fintype ι]
    (A : β → Matrix ι κ ℂ) (M : Matrix β β ℂ) (D : Matrix ι ι ℂ) :
    (stackFamily A)ᴴ * (M ⊗ₖ D) * stackFamily A =
      ∑ b, ∑ c, M b c • ((A b)ᴴ * D * A c) := by
  ext i j
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    stackFamily, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext c
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem isHermitian_kronecker {β ι : Type*} (M : Matrix β β ℂ) (D : Matrix ι ι ℂ)
    (hM : M.IsHermitian) (hD : D.IsHermitian) : (M ⊗ₖ D).IsHermitian := by
  change (M ⊗ₖ D)ᴴ = _
  rw [Matrix.conjTranspose_kronecker, hM.eq, hD.eq]

 
theorem family_gram_majorant {β : Type*} [Fintype β]
    (L P : ℕ) (p : β → ℕ) (j k : β → Orbital L) (hp : ∀ b, p b < P) :
    ((Fintype.card β : ℝ) • limitHamiltonian L P -
      (stackFamily (fun b => annihilator L (k b) * annihilator L (j b) *
        limitPairAnnihilator L (p b)))ᴴ *
      stackFamily (fun b => annihilator L (k b) * annihilator L (j b) *
        limitPairAnnihilator L (p b))).PosSemidef := by
  classical
  have hH : (limitHamiltonian L P).IsHermitian :=
    (Matrix.posSemidef_sum _ (fun p _ => Matrix.posSemidef_conjTranspose_mul_self _)).isHermitian
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((hH.smul (IsSelfAdjoint.all _)).sub (Matrix.isHermitian_conjTranspose_mul_self _))
  intro ψ
  have h := finite_annihilator_family_bound L P p j k hp ψ
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
    gram_quadratic_form, star_dotProduct_self, Fintype.sum_prod_type]
  apply Complex.nonneg_iff.mpr
  constructor
  · simpa only [Complex.sub_re, Complex.smul_re, Complex.ofReal_re, smul_eq_mul,
      stackFamily_mulVec, sub_nonneg] using h
  · simp only [Complex.sub_im, Complex.smul_im, Complex.ofReal_im, smul_eq_mul,
]
    have him : (star ψ ⬝ᵥ (limitHamiltonian L P *ᵥ ψ)).im = 0 :=
      hH.im_star_dotProduct_mulVec_self ψ
    rw [him, mul_zero, sub_self]

 

def localBlockError {β : Type*} [Fintype β] (L Q : ℕ)
    (M Mstar : Matrix β β ℂ) : Matrix (β × Occupation L) (β × Occupation L) ℂ :=
  M ⊗ₖ ((localDeltaInv L Q)ᴴ * localDeltaInv L Q) - Mstar ⊗ₖ 1

theorem localBlockError_hermitian {β : Type*} [Fintype β] (L Q : ℕ)
    (M Mstar : Matrix β β ℂ) (hM : M.IsHermitian) (hS : Mstar.IsHermitian) :
    (localBlockError L Q M Mstar).IsHermitian :=
  (isHermitian_kronecker _ _ hM (Matrix.isHermitian_conjTranspose_mul_self _)).sub
    (isHermitian_kronecker _ _ hS Matrix.isHermitian_one)

theorem localBlockError_tendsto {β : Type*} [Fintype β] (L : ℕ)
    (M : ℕ → Matrix β β ℂ) (Mstar : Matrix β β ℂ)
    (hM : Tendsto M atTop (𝓝 Mstar)) :
    Tendsto (fun Q => localBlockError L Q (M Q) Mstar) atTop (𝓝 0) := by
  have hD : Tendsto (fun Q => (localDeltaInv L Q)ᴴ * localDeltaInv L Q)
      atTop (𝓝 1) := by
    have hc := ((continuous_id (X := FockMatrix L)).matrix_conjTranspose.tendsto 1).comp
      (localDeltaInv_tendsto L)
    simpa using hc.mul (localDeltaInv_tendsto L)
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_pi_nhds.mpr
  intro b
  have hm := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hM a.1) b.1
  have hd := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hD a.2) b.2
  simpa only [localBlockError, Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.zero_apply,
    sub_self] using (hm.mul hd).sub_const (Mstar a.1 b.1 * (1 : FockMatrix L) a.2 b.2)

 

theorem local_relative_error {β : Type*} [Fintype β]
    (L P : ℕ) (p : β → ℕ) (j k : β → Orbital L) (hp : ∀ b, p b < P)
    (M : ℕ → Matrix β β ℂ) (Mstar : Matrix β β ℂ)
    (hMH : ∀ Q, (M Q).IsHermitian) (hSH : Mstar.IsHermitian)
    (hM : Tendsto M atTop (𝓝 Mstar))
    (hLimit : (∑ b, ∑ c, Mstar b c •
      ((annihilator L (k b) * annihilator L (j b) * limitPairAnnihilator L (p b))ᴴ *
        (annihilator L (k c) * annihilator L (j c) * limitPairAnnihilator L (p c)))).PosSemidef) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Tendsto ρ atTop (𝓝 0) ∧
      ∀ Q, 0 < Q → L ≤ Q → P ≤ 2*Q-1 →
      (localDelta L Q *
        (∑ b, ∑ c, (M Q) b c •
          ((annihilator L (k b) * annihilator L (j b) * limitPairAnnihilator L (p b))ᴴ *
            ((localDeltaInv L Q)ᴴ * localDeltaInv L Q) *
            (annihilator L (k c) * annihilator L (j c) * limitPairAnnihilator L (p c)))) *
          localDelta L Q + ρ Q • localHamiltonian L P Q).PosSemidef := by
  classical
  let A : β → FockMatrix L := fun b =>
    annihilator L (k b) * annihilator L (j b) * limitPairAnnihilator L (p b)
  let C : ℝ := Fintype.card β
  let ρ : ℕ → ℝ := fun Q => C * entryNormBound (localBlockError L Q (M Q) Mstar)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  refine ⟨ρ, (fun Q => mul_nonneg hC (entryNormBound_nonneg _)), ?_, ?_⟩
  · simpa only [mul_zero] using
      (entryNormBound_tendsto_zero (localBlockError_tendsto L M Mstar hM)).const_mul C
  · intro Q hQ hL hP
    have hLim : ((stackFamily A)ᴴ * (Mstar ⊗ₖ (1 : FockMatrix L)) * stackFamily A).PosSemidef := by
      simpa only [stackFamily_kronecker, Matrix.mul_one] using hLimit
    have h := relative_compression_bound (stackFamily A) (localDelta L Q)
      (localDelta_posSemidef L Q).isHermitian (Mstar ⊗ₖ (1 : FockMatrix L))
      (localBlockError L Q (M Q) Mstar)
      (localBlockError_hermitian L Q _ _ (hMH Q) hSH)
      (limitHamiltonian L P) (localHamiltonian L P Q) C hC hLim
      (family_gram_majorant L P p j k hp)
      (localHamiltonian_energy_transfer hQ hL hP)
    have heq : (Mstar ⊗ₖ (1 : FockMatrix L)) + localBlockError L Q (M Q) Mstar =
        (M Q) ⊗ₖ ((localDeltaInv L Q)ᴴ * localDeltaInv L Q) := by
      unfold localBlockError
      abel
    rw [heq, stackFamily_kronecker] at h
    exact h

 

theorem stackFamily_coupled {α β ι κ : Type*} [Fintype β] [Fintype ι]
    (A : β → Matrix ι κ ℂ) (S : Matrix α β ℂ) (D : Matrix ι ι ℂ) :
    stackFamily (fun r => D * (∑ b, S r b • A b)) = (S ⊗ₖ D) * stackFamily A := by
  ext ⟨r,i⟩ j
  simp only [stackFamily, Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem stackFamily_mul {β ι κ ν : Type*} [Fintype κ]
    (A : β → Matrix ι κ ℂ) (D : Matrix κ ν ℂ) :
    stackFamily (fun r => A r * D) = stackFamily A * D := rfl

 

theorem quadratic_family_change {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    [DecidableEq ι] (A : β → Matrix ι ι ℂ) (S : Matrix α β ℂ) (C : Matrix α α ℂ)
    (D J : Matrix ι ι ℂ) (hD : D.IsHermitian) :
    (∑ r, ∑ s, C r s •
      ((J * (∑ b, S r b • A b) * D)ᴴ * (J * (∑ b, S s b • A b) * D))) =
    D * (∑ b, ∑ c, (Sᴴ * C * S) b c • (A b)ᴴ * (Jᴴ * J) * A c) * D := by
  let B : α → Matrix ι ι ℂ := fun r => J * (∑ b, S r b • A b) * D
  have hB : stackFamily B = (S ⊗ₖ J) * stackFamily A * D := by
    rw [show B = (fun r => (J * (∑ b, S r b • A b)) * D) from rfl,
      stackFamily_mul, stackFamily_coupled]
  have heq : (S ⊗ₖ J)ᴴ * (C ⊗ₖ (1 : Matrix ι ι ℂ)) * (S ⊗ₖ J) =
      (Sᴴ * C * S) ⊗ₖ (Jᴴ * J) := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  calc
    _ = (stackFamily B)ᴴ * (C ⊗ₖ (1 : Matrix ι ι ℂ)) * stackFamily B := by
      simp only [stackFamily_kronecker, Matrix.mul_one, B]
    _ = D * ((stackFamily A)ᴴ * ((S ⊗ₖ J)ᴴ * (C ⊗ₖ (1 : Matrix ι ι ℂ)) *
        (S ⊗ₖ J)) * stackFamily A) * D := by
      rw [hB]
      simp only [Matrix.conjTranspose_mul, hD.eq, Matrix.mul_assoc]
    _ = _ := by
      rw [heq, stackFamily_kronecker]
      simp only [Matrix.smul_mul]

 
theorem tendsto_matrix_mul {α β ι : Type*} [Fintype β]
    {A : ℕ → Matrix α β ℂ} {B : ℕ → Matrix β ι ℂ}
    {Astar : Matrix α β ℂ} {Bstar : Matrix β ι ℂ}
    (hA : Tendsto A atTop (𝓝 Astar)) (hB : Tendsto B atTop (𝓝 Bstar)) :
    Tendsto (fun Q => A Q * B Q) atTop (𝓝 (Astar * Bstar)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact tendsto_finsetSum Finset.univ (fun b _ =>
    (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hA i) b).mul
      (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hB b) j))

theorem tendsto_matrix_adjoint {α β : Type*} {A : ℕ → Matrix α β ℂ}
    {Astar : Matrix α β ℂ} (hA : Tendsto A atTop (𝓝 Astar)) :
    Tendsto (fun Q => (A Q)ᴴ) atTop (𝓝 Astarᴴ) := by
  apply tendsto_pi_nhds.mpr
  intro j
  apply tendsto_pi_nhds.mpr
  intro i
  exact (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hA i) j).star

theorem hermitian_congruence {α β : Type*} [Fintype α] (S : Matrix α β ℂ)
    (C : Matrix α α ℂ) (hC : C.IsHermitian) : (Sᴴ * C * S).IsHermitian := by
  change (Sᴴ * C * S)ᴴ = _
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hC.eq,
    Matrix.mul_assoc]

 

theorem quadratic_family_mix {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    [DecidableEq ι] (A : β → Matrix ι ι ℂ) (S : Matrix α β ℂ) (C : Matrix α α ℂ) :
    (∑ r, ∑ s, C r s • ((∑ b, S r b • A b)ᴴ * (∑ b, S s b • A b))) =
      ∑ b, ∑ c, (Sᴴ * C * S) b c • ((A b)ᴴ * A c) := by
  simpa only [Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one, Matrix.smul_mul]
    using quadratic_family_change A S C 1 1 Matrix.isHermitian_one

 
def localFourScale (Q p j k : ℕ) : ℝ :=
  pairScale Q p / (modeScale Q j * modeScale Q k)

theorem localFourScale_tendsto (p j k : ℕ) :
    Tendsto (fun Q => localFourScale Q p j k) atTop (𝓝 1) := by
  simpa only [localFourScale, Pi.div_def, mul_one, div_one] using
    (pairScale_tendsto p).div ((modeScale_tendsto j).mul (modeScale_tendsto k)) (by norm_num)

 

theorem local_transfer_of_limitpositive {α β : Type*} [Fintype α] [Fintype β]
    (L P : ℕ) (p : β → ℕ) (j k : β → Orbital L) (hp : ∀ b, p b < P)
    (S : ℕ → Matrix α β ℂ) (Sstar : Matrix α β ℂ)
    (C : ℕ → Matrix α α ℂ) (Cstar : Matrix α α ℂ)
    (hS : Tendsto S atTop (𝓝 Sstar)) (hC : Tendsto C atTop (𝓝 Cstar))
    (hCH : ∀ Q, (C Q).IsHermitian) (hCSH : Cstar.IsHermitian)
    (hLimit : (∑ r, ∑ s, Cstar r s •
      ((∑ b, Sstar r b • (annihilator L (k b) * annihilator L (j b) *
        limitPairAnnihilator L (p b)))ᴴ *
       (∑ b, Sstar s b • (annihilator L (k b) * annihilator L (j b) *
        limitPairAnnihilator L (p b))))).PosSemidef) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Tendsto ρ atTop (𝓝 0) ∧
      ∀ Q, 0 < Q → L ≤ Q → P ≤ 2*Q-1 →
      ((∑ r, ∑ s, (C Q) r s •
        ((∑ b, (S Q) r b • (annihilator L (k b) * annihilator L (j b) *
          localPairAnnihilator L Q (p b)))ᴴ *
         (∑ b, (S Q) s b • (annihilator L (k b) * annihilator L (j b) *
          localPairAnnihilator L Q (p b))))) + ρ Q • localHamiltonian L P Q).PosSemidef := by
  classical
  let A : β → FockMatrix L := fun b =>
    annihilator L (k b) * annihilator L (j b) * limitPairAnnihilator L (p b)
  let B : ℕ → Matrix α β ℂ := fun Q r b =>
    S Q r b * (localFourScale Q (p b) (j b).val (k b).val : ℂ)
  have hB : Tendsto B atTop (𝓝 Sstar) := by
    apply tendsto_pi_nhds.mpr
    intro r
    apply tendsto_pi_nhds.mpr
    intro b
    have hb := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (localFourScale_tendsto (p b) (j b).val (k b).val)
    simpa only [B, Function.comp_apply, Complex.ofReal_one, mul_one] using
      (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hS r) b).mul hb
  let M : ℕ → Matrix β β ℂ := fun Q => (B Q)ᴴ * C Q * B Q
  let Mstar : Matrix β β ℂ := Sstarᴴ * Cstar * Sstar
  have hM : Tendsto M atTop (𝓝 Mstar) :=
    tendsto_matrix_mul (tendsto_matrix_mul (tendsto_matrix_adjoint hB) hC) hB
  have hMH : ∀ Q, (M Q).IsHermitian := fun Q => hermitian_congruence _ _ (hCH Q)
  have hMS : Mstar.IsHermitian := hermitian_congruence _ _ hCSH
  rw [quadratic_family_mix] at hLimit
  obtain ⟨ρ, hρ0, hρlim, hρ⟩ := local_relative_error L P p j k hp M Mstar hMH hMS hM hLimit
  refine ⟨ρ, hρ0, hρlim, ?_⟩
  intro Q hQ hL hP
  have hb (r : α) :
      (∑ b, (S Q) r b • (annihilator L (k b) * annihilator L (j b) *
          localPairAnnihilator L Q (p b))) =
        localDeltaInv L Q * (∑ b, (B Q) r b • A b) * localDelta L Q := by
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    apply Finset.sum_congr rfl
    intro b _
    rw [localFour_conjugation hQ hL (by have := hp b; omega), smul_smul]
    simp only [B, A, localFourScale, Complex.ofReal_div, Complex.ofReal_mul]
  simp_rw [hb]
  rw [quadratic_family_change _ _ _ _ _ (localDelta_posSemidef L Q).isHermitian]
  simpa only [Matrix.smul_mul] using hρ Q hQ hL hP

 
def orbitalMerge (L R : ℕ) : Orbital L ⊕ Fin R ≃ Orbital (L+R) :=
  finSumFinEquiv.trans (finCongr (by omega))

def localOrbital (L R : ℕ) (j : Orbital L) : Orbital (L+R) :=
  orbitalMerge L R (Sum.inl j)

def spectatorOrbital (L R : ℕ) (j : Fin R) : Orbital (L+R) :=
  orbitalMerge L R (Sum.inr j)

@[simp] theorem localOrbital_val (L R : ℕ) (j : Orbital L) :
    (localOrbital L R j).val = j.val := rfl

@[simp] theorem spectatorOrbital_val (L R : ℕ) (j : Fin R) :
    (spectatorOrbital L R j).val = L+1+j.val := rfl

 

def occupationMerge (L R : ℕ) : Occupation L × Finset (Fin R) ≃ Occupation (L+R) :=
  Finset.sumEquiv.toEquiv.symm.trans (orbitalMerge L R).finsetCongr

theorem occupationMerge_apply (L R : ℕ) (A : Occupation L) (S : Finset (Fin R)) :
    occupationMerge L R (A,S) = (A.disjSum S).map (orbitalMerge L R).toEmbedding := rfl

@[simp] theorem localOrbital_mem_occupationMerge (L R : ℕ) (j : Orbital L)
    (A : Occupation L) (S : Finset (Fin R)) :
    localOrbital L R j ∈ occupationMerge L R (A,S) ↔ j ∈ A := by
  simp only [occupationMerge_apply, localOrbital,
    Finset.mem_map_equiv, Equiv.symm_apply_apply, Finset.inl_mem_disjSum]

theorem occupationMerge_erase (L R : ℕ) (j : Orbital L)
    (A : Occupation L) (S : Finset (Fin R)) :
    (occupationMerge L R (A,S)).erase (localOrbital L R j) =
      occupationMerge L R (A.erase j,S) := by
  rw [occupationMerge_apply, occupationMerge_apply, localOrbital]
  change ((A.disjSum S).map (orbitalMerge L R).toEmbedding).erase
    ((orbitalMerge L R).toEmbedding (Sum.inl j)) = _
  rw [← Finset.map_erase]
  congr 1
  ext x
  cases x <;> simp

 
theorem occupationMerge_lower_count (L R : ℕ) (j : Orbital L)
    (A : Occupation L) (S : Finset (Fin R)) :
    ((occupationMerge L R (A,S)).filter (fun x => x < localOrbital L R j)).card =
      (A.filter (fun x => x < j)).card := by
  rw [occupationMerge_apply, Finset.filter_map, Finset.card_map]
  have heq : (A.disjSum S).filter (fun x => orbitalMerge L R x < localOrbital L R j) =
      (A.filter (fun x => x < j)).disjSum (∅ : Finset (Fin R)) := by
    ext x
    cases x with
    | inl i => simp only [Finset.mem_filter, Finset.inl_mem_disjSum]; rfl
    | inr i =>
      have hn : ¬ orbitalMerge L R (Sum.inr i) < localOrbital L R j := by
        change ¬ L+1+i.val < j.val
        omega
      simp [hn]
  change ((A.disjSum S).filter
    (fun x => orbitalMerge L R x < localOrbital L R j)).card = _
  rw [heq, Finset.card_disjSum, Finset.card_empty, add_zero]

 

theorem annihilator_spectator_factorization (L R : ℕ) (j : Orbital L) :
    (annihilator (L+R) (localOrbital L R j)).submatrix
      (occupationMerge L R) (occupationMerge L R) =
        annihilator L j ⊗ₖ (1 : Matrix (Finset (Fin R)) (Finset (Fin R)) ℂ) := by
  ext ⟨A,S⟩ ⟨B,T⟩
  simp only [Matrix.submatrix_apply, annihilator, localOrbital_mem_occupationMerge,
    occupationMerge_erase, Equiv.apply_eq_iff_eq, Prod.mk.injEq,
    occupationMerge_lower_count, Matrix.kroneckerMap_apply, Matrix.one_apply]
  by_cases h : S=T <;> by_cases hB : j ∈ B ∧ A=B.erase j <;> simp_all

 
def spectatorExtension (L R : ℕ) (M : FockMatrix L) : FockMatrix (L+R) :=
  (M ⊗ₖ (1 : Matrix (Finset (Fin R)) (Finset (Fin R)) ℂ)).submatrix
    (occupationMerge L R).symm (occupationMerge L R).symm

theorem spectatorExtension_annihilator (L R : ℕ) (j : Orbital L) :
    spectatorExtension L R (annihilator L j) = annihilator (L+R) (localOrbital L R j) := by
  ext A B
  have h := congrArg (fun M => M ((occupationMerge L R).symm A) ((occupationMerge L R).symm B))
    (annihilator_spectator_factorization L R j)
  simpa only [spectatorExtension, Matrix.submatrix_apply, Equiv.apply_symm_apply] using h.symm

theorem spectatorExtension_mul (L R : ℕ) (A B : FockMatrix L) :
    spectatorExtension L R (A*B) = spectatorExtension L R A * spectatorExtension L R B := by
  unfold spectatorExtension
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem spectatorExtension_adjoint (L R : ℕ) (M : FockMatrix L) :
    spectatorExtension L R Mᴴ = (spectatorExtension L R M)ᴴ := by
  simp only [spectatorExtension, Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

theorem spectatorExtension_sum (L R : ℕ) {β : Type*} (s : Finset β) (M : β → FockMatrix L) :
    spectatorExtension L R (∑ b ∈ s, M b) = ∑ b ∈ s, spectatorExtension L R (M b) := by
  ext A B
  simp only [spectatorExtension, Matrix.sum_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Finset.sum_mul]

theorem spectatorExtension_add (L R : ℕ) (M N : FockMatrix L) :
    spectatorExtension L R (M+N) = spectatorExtension L R M + spectatorExtension L R N := by
  ext A B
  simp only [spectatorExtension, Matrix.add_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, add_mul]

theorem spectatorExtension_smul (L R : ℕ) (c : ℂ) (M : FockMatrix L) :
    spectatorExtension L R (c • M) = c • spectatorExtension L R M := by
  ext A B
  simp only [spectatorExtension, Matrix.smul_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, smul_eq_mul, mul_assoc]

theorem spectatorExtension_real_smul (L R : ℕ) (c : ℝ) (M : FockMatrix L) :
    spectatorExtension L R (c • M) = c • spectatorExtension L R M := by
  ext A B
  simp only [spectatorExtension, Matrix.smul_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Algebra.smul_mul_assoc]

theorem spectatorExtension_posSemidef (L R : ℕ) (M : FockMatrix L) (hM : M.PosSemidef) :
    (spectatorExtension L R M).PosSemidef := by
  exact (hM.kronecker Matrix.PosSemidef.one).submatrix _

@[simp] theorem spectatorExtension_zero (L R : ℕ) :
    spectatorExtension L R 0 = 0 := by
  simp only [spectatorExtension, Matrix.zero_kronecker, Matrix.submatrix_zero,
    Pi.zero_apply]

 

theorem spectatorExtension_pair {L p : ℕ} (R : ℕ) (hp : p+1 ≤ L) :
    spectatorExtension L R (localPairAnnihilator L (L+R) p) = pairAnnihilator (L+R) p := by
  classical
  let f : Orbital (L+R) → Orbital (L+R) → FockMatrix (L+R) := fun i j =>
    if i < j then (pairCoefficient (L+R) p i j : ℂ) •
      (annihilator (L+R) j * annihilator (L+R) i) else 0
  have hloc (i j : Orbital L) :
      f (localOrbital L R i) (localOrbital L R j) =
        spectatorExtension L R (if i < j then
          (sphericalPairCoefficient (L+R) p i.val j.val : ℂ) •
            (annihilator L j * annihilator L i) else 0) := by
    unfold f
    have he : localOrbital L R i < localOrbital L R j ↔ i < j := Iff.rfl
    simp only [he]
    split_ifs
    · rw [spectatorExtension_smul, spectatorExtension_mul,
        spectatorExtension_annihilator, spectatorExtension_annihilator]
      rw [pairCoefficient_eq_sphericalPairCoefficient]
      rfl
    · simp
  have hsleft (i : Fin R) (j : Orbital (L+R)) : f (spectatorOrbital L R i) j = 0 := by
    have he : (spectatorOrbital L R i).val + j.val ≠ p+1 := by
      rw [spectatorOrbital_val]; omega
    simp only [f, pairCoefficient_eq_sphericalPairCoefficient, sphericalPairCoefficient,
      ite_eq_right he, Complex.ofReal_zero, zero_smul, ite_self]
  have hsright (i : Orbital (L+R)) (j : Fin R) : f i (spectatorOrbital L R j) = 0 := by
    have he : i.val + (spectatorOrbital L R j).val ≠ p+1 := by
      rw [spectatorOrbital_val]; omega
    simp only [f, pairCoefficient_eq_sphericalPairCoefficient, sphericalPairCoefficient,
      ite_eq_right he, Complex.ofReal_zero, zero_smul, ite_self]
  change _ = ∑ i, ∑ j, f i j
  rw [← (orbitalMerge L R).sum_comp (fun i => ∑ j, f i j), Fintype.sum_sum_type]
  have hright : (∑ i : Fin R, ∑ j, f (orbitalMerge L R (Sum.inr i)) j) = 0 := by
    change (∑ i : Fin R, ∑ j, f (spectatorOrbital L R i) j) = 0
    simp only [hsleft, Finset.sum_const_zero]
  rw [hright, add_zero]
  unfold localPairAnnihilator coefficientPairAnnihilator
  rw [spectatorExtension_sum]
  apply Finset.sum_congr rfl
  intro i _
  change _ = ∑ j, f (localOrbital L R i) j
  rw [spectatorExtension_sum, ← (orbitalMerge L R).sum_comp (f (localOrbital L R i)),
    Fintype.sum_sum_type]
  simp only [localOrbital, spectatorOrbital] at hsright hloc
  simp only [hsright, Finset.sum_const_zero, add_zero, hloc, localOrbital]

 

def partialHamiltonian (Q P : ℕ) : FockMatrix Q :=
  ∑ p ∈ Finset.range P, (pairAnnihilator Q p)ᴴ * pairAnnihilator Q p

theorem partialHamiltonian_posSemidef (Q P : ℕ) :
    (partialHamiltonian Q P).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun p _ => Matrix.posSemidef_conjTranspose_mul_self _)

theorem spectatorExtension_localHamiltonian {L P : ℕ} (R : ℕ) (hP : P ≤ L) :
    spectatorExtension L R (localHamiltonian L P (L+R)) = partialHamiltonian (L+R) P := by
  unfold localHamiltonian partialHamiltonian
  rw [spectatorExtension_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [spectatorExtension_mul, spectatorExtension_adjoint,
    spectatorExtension_pair R (by have := Finset.mem_range.mp hp; omega)]

 

theorem fock_transfer_of_limitpositive {α β : Type*} [Fintype α] [Fintype β]
    (L P : ℕ) (hL : 1 ≤ L) (hP : P ≤ L)
    (p : β → ℕ) (j k : β → Orbital L) (hp : ∀ b, p b < P)
    (S : ℕ → Matrix α β ℂ) (Sstar : Matrix α β ℂ)
    (C : ℕ → Matrix α α ℂ) (Cstar : Matrix α α ℂ)
    (hS : Tendsto S atTop (𝓝 Sstar)) (hC : Tendsto C atTop (𝓝 Cstar))
    (hCH : ∀ Q, (C Q).IsHermitian) (hCSH : Cstar.IsHermitian)
    (hLimit : (∑ r, ∑ s, Cstar r s •
      ((∑ b, Sstar r b • (annihilator L (k b) * annihilator L (j b) *
        limitPairAnnihilator L (p b)))ᴴ *
       (∑ b, Sstar s b • (annihilator L (k b) * annihilator L (j b) *
        limitPairAnnihilator L (p b))))).PosSemidef) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Tendsto ρ atTop (𝓝 0) ∧
      ∀ R, ((∑ r, ∑ s, C (L+R) r s •
        ((∑ b, S (L+R) r b •
           (annihilator (L+R) (localOrbital L R (k b)) *
            annihilator (L+R) (localOrbital L R (j b)) * pairAnnihilator (L+R) (p b)))ᴴ *
         (∑ b, S (L+R) s b •
           (annihilator (L+R) (localOrbital L R (k b)) *
            annihilator (L+R) (localOrbital L R (j b)) * pairAnnihilator (L+R) (p b))))) +
        ρ (L+R) • partialHamiltonian (L+R) P).PosSemidef := by
  classical
  obtain ⟨ρ, hρ0, hρlim, hρ⟩ := local_transfer_of_limitpositive L P p j k hp
    S Sstar C Cstar hS hC hCH hCSH hLimit
  refine ⟨ρ, hρ0, hρlim, fun R => ?_⟩
  have h := spectatorExtension_posSemidef L R _
    (hρ (L+R) (by omega) (by omega) (by omega))
  simp only [spectatorExtension_add, spectatorExtension_sum,
    spectatorExtension_smul, spectatorExtension_real_smul, spectatorExtension_mul,
    spectatorExtension_adjoint, spectatorExtension_annihilator,
    spectatorExtension_localHamiltonian R hP] at h
  have hb (b : β) : spectatorExtension L R (localPairAnnihilator L (L+R) (p b)) =
      pairAnnihilator (L+R) (p b) := spectatorExtension_pair R (by have := hp b; omega)
  simpa only [hb] using h
end LaughlinFock
end

end OAI
