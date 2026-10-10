import OAI.InformationTheory.AmplitudeDamping.PhaseStates

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace GAD

def tensorMatrix (n : ℕ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : QMatrix n :=
  fun i j ↦ ∏ k, A k (i k) (j k)

def tensorSplit (n : ℕ) : Basis (n+1) ≃ Fin 2 × Basis n :=
  (Fin.consEquiv (fun _ : Fin (n+1) ↦ Fin 2)).symm

theorem tensorMatrix_split {n : ℕ} (A : Fin (n+1) → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.reindex (tensorSplit n) (tensorSplit n) (tensorMatrix (n+1) A) =
      A 0 ⊗ₖ tensorMatrix n (fun k ↦ A k.succ) := by
  ext i j
  simp [Matrix.reindex_apply,Matrix.submatrix_apply,tensorSplit,tensorMatrix,
    Fin.prod_univ_succ]

theorem tensorMatrix_trace (n : ℕ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    (tensorMatrix n A).trace = ∏ k, (A k).trace := by
  exact (Fintype.prod_sum (fun k i ↦ A k i i)).symm

theorem tensorMatrix_zero (A : Fin 0 → Matrix (Fin 2) (Fin 2) ℂ) :
    tensorMatrix 0 A = 1 := by
  ext i j
  simp [tensorMatrix,Matrix.one_apply,Subsingleton.elim i j]

theorem tensorMatrix_posSemidef (n : ℕ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ k, (A k).PosSemidef) : (tensorMatrix n A).PosSemidef := by
  induction n with
  | zero => rw [tensorMatrix_zero]; exact Matrix.PosSemidef.one
  | succ n ih =>
      have h := (hA 0).kronecker (ih (fun k ↦ A k.succ) (fun k ↦ hA k.succ))
      rw [← tensorMatrix_split A] at h
      have h' := h.submatrix (tensorSplit n)
      simpa only [Matrix.reindex_apply,Matrix.submatrix_submatrix,Equiv.symm_comp_self,
        Matrix.submatrix_id_id] using h'

theorem tensorMatrix_state (n : ℕ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ k, IsState (A k)) : IsState (tensorMatrix n A) := by
  refine ⟨tensorMatrix_posSemidef n A (fun k ↦ (hA k).1), ?_⟩
  rw [tensorMatrix_trace]
  simp only [(hA _).2,Finset.prod_const_one]

theorem tensorMatrix_entropy (n : ℕ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ k, IsState (A k)) : entropy (tensorMatrix n A) = ∑ k, entropy (A k) := by
  induction n with
  | zero =>
      rw [tensorMatrix_zero]
      have hdiag : (1 : QMatrix 0) = Matrix.diagonal (fun _ : Basis 0 ↦ (1:ℂ)) := by simp
      rw [hdiag]
      change entropy (Matrix.diagonal (fun _ : Basis 0 ↦ ((1:ℝ):ℂ))) = _
      rw [entropy_diagonal]
      simp
  | succ n ih =>
      rw [← entropy_reindex (tensorSplit n) (tensorMatrix_state (n+1) A hA).1.isHermitian,
        tensorMatrix_split,entropy_kronecker_state (hA 0)
          (tensorMatrix_state n _ (fun k ↦ hA k.succ)),ih _ (fun k ↦ hA k.succ),Fin.sum_univ_succ]

theorem channel_tensorMatrix (γ ν : ℝ) (n : ℕ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    channel γ ν n (tensorMatrix n A) =
      tensorMatrix n (fun k ↦ applyKraus (kraus γ ν) (A k)) := by
  ext i j
  simp only [channel,applyKraus,tensorMatrix,Matrix.mul_apply,Matrix.sum_apply,Matrix.conjTranspose_apply]
  change (∑ r : Fin n → Fin 4, ∑ v : Basis n,
      (∑ u : Basis n, (∏ k, kraus γ ν (r k) (i k) (u k)) * (∏ k, A k (u k) (v k))) *
        star (∏ k, kraus γ ν (r k) (j k) (v k))) =
    ∏ k, ∑ r : Fin 4, ∑ v : Fin 2,
      (∑ u : Fin 2, kraus γ ν r (i k) u * A k u v) * star (kraus γ ν r (j k) v)
  simp only [star_prod,Finset.sum_mul,← Finset.prod_mul_distrib]
  have hinner (r : Fin n → Fin 4) (v : Basis n) :
      (∑ u : Basis n, ∏ k, (kraus γ ν (r k) (i k) (u k) * A k (u k) (v k)) *
        star (kraus γ ν (r k) (j k) (v k))) =
      ∏ k, ∑ u : Fin 2, (kraus γ ν (r k) (i k) u * A k u (v k)) *
        star (kraus γ ν (r k) (j k) (v k)) :=
    (Fintype.prod_sum (fun k u ↦ (kraus γ ν (r k) (i k) u * A k u (v k)) *
      star (kraus γ ν (r k) (j k) (v k)))).symm
  simp only [hinner]
  have hmid (r : Fin n → Fin 4) :
      (∑ v : Basis n, ∏ k, ∑ u : Fin 2,
        (kraus γ ν (r k) (i k) u * A k u (v k)) * star (kraus γ ν (r k) (j k) (v k))) =
      ∏ k, ∑ v : Fin 2, ∑ u : Fin 2,
        (kraus γ ν (r k) (i k) u * A k u v) * star (kraus γ ν (r k) (j k) v) :=
    (Fintype.prod_sum (fun k v ↦ ∑ u : Fin 2,
      (kraus γ ν (r k) (i k) u * A k u v) * star (kraus γ ν (r k) (j k) v))).symm
  simp only [hmid]
  exact (Fintype.prod_sum (fun k r ↦ ∑ v : Fin 2, ∑ u : Fin 2,
    (kraus γ ν r (i k) u * A k u v) * star (kraus γ ν r (j k) v))).symm

theorem tensorMatrix_sum {n : ℕ} (B : Fin n → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ s : Basis n, tensorMatrix n (fun k ↦ B k (s k))) =
      tensorMatrix n (fun k ↦ ∑ s, B k s) := by
  ext i j
  simp only [Matrix.sum_apply,tensorMatrix]
  exact (Fintype.prod_sum (fun k s ↦ B k s (i k) (j k))).symm

theorem tensorMatrix_smul {n : ℕ} (c : Fin n → ℝ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    tensorMatrix n (fun k ↦ c k • A k) = (∏ k, c k) • tensorMatrix n A := by
  ext i j
  simp [tensorMatrix,Complex.real_smul,Finset.prod_mul_distrib]

theorem tensorMatrix_average {n : ℕ} (B : Fin n → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ s : Basis n, ((2:ℝ)^n)⁻¹ • tensorMatrix n (fun k ↦ B k (s k))) =
      tensorMatrix n (fun k ↦ (1/2:ℝ) • B k 0+(1/2:ℝ) • B k 1) := by
  rw [← Finset.smul_sum,tensorMatrix_sum]
  have hm : (fun k ↦ (1/2:ℝ) • B k 0+(1/2:ℝ) • B k 1) =
      (fun k ↦ (1/2:ℝ) • (∑ s, B k s)) := by
    funext k
    rw [Fin.sum_univ_two,smul_add]
  rw [hm,tensorMatrix_smul]
  simp [Finset.prod_const,one_div]

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem phaseState_tensor {n : ℕ} (p : ℝ) (s : Basis n) :
    phaseState p s = tensorMatrix n (fun k ↦ pure (phaseSignal p (s k))) := by
  ext i j
  simp only [phaseState,phaseProduct,pure,tensorMatrix,star_prod,Finset.prod_mul_distrib]

theorem phaseState_state {n : ℕ} {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (s : Basis n) :
    IsState (phaseState p s) := by
  rw [phaseState_tensor]
  exact tensorMatrix_state n _ (fun k ↦ pure_state (phaseSignal_mass hp (s k)))

theorem phaseState_output {n : ℕ} (γ ν p : ℝ) (s : Basis n) :
    channel γ ν n (phaseState p s) = tensorMatrix n (fun k ↦ phaseOutput γ ν p (s k)) := by
  rw [phaseState_tensor,channel_tensorMatrix]
  rfl

theorem phaseState_entropy {n : ℕ} (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (s : Basis n) :
    entropy (channel γ ν n (phaseState p s)) = (n:ℝ)*g (v γ ν p) := by
  rw [phaseState_output,tensorMatrix_entropy n _ (fun k ↦ phaseOutput_state γ ν hγ hν hp (s k))]
  simp only [phaseOutput_entropy γ ν hγ hν hp,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]

theorem phaseState_average_entropy (n : ℕ) (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    entropy (∑ s : Basis n, (((2:ℝ)^n)⁻¹ : ℂ) • channel γ ν n (phaseState p s)) =
      (n:ℝ)*Real.binEntropy ((1-γ)*p+γ*ν) := by
  simp only [← Complex.ofReal_pow,← Complex.ofReal_inv,Complex.coe_smul,phaseState_output]
  rw [tensorMatrix_average]
  have hs : IsState ((1/2:ℝ) • phaseOutput γ ν p 0+(1/2:ℝ) • phaseOutput γ ν p 1) := by
    have h := state_mixture (fun _ : Fin 2 ↦ (1/2:ℝ)) (phaseOutput γ ν p)
      (by intro a; norm_num) (by norm_num [Fin.sum_univ_two])
      (fun s ↦ phaseOutput_state γ ν hγ hν hp s)
    simpa only [Fin.sum_univ_two] using h
  rw [tensorMatrix_entropy n _ (fun _ ↦ hs)]
  simp only [phaseOutput_average_entropy γ ν hγ hν hp,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem basis_card (n : ℕ) : Fintype.card (Basis n) = 2^n := by
  simp [Basis]

theorem phase_weights_sum (n : ℕ) : (∑ _s : Basis n, ((2:ℝ)^n)⁻¹) = 1 := by
  simp only [Finset.sum_const,Finset.card_univ,basis_card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  exact mul_inv_cancel₀ (pow_ne_zero n (by norm_num))

theorem phaseValue_formula (n : ℕ) (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    phaseValue γ ν p n = (n:ℝ)/Real.log 2*objective γ ν p := by
  unfold phaseValue
  rw [phaseState_average_entropy n γ ν hγ hν hp]
  simp only [phaseState_entropy γ ν hγ hν hp,← Finset.sum_mul,phase_weights_sum,one_mul]
  unfold objective
  ring

def phaseEnsemble (n : ℕ) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) : Ensemble n where
  size := Fintype.card (Basis n)
  weight := fun _ ↦ ((2:ℝ)^n)⁻¹
  weight_nonneg := fun _ ↦ inv_nonneg.mpr (pow_nonneg (by norm_num) n)
  weight_sum := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      phase_weights_sum n
  signal := fun a ↦ phaseState p ((Fintype.equivFin (Basis n)).symm a)
  signal_state := fun a ↦ phaseState_state hp _

theorem phaseEnsemble_value (n : ℕ) (γ ν p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    ensembleValue γ ν (phaseEnsemble n p hp) = phaseValue γ ν p n := by
  unfold ensembleValue phaseEnsemble phaseValue
  simp only [← Complex.ofReal_inv,← Complex.ofReal_pow]
  rw [Equiv.sum_comp (Fintype.equivFin (Basis n)).symm
    (fun s ↦ Complex.ofReal ((2:ℝ)^n)⁻¹ • channel γ ν n (phaseState p s)),
    Equiv.sum_comp (Fintype.equivFin (Basis n)).symm
    (fun s ↦ ((2:ℝ)^n)⁻¹ * entropy (channel γ ν n (phaseState p s)))]

end GAD

end

end OAI
