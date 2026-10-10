import Mathlib
import OAI.Analysis.MatrixSigning.Potential.LightPoint
import OAI.Analysis.MatrixSigning.Potential.InverseProductLeft
import OAI.Analysis.MatrixSigning.Potential.ResponseMatrix
import OAI.Analysis.MatrixSigning.Matrices.SquareShift

namespace OAI

open Matrix

namespace CurrentKS.State.LightPoint
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Interaction
open CurrentKS.Covariance CurrentKS.Movement Matrix WithLp
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {d N : ℕ} (p : LightPoint d N)

def IA : Covariance.Mat N := interaction 384 p.A p.l p.X
def IB : Covariance.Mat N := interaction 384 p.A p.m p.Y
def wP (i : Fin N) : ℝ := p.l i*p.pp i
def wQ (i : Fin N) : ℝ := p.m i*p.qq i
def s0 : ℝ := p.ε/40000
def J : ℝ := 1+(3*(N : ℝ))^2/p.s0
def E0 : ℝ := 2*p.J^2*(1+3*(N : ℝ))^2
def C1 : ℝ := max 1 (max (48*p.E0/23) (4*(1+9*(N : ℝ)^2)))
lemma s0_pos : 0 < p.s0 := div_pos p.ε_pos (by norm_num)
lemma s0_le_one : p.s0 ≤ 1 := by dsimp [s0]; linarith [p.ε_le_one]
lemma E0_pos : 0 < p.E0 := by
  dsimp [E0,J]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hs := p.s0_pos
  positivity
lemma C1_ge_one : (1 : ℝ) ≤ p.C1 := le_max_left ..
lemma C1_pos : 0 < p.C1 := lt_of_lt_of_le (by norm_num) p.C1_ge_one

lemma primal_lower [NeZero d] :
    (1/200 : ℝ) • (Hermitian.one : H d) ≤ p.X ∧
    (1/200 : ℝ) • (Hermitian.one : H d) ≤ p.Y := by
  have hh := sublevel_box (p.fixedPart+S p.A p.x) (eta 384 p.A p.x)
    (eta_positive (by norm_num) p.A (fun i => (p.interior i).le)) p.ε_pos (by norm_num : (0 : ℝ) < 100)
    p.lower p.upper p.feasible p.sublevel
  norm_num only [show (2 : ℝ)*100 = 200 by norm_num,show (200 : ℝ)⁻¹ = 1/200 by norm_num] at hh
  exact ⟨hh.2.1.1,hh.2.2.1⟩

lemma primal_square_lower [NeZero d] :
    (1/40000 : ℝ) • (Hermitian.one : H d) ≤ sandwich p.X one ∧
    (1/40000 : ℝ) • (Hermitian.one : H d) ≤ sandwich p.Y one := by
  have hX := square_lower p.X (by norm_num : (0 : ℝ) ≤ 1/200) p.primal_lower.1
  have hY := square_lower p.Y (by norm_num : (0 : ℝ) ≤ 1/200) p.primal_lower.2
  norm_num only [div_pow,one_pow] at hX hY
  exact ⟨hX,hY⟩

open scoped Matrix.Norms.Frobenius in

lemma interaction_row_gap [NeZero d] :
    (∀ i, (p.IA *ᵥ p.wQ) i ≤ (1-p.s0)*p.wP i) ∧
    (∀ i, (p.IB *ᵥ p.wP) i ≤ (1-p.s0)*p.wQ i) := by
  constructor
  · intro i
    have h₁ := inner_mono_right_psd (p.A i) (p.A_pos i) p.primal_square_lower.1
    rw [inner_smul_right_fixed] at h₁
    have h₂ := inner_mono_right_psd (p.A i) (p.A_pos i) p.P_le
    have h₃ : (1/40000 : ℝ)*p.pp i ≤ inner ℝ (p.A i) (sandwich p.X one) := by
      dsimp only [pp]; nlinarith
    change (interaction 384 p.A p.l p.X *ᵥ fun j => p.m j*inner ℝ (p.A j) p.Q) i ≤
      (1-p.s0)*(p.l i*inner ℝ (p.A i) p.P)
    rw [interaction_duality 384 p.ε p.A p.x p.A_pos p.A_rank p.l p.m p.lm_eq
      p.X p.P p.Q p.X_pos p.stationary_X i]
    have hh := mul_le_mul_of_nonneg_left h₃ (mul_nonneg p.ε_pos.le (p.scales_pos i).2.1.le)
    dsimp only [s0,pp] at *
    nlinarith
  · intro i
    have h₁ := inner_mono_right_psd (p.A i) (p.A_pos i) p.primal_square_lower.2
    rw [inner_smul_right_fixed] at h₁
    have h₂ := inner_mono_right_psd (p.A i) (p.A_pos i) p.Q_le
    have h₃ : (1/40000 : ℝ)*p.qq i ≤ inner ℝ (p.A i) (sandwich p.Y one) := by
      dsimp only [qq]; nlinarith
    change (interaction 384 p.A p.m p.Y *ᵥ fun j => p.l j*inner ℝ (p.A j) p.P) i ≤
      (1-p.s0)*(p.m i*inner ℝ (p.A i) p.Q)
    rw [interaction_duality 384 p.ε p.A p.x p.A_pos p.A_rank p.m p.l
      (fun i => (mul_comm _ _).trans (p.lm_eq i)) p.Y p.Q p.P p.Y_pos p.stationary_Y i]
    have hh := mul_le_mul_of_nonneg_left h₃ (mul_nonneg p.ε_pos.le (p.scales_pos i).2.2.le)
    dsimp only [s0,qq] at *
    nlinarith

lemma IA_psd : p.IA.PosSemidef := interaction_psd (by norm_num) p.A p.l p.X p.X_pos.posSemidef
lemma IB_psd : p.IB.PosSemidef := interaction_psd (by norm_num) p.A p.m p.Y p.Y_pos.posSemidef
lemma IA_norm_le [NeZero d] : ‖p.IA‖ ≤ 3*(N : ℝ) := by
  apply (psd_norm_le_trace p.IA p.IA_psd).trans
  calc
    p.IA.trace ≤ ∑ _ : Fin N, (3 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      dsimp only [IA,Matrix.diag]
      rw [interaction_diag 384 p.A p.A_pos p.A_rank p.l p.X i]
      have hh := p.square_bounds i
      dsimp only [a] at hh
      norm_num at hh
      linarith
    _ = _ := by simp; ring
lemma IB_norm_le [NeZero d] : ‖p.IB‖ ≤ 3*(N : ℝ) := by
  apply (psd_norm_le_trace p.IB p.IB_psd).trans
  calc
    p.IB.trace ≤ ∑ _ : Fin N, (3 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      dsimp only [IB,Matrix.diag]
      rw [interaction_diag 384 p.A p.A_pos p.A_rank p.m p.Y i]
      have hh := p.square_bounds i
      dsimp only [b] at hh
      norm_num at hh
      linarith
    _ = _ := by simp; ring

lemma coupled_movement [NeZero d] (v : Covariance.E (2*N)) (hv : constraintLin p.IA p.IB v = 0) :
    ‖v‖^2 ≤ p.E0*‖responseLin p.IB v‖^2 := by
  rw [pair_norm_sq]
  obtain ⟨hf,hg⟩ := constraints_responses p.IA p.IB v hv
  exact matrix_coupled_response_bound p.IA p.IB p.IA_psd p.IB_psd
    (interaction_nonneg (by norm_num) p.A p.A_pos p.l (fun i => (p.scales_pos i).2.1.le) p.X)
    (interaction_nonneg (by norm_num) p.A p.A_pos p.m (fun i => (p.scales_pos i).2.2.le) p.Y)
    p.wP p.wQ (fun i => mul_pos (p.scales_pos i).2.1 (p.pp_pos i))
    (fun i => mul_pos (p.scales_pos i).2.2 (p.qq_pos i)) p.s0_pos p.s0_le_one (by positivity)
    p.interaction_row_gap.1 p.interaction_row_gap.2 p.IA_norm_le p.IB_norm_le _ _ _ hf hg

lemma covariance_movement_bounds [NeZero d] {Γ : Covariance.Mat (2*N)}
    (hΓ : Γ.PosSemidef) (hbound : ((4 : ℝ) • (1 : Covariance.Mat (2*N))-Γ).PosSemidef)
    (htr : (23/48 : ℝ)*N ≤ Γ.trace)
    (hc : ∀ j, constraintLin p.IA p.IB (column (CFC.sqrt Γ) j) = 0) :
    (N : ℝ)/p.C1 ≤ (∑ i, ∑ j, (responseLin p.IB (column (CFC.sqrt Γ) j) i)^2) ∧
    ∀ i, (∑ j, (responseLin p.IB (column (CFC.sqrt Γ) j) i)^2) ≤ p.C1 := by
  have hE : p.E0*(∑ i, ∑ j, (responseLin p.IB (column (CFC.sqrt Γ) j) i)^2) ≥ (23/48 : ℝ)*N := by
    calc
      _ = ∑ j, p.E0*‖responseLin p.IB (column (CFC.sqrt Γ) j)‖^2 := by
        simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,Finset.mul_sum]
        rw [Finset.sum_comm]
      _ ≥ ∑ j, ‖column (CFC.sqrt Γ) j‖^2 := Finset.sum_le_sum fun j _ => p.coupled_movement _ (hc j)
      _ = Γ.trace := total_movement hΓ
      _ ≥ _ := htr
  refine ⟨?_,fun i => ?_⟩
  · have hC : 48*p.E0/23 ≤ p.C1 := (le_max_left _ _).trans (le_max_right _ _)
    have hn : 0 ≤ ∑ i, ∑ j, (responseLin p.IB (column (CFC.sqrt Γ) j) i)^2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    apply (div_le_iff₀ p.C1_pos).mpr
    have hh := mul_le_mul_of_nonneg_right hC hn
    nlinarith
  · have hh := response_moment_upper p.IB p.IB_psd.isHermitian hΓ hbound i
    have hn := p.IB_norm_le
    have hC : 4*(1+9*(N : ℝ)^2) ≤ p.C1 := (le_max_right _ _).trans (le_max_right _ _)
    have hsq := pow_le_pow_left₀ (norm_nonneg p.IB) hn 2
    nlinarith

end
end CurrentKS.State.LightPoint

end OAI
