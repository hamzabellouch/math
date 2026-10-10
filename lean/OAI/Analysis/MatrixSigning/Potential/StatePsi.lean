import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Drift
import OAI.Analysis.MatrixSigning.Potential.StateR

namespace OAI

open Matrix

namespace CurrentKS.State.LightPoint
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Interaction CurrentKS.Covariance
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ} (p : LightPoint d N)

lemma contDiffAt_R [NeZero d] : ContDiffAt ℝ ∞ p.R p.x := by
  exact contDiffAt_value p.ε p.ε_pos (fun y => p.fixedPart+S p.A y) (eta 384 p.A) p.x
    (contDiffAt_const.add (contDiff_S p.A).contDiffAt) (contDiffAt_eta 384 p.A p.interior)
    (eta_positive (by norm_num) p.A (fun i => (p.interior i).le))
    (Filter.Eventually.of_forall fun y => eta_symmetric 384 p.A y) p.lower p.upper
    p.primal p.feasible p.minimal

lemma contDiffAt_R_line [NeZero d] (h : Coordinates N) :
    ContDiffAt ℝ ∞ (fun s => p.R (line p.x h s)) 0 := by
  have hh : ContDiffAt ℝ ∞ p.R (line p.x h 0) := by simpa only [line_zero] using p.contDiffAt_R
  exact hh.comp 0 (contDiff_line p.x h).contDiffAt

lemma contDiffAt_penalty_line (h : Coordinates N) :
    ContDiffAt ℝ ∞ (fun s => penalty (line p.x h s)) 0 := by
  have hh : ContDiffAt ℝ ∞ penalty (line p.x h 0) := by
    simpa only [line_zero] using (contDiffAt_penalty p.interior : ContDiffAt ℝ ∞ penalty p.x)
  exact hh.comp 0 (contDiff_line p.x h).contDiffAt

def Psi (lam : ℝ) (y : Coordinates N) : ℝ := p.R y+lam*penalty y

def omega (Γ : Covariance.Mat (2*N)) (i : Fin N) : ℝ :=
  ∑ j, (p.resp (column (CFC.sqrt Γ) j) i)^2

def mu (Γ : Covariance.Mat (2*N)) : Coordinates N :=
  fun i => Progress.drift (p.T i) (p.tildeA i) (p.tildeB i) (p.omega Γ i)

def dirs (Γ : Covariance.Mat (2*N)) (j : Fin (2*N)) : Coordinates N :=
  p.direction (column (CFC.sqrt Γ) j)

def driftCurvature (f : Coordinates N → ℝ) (Γ : Covariance.Mat (2*N)) : ℝ :=
  deriv (fun s => f (line p.x (p.mu Γ) s)) 0+
    (1/2 : ℝ)*(∑ j,deriv (deriv (fun s => f (line p.x (p.dirs Γ j) s))) 0)

lemma omega_nonneg (Γ : Covariance.Mat (2*N)) (i : Fin N) : 0 ≤ p.omega Γ i :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma Psi_first [NeZero d] (lam : ℝ) (h : Coordinates N) :
    deriv (fun s => p.Psi lam (line p.x h s)) 0 =
      deriv (fun s => p.R (line p.x h s)) 0+lam*penalty₁ p.x h := by
  have hP := (p.contDiffAt_penalty_line h).differentiableAt (by norm_num)
  change deriv (fun s => p.R (line p.x h s)+lam*penalty (line p.x h s)) 0 = _
  have hd := (((p.contDiffAt_R_line h).differentiableAt (by norm_num)).hasDerivAt.add
    (hP.hasDerivAt.const_mul lam)).deriv
  change deriv (fun s => p.R (line p.x h s)+lam*penalty (line p.x h s)) 0 = _ at hd
  rw [hd,penalty_line_first p.x h p.interior]

lemma Psi_second [NeZero d] (lam : ℝ) (h : Coordinates N) :
    deriv (deriv (fun s => p.Psi lam (line p.x h s))) 0 =
      deriv (deriv (fun s => p.R (line p.x h s))) 0+lam*penalty₂ p.x h := by
  have hR : ContDiffAt ℝ 2 (fun s => p.R (line p.x h s)) 0 :=
    (p.contDiffAt_R_line h).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hP : ContDiffAt ℝ 2 (fun s => penalty (line p.x h s)) 0 :=
    (p.contDiffAt_penalty_line h).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  change deriv (deriv (fun s => p.R (line p.x h s)+lam*penalty (line p.x h s))) 0 = _
  rw [second_deriv_add hR (contDiffAt_const.mul hP),second_deriv_const_mul,
    penalty_line_second p.x h p.interior]

lemma R_driftCurvature_nonpos [NeZero d] {Γ : Covariance.Mat (2*N)}
    (hc : ∀ j, constraintLin p.IA p.IB (column (CFC.sqrt Γ) j) = 0)
    (he : (∑ j, p.invEnergy (column (CFC.sqrt Γ) j)) ≤
      16*(∑ i,(p.tildeA i*p.wP i+p.tildeB i*p.wQ i)*p.omega Γ i)) :
    p.driftCurvature p.R Γ ≤ 0 := by
  have hh := p.R_ensemble_curvature hc he
  have hd := Progress.weighted_drift_nonpositive p.T p.tildeA p.tildeB p.wP p.wQ (p.omega Γ)
    (fun i => (p.scales_pos i).1.ne') (fun i => (p.tildeA_pos i).le) (fun i => (p.tildeB_pos i).le)
    (fun i => (p.wP_pos i).le) (fun i => (p.wQ_pos i).le) (p.omega_nonneg Γ) hh
  dsimp only [driftCurvature]
  rw [p.R_first]
  convert hd using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

lemma dirs_energy (Γ : Covariance.Mat (2*N)) :
    (∑ j,∑ i,(p.dirs Γ j i)^2) = ∑ i,p.omega Γ i/p.T i^2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [dirs,direction,div_pow,omega,Finset.sum_div]

lemma penalty_driftCurvature [NeZero d] (Γ : Covariance.Mat (2*N)) :
    p.driftCurvature penalty Γ ≤ -(1/8 : ℝ)*(∑ i,p.omega Γ i) := by
  have hh := Progress.penalty_drift_quantitative p.T p.tildeA p.tildeB (p.omega Γ)
    (fun i => psi (p.x i)) (fun i => psi₁ (p.x i)) (fun i => kappa (p.x i))
    (fun i => (p.scales_pos i).1) (fun i => (p.tildeA_pos i).le) (fun i => (p.tildeB_pos i).le)
    (p.omega_nonneg Γ) (fun i => psi_pos (p.interior i)) (fun i => (kappa_pos (p.interior i)).le)
    (fun i => (div_le_one (mul_pos (psi_pos (p.interior i)) (kappa_pos (p.interior i)))).mp
      (abs_derivative_ratio_le (p.interior i))) (fun i => (p.drift_bounds i).1) (fun i => (p.kappa_bounds i).1)
  dsimp only [driftCurvature]
  rw [penalty_line_first p.x (p.mu Γ) p.interior]
  simp_rw [penalty_line_second p.x _ p.interior]
  convert hh using 1
  dsimp only [penalty₁,penalty₂,mu,dirs,direction]
  rw [Finset.sum_comm (f := fun j i => -kappa (p.x i)*(p.resp (column (CFC.sqrt Γ) j) i/p.T i)^2)]
  simp only [Finset.mul_sum,Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [omega]
  simp only [Finset.sum_div,Finset.mul_sum,← Finset.sum_neg_distrib]
  symm
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma Psi_driftCurvature [NeZero d] (lam : ℝ) (Γ : Covariance.Mat (2*N)) :
    p.driftCurvature (p.Psi lam) Γ = p.driftCurvature p.R Γ+lam*p.driftCurvature penalty Γ := by
  dsimp only [driftCurvature]
  rw [p.Psi_first]
  simp_rw [p.Psi_second,penalty_line_first p.x (p.mu Γ) p.interior,penalty_line_second p.x _ p.interior]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  ring

theorem exists_descent_ensemble [NeZero d] (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ Γ : Covariance.Mat (2*N), Γ.PosSemidef ∧
      (∀ i, |p.mu Γ i| ≤ p.C1) ∧
      (∑ j,∑ i,(p.dirs Γ j i)^2) ≤ 8*p.C1*N ∧
      p.driftCurvature (p.Psi lam) Γ ≤ -lam*N/(8*p.C1) := by
  obtain ⟨Γ,hΓ,_,hb,ht,hc,he⟩ := state_energy_ensemble (show (384 : ℝ) ≤ 384 from le_rfl) p.ε_pos.le
    p.A p.x p.A_pos p.A_ne_zero p.A_rank p.l p.m (fun i => (p.scales_pos i).2.1)
    (fun i => (p.scales_pos i).2.2) p.lm_eq p.X p.Y p.P p.Q p.X_pos p.Y_pos p.P_pos p.Q_pos
    p.stationary_X p.stationary_Y p.product_bound
  have hem : (∑ j,p.invEnergy (column (CFC.sqrt Γ) j)) ≤
      16*(∑ i,(p.tildeA i*p.wP i+p.tildeB i*p.wQ i)*p.omega Γ i) := he
  obtain ⟨hlo,hi⟩ := p.covariance_movement_bounds hΓ hb ht hc
  change (N : ℝ)/p.C1 ≤ ∑ i,p.omega Γ i at hlo
  change ∀ i, p.omega Γ i ≤ p.C1 at hi
  refine ⟨Γ,hΓ,?_,?_,?_⟩
  · intro i
    exact Progress.drift_size (p.scales_pos i).1 (p.tildeA_pos i).le (p.tildeB_pos i).le
      (p.omega_nonneg Γ i) (p.drift_bounds i).2 (hi i)
  · rw [p.dirs_energy]
    calc
      _ ≤ ∑ _ : Fin N, (3/2 : ℝ)*p.C1 := by
        apply Finset.sum_le_sum
        intro i _
        have hh := mul_le_mul_of_nonneg_left (p.kappa_bounds i).2 (p.omega_nonneg Γ i)
        have hhi := mul_le_mul_of_nonneg_left (hi i) (by norm_num : (0 : ℝ) ≤ 3/2)
        rw [div_eq_mul_inv]
        nlinarith
      _ ≤ 8*p.C1*N := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith [p.C1_pos]
  · rw [p.Psi_driftCurvature]
    apply Progress.combine_progress hlam p.C1_pos (p.R_driftCurvature_nonpos hc hem)
    have hh := p.penalty_driftCurvature Γ
    have heq : -(1/8 : ℝ)*((N : ℝ)/p.C1) = -(N : ℝ)/(8*p.C1) := by ring
    rw [← heq]
    linarith

end
end CurrentKS.State.LightPoint

end OAI
