import Mathlib
import OAI.Analysis.MatrixSigning.Potential.StatePsi
import OAI.Analysis.MatrixSigning.Potential.DerivLine

namespace OAI

open Matrix

namespace CurrentKS.Difference
open scoped BigOperators

variable {N K : ℕ}

theorem ensemble_forces_negative (L : (Fin N → ℝ) →L[ℝ] ℝ)
    (B : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ)
    (μ : Fin N → ℝ) (dirs : Fin K → Fin N → ℝ)
    (test : (Fin N → ℝ) → ℝ) {lam a C : ℝ}
    (hN : 0 < N) (ha : 0 < a) (hC : 0 < C) (hrel : lam=512*a*C^2)
    (hμ : ∀ i,|μ i| ≤ C) (hdirs : (∑ j,∑ i,dirs j i^2) ≤ 8*C*N)
    (hprogress : L μ+(1/2:ℝ)*(∑ j,B (dirs j) (dirs j)) ≤ -lam*N/(8*C))
    (hgrad : ∀ i,|L (Pi.single i (1:ℝ))| ≤ a)
    (herr : ∀ u,|test u-B u u| ≤ a/16*(∑ i,u i^2)) :
    ¬∀ u,test u+7*a*(∑ i,u i^2) ≥ 0 := by
  intro hpsd
  have hlinear := (abs_le.mp (linear_coordinate_bound L μ ha.le hC.le hμ hgrad)).1
  have hi (j : Fin K) : -((113/16:ℝ)*a)*(∑ i,dirs j i^2) ≤ B (dirs j) (dirs j) := by
    have he := (abs_le.mp (herr (dirs j))).2
    have hp := hpsd (dirs j)
    linarith
  have hsum := Finset.sum_le_sum (fun (j : Fin K) (_ : j ∈ Finset.univ) => hi j)
  rw [← Finset.mul_sum] at hsum
  have hh := mul_le_mul_of_nonneg_left hdirs (show 0≤(113/16:ℝ)*a by positivity)
  have he : -lam*(N:ℝ)/(8*C) = -64*a*C*N := by rw [hrel];field_simp;ring
  rw [he] at hprogress
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hp : 0<a*C*(N:ℝ) := by positivity
  nlinarith

end CurrentKS.Difference

namespace CurrentKS.State.LightPoint
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Difference
open scoped BigOperators Topology ContDiff

variable {d N : ℕ} (p : LightPoint d N)

lemma contDiffAt_Psi_two [NeZero d] (lam : ℝ) : ContDiffAt ℝ 2 (p.Psi lam) p.x := by
  exact p.contDiffAt_R.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)) |>.add
    (contDiffAt_const.mul (contDiffAt_penalty p.interior))

lemma Psi_deriv_coordinates [NeZero d] (lam : ℝ) (h : Coordinates N) :
    deriv (fun s => p.Psi lam (line p.x h s)) 0 = fderiv ℝ (p.Psi lam) p.x h := by
  have hf : DifferentiableAt ℝ (p.Psi lam) (p.x+(0:ℝ) • h) := by
    simpa only [zero_smul,add_zero] using (p.contDiffAt_Psi_two lam).differentiableAt (by norm_num)
  have hh := deriv_line (x:=p.x) (h:=h) (t:=0) hf
  simp only [zero_smul,add_zero] at hh
  exact hh

lemma Psi_second_coordinates [NeZero d] (lam : ℝ) (h : Coordinates N) :
    deriv (deriv (fun s => p.Psi lam (line p.x h s))) 0 =
      fderiv ℝ (fderiv ℝ (p.Psi lam)) p.x h h := by
  have hf : ContDiffAt ℝ 2 (p.Psi lam) (p.x+(0:ℝ) • h) := by
    simpa only [zero_smul,add_zero] using p.contDiffAt_Psi_two lam
  have hh := second_deriv_line (x:=p.x) (h:=h) (t:=0) hf
  simp only [zero_smul,add_zero] at hh
  exact hh

theorem shifted_hessian_not_psd [NeZero d] [NeZero N] {lam a : ℝ}
    (ha : 0 < a) (hrel : lam=512*a*p.C1^2)
    (test : Coordinates N → ℝ)
    (hgrad : ∀ i,|fderiv ℝ (p.Psi lam) p.x (Pi.single i (1:ℝ))| ≤ a)
    (herr : ∀ u,|test u-fderiv ℝ (fderiv ℝ (p.Psi lam)) p.x u u| ≤ a/16*(∑ i,u i^2)) :
    ¬∀ u,test u+7*a*(∑ i,u i^2) ≥ 0 := by
  have hlam : 0 ≤ lam := by rw [hrel];positivity
  obtain ⟨Γ,_,hμ,hdirs,hprogress⟩ := p.exists_descent_ensemble lam hlam
  have he : p.driftCurvature (p.Psi lam) Γ =
      fderiv ℝ (p.Psi lam) p.x (p.mu Γ)+(1/2:ℝ)*
        (∑ j,fderiv ℝ (fderiv ℝ (p.Psi lam)) p.x (p.dirs Γ j) (p.dirs Γ j)) := by
    unfold driftCurvature
    simp_rw [p.Psi_deriv_coordinates,p.Psi_second_coordinates]
  rw [he] at hprogress
  exact ensemble_forces_negative (fderiv ℝ (p.Psi lam) p.x)
    (fderiv ℝ (fderiv ℝ (p.Psi lam)) p.x) (p.mu Γ) (p.dirs Γ) test
    (NeZero.pos N) ha p.C1_pos hrel hμ hdirs hprogress hgrad herr

end
end CurrentKS.State.LightPoint

end OAI
