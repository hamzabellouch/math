import Mathlib
import OAI.Geometry.PrescribedPotential.JetEnergyUniform

namespace OAI

/-! Uniform Jet Controls. -/

section

noncomputable section
open Set Filter Topology Finset Module
open scoped ContDiff
namespace HigherJet
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {ι : Type*} [Fintype ι]

lemma sqrt_coercivity {S D q : ℝ} (_hS : 0 ≤ S) (hD : 0 ≤ D) (hq : 0 ≤ q)
    (h : S ≤ q*D) : Real.sqrt S ≤ (1+q)*Real.sqrt D := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  rw [mul_pow,Real.sq_sqrt hD]
  have hh : q ≤ (1+q)^2 := by nlinarith only [sq_nonneg q]
  exact h.trans (mul_le_mul_of_nonneg_right hh hD)

lemma uniform_jet_controls (e : OrthonormalBasis ι ℝ E) (m : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (U : Set E), IsOpen U → ∀ u : E → F, ContDiffOn ℝ ∞ u U →
      ∀ x ∈ U, ∀ τ : E ≃L[ℝ] E, ‖τ.toContinuousLinearMap‖ ≤ B → ‖τ.symm.toContinuousLinearMap‖ ≤ B →
        ‖iteratedFDeriv ℝ m u x‖ ≤ A*Real.sqrt (jetEnergy e m u x) ∧
        ‖iteratedFDeriv ℝ (m+1) u x‖ ≤ A*Real.sqrt (familyDissipation (fun i => τ (e i)) (jetFamily e m u) x) ∧
        jetEnergy e (m+1) u x ≤ A*familyDissipation (fun i => τ (e i)) (jetFamily e m u) x ∧
        familyDissipation (fun i => τ (e i)) (jetFamily e m u) x ≤ A*jetEnergy e (m+1) u x := by
  obtain ⟨N,hN,hn⟩ := norm_iteratedFDeriv_le_jetEnergy (F := F) e.toBasis m
  obtain ⟨P,hP,hp⟩ := norm_iteratedFDeriv_le_jetEnergy (F := F) e.toBasis (m+1)
  obtain ⟨C,hC,hc⟩ := jetEnergy_frame_coercivity (F := F) e
  obtain ⟨D,hD,hd⟩ := jetEnergy_frame_upper (F := F) e
  let A := 1+N+P*(1+C*B^2)+C*B^2+D*B^2
  have ht : 0 ≤ P*(1+C*B^2) := by positivity
  have hc0 : 0 ≤ C*B^2 := by positivity
  have hd0 : 0 ≤ D*B^2 := by positivity
  have hnA : N ≤ A := by dsimp [A]; linarith only [hN,ht,hc0,hd0]
  have hpA : P*(1+C*B^2) ≤ A := by dsimp [A]; nlinarith only [hN,hC,hD,sq_nonneg B,mul_nonneg hC.le (sq_nonneg B),mul_nonneg hD.le (sq_nonneg B)]
  have hcA : C*B^2 ≤ A := by dsimp [A]; linarith only [hN,ht,hc0,hd0]
  have hdA : D*B^2 ≤ A := by dsimp [A]; linarith only [hN,ht,hc0,hd0]
  refine ⟨A,by dsimp [A]; linarith only [hN,ht,hc0,hd0],?_⟩
  intro U hU u hu x hx τ hτ hτi
  have hco := hc m u x τ B hB hτi
  have hup := hd m u x τ B hB hτ
  have hs := sqrt_coercivity (jetEnergy_nonneg _ _ _ _) (familyDissipation_nonneg _ _ _)
    (show 0 ≤ C*B^2 by positivity) hco
  refine ⟨(hn U hU u hu x hx).trans (mul_le_mul_of_nonneg_right hnA (Real.sqrt_nonneg _)),?_,
    hco.trans (mul_le_mul_of_nonneg_right hcA (familyDissipation_nonneg _ _ _)),
    hup.trans (mul_le_mul_of_nonneg_right hdA (jetEnergy_nonneg _ _ _ _))⟩
  exact (hp U hU u hu x hx).trans ((mul_le_mul_of_nonneg_left hs hP.le).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hpA (Real.sqrt_nonneg _)))
end HigherJet

end
end

end OAI
