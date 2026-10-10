import OAI.Geometry.NodalSets.Persistence.SphereFiniteNormSimplePersistence

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff
noncomputable section

lemma sphereWeightedPairing_smul_self (rho u : Base → ℝ) (c : ℝ) :
    sphereWeightedPairing rho (c • u) (c • u)=c^2*sphereWeightedPairing rho u u := by
  rw [sphereWeightedPairing_smul_left,sphereWeightedPairing_symm rho u (c • u),sphereWeightedPairing_smul_left]
  ring

theorem sphere_normalized_simple_eigenfunction_signed (d : SphereEnergyData)
    (u : Base → ℝ) (hun : sphereWeightedPairing d.density u u=1) (lam : ℝ)
    (hsimple : ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
      (∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
        lam*v ((extChartAt (𝓡 4) p).symm y)) → ∃ c : ℝ, v=c • u)
    (v : Base → ℝ) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (hvn : sphereWeightedPairing d.density v v=1)
    (he : ∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
      lam*v ((extChartAt (𝓡 4) p).symm y)) : v=u ∨ v=-u := by
  obtain ⟨c,rfl⟩ := hsimple v hv he
  rw [sphereWeightedPairing_smul_self,hun,mul_one] at hvn
  have hc : c=1 ∨ c=-1 := by
    have h : (c-1)*(c+1)=0 := by nlinarith
    rcases mul_eq_zero.mp h with h | h
    · left; linarith
    · right; linarith
  rcases hc with rfl | rfl <;> simp

end
end Yau.Target

end OAI
