import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ScaledNuclearNear
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.TransportedNodes

namespace OAI

/-! The actual transported Gauss nuclei satisfy the separation hypothesis
in the full weak-H1 near-field bound, uniformly over the chosen finite grid. -/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace ContinuumCoulomb

theorem transportedGauss_separation {m : ℕ} {h : ℝ} (hh : 0 < h)
    (index : Fin m → GaussLatticeIndex) (hindex : Function.Injective index)
    (G : Position → Position) {K : ℝ≥0} (hK : 0 < K) (hG : AntilipschitzWith K G)
    (a b : Fin m) (hab : a ≠ b) :
    h/(3*(K:ℝ)) ≤ ‖G (gaussLatticePoint h (index a))-G (gaussLatticePoint h (index b))‖ := by
  have hb := gaussLatticePoint_separation hh (index a) (index b) (fun he => hab (hindex he))
  have ht := hG.le_mul_dist (gaussLatticePoint h (index a)) (gaussLatticePoint h (index b))
  simp only [dist_eq_norm] at ht
  apply (div_le_iff₀ (show 0 < 3*(K:ℝ) by positivity)).mpr
  nlinarith

theorem transportedGauss_near_form {κ : ℝ} (hκ : 0 < κ)
    (K : ℝ≥0) (hK : 0 < K) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (m n : ℕ) (u : Coulomb.H1Vector n)
      (s : SpinConfiguration n) (i : Fin n) (h ρ : ℝ),
      0 < h → h ≤ 1 → 0 ≤ ρ →
      ∀ (index : Fin m → GaussLatticeIndex), Function.Injective index →
      ∀ (G : Position → Position), AntilipschitzWith K G →
      (ρ*h^3/8)*(∑ a, ∫ x in electronBall i (G (gaussLatticePoint h (index a))) (κ*h),
        Coulomb.coulombKernel (Coulomb.position x i-G (gaussLatticePoint h (index a)))*
          ‖u.value s x‖^2) ≤
      ρ*A*h^2*((∫ x, ‖u.value s x‖^2)+
        ∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2) := by
  have hσ : 0 < 1/(3*(K:ℝ)) := by positivity
  obtain ⟨A,hA,hbound⟩ := scaled_nuclear_near_bound hκ hσ
  refine ⟨A,hA,fun m n u s i h ρ hh hh1 hρ index hindex G hG => ?_⟩
  apply hbound m n u s i (fun a => G (gaussLatticePoint h (index a))) h ρ hh hh1 hρ
  intro a b hab
  have he := transportedGauss_separation hh index hindex G hK hG a b hab
  convert he using 1
  ring

end ContinuumCoulomb

end

end OAI
