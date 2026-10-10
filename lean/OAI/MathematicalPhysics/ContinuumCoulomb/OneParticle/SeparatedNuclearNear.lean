import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearPacking
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearNearEstimate

namespace OAI

/-! Separation of the actual point nuclei supplies the bounded-overlap
hypothesis in the weak-H1 near-node estimate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem separated_electron_ball_overlap {m n : ℕ} (R : Fin m → Position) (i : Fin n)
    {d L : ℝ} (hd : 0 < d) (hL : 0 ≤ L)
    (hsep : ∀ a b, a ≠ b → d ≤ ‖R a-R b‖) (x : Configuration n) :
    (∑ a, if x ∈ electronBall i (R a) L then (1:ℝ) else 0) ≤ (2*L+d)^3/d^3 := by
  have h := separated_ball_overlap R (Coulomb.position x i) hd hL hsep
  apply (le_div_iff₀ (pow_pos hd 3)).mpr
  convert h using 1
  congr 1
  simp only [electronBall,Set.mem_ofPred_eq,norm_sub_rev,← Finset.sum_filter,
    Finset.sum_const,nsmul_eq_mul,mul_one]

theorem separated_nuclear_near_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (m n : ℕ) (u : Coulomb.H1Vector n)
      (s : SpinConfiguration n) (i : Fin n) (R : Fin m → Position) (r d : ℝ),
      0 < r → 0 < d → (∀ a b, a ≠ b → d ≤ ‖R a-R b‖) →
      (∑ a, ∫ x in electronBall i (R a) r,
        Coulomb.coulombKernel (Coulomb.position x i-R a)*‖u.value s x‖^2) ≤
      ((4*r+d)^3/d^3)*((24*C^2/r)*(∫ x, ‖u.value s x‖^2)+
        8*r*(∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2)) := by
  obtain ⟨C,hC,hbound⟩ := nuclear_near_sum_bound
  refine ⟨C,hC,fun m n u s i R r d hr hd hsep => ?_⟩
  have hb := hbound m n u s i R r ((2*(2*r)+d)^3/d^3) hr
    (separated_electron_ball_overlap R i hd (by positivity) hsep)
  convert hb using 1
  ring

end ContinuumCoulomb

end

end OAI
