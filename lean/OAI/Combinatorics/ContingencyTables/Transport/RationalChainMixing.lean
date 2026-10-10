import OAI.Combinatorics.ContingencyTables.Transport.RationalChainCast
import OAI.Combinatorics.ContingencyTables.Transport.FiniteDependentApproximation

namespace OAI

/-! # A real pointwise mixing bound for the corresponding rational walk -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture CommonBasesFPRAS

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem rationalWalk_variation (K : X → RationalLaw X) (C : FiniteChain X)
    (hK : ∀ x y,((K x).mass y:ℝ)=C.P x y) (π : RationalLaw X)
    (hπ : ∀ y,(π.mass y:ℝ)=C.π y) (x : X) (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hpoint : ∀ y,|C.iterate n (C.pointDensity y) x-1| ≤ δ) :
    (variation (walkLaw K x n) π:ℝ) ≤ δ := by
  have hp (y : X) : |(C.kernel.power n).P x y-C.π y| ≤ C.π y*δ := by
    have hh := hpoint y
    rw [←C.kernel_power_density] at hh
    calc
      _ = C.π y*|(C.kernel.power n).P x y/C.π y-1| := by
        calc
          _ = |C.π y*((C.kernel.power n).P x y/C.π y-1)| := by
            congr 1
            field_simp [(C.positive y).ne']
          _ = _ := by rw [abs_mul,abs_of_pos (C.positive y)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (C.positive y).le
  have hs := Finset.sum_le_sum (fun y (_ : y∈Finset.univ) => hp y)
  rw [←Finset.sum_mul,C.normalized,one_mul] at hs
  unfold variation
  simp only [Rat.cast_div,Rat.cast_sum,Rat.cast_abs,Rat.cast_sub,Rat.cast_ofNat,
    walkLaw_cast_kernel K C hK,hπ]
  linarith

end ContingencyTables.FirstSuccess

end OAI
