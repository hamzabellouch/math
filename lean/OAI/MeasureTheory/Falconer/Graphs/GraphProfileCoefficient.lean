import OAI.MeasureTheory.Falconer.Estimates.ProfileMassError

namespace OAI

namespace PlanarFalconer
open MeasureTheory

noncomputable def graphProfileCoefficient (N : ℕ) (mass : Fin 4 → ℝ → ℝ) (a p : ℝ) : ℝ :=
  ∏ l : Fin 4, ((2:ℝ)^N)^(-mass l p) / ((2:ℝ)^N)^(-mass l a)

theorem graphProfileCoefficient_bounds
    (Q : Fin 4 → DyadicSquare) (ρ : Fin 4 → Measure Plane) (N B : ℕ)
    (δ lam : ℝ) (mass : Fin 4 → ℝ → ℝ)
    (hd : ∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l))
    {a p : ℝ} (ha : 0 ≤ a) (hap : a ≤ p) (hp : p ≤ N) :
    0 ≤ graphProfileCoefficient N mass a p ∧ graphProfileCoefficient N mass a p ≤ 1 := by
  have hn (l : Fin 4) : 0 ≤ ((2:ℝ)^N)^(-mass l p) / ((2:ℝ)^N)^(-mass l a) := by positivity
  constructor
  · exact Finset.prod_nonneg (fun l _ => hn l)
  · apply Finset.prod_le_one₀ (fun l _ => hn l)
    intro l _
    apply (div_le_one (by positivity : 0 < ((2:ℝ)^N)^(-mass l a))).mpr
    apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
    have hs := (hd l).slope a p ha hap hp
    linarith [hs.1]

theorem graph_original_outer_le (N : ℕ) {a v : ℝ} (hv : v-a ≤ (N:ℝ)) :
    |(2:ℝ)^(2*(v-a))| ≤ ((2:ℝ)^N)^2 := by
  rw [abs_of_pos (by positivity : 0 < (2:ℝ)^(2*(v-a))),← pow_mul,
    ← Real.rpow_natCast (2:ℝ) (N*2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast
  linarith

end PlanarFalconer

end OAI
