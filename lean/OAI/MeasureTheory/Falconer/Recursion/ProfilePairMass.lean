import OAI.MeasureTheory.Falconer.Recursion.ProfileNear

namespace OAI

/-! # The original pair mass in its exact profile normalization -/

namespace Falconer
open Set MeasureTheory

theorem regularized_pair_model_mass {d : ℕ} (Q : DyadicCube d) (ρ : Measure (Space d))
    {profile : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam profile)
    {a : ℕ} (ha : a ≤ N) (X Y : List (Fin d → Bool))
    (hX : X.length = a) (hY : Y.length = a) :
    |(profileModelMass profile N a)⁻¹*(profileModelMass profile N a)⁻¹| *
      ((ρ.restrict (Q.descendant X).carrier).prod
        (ρ.restrict (Q.descendant Y).carrier)).real univ ≤
      ((2:ℝ)^N)^(2*((d:ℝ)+1)*lam) := by
  let := hreg.probability
  have hR : 0 < (2:ℝ)^N := by positivity
  have hM : 0 < profileModelMass profile N a := by unfold profileModelMass; positivity
  have hm (Z : List (Fin d → Bool)) (hZ : Z.length = a) :
      (ρ.restrict (Q.descendant Z).carrier).real univ/profileModelMass profile N a ≤
        ((2:ℝ)^N)^(((d:ℝ)+1)*lam) := by
    rw [measureReal_def,Measure.restrict_apply_univ]
    apply (div_le_iff₀ hM).mpr
    exact (hreg.cell_mass_upper ha Z hZ).trans_eq
      (by rw [profileModelMass,← Real.rpow_add hR]; rfl)
  have hp : ((ρ.restrict (Q.descendant X).carrier).prod
      (ρ.restrict (Q.descendant Y).carrier)).real univ =
      (ρ.restrict (Q.descendant X).carrier).real univ *
        (ρ.restrict (Q.descendant Y).carrier).real univ := by
    simp only [measureReal_def,← univ_prod_univ,Measure.prod_prod,ENNReal.toReal_mul]
  rw [hp,abs_of_pos (mul_pos (inv_pos.mpr hM) (inv_pos.mpr hM))]
  calc
    _ = ((ρ.restrict (Q.descendant X).carrier).real univ/profileModelMass profile N a)*
        ((ρ.restrict (Q.descendant Y).carrier).real univ/profileModelMass profile N a) := by ring
    _ ≤ ((2:ℝ)^N)^(((d:ℝ)+1)*lam)*((2:ℝ)^N)^(((d:ℝ)+1)*lam) :=
      mul_le_mul (hm X hX) (hm Y hY) (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring

end Falconer

end OAI
