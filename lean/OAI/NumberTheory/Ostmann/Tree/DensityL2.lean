import OAI.NumberTheory.Ostmann.Tree.DensityDomination
import OAI.NumberTheory.Ostmann.Tree.UnitSums

namespace OAI

namespace Ostmann.Tree.Density
noncomputable section
open scoped BigOperators
local instance {F : Type*} [Field F] : DecidableEq F := Classical.decEq F
variable {p : ℕ} [Fact p.Prime]

theorem unit_second_moment_le (hp : 3 ≤ p) (g : ZMod p → ℂ)
    (hg : Ostmann.FiniteField.l2Sq g ≤ 1) :
    average (fun u : (ZMod p)ˣ => ‖g u‖^2) ≤ 3/2 := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<3) hp)
  have hs : (∑ x, ‖g x‖^2) ≤ (p : ℝ) := by
    calc
      _ = (p : ℝ) * Ostmann.FiniteField.l2Sq g := by
        unfold Ostmann.FiniteField.l2Sq
        rw [← mul_assoc, mul_inv_cancel₀ hp0.ne', one_mul]
      _ ≤ (p : ℝ) * 1 := mul_le_mul_of_nonneg_left hg hp0.le
      _ = _ := mul_one _
  have hu := (Ostmann.FiniteField.sum_units_le (fun x : ZMod p => ‖g x‖^2)
    (fun x => sq_nonneg _)).trans hs
  have hcard : (Fintype.card (ZMod p)ˣ : ℝ) = (p : ℝ)-1 := by
    rw [ZMod.card_units, Nat.cast_sub (by omega), Nat.cast_one]
  unfold average
  rw [hcard]
  have hp3 : (3:ℝ) ≤ p := by exact_mod_cast hp
  have hden : 0 < (p:ℝ)-1 := by linarith
  calc
    _ ≤ ((p:ℝ)-1)⁻¹ * p := mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hden.le)
    _ ≤ 3/2 := by rw [inv_mul_eq_div]; apply (div_le_iff₀ hden).mpr; linarith

theorem diagram_average_norm_sq {F : Type*} [Field F] [Fintype F]
    {d : ℕ} (T : Diagram F d) (g : F → ℂ) :
    average (fun M => ‖T.value g M‖^2) =
      average (fun M => integrate (weight g) (diagramArguments T M)) := by
  congr 1
  funext M
  rw [diagram_value_norm_sq]
  cases diagramArguments T M <;> rfl

theorem diagram_moment_domination {F : Type*} [Field F] [Fintype F]
    {d : ℕ} (T : Diagram F d) (g : F → ℂ) :
    average (fun M => ‖T.value g M‖^2) ≤
      ((2^(2^d-1) : ℕ) : ℝ) * (average (fun u : Fˣ => ‖g u‖^2))^(2^d) := by
  rw [diagram_average_norm_sq]
  have hweight : ∀ y : Leaves d → Fˣ, 0 ≤ weight g y := by
    intro y
    exact Finset.prod_nonneg (fun _ _ => sq_nonneg _)
  have hdom := diagram_domination T (weight g) hweight
  rw [average_weight] at hdom
  exact hdom

theorem density_power_bound (d : ℕ) (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 3/2) :
    ((2^(2^d-1) : ℕ) : ℝ) * a^(2^d) ≤ (3:ℝ)^(2^d) := by
  have hmult : ((2^(2^d-1) : ℕ) : ℝ) ≤ (2:ℝ)^(2^d) := by
    norm_cast
    exact Nat.pow_le_pow_right (by decide : 0<2) (Nat.sub_le _ _)
  calc
    _ ≤ (2:ℝ)^(2^d) * (3/2)^(2^d) :=
      mul_le_mul hmult (pow_le_pow_left₀ ha0 ha _) (pow_nonneg ha0 _) (by positivity)
    _ = (3:ℝ)^(2^d) := by rw [← mul_pow]; norm_num


theorem diagram_l2_bound {d : ℕ} (T : Diagram (ZMod p) d) (hp : 3 ≤ p)
    (g : ZMod p → ℂ) (hg : Ostmann.FiniteField.l2Sq g ≤ 1) :
    average (fun M => ‖T.value g M‖^2) ≤ (3:ℝ)^(2^d) := by
  have hu := unit_second_moment_le hp g hg
  have hu0 : 0 ≤ average (fun u : (ZMod p)ˣ => ‖g u‖^2) := by
    unfold average
    positivity
  have h₁ := diagram_moment_domination (F := ZMod p) (d := d) T g
  have h₂ : ((2^(2^d-1) : ℕ) : ℝ) *
      (average (fun u : (ZMod p)ˣ => ‖g u‖^2))^(2^d) ≤ (3:ℝ)^(2^d) :=
    density_power_bound d (average (fun u : (ZMod p)ˣ => ‖g u‖^2)) hu0 hu
  have havg {A : Type} (i j : Fintype A) (f : A → ℝ) :
      @average A i f = @average A j f := by
    congr
    exact Subsingleton.elim _ _
  simp only [havg _ (inferInstance : Fintype (Leaves d → (ZMod p)ˣ)),
    havg _ (inferInstance : Fintype (ZMod p)ˣ)] at h₁
  exact le_trans h₁ h₂

end
end Ostmann.Tree.Density

end OAI
