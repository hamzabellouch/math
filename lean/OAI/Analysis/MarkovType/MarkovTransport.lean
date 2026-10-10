import OAI.Analysis.MarkovType.FiniteChains
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace FiniteReversibleChain

def reindex {S T : Type*} [Fintype S] [Fintype T]
    (C : FiniteReversibleChain S) (e : T ≃ S) : FiniteReversibleChain T where
  π t := C.π (e t)
  P t u := C.P (e t) (e u)
  π_nonneg t := C.π_nonneg (e t)
  sum_π := (e.sum_comp C.π).trans C.sum_π
  P_nonneg t u := C.P_nonneg (e t) (e u)
  sum_P t := (e.sum_comp (C.P (e t))).trans (C.sum_P (e t))
  balance t u := C.balance (e t) (e u)

end FiniteReversibleChain

theorem stateCost_reindex {S T X : Type*} [Fintype S] [Fintype T]
    [NormedAddCommGroup X] (C : FiniteReversibleChain S) (e : T ≃ S)
    (f : S → X) (p : ℝ) (n : ℕ) :
    stateCost (C.reindex e) (f ∘ e) p n = stateCost C f p n := by
  let ePath : StatePath T n ≃ StatePath S n := Equiv.piCongrRight (fun _ => e)
  let G : StatePath S n → ℝ := fun ω =>
    pathWeight C n ω * Real.rpow (‖f (ω (Fin.last n)) - f (ω 0)‖) p
  change (∑ ω : StatePath T n, G (ePath ω)) = ∑ ω : StatePath S n, G ω
  exact ePath.sum_comp G

theorem MarkovTypeWith.bound {X S : Type*} [NormedAddCommGroup X] [Fintype S]
    {p K : ℝ} (hX : MarkovTypeWith p K X) (C : FiniteReversibleChain S)
    (f : S → X) (n : ℕ) (hn : 1 ≤ n) :
    stateCost C f p n ≤ Real.rpow K p * (n : ℝ) * stateCost C f p 1 := by
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  have h := hX.2.2 (Fintype.card S) (C.reindex e) (f ∘ e) n hn
  simpa only [stateCost_reindex] using h

theorem stateCost_le_mul_of_norm_le {S X Y : Type*} [Fintype S]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (C : FiniteReversibleChain S) (f : S → X) (g : S → Y)
    {p c : ℝ} (hp : 0 ≤ p) (hc : 0 ≤ c)
    (hfg : ∀ i j, ‖f j - f i‖ ≤ c * ‖g j - g i‖) (n : ℕ) :
    stateCost C f p n ≤ Real.rpow c p * stateCost C g p n := by
  calc
    stateCost C f p n ≤
        ∑ ω : StatePath S n, pathWeight C n ω *
          (Real.rpow c p * Real.rpow (‖g (ω (Fin.last n)) - g (ω 0)‖) p) := by
      apply Finset.sum_le_sum
      intro ω _
      apply mul_le_mul_of_nonneg_left _ (pathWeight_nonneg C n ω)
      calc
        Real.rpow (‖f (ω (Fin.last n)) - f (ω 0)‖) p ≤
            Real.rpow (c * ‖g (ω (Fin.last n)) - g (ω 0)‖) p :=
          Real.rpow_le_rpow (norm_nonneg _) (hfg _ _) hp
        _ = Real.rpow c p * Real.rpow (‖g (ω (Fin.last n)) - g (ω 0)‖) p :=
          Real.mul_rpow hc (norm_nonneg _)
    _ = Real.rpow c p * stateCost C g p n := by
      simp only [stateCost, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring

theorem MarkovTypeWith.of_distortion_map {X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] {p K a b : ℝ}
    (hX : MarkovTypeWith p K X) (T : Y → X) (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ y z, a * ‖y - z‖ ≤ ‖T y - T z‖)
    (hupper : ∀ y z, ‖T y - T z‖ ≤ b * ‖y - z‖) :
    MarkovTypeWith p ((b / a) * K) Y := by
  refine ⟨hX.1, mul_pos (div_pos hb ha) hX.2.1, ?_⟩
  intro m C f n hn
  have hInv : 0 ≤ a⁻¹ := (inv_pos.mpr ha).le
  have hlo : ∀ i j, ‖f j - f i‖ ≤ a⁻¹ * ‖T (f j) - T (f i)‖ := by
    intro i j
    have h := mul_le_mul_of_nonneg_left (hlower (f j) (f i)) hInv
    simpa only [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] using h
  have hhi : ∀ i j, ‖T (f j) - T (f i)‖ ≤ b * ‖f j - f i‖ :=
    fun i j => hupper (f j) (f i)
  have hkn : 0 ≤ Real.rpow K p * (n : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hX.2.1.le _) (Nat.cast_nonneg _)
  calc
    stateCost C f p n ≤ Real.rpow (a⁻¹) p * stateCost C (T ∘ f) p n :=
      stateCost_le_mul_of_norm_le C f (T ∘ f) hX.1.le hInv hlo n
    _ ≤ Real.rpow (a⁻¹) p *
        (Real.rpow K p * (n : ℝ) * stateCost C (T ∘ f) p 1) :=
      mul_le_mul_of_nonneg_left (hX.bound C (T ∘ f) n hn)
        (Real.rpow_nonneg hInv _)
    _ ≤ Real.rpow (a⁻¹) p *
        (Real.rpow K p * (n : ℝ) * (Real.rpow b p * stateCost C f p 1)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hInv _)
      exact mul_le_mul_of_nonneg_left
        (stateCost_le_mul_of_norm_le C (T ∘ f) f hX.1.le hb.le hhi 1) hkn
    _ = Real.rpow ((b / a) * K) p * (n : ℝ) * stateCost C f p 1 := by
      simp only [Real.rpow_eq_pow]
      rw [Real.mul_rpow (div_pos hb ha).le hX.2.1.le,
        div_eq_mul_inv b a, Real.mul_rpow hb.le hInv]
      ring

end MarkovSuperreflexivity

end

end OAI
