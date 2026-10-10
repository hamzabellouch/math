import OAI.Analysis.MarkovType.MarkovTransport
import OAI.Analysis.MarkovType.FinitelyRepresentable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace MarkovSuperreflexivity

theorem le_of_le_one_add_rpow_mul {A B p : ℝ}
    (h : ∀ η : ℝ, 0 < η → A ≤ Real.rpow (1 + η) p * B) : A ≤ B := by
  have ht : Tendsto (fun k : ℕ => 1 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hr : Tendsto
      (fun k : ℕ => Real.rpow (1 + 1 / ((k : ℝ) + 1)) p * B) atTop (𝓝 B) := by
    simpa only [Function.comp_apply, Real.rpow_eq_pow, Real.one_rpow, one_mul] using
      ((Real.continuousAt_rpow_const 1 p (Or.inl one_ne_zero)).tendsto.comp ht).mul_const B
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds hr
  intro k
  exact h (1 / ((k : ℝ) + 1))
    (div_pos zero_lt_one (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one))

theorem MarkovTypeWith.of_finitelyRepresentable {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {p K : ℝ} (hX : MarkovTypeWith p K X)
    (hYX : FinitelyRepresentable Y X) : MarkovTypeWith p K Y := by
  refine ⟨hX.1, hX.2.1, ?_⟩
  intro m C f n hn
  let E : Submodule ℝ Y := Submodule.span ℝ (Set.range f)
  let : FiniteDimensional ℝ E :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  let fE : Fin m → E := fun i => ⟨f i, Submodule.subset_span (Set.mem_range_self i)⟩
  have hcost : ∀ t, stateCost C fE p t = stateCost C f p t := fun _ => rfl
  apply le_of_le_one_add_rpow_mul
  intro η hη
  obtain ⟨T, hT⟩ := hYX E η hη
  have hlo : ∀ i j, ‖fE j - fE i‖ ≤ (1 : ℝ) * ‖T (fE j) - T (fE i)‖ := by
    intro i j
    simpa only [map_sub, one_mul] using (hT (fE j - fE i)).1
  have hhi : ∀ i j, ‖T (fE j) - T (fE i)‖ ≤ (1 + η) * ‖fE j - fE i‖ := by
    intro i j
    simpa only [map_sub] using (hT (fE j - fE i)).2
  have hkn : 0 ≤ Real.rpow K p * (n : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hX.2.1.le _) (Nat.cast_nonneg _)
  calc
    stateCost C f p n = stateCost C fE p n := (hcost n).symm
    _ ≤ stateCost C (T ∘ fE) p n := by
      simpa only [Real.rpow_eq_pow, Real.one_rpow, one_mul] using
        stateCost_le_mul_of_norm_le C fE (T ∘ fE) hX.1.le zero_le_one hlo n
    _ ≤ Real.rpow K p * (n : ℝ) * stateCost C (T ∘ fE) p 1 :=
      hX.bound C (T ∘ fE) n hn
    _ ≤ Real.rpow K p * (n : ℝ) *
        (Real.rpow (1 + η) p * stateCost C fE p 1) :=
      mul_le_mul_of_nonneg_left
        (stateCost_le_mul_of_norm_le C (T ∘ fE) fE hX.1.le
          (add_pos zero_lt_one hη).le hhi 1) hkn
    _ = Real.rpow (1 + η) p *
        (Real.rpow K p * (n : ℝ) * stateCost C f p 1) := by
      rw [hcost 1]
      ring

theorem HasMarkovType.of_finitelyRepresentable {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {p : ℝ} (hX : HasMarkovType p X) (hYX : FinitelyRepresentable Y X) :
    HasMarkovType p Y := by
  obtain ⟨K, hK⟩ := hX
  exact ⟨K, hK.of_finitelyRepresentable hYX⟩

end MarkovSuperreflexivity

end

end OAI
