import OAI.MeasureTheory.Falconer.Shells.FilteredShellEndgame
import OAI.MeasureTheory.Falconer.Shells.ShellSummability

namespace OAI

/-! # The monotone original-law endgame with bounds at the same scale -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

private theorem summable_shift_one {f : ℕ → ℝ} (hf : Summable f) :
    Summable (fun n => f (n+1)) := (summable_nat_add_iff 1).mpr hf

theorem positive_volume_of_same_scale_summable {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (hf : Measurable f) (ρ : Measure X) [IsFiniteMeasure ρ]
    (G : ℕ → Set X) (hG : ∀ n, MeasurableSet (G n)) (hmono : Antitone G)
    (D : Set ℝ) (hD : MeasurableSet D) (hcarry : ρ (f ⁻¹' Dᶜ) = 0)
    (hpositive : 0 < ρ (⋂ n, G n)) (τ : ℕ → FiniteMeasure ℝ)
    (herror : Summable (fun N => (PlanarFalconer.variationDistance
      ⟨filteredPushforward f ρ (G N),inferInstance⟩ (τ N)).toReal))
    {γ Cshell : ℝ} (hγ : 0 < γ) (hCshell : 0 < Cshell) (N₀ : ℕ)
    (hshell : ∀ N ≥ N₀, PlanarFalconer.shellEnergy (τ N) N ≤ Cshell*(2:ℝ)^(-γ*(N:ℝ))) :
    0 < volume D := by
  have hpos : 0 < ρ (⋂ n, G (n+1)) := hpositive.trans_le (measure_mono (by
    intro x hx
    exact mem_iInter.mpr (fun n => mem_iInter.mp hx (n+1))))
  apply positive_volume_of_filtered_shells f hf ρ (fun n => G (n+1)) (fun n => hG (n+1))
    (fun n k hnk => hmono (Nat.add_le_add_right hnk 1)) D hD hcarry hpos τ
  · convert summable_shift_one herror using 1
  · exact PlanarFalconer.shellL2Term_norm_summable τ hγ hCshell N₀ hshell

theorem positive_volume_of_same_scale_decay {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (hf : Measurable f) (ρ : Measure X) [IsFiniteMeasure ρ]
    (G : ℕ → Set X) (hG : ∀ n, MeasurableSet (G n)) (hmono : Antitone G)
    (D : Set ℝ) (hD : MeasurableSet D) (hcarry : ρ (f ⁻¹' Dᶜ) = 0)
    (hpositive : 0 < ρ (⋂ n, G n)) (τ : ℕ → FiniteMeasure ℝ)
    {η γ Ctv Cshell : ℝ} (hη : 0 < η) (hγ : 0 < γ) (hCtv : 0 < Ctv) (hCshell : 0 < Cshell)
    (N₀ : ℕ)
    (htv : ∀ N ≥ N₀, PlanarFalconer.variationDistance
      ⟨filteredPushforward f ρ (G N),inferInstance⟩ (τ N) ≤
        ENNReal.ofReal (Ctv*(2:ℝ)^(-η*(N:ℝ))))
    (hshell : ∀ N ≥ N₀, PlanarFalconer.shellEnergy (τ N) N ≤ Cshell*(2:ℝ)^(-γ*(N:ℝ))) :
    0 < volume D := by
  have hpos : 0 < ρ (⋂ n, G (n+1)) := hpositive.trans_le (measure_mono (by
    intro x hx
    exact mem_iInter.mpr (fun n => mem_iInter.mp hx (n+1))))
  apply positive_volume_of_filtered_shells f hf ρ (fun n => G (n+1)) (fun n => hG (n+1))
    (fun n k hnk => hmono (Nat.add_le_add_right hnk 1)) D hD hcarry hpos τ
  · apply ((PlanarFalconer.summable_dyadic_decay hη).mul_left Ctv).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop N₀] with n hn
    rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top (htv (n+1) (by omega))
    rw [ENNReal.toReal_ofReal (by positivity)] at hle
    apply hle.trans
    apply mul_le_mul_of_nonneg_left _ hCtv.le
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    nlinarith
  · exact PlanarFalconer.shellL2Term_norm_summable τ hγ hCshell N₀ hshell

end Falconer

end OAI
