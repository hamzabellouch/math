import OAI.Probability.BenjaminiSchramm.GhostVolume

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem volume_probability_aut [Countable E] (G : BondGraph V E) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) (n : ℕ) :
    law p (volumeEvent G (a x) n) = law p (volumeEvent G x n) := by
  have he : volumeEvent G (a x) n =
      (fun ω => b ⁻¹' ω) ⁻¹' volumeEvent G x n := by
    ext ω
    change (n : ℕ∞) ≤ (cluster G ω (a x)).encard ↔
      (n : ℕ∞) ≤ (cluster G (b ⁻¹' ω) x).encard
    rw [←cluster_aut G hab,a.injective.encard_image]
  rw [he,←Measure.map_apply (measurable_set_preimage b)
    (measurableSet_volumeEvent G x n),law_map_preimage_equiv]

theorem uniform_critical_volume_upper [Countable E]
    (G : BondGraph V E) (hqt : QuasiTransitive G)
    (hvol : ∀ x, ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      criticalTail G (volumeEvent G) x n ≤ C / Real.sqrt n) :
    ∃ C : ℝ, 0 < C ∧ ∀ x n, 0 < n →
      criticalTail G (volumeEvent G) x n ≤ C / Real.sqrt n := by
  obtain ⟨O,hO⟩ := hqt
  choose c hc hb using hvol
  let C := 1 + ∑ o ∈ O, c o
  have hC : 0 < C := by
    have hs := Finset.sum_nonneg (s := O) (fun o _ => (hc o).le)
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro x n hn
  obtain ⟨o,ho,a,b,hab,rfl⟩ := hO x
  have he : criticalTail G (volumeEvent G) (a o) n =
      criticalTail G (volumeEvent G) o n := by
    unfold criticalTail
    rw [volume_probability_aut G (pc G) hab]
  rw [he]
  apply (hb o n hn).trans
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hs := Finset.single_le_sum (s := O) (fun z _ => (hc z).le) ho
  dsimp [C]
  linarith

theorem uniform_critical_volume_upper_of_powerTail [Countable E]
    (G : BondGraph V E) (hqt : QuasiTransitive G)
    (hvol : ∀ x, PowerTail (criticalTail G (volumeEvent G) x) (1 / 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x n, 0 < n →
      criticalTail G (volumeEvent G) x n ≤ C / Real.sqrt n := by
  apply uniform_critical_volume_upper G hqt
  intro x
  obtain ⟨c,C,_hc,hC,hb⟩ := hvol x
  refine ⟨C,hC,?_⟩
  intro n hn
  have hh := (hb n hn).2
  rw [Real.rpow_neg (Nat.cast_nonneg n),←Real.sqrt_eq_rpow] at hh
  simpa only [div_eq_mul_inv] using hh

theorem critical_ghost_bound_at_square_scale [Countable E]
    (G : BondGraph V E) (C : ℝ) (hC : 0 ≤ C)
    (hvol : ∀ x n, 0 < n → criticalTail G (volumeEvent G) x n ≤ C / Real.sqrt n)
    (Q : Finset E) (x : V) (p h : unitInterval) (hp : p ≤ pc G)
    (m : ℕ) (hm : 0 < m) (hh : (h : ℝ) * (m : ℝ) ^ 2 ≤ 1) :
    markedConnectionPolynomial G Q x h p ≤ 3 * C / m := by
  exact markedConnection_le_sqrt_scale G Q x p h m hm C hC hh
    (fun n hn => (finiteClusterTail_le_criticalTail G Q x n p hp).trans (hvol x n hn))

end Percolation.BenjaminiSchramm

end OAI
