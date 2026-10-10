import OAI.Probability.BenjaminiSchramm.GhostCritical

namespace OAI

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem volume_threshold_le_clusterMass (G : BondGraph V E) (ω : Set E)
    (x : V) (n : ℕ) (hn : ω ∈ volumeEvent G x n) :
    (n : ℝ≥0∞) ≤ clusterMass G ω x := by
  rw [volumeEvent_eq_clusterLarge] at hn
  obtain ⟨F,hF,hsub⟩ := hn
  have he : (∑ y ∈ F, if Conn G ω x y then (1 : ℝ≥0∞) else 0) = F.card := by
    calc
      _ = ∑ _y ∈ F, (1 : ℝ≥0∞) :=
        Finset.sum_congr rfl (fun y hy => ite_eq_left (hsub y hy))
      _ = _ := by simp
  calc
    (n : ℝ≥0∞) ≤ F.card := by exact_mod_cast hF
    _ = ∑ y ∈ F, if Conn G ω x y then (1 : ℝ≥0∞) else 0 := he.symm
    _ ≤ clusterMass G ω x := ENNReal.sum_le_tsum F

theorem volume_probability_times_threshold_le_mass [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x : V) (n : ℕ) :
    (n : ℝ≥0∞) * law p (volumeEvent G x n) ≤
      ∑' y, law p {ω | Conn G ω x y} := by
  rw [←lintegral_clusterMass]
  rw [←lintegral_indicator_const (measurableSet_volumeEvent G x n) (n : ℝ≥0∞)]
  apply lintegral_mono
  intro ω
  by_cases hn : ω ∈ volumeEvent G x n
  · rw [Set.indicator_of_mem hn]
    exact volume_threshold_le_clusterMass G ω x n hn
  · rw [Set.indicator_of_notMem hn]
    exact bot_le

theorem critical_mass_expectation_top_of_volume_lower [Countable V] [Countable E]
    (G : BondGraph V E) (x : V)
    (hvol : PowerTail (criticalTail G (volumeEvent G) x) (1 / 2)) :
    (∑' y, law (pc G) {ω | Conn G ω x y}) = ⊤ := by
  obtain ⟨c,C,hc,_hC,hb⟩ := hvol
  by_contra htop
  let R := (∑' y, law (pc G) {ω | Conn G ω x y}).toReal
  obtain ⟨m,hm⟩ := exists_nat_gt (max 0 (R / c))
  have hmR : 0 < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have hm0 : 0 < m := by exact_mod_cast hmR
  have hcm : R < c * m := by
    have hh := (le_max_right 0 (R / c)).trans_lt hm
    exact (div_lt_iff₀ hc).mp hh |>.trans_eq (mul_comm _ _)
  have hlower := (hb (m ^ 2) (pow_pos hm0 _)).1
  rw [Real.rpow_neg (Nat.cast_nonneg _),←Real.sqrt_eq_rpow,Nat.cast_pow,
    Real.sqrt_sq hmR.le] at hlower
  have hupp := ENNReal.toReal_mono htop
    (volume_probability_times_threshold_le_mass G (pc G) x (m ^ 2))
  rw [ENNReal.toReal_mul,ENNReal.toReal_natCast] at hupp
  have htail : criticalTail G (volumeEvent G) x (m ^ 2) =
      (law (pc G) (volumeEvent G x (m ^ 2))).toReal := rfl
  rw [←htail,Nat.cast_pow] at hupp
  have hl := mul_le_mul_of_nonneg_left hlower (sq_nonneg (m : ℝ))
  have hid : (m : ℝ) ^ 2 * (c * (m : ℝ)⁻¹) = c * m := by
    field_simp
  rw [hid] at hl
  exact (not_lt_of_ge (hl.trans hupp)) hcm

theorem susceptibility_unbounded_below_critical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hpc0 : 0 < pc G) (x : V)
    (hvol : PowerTail (criticalTail G (volumeEvent G) x) (1 / 2))
    (a : unitInterval) (ha : a < pc G) (B : ℝ) :
    ∃ p : unitInterval, a ≤ p ∧ p < pc G ∧ B < susceptibility G p x := by
  by_contra! hbound
  obtain ⟨p,hp,hpcrit,hlim⟩ := exists_seq_strictMono_tendsto' hpc0
  have hpa : ∀ᶠ n in atTop, a ≤ p n :=
    (tendsto_order.mp hlim).1 a ha |>.mono (fun _ h => h.le)
  have hrow (F : Finset V) : ∑ y ∈ F, twoPoint G (pc G) x y ≤ B := by
    apply le_of_tendsto (tendsto_finsetSum F (fun y _ =>
      twoPoint_tendsto_of_monotone G p hp.monotone (pc G)
        (fun n => (hpcrit n).2.le) hlim x y))
    filter_upwards [hpa] with n hn
    exact ((summable_twoPoint_subcritical G hloc hqt (p n) (hpcrit n).2 x).sum_le_tsum F
      (fun y _ => twoPoint_nonneg G (p n) x y)).trans
      (hbound (p n) hn (hpcrit n).2)
  have hs := summable_of_sum_le (twoPoint_nonneg G (pc G) x) hrow
  have he : ENNReal.ofReal (susceptibility G (pc G) x) =
      ∑' y, law (pc G) {ω | Conn G ω x y} := by
    rw [susceptibility,ENNReal.ofReal_tsum_of_nonneg (twoPoint_nonneg G (pc G) x) hs]
    apply tsum_congr
    intro y
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [critical_mass_expectation_top_of_volume_lower G x hvol] at he
  exact ENNReal.ofReal_ne_top he

end Percolation.BenjaminiSchramm

end OAI
