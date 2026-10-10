import OAI.Probability.BenjaminiSchramm.Nonunimodular

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq Classical.propDecidable

theorem threeQuarter_sum_le (f : ℤ → ℝ≥0∞) (s : Finset ℤ) :
    (∑ k ∈ s, f k) ^ (3 / 4 : ℝ) ≤ ∑ k ∈ s, f k ^ (3 / 4 : ℝ) := by
  induction s using Finset.induction_on with
  | empty => norm_num
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans
      (add_le_add le_rfl ih)

theorem threeQuarter_tsum_le (f : ℤ → ℝ≥0∞) :
    (∑' k, f k) ^ (3 / 4 : ℝ) ≤ ∑' k, f k ^ (3 / 4 : ℝ) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  change (ENNReal.orderIsoRpow (3 / 4) (by norm_num))
    (⨆ s : Finset ℤ, ∑ k ∈ s, f k) ≤ _
  rw [OrderIso.map_iSup]
  exact iSup_le fun s => (threeQuarter_sum_le f s).trans (ENNReal.sum_le_tsum _)

noncomputable def quarterTiltedClusterMass (G : BondGraph V E) (h : V → ℝ)
    (ω : Set E) (o : V) : ℝ≥0∞ :=
  ∑' x, if Conn G ω o x then ENNReal.ofReal (Real.exp (h x / 4)) else 0

noncomputable def modularLayerCount (G : BondGraph V E) (h : V → ℝ)
    (ω : Set E) (o : V) (k : ℤ) : ℝ≥0∞ :=
  ∑' x : {x : V // ⌊h x⌋ = k}, if Conn G ω o x then 1 else 0

theorem measurable_modularLayerCount [Countable V] [Countable E]
    (G : BondGraph V E) (h : V → ℝ) (o : V) (k : ℤ) :
    Measurable (fun ω => modularLayerCount G h ω o k) := by
  apply Measurable.tsum
  intro x
  exact measurable_const.ite (measurableSet_conn G o x) measurable_const

theorem quarterTiltedClusterMass_le_layers (G : BondGraph V E) (h : V → ℝ)
    (ω : Set E) (o : V) :
    quarterTiltedClusterMass G h ω o ≤
      ∑' k : ℤ, ENNReal.ofReal (Real.exp (((k : ℝ) + 1) / 4)) *
        modularLayerCount G h ω o k := by
  unfold quarterTiltedClusterMass
  rw [← ENNReal.tsum_fiberwise _ (fun x => ⌊h x⌋)]
  apply ENNReal.tsum_le_tsum
  intro k
  rw [modularLayerCount, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hc : Conn G ω o x
  · simp only [hc, ↓reduceIte, mul_one]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hh := Int.lt_floor_add_one (h x)
    have hx : ⌊h (x : V)⌋ = k := x.property
    rw [hx] at hh
    linarith
  · simp [hc]

theorem quarterTiltedClusterMass_threeQuarter_le_layers
    (G : BondGraph V E) (h : V → ℝ) (ω : Set E) (o : V) :
    quarterTiltedClusterMass G h ω o ^ (3 / 4 : ℝ) ≤
      ∑' k : ℤ, ENNReal.ofReal (Real.exp (3 * ((k : ℝ) + 1) / 16)) *
        modularLayerCount G h ω o k ^ (3 / 4 : ℝ) := by
  refine (ENNReal.rpow_le_rpow (quarterTiltedClusterMass_le_layers G h ω o)
    (by norm_num : (0 : ℝ) ≤ 3 / 4)).trans ?_
  apply (threeQuarter_tsum_le _).trans
  apply ENNReal.tsum_le_tsum
  intro k
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have he : ENNReal.ofReal (Real.exp (((k : ℝ) + 1) / 4)) ^ (3 / 4 : ℝ) =
      ENNReal.ofReal (Real.exp (3 * ((k : ℝ) + 1) / 16)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) (by norm_num),
      ← Real.exp_mul]
    congr 2
    ring
  rw [he]

theorem quarterTilted_moment_le_layers [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (h : V → ℝ) (o : V) :
    (∫⁻ ω, quarterTiltedClusterMass G h ω o ^ (3 / 4 : ℝ) ∂law p) ≤
      ∑' k : ℤ, ENNReal.ofReal (Real.exp (3 * ((k : ℝ) + 1) / 16)) *
        ∫⁻ ω, modularLayerCount G h ω o k ^ (3 / 4 : ℝ) ∂law p := by
  have hm (k : ℤ) : Measurable (fun ω => modularLayerCount G h ω o k ^ (3 / 4 : ℝ)) :=
    (ENNReal.continuous_rpow_const (y := (3 / 4 : ℝ))).measurable.comp
      (measurable_modularLayerCount G h o k)
  calc
    _ ≤ ∫⁻ ω, ∑' k : ℤ, ENNReal.ofReal (Real.exp (3 * ((k : ℝ) + 1) / 16)) *
        modularLayerCount G h ω o k ^ (3 / 4 : ℝ) ∂law p :=
      lintegral_mono fun ω => quarterTiltedClusterMass_threeQuarter_le_layers G h ω o
    _ = _ := by
      rw [lintegral_tsum]
      · congr 1
        ext k
        exact lintegral_const_mul _ (hm k)
      · intro k
        exact (measurable_const.mul (hm k)).aemeasurable

theorem quarterTilted_moment_lt_top_of_layer_bounds [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (h : V → ℝ) (o : V)
    (C : ℝ) (hC : 0 ≤ C)
    (hpos : ∀ k : ℤ, 0 ≤ k →
      (∫⁻ ω, modularLayerCount G h ω o k ^ (3 / 4 : ℝ) ∂law p) ≤
        ENNReal.ofReal (C * Real.exp (-(k : ℝ) / 2)))
    (hneg : ∀ k : ℤ, k ≤ 0 →
      (∫⁻ ω, modularLayerCount G h ω o k ^ (3 / 4 : ℝ) ∂law p) ≤
        ENNReal.ofReal (C * Real.exp (-(k : ℝ) / 16))) :
    (∫⁻ ω, quarterTiltedClusterMass G h ω o ^ (3 / 4 : ℝ) ∂law p) < ∞ := by
  let F (k : ℤ) : ℝ := C * Real.exp (3 / 16) * Real.exp (-|(k : ℝ)| / 8)
  have hs : Summable F := by
    apply summable_int_iff_summable_nat_and_neg.mpr
    have hn : Summable (fun n : ℕ => C * Real.exp (3 / 16) *
        Real.exp ((n : ℝ) * (-1 / 8))) :=
      (Real.summable_exp_nat_mul_iff.mpr (by norm_num : (-1 / 8 : ℝ) < 0)).mul_left _
    constructor
    · convert hn using 1
      ext n
      simp only [F, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      congr 2
      ring
    · convert hn using 1
      ext n
      simp only [F, Int.cast_neg, Int.cast_natCast, abs_neg,
        abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      congr 2
      ring
  apply lt_of_le_of_lt (quarterTilted_moment_le_layers G p h o)
  apply lt_of_le_of_lt _ hs.tsum_ofReal_lt_top
  apply ENNReal.tsum_le_tsum
  intro k
  have hk : (0 : ℝ) ≤ k ∨ (k : ℝ) ≤ 0 := le_total 0 _
  rcases hk with hk | hk
  · calc
      _ ≤ ENNReal.ofReal (Real.exp (3 * ((k : ℝ) + 1) / 16)) *
          ENNReal.ofReal (C * Real.exp (-(k : ℝ) / 2)) := by
        gcongr
        exact hpos k (by exact_mod_cast hk)
      _ = ENNReal.ofReal (C * Real.exp (3 / 16) * Real.exp (-(5 * (k : ℝ)) / 16)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
        congr 1
        have he : Real.exp (3 * ((k : ℝ) + 1) / 16) * Real.exp (-(k : ℝ) / 2) =
            Real.exp (3 / 16) * Real.exp (-(5 * (k : ℝ)) / 16) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        calc
          _ = C * (Real.exp (3 * ((k : ℝ) + 1) / 16) *
              Real.exp (-(k : ℝ) / 2)) := by ring
          _ = _ := by rw [he]; ring
      _ ≤ ENNReal.ofReal (F k) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (Real.exp_nonneg _))
        apply Real.exp_le_exp.mpr
        rw [abs_of_nonneg hk]
        linarith
  · calc
      _ ≤ ENNReal.ofReal (Real.exp (3 * ((k : ℝ) + 1) / 16)) *
          ENNReal.ofReal (C * Real.exp (-(k : ℝ) / 16)) := by
        gcongr
        exact hneg k (by exact_mod_cast hk)
      _ = ENNReal.ofReal (C * Real.exp (3 / 16) * Real.exp ((k : ℝ) / 8)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
        congr 1
        have he : Real.exp (3 * ((k : ℝ) + 1) / 16) * Real.exp (-(k : ℝ) / 16) =
            Real.exp (3 / 16) * Real.exp ((k : ℝ) / 8) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        calc
          _ = C * (Real.exp (3 * ((k : ℝ) + 1) / 16) *
              Real.exp (-(k : ℝ) / 16)) := by ring
          _ = _ := by rw [he]; ring
      _ = ENNReal.ofReal (F k) := by simp [F, abs_of_nonpos hk]

end Percolation.BenjaminiSchramm

end OAI
