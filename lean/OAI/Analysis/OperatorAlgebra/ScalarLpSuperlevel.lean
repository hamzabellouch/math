import OAI.Analysis.OperatorAlgebra.ScalarLpContinuousCutoffs

namespace OAI

/-! Superlevel spectral projections of cosine multipliers belong to the
strong commutant of every operator commuting with the character group.
The projections here are the actual indicator multipliers on scalar L². -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace WeakPureInfiniteness

def realUpperCutoff (c : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  max 0 (min 1 (1 + (n : ℝ) * (x - c)))

lemma realUpperCutoff_continuous (c : ℝ) (n : ℕ) :
    Continuous (realUpperCutoff c n) := by unfold realUpperCutoff; fun_prop

lemma realUpperCutoff_nonneg (c : ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ realUpperCutoff c n x := le_max_left _ _

lemma realUpperCutoff_le_one (c : ℝ) (n : ℕ) (x : ℝ) :
    realUpperCutoff c n x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma realUpperCutoff_eventually (c x : ℝ) :
    ∀ᶠ n : ℕ in atTop, realUpperCutoff c n x = if c ≤ x then 1 else 0 := by
  by_cases hcx : c ≤ x
  · filter_upwards [] with n
    have hn : 0 ≤ (n : ℝ) * (x - c) :=
      mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hcx)
    have h : 1 ≤ 1 + (n : ℝ) * (x - c) := by linarith
    simp only [realUpperCutoff, ite_eq_left hcx, min_eq_left h, max_eq_right zero_le_one]
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / (c - x))
    filter_upwards [eventually_ge_atTop N] with n hn
    have hp : 0 < c - x := sub_pos.mpr (lt_of_not_ge hcx)
    have hn' : 1 / (c - x) < (n : ℝ) := hN.trans_le (by exact_mod_cast hn)
    have hm : 1 < (n : ℝ) * (c - x) := (div_lt_iff₀ hp).mp hn'
    have hz : 1 + (n : ℝ) * (x - c) ≤ 0 := by nlinarith
    have hmz : min 1 (1 + (n : ℝ) * (x - c)) ≤ 0 := (min_le_right _ _).trans hz
    simp only [realUpperCutoff, ite_eq_right hcx, max_eq_left hmz]

def scalarCosineSuperlevel (r c : ℝ) : Set ℝ := {t | c ≤ Real.cos (r * t)}

lemma scalarCosineSuperlevel_measurable (r c : ℝ) :
    MeasurableSet (scalarCosineSuperlevel r c) :=
  measurableSet_le measurable_const (by fun_prop)

def scalarCosineSuperlevelProjection (r c : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  scalarLpProjection volume (scalarCosineSuperlevel r c)
    (scalarCosineSuperlevel_measurable r c)

lemma scalarCosineSuperlevel_strong (r c : ℝ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun n => scalarLpRepresentation volume
      (cfc (realUpperCutoff c n) (scalarCosine r)) f) atTop
      (𝓝 (scalarCosineSuperlevelProjection r c f)) := by
  let s := scalarCosineSuperlevel r c
  have hs : MeasurableSet s := scalarCosineSuperlevel_measurable r c
  let a : ℝ → ℂ := s.indicator (fun _ => 1)
  have ha : AEStronglyMeasurable a volume :=
    (measurable_const.indicator hs).aestronglyMeasurable
  have han (t : ℝ) : ‖a t‖ ≤ 1 := by
    dsimp only [a]
    by_cases ht : t ∈ s <;> simp [ht]
  have hbn (n : ℕ) (t : ℝ) :
      ‖cfc (realUpperCutoff c n) (scalarCosine r) t‖ ≤ 1 := by
    rw [scalarCosine_cfc_apply r t _ (realUpperCutoff_continuous c n)]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (realUpperCutoff_nonneg c n _)]
    exact realUpperCutoff_le_one c n _
  have hlim (t : ℝ) : Tendsto
      (fun n => cfc (realUpperCutoff c n) (scalarCosine r) t) atTop (𝓝 (a t)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [realUpperCutoff_eventually c (Real.cos (r * t))] with n hn
    rw [scalarCosine_cfc_apply r t _ (realUpperCutoff_continuous c n), hn]
    by_cases ht : c ≤ Real.cos (r * t) <;> simp [a, s, scalarCosineSuperlevel, ht]
  have h := scalarLpRepresentation_strong
    (fun n => cfc (realUpperCutoff c n) (scalarCosine r)) a ha 1 zero_le_one hbn han hlim f
  have heq : boundedScalarLp volume a ha 1 han = scalarCosineSuperlevelProjection r c := by
    apply ContinuousLinearMap.ext
    intro g
    apply Lp.ext
    filter_upwards [boundedScalarLp_ae volume a ha 1 han g,
      scalarLpProjection_ae volume s hs g] with t hb hp
    change (scalarCosineSuperlevelProjection r c g) t = s.indicator (g : ℝ → ℂ) t at hp
    rw [hb, hp]
    by_cases ht : t ∈ s <;> simp [a, ht]
  simpa only [heq] using h

lemma scalarLp_commute_cosine_superlevel
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hc : ∀ s, Commute T
      (modularDualUnitary (H := ℂ) volume s : Lp ℂ 2 volume →L[ℂ] Lp ℂ 2 volume))
    (r c : ℝ) : Commute T (scalarCosineSuperlevelProjection r c) :=
  commute_of_strong_limit T (scalarCosineSuperlevelProjection r c)
    (fun n => scalarLpRepresentation volume (cfc (realUpperCutoff c n) (scalarCosine r)))
    (fun n => scalarLp_commute_cosine_cfc T hc r _ (realUpperCutoff_continuous c n))
    (scalarCosineSuperlevel_strong r c)

end WeakPureInfiniteness

end

end OAI
