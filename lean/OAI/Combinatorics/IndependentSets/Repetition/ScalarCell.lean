import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.Supported
import OAI.Combinatorics.IndependentSets.Reduction.SliceDifferenceVariation

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set
open scoped NNReal BigOperators Classical

noncomputable def scalarCell : {m : ℕ} → Cube m → ℝ → ℝ
  | 0, _, y => y
  | _+1, (b,q), y => ((if b then 1 else 0) + scalarCell q y)/2

lemma scalarCell_mem {m : ℕ} (q : Cube m) {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) :
    scalarCell q y ∈ Icc (0:ℝ) 1 := by
  induction m with
  | zero => exact hy
  | succ m ih =>
    obtain ⟨b,q⟩ := q
    have h := ih q
    cases b <;> simp only [scalarCell, Bool.false_eq_true, ↓reduceIte, zero_add] <;>
      constructor <;> linarith [h.1, h.2]

lemma scalarCell_lipschitz {m : ℕ} (q : Cube m) :
    LipschitzWith ((1/2:ℝ≥0)^m) (scalarCell q) := by
  induction m with
  | zero =>
    change LipschitzWith 1 (id : ℝ→ℝ)
    exact LipschitzWith.id
  | succ m ih =>
    obtain ⟨b,q⟩ := q
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := (ih q).dist_le_mul x y
    simp only [Real.dist_eq] at h ⊢
    have he : scalarCell (m:=m+1) (b,q) x - scalarCell (m:=m+1) (b,q) y =
        (scalarCell q x - scalarCell q y)/2 := by dsimp [scalarCell]; ring
    rw [he, abs_div]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2), NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat, pow_succ, NNReal.coe_mul] at ⊢
    norm_num only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at h
    linarith

noncomputable def scalarAvg {m : ℕ} (f : ℝ → ℝ) (q : Cube m) : ℝ :=
  ∫ y in (0:ℝ)..1, f (scalarCell q y)

noncomputable def variation (f : ℝ → ℝ) : ℝ := ∫ y in (0:ℝ)..1, |deriv f y|

noncomputable def halfInput (b : Bool) (y : ℝ) : ℝ := ((if b then 1 else 0)+y)/2

lemma halfInput_lipschitz (b : Bool) : LipschitzWith (1/2) (halfInput b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, halfInput]
  have he : ((if b then 1 else 0)+x)/2 - ((if b then 1 else 0)+y)/2 = (x-y)/2 := by ring
  rw [he, abs_div]
  norm_num
  ring_nf
  exact le_rfl

lemma scalarAvg_cons {m : ℕ} (f : ℝ → ℝ) (b : Bool) (q : Cube m) :
    scalarAvg (m:=m+1) f (b,q) = scalarAvg (f ∘ halfInput b) q := rfl

lemma variation_nonneg (f : ℝ → ℝ) : 0 ≤ variation f :=
  intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => abs_nonneg _)

lemma variation_half_sum {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f) :
    variation (f ∘ halfInput false) + variation (f ∘ halfInput true) = variation f := by
  have hder (b : Bool) (x : ℝ) :
      deriv (f ∘ halfInput b) x = (1/2:ℝ) * deriv f (halfInput b x) := by
    have he : f ∘ halfInput b = (fun y => f (((if b then 1 else 0)+y)/2)) := rfl
    rw [he]
    have he' : (fun y => f (((if b then 1 else 0)+y)/2)) =
        (fun y => (fun z => f ((1/2:ℝ)*z)) ((if b then 1 else 0)+y)) := by
      funext y; congr 1; ring
    rw [he']
    have hadd := deriv_comp_const_add (fun z => f ((1/2:ℝ)*z)) (if b then 1 else 0) x
    rw [hadd, deriv_comp_mul_left, smul_eq_mul]
    congr 2
    dsimp [halfInput]
    ring
  have hv (b : Bool) : variation (f ∘ halfInput b) =
      ∫ y in (if b then (1/2:ℝ) else 0)..(if b then 1 else 1/2), |deriv f y| := by
    simp only [variation, hder, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    rw [intervalIntegral.integral_const_mul]
    have he : (fun y => |deriv f (halfInput b y)|) =
        (fun y => |deriv f (y/2 + (if b then (1/2:ℝ) else 0))|) := by
      funext y
      congr 2
      cases b <;> simp [halfInput]
      ring
    rw [he, intervalIntegral.integral_comp_div_add (fun y => |deriv f y|) (by norm_num : (2:ℝ)≠0)]
    cases b <;> norm_num [smul_eq_mul] <;> ring
  rw [hv, hv]
  have hac : AbsolutelyContinuousOnInterval f 0 1 :=
    hf.lipschitzOnWith.absolutelyContinuousOnInterval
  exact intervalIntegral.integral_add_adjacent_intervals
    (hac.intervalIntegrable_deriv.abs.mono_set (by intro x hx; simp only [Set.mem_uIcc] at *; grind))
    (hac.intervalIntegrable_deriv.abs.mono_set (by intro x hx; simp only [Set.mem_uIcc] at *; grind))

lemma half_integral_sum {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ y in (0:ℝ)..1, f (halfInput false y)) +
    (∫ y in (0:ℝ)..1, f (halfInput true y)) = 2 * ∫ y in (0:ℝ)..1, f y := by
  have he (b : Bool) : (∫ y in (0:ℝ)..1, f (halfInput b y)) =
      2 * ∫ y in (if b then (1/2:ℝ) else 0)..(if b then 1 else 1/2), f y := by
    have hh : (fun y => f (halfInput b y)) =
        (fun y => f (y/2 + (if b then (1/2:ℝ) else 0))) := by
      funext y; congr 1; cases b <;> simp [halfInput]
      ring
    rw [hh, intervalIntegral.integral_comp_div_add f (by norm_num : (2:ℝ)≠0)]
    cases b <;> norm_num [smul_eq_mul]
  rw [he, he]
  simp only [Bool.false_eq_true, ↓reduceIte, ← mul_add]
  rw [intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]

lemma mean_scalarAvg {m : ℕ} {f : ℝ → ℝ} (hf : Continuous f) :
    mean (scalarAvg (m:=m) f) = ∫ y in (0:ℝ)..1, f y := by
  induction m generalizing f with
  | zero => rw [mean_zero]; rfl
  | succ m ih =>
    rw [mean_succ]
    simp only [scalarAvg_cons]
    rw [ih (hf.comp (halfInput_lipschitz false).continuous),
      ih (hf.comp (halfInput_lipschitz true).continuous)]
    have h := half_integral_sum hf
    dsimp [Function.comp_def]
    linarith

lemma scalarAvg_difference {m : ℕ} {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (q r : Cube m) :
    |scalarAvg f q - scalarAvg f r| ≤ variation f := by
  have hqint : IntervalIntegrable (fun y => f (scalarCell q y)) volume 0 1 :=
    (hf.continuous.comp (scalarCell_lipschitz q).continuous).intervalIntegrable _ _
  have hrint : IntervalIntegrable (fun y => f (scalarCell r y)) volume 0 1 :=
    (hf.continuous.comp (scalarCell_lipschitz r).continuous).intervalIntegrable _ _
  rw [scalarAvg, scalarAvg, ← intervalIntegral.integral_sub hqint hrint]
  apply (intervalIntegral.abs_integral_le_integral_abs (by norm_num : (0:ℝ)≤1)).trans
  have hc : Continuous (fun y => |f (scalarCell q y) - f (scalarCell r y)|) := by
    exact ((hf.continuous.comp (scalarCell_lipschitz q).continuous).sub
      (hf.continuous.comp (scalarCell_lipschitz r).continuous)).abs
  have hle : (∫ y in (0:ℝ)..1, |f (scalarCell q y) - f (scalarCell r y)|) ≤
      ∫ _y in (0:ℝ)..1, variation f := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hc.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
    intro y hy
    have hq := scalarCell_mem q hy
    have hr := scalarCell_mem r hy
    rcases le_total (scalarCell q y) (scalarCell r y) with h | h
    · rw [abs_sub_comm]
      exact CubeGradient.slice_difference_le_variation hf hq.1 h hr.2
    · exact CubeGradient.slice_difference_le_variation hf hr.1 h hq.2
  simpa using hle

lemma influence_succ {m : ℕ} (f : Cube (m+1) → ℝ) (i : Fin m) :
    influence f i.succ =
      (influence (fun q => f (false,q)) i + influence (fun q => f (true,q)) i)/2 := by
  rw [influence, mean_succ]
  rfl

theorem dyadic_total_influence {m : ℕ} {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) :
    (∑ i, influence (scalarAvg (m:=m) f) i) ≤ variation f := by
  induction m generalizing L f with
  | zero => simpa using variation_nonneg f
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    have hhead : influence (scalarAvg (m:=m+1) f) 0 ≤ variation f / 2 := by
      apply (mean_mono (fun x => ?_)).trans_eq
        (show mean (fun _ : Cube (m+1) => variation f / 2) = variation f / 2 by simp [mean])
      change |(scalarAvg f x - scalarAvg f (flip 0 x))/2| ≤ variation f/2
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
      exact div_le_div_of_nonneg_right (scalarAvg_difference hf _ _) (by norm_num)
    have ht : (∑ i : Fin m, influence (scalarAvg (m:=m+1) f) i.succ) =
        ((∑ i : Fin m, influence (scalarAvg (m:=m) (f ∘ halfInput false)) i) +
         (∑ i : Fin m, influence (scalarAvg (m:=m) (f ∘ halfInput true)) i))/2 := by
      simp only [influence_succ, scalarAvg_cons]
      change (∑ i : Fin m, (influence (scalarAvg (m:=m) (f ∘ halfInput false)) i +
        influence (scalarAvg (m:=m) (f ∘ halfInput true)) i)/2) = _
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    rw [ht]
    have h0 := ih (hf.comp (halfInput_lipschitz false))
    have h1 := ih (hf.comp (halfInput_lipschitz true))
    have hv := variation_half_sum hf
    linarith

end LargeIndependentSets.BooleanJunta

end OAI
