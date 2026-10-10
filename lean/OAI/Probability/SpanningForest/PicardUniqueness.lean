import OAI.Probability.SpanningForest.PicardBounds
import OAI.Probability.SpanningForest.Picard

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace Problem336.DeterministicDecoder

@[simp] theorem picardBound_zero (L t : ℝ) : picardBound L t 0 = t := by
  simp [picardBound]

theorem integral_picardBound (L t : ℝ) (n : ℕ) :
    (∫ s in (0 : ℝ)..t, L * picardBound L s n) = picardBound L t (n + 1) := by
  exact Picard.integral_majorant L t n

def BoundedDifferenceResponse {I : Type*}
    (b : ℝ → (I → ℝ) → I → ℝ) (L : ℝ) : Prop :=
  ∀ t, 0 ≤ t → ∀ y y' : I → ℝ, ∀ d : ℝ, 0 ≤ d →
    (∀ i, |y i - y' i| ≤ d) → ∀ i, |b t y i - b t y' i| ≤ L * d

theorem solution_picard_bound {I : Type*} (L : ℝ) (hL : 0 ≤ L)
    (b : ℝ → (I → ℝ) → I → ℝ) (z : ℕ → ℝ → I → ℝ)
    (x : ℝ → I → ℝ)
    (hb : ∀ t, 0 ≤ t → ∀ y i, |b t y i| ≤ 1)
    (hlip : BoundedDifferenceResponse b L)
    (hint : ∀ n t, 0 ≤ t → ∀ i,
      IntervalIntegrable (fun s => b s (z n s) i) volume 0 t)
    (hxint : ∀ t, 0 ≤ t → ∀ i,
      IntervalIntegrable (fun s => b s (x s) i) volume 0 t)
    (hstep : ∀ n t i,
      z (n + 1) t i = z 0 t i + ∫ s in (0 : ℝ)..t, b s (z n s) i)
    (hsol : ∀ t, 0 ≤ t → ∀ i,
      x t i = z 0 t i + ∫ s in (0 : ℝ)..t, b s (x s) i) :
    ∀ n t, 0 ≤ t → ∀ i,
      |x t i - z n t i| ≤ picardBound L t n := by
  intro n
  induction n with
  | zero =>
      intro t ht i
      rw [hsol t ht, add_sub_cancel_left, picardBound_zero, ← Real.norm_eq_abs]
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := t) (C := (1 : ℝ))
        (f := fun s => b s (x s) i) (fun s hs => by
          rw [uIoc_of_le ht] at hs
          exact (Real.norm_eq_abs _).le.trans (hb s hs.1.le _ i))
      simpa only [sub_zero, abs_of_nonneg ht, one_mul] using h
  | succ n ih =>
      intro t ht i
      rw [hsol t ht, hstep n, add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub (hxint t ht i) (hint n t ht i),
        ← Real.norm_eq_abs]
      calc
        ‖∫ s in (0 : ℝ)..t, b s (x s) i - b s (z n s) i‖
            ≤ ∫ s in (0 : ℝ)..t, L * picardBound L s n := by
          apply intervalIntegral.norm_integral_le_of_norm_le ht
          · apply Filter.Eventually.of_forall
            intro s hs
            rw [Real.norm_eq_abs]
            exact hlip s hs.1.le _ _ _ (picardBound_nonneg hL hs.1.le n)
              (ih s hs.1.le) i
          · exact (show Continuous (fun s => L * picardBound L s n) by
              unfold picardBound
              fun_prop).intervalIntegrable _ _
        _ = picardBound L t (n + 1) := integral_picardBound L t n

theorem integral_solution_unique {I : Type*} (L : ℝ) (hL : 0 ≤ L)
    (b : ℝ → (I → ℝ) → I → ℝ) (z : ℕ → ℝ → I → ℝ)
    (x y : ℝ → I → ℝ)
    (hb : ∀ t, 0 ≤ t → ∀ u i, |b t u i| ≤ 1)
    (hlip : BoundedDifferenceResponse b L)
    (hint : ∀ n t, 0 ≤ t → ∀ i,
      IntervalIntegrable (fun s => b s (z n s) i) volume 0 t)
    (hxint : ∀ t, 0 ≤ t → ∀ i,
      IntervalIntegrable (fun s => b s (x s) i) volume 0 t)
    (hyint : ∀ t, 0 ≤ t → ∀ i,
      IntervalIntegrable (fun s => b s (y s) i) volume 0 t)
    (hstep : ∀ n t i,
      z (n + 1) t i = z 0 t i + ∫ s in (0 : ℝ)..t, b s (z n s) i)
    (hx : ∀ t, 0 ≤ t → ∀ i,
      x t i = z 0 t i + ∫ s in (0 : ℝ)..t, b s (x s) i)
    (hy : ∀ t, 0 ≤ t → ∀ i,
      y t i = z 0 t i + ∫ s in (0 : ℝ)..t, b s (y s) i) :
    ∀ t, 0 ≤ t → x t = y t := by
  intro t ht
  apply unique_of_picard_approximation (fun n => z n t) (x t) (y t) hL ht
  · intro n i
    exact solution_picard_bound L hL b z x hb hlip hint hxint hstep hx n t ht i
  · intro n i
    exact solution_picard_bound L hL b z y hb hlip hint hyint hstep hy n t ht i

end Problem336.DeterministicDecoder

namespace Problem336.Picard

theorem solution_iterate_bound {I : Type*}
    (w x : I → ℝ → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (hw : ∀ i, Continuous (w i)) (hx : ∀ i, Measurable (x i))
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ (s : ℝ) (y y' : I → ℝ) (D : ℝ),
      0 ≤ D → (∀ j, |y j - y' j| ≤ D) →
      ∀ i, |b s y i - b s y' i| ≤ L * D)
    (hsol : ∀ t, 0 ≤ t → ∀ i,
      x i t = w i t + ∫ s in (0 : ℝ)..t, b s (fun j => x j s) i) :
    ∀ n i t, 0 ≤ t →
      |x i t - iterate w b n i t| ≤ majorant L t n := by
  have hxi (t : ℝ) (i : I) :
      IntervalIntegrable (fun s => b s (fun j => x j s) i) volume 0 t := by
    apply intervalIntegrable_of_measurable_bounded
    · exact (hb i).comp (measurable_id.prodMk (Measurable.of_eval hx))
    · exact fun s => hbound s _ i
  have h := DeterministicDecoder.solution_picard_bound L hL b
    (fun n t i => iterate w b n i t) (fun t i => x i t)
    (fun t _ y i => hbound t y i)
    (fun t _ y y' D hD hdiff i => hresponse t y y' D hD hdiff i)
    (fun n t _ i => intervalIntegrable_drift_iterate w b hw hb hbound n i 0 t)
    (fun t _ i => hxi t i) (fun _ _ _ => rfl) hsol
  exact fun n i t ht => h n t ht i

theorem decode_eq_solution {I : Type*}
    (w x : I → ℝ → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (hw : ∀ i, Continuous (w i)) (hx : ∀ i, Measurable (x i))
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ (s : ℝ) (y y' : I → ℝ) (D : ℝ),
      0 ≤ D → (∀ j, |y j - y' j| ≤ D) →
      ∀ i, |b s y i - b s y' i| ≤ L * D)
    (hsol : ∀ t, 0 ≤ t → ∀ i,
      x i t = w i t + ∫ s in (0 : ℝ)..t, b s (fun j => x j s) i) :
    ∀ i t, 0 ≤ t → decode w b i t = x i t := by
  intro i t ht
  apply Filter.Tendsto.limUnder_eq
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ => dist_nonneg)
  · intro n
    simpa only [Real.dist_eq, abs_sub_comm] using
      solution_iterate_bound w x b hw hx hb hbound hL hresponse hsol n i t ht
  · exact DeterministicDecoder.tendsto_picardBound_zero hL ht

end Problem336.Picard

end

end OAI
