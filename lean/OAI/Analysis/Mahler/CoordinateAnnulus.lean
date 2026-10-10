import OAI.Analysis.Mahler.CoordinateBall
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

/-- The closed annulus is used only for local differentiability and continuity. -/
def closedShell (n : ℕ) (a R : ℝ) : Set (Fin n → ℝ) :=
  {x | a^2 ≤ radiusSq x ∧ radiusSq x ≤ R^2}

/-- Fundamental theorem of calculus on a punctured chord. No regularity
is required in the deleted middle interval. -/
theorem integral_punctured_chord {a A : ℝ} (ha : 0 ≤ a) (hA : a ≤ A)
    (f g : ℝ → ℝ)
    (hl : ∀ t ∈ Icc (-A) (-a), HasDerivAt f (g t) t)
    (hr : ∀ t ∈ Icc a A, HasDerivAt f (g t) t)
    (hgl : IntervalIntegrable g volume (-A) (-a))
    (hgr : IntervalIntegrable g volume a A) :
    (∫ t in Ioo (-A) A \ Ioo (-a) a, g t) =
      (f A - f (-A)) - (f a - f (-a)) := by
  have hs : Ioo (-A) A \ Ioo (-a) a = Ioc (-A) (-a) ∪ Ico a A := by
    ext t
    simp only [mem_sdiff, mem_Ioo, mem_union, mem_Ioc, mem_Ico]
    constructor
    · rintro ⟨⟨htl,htr⟩, ht⟩
      by_cases hta : t ≤ -a
      · exact Or.inl ⟨htl, hta⟩
      · exact Or.inr ⟨le_of_not_gt (fun h => ht ⟨lt_of_not_ge hta,h⟩), htr⟩
    · rintro (⟨htl,htr⟩ | ⟨htl,htr⟩)
      · exact ⟨⟨htl, by linarith⟩, fun h => by linarith [h.1]⟩
      · exact ⟨⟨by linarith, htr⟩, fun h => by linarith [h.2]⟩
  have hd : AEDisjoint volume (Ioc (-A) (-a)) (Ico a A) := by
    apply measure_mono_null (t := ({0} : Set ℝ))
    · intro t ht
      simp only [mem_inter_iff, mem_Ioc, mem_Ico, mem_singleton_iff] at ht ⊢
      linarith [ht.1.2, ht.2.1]
    · exact measure_singleton 0
  rw [hs, setIntegral_union₀ hd measurableSet_Ico.nullMeasurableSet
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (neg_le_neg hA)).1 hgl)
    ((intervalIntegrable_iff_integrableOn_Ico_of_le hA).1 hgr),
    integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (neg_le_neg hA),
    ← intervalIntegral.integral_of_le hA]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (by simpa [uIcc_of_le (neg_le_neg hA)] using hl) hgl,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (by simpa [uIcc_of_le hA] using hr) hgr]
  ring

lemma chord_mono {n : ℕ} {a R : ℝ} (h : a^2 ≤ R^2) (y : Fin n → ℝ) :
    chord a y ≤ chord R y := Real.sqrt_le_sqrt (sub_le_sub_right h _)

lemma chord_shell {n : ℕ} {a R : ℝ} {y : Fin n → ℝ}
    (hy : y ∈ coordBall n R) {t : ℝ}
    (ht : t ∈ Icc (-chord R y) (-chord a y) ∪ Icc (chord a y) (chord R y))
    (i : Fin (n+1)) : i.insertNth t y ∈ closedShell (n+1) a R := by
  have hR : (chord R y)^2 = R^2 - radiusSq y :=
    Real.sq_sqrt (by change radiusSq y < R^2 at hy; linarith)
  have ha : a^2 - radiusSq y ≤ (chord a y)^2 := by
    by_cases h : 0 ≤ a^2 - radiusSq y
    · exact (Real.sq_sqrt h).ge
    · exact le_trans (le_of_not_ge h) (sq_nonneg _)
  have hnA : 0 ≤ chord R y := Real.sqrt_nonneg _
  have hna : 0 ≤ chord a y := Real.sqrt_nonneg _
  have htabs : chord a y ≤ |t| ∧ |t| ≤ chord R y := by
    rcases ht with ht | ht
    · rw [abs_of_nonpos (by linarith [ht.2])]
      constructor <;> linarith [ht.1, ht.2]
    · rw [abs_of_nonneg (by linarith [ht.1])]
      exact ht
  have hlo := (sq_le_sq₀ hna (abs_nonneg t)).2 htabs.1
  have hhi := (sq_le_sq₀ (abs_nonneg t) hnA).2 htabs.2
  change a^2 ≤ radiusSq (i.insertNth t y) ∧ radiusSq (i.insertNth t y) ≤ R^2
  rw [radiusSq_insertNth]
  rw [sq_abs] at hlo hhi
  constructor <;> linarith

/-- Open-ball puncture; the inner sphere has zero volume. -/
def coordAnnulus (n : ℕ) (a R : ℝ) : Set (Fin n → ℝ) :=
  coordBall n R \ coordBall n a

lemma boundary_difference_zero {n : ℕ} (i : Fin (n+1)) (R : ℝ)
    (f : (Fin (n+1) → ℝ) → ℝ) {y : Fin n → ℝ} (hy : y ∉ coordBall n R) :
    f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y) = 0 := by
  have hz : chord R y = 0 := Real.sqrt_eq_zero_of_nonpos
    (by change ¬ radiusSq y < R^2 at hy; linarith)
  simp [hz]

lemma integral_boundary_difference {n : ℕ} (i : Fin (n+1)) (R : ℝ)
    (f : (Fin (n+1) → ℝ) → ℝ) :
    (∫ y : Fin n → ℝ, f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y)) =
      ∫ y in coordBall n R, f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y) := by
  rw [← integral_indicator (measurableSet_coordBall n R)]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ coordBall n R
  · simp [hy]
  · simp [hy, boundary_difference_zero i R f hy]

/-- Divergence for one component on an annulus. Differentiability and
continuity of the actual partial derivative are required only on its closed
shell, so a singularity anywhere inside the hole is permitted. -/
theorem integral_partial_coordAnnulus {n : ℕ} (i : Fin (n+1)) {a R : ℝ}
    (haR : a^2 ≤ R^2) (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : ∀ x ∈ closedShell (n+1) a R, DifferentiableAt ℝ f x)
    (hg : ContinuousOn (fun x => fderiv ℝ f x (Pi.single i 1)) (closedShell (n+1) a R))
    (hgi : IntegrableOn (fun x => fderiv ℝ f x (Pi.single i 1)) (coordAnnulus (n+1) a R))
    (hbR : Integrable (fun y : Fin n → ℝ =>
      f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y)))
    (hba : Integrable (fun y : Fin n → ℝ =>
      f (i.insertNth (chord a y) y) - f (i.insertNth (-chord a y) y))) :
    (∫ x in coordAnnulus (n+1) a R, fderiv ℝ f x (Pi.single i 1)) =
      (∫ y in coordBall n R, f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y)) -
      ∫ y in coordBall n a, f (i.insertNth (chord a y) y) - f (i.insertNth (-chord a y) y) := by
  rw [setIntegral_slice i (s := coordAnnulus (n+1) a R) ((measurableSet_coordBall _ _).diff (measurableSet_coordBall _ _)) _ hgi]
  have hslice (y : Fin n → ℝ) :
      {t : ℝ | i.insertNth t y ∈ coordAnnulus (n+1) a R} =
        Ioo (-chord R y) (chord R y) \ Ioo (-chord a y) (chord a y) := by
    change {t | i.insertNth t y ∈ coordBall (n+1) R} \ {t | i.insertNth t y ∈ coordBall (n+1) a} = _
    rw [ball_slice, ball_slice]
  simp_rw [hslice]
  have he (y : Fin n → ℝ) :
      (∫ t in Ioo (-chord R y) (chord R y) \ Ioo (-chord a y) (chord a y),
        fderiv ℝ f (i.insertNth t y) (Pi.single i 1)) =
      (f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y)) -
      (f (i.insertNth (chord a y) y) - f (i.insertNth (-chord a y) y)) := by
    by_cases hy : y ∈ coordBall n R
    · have hleft : MapsTo (fun t : ℝ => i.insertNth t y) (Icc (-chord R y) (-chord a y))
          (closedShell (n+1) a R) := fun t ht => chord_shell hy (Or.inl ht) i
      have hright : MapsTo (fun t : ℝ => i.insertNth t y) (Icc (chord a y) (chord R y))
          (closedShell (n+1) a R) := fun t ht => chord_shell hy (Or.inr ht) i
      apply integral_punctured_chord (a := chord a y) (A := chord R y) (Real.sqrt_nonneg _) (chord_mono haR y)
        (fun t => f (i.insertNth t y)) (fun t => fderiv ℝ f (i.insertNth t y) (Pi.single i 1))
      · intro t ht
        exact (hf _ (hleft ht)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_insertNth i y t)
      · intro t ht
        exact (hf _ (hright ht)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_insertNth i y t)
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le (neg_le_neg (chord_mono haR y))]
        exact hg.comp (by fun_prop) hleft
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le (chord_mono haR y)]
        exact hg.comp (by fun_prop) hright
    · have hya : y ∉ coordBall n a := by
        intro h; apply hy; change radiusSq y < R^2; exact lt_of_lt_of_le h haR
      have hz : chord R y = 0 := Real.sqrt_eq_zero_of_nonpos
        (by change ¬radiusSq y < R^2 at hy; linarith)
      simp [hz, boundary_difference_zero i a f hya]
  simp_rw [he]
  rw [integral_sub hbR hba, integral_boundary_difference i R f, integral_boundary_difference i a f]

end MahlerStokes

end

end OAI
