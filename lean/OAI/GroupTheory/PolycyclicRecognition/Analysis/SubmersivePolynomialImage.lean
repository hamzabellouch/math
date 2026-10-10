import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConvergingPolynomialImage
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinateMinorPermutation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SurjectiveColumns

namespace OAI

/-! # Subexponential image volume from a surjective limiting differential -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem converging_submersive_polynomial_image
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {m n : ℕ}
    (rem : RemezPolynomialInput) (hn : 1 ≤ n)
    (f : P × (Fin m → ℝ) → (Fin n → ℝ)) (hf : ContDiff ℝ 2 f)
    (hpoly : HasPolynomialCoordinates (fun a x => f (a, x)))
    (S : Set P) (hS : IsCompact S) (b : ℝ → P) (hb : ∀ r, b r ∈ S)
    (b₀ : P) (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (R : ℝ) (hR : 1 ≤ R) (t₀ : Fin m → ℝ) (ht₀ : ‖t₀‖ ≤ R)
    (hs : Function.Surjective (fderiv ℝ (fun x => f (b₀, x)) t₀))
    (E : ℝ → Set (Fin m → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 R)
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBound (fun r => (volume (E r)).toReal)) :
    ∃ C : ℝ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun x => f (b r, x)) '' E r) ∧
      HasSubexponentialLowerBound (fun r => (volume (C r)).toReal) := by
  classical
  obtain ⟨j, hj, hminor⟩ := exists_nonsingular_column_minor
    (fderiv ℝ (fun x => f (b₀, x)) t₀).toLinearMap hs
  obtain ⟨k, e, he⟩ := exists_fin_equiv_extending_injection j hj
  let u₀ := reindexParameters e.symm t₀
  let v₀ := fun i : Fin n => u₀ (Fin.castAdd k i)
  let z₀ := fun i : Fin k => u₀ (Fin.natAdd n i)
  have hu : Fin.append v₀ z₀ = u₀ := by
    ext i
    refine Fin.addCases ?_ ?_ i <;> intro i <;> simp [v₀, z₀]
  have hback : reindexParameters e (Fin.append v₀ z₀) = t₀ := by
    rw [hu]
    ext i
    simp [u₀]
  let g := fun p : P × (Fin (n + k) → ℝ) => f (p.1, reindexParameters e p.2)
  have hg : ContDiff ℝ 2 g :=
    hf.comp (contDiff_fst.prodMk ((reindexParameters e).contDiff.comp contDiff_snd))
  have hgpoly : HasPolynomialCoordinates (fun a x => g (a, x)) :=
    fun i => (hpoly i).reindex e
  have hd : (fderiv ℝ (fun v => g (b₀, Fin.append v z₀)) v₀).det ≠ 0 := by
    have hfd : DifferentiableAt ℝ (fun x => f (b₀, x))
        (reindexParameters e (Fin.append v₀ z₀)) := by
      rw [hback]
      exact ((hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)).differentiableAt
    rw [show (fun v => g (b₀, Fin.append v z₀)) =
      (fun v => f (b₀, reindexParameters e (Fin.append v z₀))) from rfl,
      det_reindexed_slice e (fun x => f (b₀, x)) v₀ z₀ hfd, hback]
    simpa only [he, ContinuousLinearMap.coe_coe] using hminor
  let E' := fun r => reindexParameters e ⁻¹' E r
  have hE' : ∀ r, MeasurableSet (E' r) :=
    fun r => (hE r).preimage (reindexParameters e).continuous.measurable
  have hvol (r : ℝ) : volume (E' r) = volume (E r) :=
    (measurePreserving_reindexParameters e).measure_preimage (hE r).nullMeasurableSet
  have hER' (r : ℝ) : E' r ⊆ closedBall 0 R := by
    intro x hx
    have hh := hER r hx
    simpa only [mem_closedBall, dist_zero_right, reindexParameters_norm] using hh
  have hanchor : Fin.append v₀ z₀ ∈ closedBall 0 R := by
    rw [hu, mem_closedBall, dist_zero_right, reindexParameters_norm]
    exact ht₀
  obtain ⟨C, hC, hCE, hClower⟩ := converging_smooth_polynomial_family_image
    rem n k hn g hg hgpoly S hS b hb b₀ hb₀ hlim R hR v₀ z₀ hanchor hd
    E' hE' hER' (fun r => by rw [hvol]; exact hm r) (by simpa only [hvol] using hmlower)
  refine ⟨C, hC, ?_, hClower⟩
  filter_upwards [hCE] with r hr
  rintro y hy
  obtain ⟨x, hx, rfl⟩ := hr hy
  exact ⟨reindexParameters e x, hx, rfl⟩

end PolycyclicRecognition

end

end OAI
