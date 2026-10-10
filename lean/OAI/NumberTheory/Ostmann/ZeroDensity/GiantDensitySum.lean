import OAI.NumberTheory.Ostmann.Construction.GiantLogMeasures

namespace OAI

/-! # Moving the finite residue average inside the common real integral -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical

theorem double_integral_finset_sum {A : Type*} (S : Finset A)
    (μ ν : Measure ℝ) (F : A → ℝ → ℝ → ℂ)
    (hinner : ∀ a ∈ S, ∀ x, Integrable (F a x) ν)
    (houter : ∀ a ∈ S, Integrable (fun x => ∫ y, F a x y ∂ν) μ) :
    (∫ x, ∫ y, ∑ a ∈ S, F a x y ∂ν ∂μ) =
      ∑ a ∈ S, ∫ x, ∫ y, F a x y ∂ν ∂μ := by
  have hin (x : ℝ) : (∫ y, ∑ a ∈ S, F a x y ∂ν) =
      ∑ a ∈ S, ∫ y, F a x y ∂ν :=
    integral_finsetSum S (fun a ha => hinner a ha x)
  simp_rw [hin]
  exact integral_finsetSum S houter

/-- The complex residue coefficient is kept signed throughout this interchange. -/
theorem bounded_density_pair_sum {A B : Type*} (S : Finset A) (T : Finset B)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (H : ℝ → ℝ → ℂ) (hH : Measurable (Function.uncurry H))
    (K : ℝ) (hK : ∀ x y, ‖H x y‖ ≤ K)
    (α : A → ℝ → ℂ) (β : B → ℝ → ℂ)
    (hα : ∀ a ∈ S, Measurable (α a)) (hβ : ∀ b ∈ T, Measurable (β b))
    (U V : ℝ) (hU : 0 ≤ U) (_hV : 0 ≤ V)
    (hαU : ∀ a ∈ S, ∀ x, ‖α a x‖ ≤ U) (hβV : ∀ b ∈ T, ∀ x, ‖β b x‖ ≤ V)
    (c : A → B → ℂ) :
    (∑ a ∈ S, ∑ b ∈ T,
      ∫ x, ∫ y, c a b * H x y * α a x * β b y ∂ν ∂μ) =
      ∫ x, ∫ y, H x y * (∑ a ∈ S, ∑ b ∈ T, c a b * α a x * β b y) ∂ν ∂μ := by
  have hK0 : 0 ≤ K := (norm_nonneg (H 0 0)).trans (hK 0 0)
  let F := fun z : A × B => fun x y => c z.1 z.2 * H x y * α z.1 x * β z.2 y
  have hf (z : A × B) (hz : z ∈ S.product T) : Measurable (Function.uncurry (F z)) := by
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hz
    exact ((measurable_const.mul hH).mul ((hα z.1 ha).comp measurable_fst)).mul
      ((hβ z.2 hb).comp measurable_snd)
  have hn (z : A × B) (hz : z ∈ S.product T) (x y : ℝ) :
      ‖F z x y‖ ≤ ‖c z.1 z.2‖ * K * U * V := by
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hz
    dsimp only [F]
    simp only [norm_mul]
    apply mul_le_mul _ (hβV z.2 hb y) (norm_nonneg _) (mul_nonneg (by positivity) hU)
    apply mul_le_mul _ (hαU z.1 ha x) (norm_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left (hK x y) (norm_nonneg _)
  have hp (z : A × B) (hz : z ∈ S.product T) :
      Integrable (Function.uncurry (F z)) (μ.prod ν) :=
    ⟨(hf z hz).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun x => hn z hz x.1 x.2)⟩
  have hi (z : A × B) (hz : z ∈ S.product T) (x : ℝ) : Integrable (F z x) ν :=
    ⟨((hf z hz).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun y => hn z hz x y)⟩
  have hs := double_integral_finset_sum (S.product T) μ ν F hi (fun z hz => (hp z hz).integral_prod_left)
  simp only [Finset.product_eq_sprod, Finset.sum_product, F] at hs
  rw [← hs]
  apply integral_congr_ae
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end Ostmann

end OAI
