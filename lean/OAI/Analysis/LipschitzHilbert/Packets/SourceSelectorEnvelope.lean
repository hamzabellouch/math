import OAI.Analysis.LipschitzHilbert.Trees.SourceSingleScaleEnvelope

namespace OAI

/-! The source selector support and local slope-label multiplicity
instantiate the pointwise overlap budget in the single-scale estimate.
The bound is uniform in the number of labels and Hilbert coordinates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem source_selector_single_scale {Λ κ : Type*} [Fintype Λ] [Fintype κ]
    (ι : Λ → Type*) [∀ b, Fintype (ι b)]
    (site : ∀ b, ι b → ℤ×ℤ) (hinj : ∀ b, Function.Injective (site b))
    (originX originY slope : Λ → ℝ) {l W d radius C M : ℝ} {K H : ℕ}
    (hl : 0 < l) (hW : 0 < W) (hd : 0 < d) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ slope d H)
    (hK : radius ≤ K)
    (selector : Λ → κ → ℝ → ℂ) (hselector : ∀ b k, Measurable (selector b k))
    (hselectorBound : ∀ b k s, ‖selector b k s‖ ≤ M)
    (hsupport : ∀ b k s, selector b k s ≠ 0 → |s-slope b| ≤ radius*d)
    (direction : ℝ×ℝ → ℝ) (hdirection : Measurable direction)
    (wave : ∀ b, ι b → κ → ℝ×ℝ → ℂ) (hwave : ∀ b i k, Measurable (wave b i k))
    (hwaveBound : ∀ b i k z, ‖wave b i k z‖ ≤
      C*tileEnvelope (originX b+l*(site b i).1) (originY b+W*(site b i).2) l W 6 z)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (z : ℝ×ℝ) :
    (∑ b, ∑ i, ‖analyzingCoefficient volume (fun _ : ι b => l*W)
      (fun i k p => selector b k (direction p)*wave b i k p) g i‖*
      tileEnvelope (originX b+l*(site b i).1) (originY b+W*(site b i).2) l W 6 z) ≤
        (64*(4*Real.pi)^2)*((C*M*((2*K+1)*H:ℕ))*Real.pi^2) := by
  let active := fun (b : Λ) (p : ℝ×ℝ) => ∃ k, selector b k (direction p) ≠ 0
  let source := fun (b : Λ) (p : ℝ×ℝ) => if active b p then C*M else 0
  have hsourceMeas (b : Λ) : Measurable (source b) := by
    have ha : MeasurableSet {p : ℝ×ℝ | active b p} := by
      have heq : {p : ℝ×ℝ | active b p} = ⋃ k : κ, {p | selector b k (direction p) ≠ 0} := by
        ext p
        simp only [Set.mem_ofPred_eq,Set.mem_iUnion,active]
      rw [heq]
      exact MeasurableSet.iUnion fun k =>
        (measurableSet_eq_fun ((hselector b k).comp hdirection) measurable_const).compl
    exact Measurable.ite ha measurable_const measurable_const
  have hsource0 (b : Λ) (p : ℝ×ℝ) : 0 ≤ source b p := by
    dsimp [source]
    split_ifs <;> positivity
  have hoverlap (p : ℝ×ℝ) : ∑ b, source b p ≤ C*M*((2*K+1)*H:ℕ) := by
    have hcard := SourceSlopeLabels.active_card_le Finset.univ slope selector
      (t := direction p) hd hlocal hK (fun b _ k => hsupport b k (direction p))
    have heq : (∑ b, source b p) =
        C*M*((SourceSlopeLabels.active Finset.univ selector (direction p)).card:ℝ) := by
      dsimp [source,SourceSlopeLabels.active]
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
      congr 2
      congr 1
      ext b
      simp only [Finset.mem_filter,active]
    rw [heq]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (mul_nonneg hC hM)
  apply source_single_scale_envelope ι site hinj originX originY hl hW (by positivity)
    source hsourceMeas hsource0 hoverlap _ _ _ g hg hg1 z
  · intro b i k
    exact ((hselector b k).comp hdirection).mul (hwave b i k)
  · intro b i k p
    by_cases ha : active b p
    · have hm := mul_le_mul (hselectorBound b k (direction p)) (hwaveBound b i k p)
        (norm_nonneg _) hM
      rw [norm_mul]
      convert hm using 1
      dsimp [source]
      rw [ite_eq_left ha]
      ring
    · have hz : selector b k (direction p) = 0 := by
        by_contra hk
        exact ha ⟨k,hk⟩
      simp only [hz,zero_mul,norm_zero,source,ite_eq_right ha,mul_zero,le_refl]

end LipschitzHilbert

end

end OAI
