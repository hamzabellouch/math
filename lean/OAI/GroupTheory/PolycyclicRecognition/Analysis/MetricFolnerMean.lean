import OAI.GroupTheory.PolycyclicRecognition.Analysis.SourceMetricFolner
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FolnerInvariantMean

namespace OAI

/-! # A discrete metric Følner sequence gives the height-correction mean -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Metric Filter
open scoped Topology symmDiff

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G] [DecidableEq G]

theorem inverse_boundaryRatio_le_metricBoundary
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite)
    (E : Finset G) (g : G) :
    boundaryRatio (E.image Inv.inv) g ≤
      2 * (((finiteMetricNeighborhood hfinite E (dist (1 : G) g⁻¹) \ E).card : ℝ) / E.card) := by
  let F := E.image (· * g⁻¹)
  let N := finiteMetricNeighborhood hfinite E (dist (1 : G) g⁻¹)
  have hFcard : F.card = E.card :=
    Finset.card_image_of_injective E (fun _ _ h => mul_right_cancel h)
  have hFN : F ⊆ N := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_finiteMetricNeighborhood hfinite E _ _).mpr
    refine ⟨p, hp, ?_⟩
    have he := dist_mul_left p g⁻¹ (1 : G)
    simpa only [mul_one, dist_comm] using he.le
  have hd : (F \ E).card ≤ (N \ E).card := Finset.card_le_card (by
    intro x hx
    obtain ⟨hx, hxE⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hFN hx, hxE⟩)
  have heq : (F \ E).card = (E \ F).card := Finset.card_sdiff_comm hFcard
  have hc : (F ∆ E).card ≤ 2 * (N \ E).card := by
    have hu : (F ∆ E).card ≤ (F \ E).card + (E \ F).card := Finset.card_union_le _ _
    omega
  have hleft : (leftTranslate g (E.image Inv.inv)).image Inv.inv = F := by
    simp only [leftTranslate, Finset.image_image, Function.comp_def, mul_inv_rev, inv_inv, F]
  have hinv : (E.image Inv.inv).image Inv.inv = E := by
    ext x
    simp
  have hcs : (leftTranslate g (E.image Inv.inv) ∆ E.image Inv.inv).card = (F ∆ E).card := by
    rw [← Finset.card_image_of_injective _
      (inv_injective : Function.Injective (fun x : G => x⁻¹)),
      Finset.image_symmDiff _ _ inv_injective, hleft, hinv]
  unfold boundaryRatio
  rw [hcs, Finset.card_image_of_injective E inv_injective]
  have hcr : ((F ∆ E).card : ℝ) ≤ 2 * ((N \ E).card : ℝ) := by exact_mod_cast hc
  calc
    ((F ∆ E).card : ℝ) / E.card ≤ (2 * ((N \ E).card : ℝ)) / E.card := by
      exact div_le_div_of_nonneg_right hcr (Nat.cast_nonneg _)
    _ = 2 * (((N \ E).card : ℝ) / E.card) := by ring

theorem invariantMean_of_metricBoundary_sequence
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite)
    (E : ℕ → Finset G) (hE : ∀ n, (E n).Nonempty)
    (hlim : ∀ R : ℝ, 0 ≤ R → Tendsto
      (fun n => ((finiteMetricNeighborhood hfinite (E n) R \ E n).card : ℝ) / (E n).card)
      atTop (𝓝 0)) : Nonempty (InvariantMean G) := by
  apply exists_invariantMean_of_folner_net (l := atTop) (fun n => (E n).image Inv.inv)
    (fun n => (hE n).image Inv.inv)
  intro g
  apply squeeze_zero (fun n => boundaryRatio_nonneg ((E n).image Inv.inv) g)
    (fun n => inverse_boundaryRatio_le_metricBoundary hfinite (E n) g)
  simpa only [mul_zero] using (hlim (dist (1 : G) g⁻¹) dist_nonneg).const_mul 2

end PolycyclicRecognition

end

end OAI
