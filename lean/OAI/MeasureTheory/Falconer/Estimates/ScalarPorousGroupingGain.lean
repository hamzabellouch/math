import OAI.MeasureTheory.Falconer.Estimates.ScalarGroupedHalfGain
import OAI.MeasureTheory.Falconer.Estimates.ScalarReverseGroupedHalfGain
import OAI.MeasureTheory.Falconer.Estimates.ScalarDenseGroup

namespace OAI

/-! The two orientations of the porous grouping argument assembled on
 original finite sets. Total branching is unrestricted above 2M. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_projection_log_mono (δ : ℝ) (B A C D E : Finset ℝ)
    (hA : A.Nonempty) (hC : C.Nonempty) (hAD : A ⊆ D) (hCE : C ⊆ E) :
    scalarAverage B (fun b => Real.log ((scalarCells δ (A+C.image (fun c => b*c))).card : ℝ)) ≤
      scalarAverage B (fun b => Real.log ((scalarCells δ (D+E.image (fun c => b*c))).card : ℝ)) := by
  apply scalarAverage_mono
  intro b _
  apply Real.log_le_log (scalar_sum_cells_pos A C hA hC)
  exact_mod_cast Finset.card_le_card (Finset.image_subset_image
    (Finset.add_subset_add hAD (Finset.image_subset_image hCE)))

 theorem scalar_porous_grouping_gain {δ r μ z K κ a : ℝ}
    (hδ : 0 < δ) (hδr : δ ≤ r) (hμ : 0 < μ) (hgap : 15*r < μ) (hK : 0 ≤ K)
    (hscale : δ ≤ 5*r/μ) (hscale1 : 5*r/μ ≤ 1)
    (B X Y : Finset ℝ) (hB : B.Nonempty) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hBb : ∀ b ∈ B, 1/3 ≤ b ∧ b ≤ 1)
    (hXbound : ∀ x ∈ X, 0 ≤ x-z ∧ x-z ≤ 2)
    (hYbound : ∀ y ∈ Y, 0 ≤ y-z ∧ y-z ≤ 2)
    (hXsep : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → μ ≤ |x-x'|)
    (hYsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → μ ≤ |y-y'|)
    (hcard : X.card = Y.card)
    (hball : ∀ u t : ℝ, δ ≤ t → t ≤ 1 → scalarBallMass B u t ≤ K*t^κ*(B.card : ℝ))
    (M : ℕ) (hM : 83521 ≤ M) (hMX : 2*M ≤ X.card)
    (hsmall : 16*(M:ℝ)^4*K*(5*r/μ)^κ ≤ 1/4)
    (U V : ℝ → Finset ℝ)
    (hUne : ∀ x ∈ X, (U x).Nonempty) (hVne : ∀ y ∈ Y, (V y).Nonempty)
    (hU : ∀ x ∈ X, ∀ u ∈ U x, |u-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ v ∈ V y, |v-y| ≤ r)
    (hchild : ∀ p ∈ X ×ˢ Y, a ≤ scalarAverage B (fun b => Real.log
      ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ))) :
    Real.log (X.card : ℝ)+(1/2 : ℝ)*Real.log (M:ℝ)+a ≤
      scalarAverage B (fun b => Real.log
        ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)) := by
  classical
  have hr : 0 < r := hδ.trans_le hδr
  obtain ⟨η,hη,hrη,j,hall,hF⟩ := scalar_pair_dense_group hμ (by linarith : 10*r ≤ μ)
    X Y hXbound hYbound hXsep hYsep M (by omega) hMX
  rcases hF with ⟨F,hF,hFc⟩ | ⟨F,hF,hFc⟩
  · have hFX : F ⊆ X := hF.trans (Finset.filter_subset _ _)
    have hFn : F.Nonempty := Finset.card_pos.mp (by rw [hFc]; omega)
    have hfgrid : ∀ x ∈ F, ⌊(x-z)/η⌋ = j := fun x hx => (Finset.mem_filter.mp (hF hx)).2
    have hg := scalar_reverse_grouped_half_gain hδ hη hδr hrη hμ hgap hK hscale hscale1
      B F Y hB hFn hY hBb
      (fun x hx x' hx' hne => hXsep x (hFX hx) x' (hFX hx') hne) hYsep hball M hM hFc
      (fun k => (hall k).2) hsmall j hfgrid U V (fun x hx => hUne x (hFX hx)) hVne
      (fun x hx => hU x (hFX hx)) hV
      (fun p hp => hchild p (Finset.mem_product.mpr ⟨hFX (Finset.mem_product.mp hp).1,(Finset.mem_product.mp hp).2⟩))
    have hu : F.biUnion U ⊆ X.biUnion U := by
      intro u hu
      obtain ⟨x,hx,hux⟩ := Finset.mem_biUnion.mp hu
      exact Finset.mem_biUnion.mpr ⟨x,hFX hx,hux⟩
    rw [← hcard] at hg
    exact hg.trans (scalar_projection_log_mono δ B _ _ _ _
      (hFn.biUnion fun x hx => hUne x (hFX hx)) (hY.biUnion hVne) hu (Finset.Subset.refl _))
  · have hFY : F ⊆ Y := hF.trans (Finset.filter_subset _ _)
    have hFn : F.Nonempty := Finset.card_pos.mp (by rw [hFc]; omega)
    have hfgrid : ∀ y ∈ F, ⌊(y-z)/η⌋ = j := fun y hy => (Finset.mem_filter.mp (hF hy)).2
    have hg := scalar_grouped_half_gain hδ hη hδr hrη hμ (by linarith : 5*r < μ) hK hscale hscale1
      B X F hB hX hFn (fun b hb => ⟨by linarith [(hBb b hb).1],(hBb b hb).2⟩)
      hXsep (fun y hy y' hy' hne => hYsep y (hFY hy) y' (hFY hy') hne) hball M (by omega) hFc
      (fun k => (hall k).1) hsmall j hfgrid U V hUne (fun y hy => hVne y (hFY hy)) hU
      (fun y hy => hV y (hFY hy))
      (fun p hp => hchild p (Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp).1,hFY (Finset.mem_product.mp hp).2⟩))
    have hv : F.biUnion V ⊆ Y.biUnion V := by
      intro v hv
      obtain ⟨y,hy,hvy⟩ := Finset.mem_biUnion.mp hv
      exact Finset.mem_biUnion.mpr ⟨y,hFY hy,hvy⟩
    exact hg.trans (scalar_projection_log_mono δ B _ _ _ _
      (hX.biUnion hUne) (hFn.biUnion fun y hy => hVne y (hFY hy)) (Finset.Subset.refl _) hv)

end Falconer

end OAI
