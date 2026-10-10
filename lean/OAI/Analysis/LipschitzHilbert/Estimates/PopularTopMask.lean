import OAI.Analysis.LipschitzHilbert.Estimates.PopularTopCount
import OAI.Analysis.LipschitzHilbert.Estimates.SlopeMaskIntegral

namespace OAI

/-! Mask removal on the actual good testing set, with the weak top-count
hypothesis discharged by the geometric witness estimate. Mask parameters
are fixed before the top family and the testing set. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert

theorem popular_top_mask_integral (hLL : LaceyLiInput) (C H A1 d : ℝ)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hd : 4 ≤ d) :
    ∃ Ccount A L0 : ℝ, 0 < Ccount ∧ 2 < A ∧ 1 ≤ L0 ∧
      ∀ L : ℝ, L0 ≤ L → ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
      (T : ι → SlopeBox) (l r R : ℝ),
      1 ≤ R → L^A1 ≤ R → (∀ i, |(T i).slope| ≤ 1) →
      ∀ (u : Plane → ℝ) (K α : ℝ≥0), LipschitzWith K u → 0 < α → α ≤ 1 →
      300*((2*K:ℝ≥0):ℝ)*(r-l) ≤ 1 →
      ∀ E : ι → Set (ℝ × ℝ), (∀ i, MeasurableSet (E i)) →
      (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ z ∈ (T i).radialDilation R) →
      (∀ i z, z ∈ E i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal ((α:ℝ)*(T i).length*(T i).width) ≤
        (volume.prod volume) (E i)) → 0 < ∑ i, (T i).area →
      ∀ G : Set (ℝ × ℝ), MeasurableSet G →
      (volume.prod volume) G ≠ 0 → (volume.prod volume) G ≠ ∞ →
      (∀ z ∈ G, z.1 ∈ Icc l r) →
      ∀ F : ι → ℝ × ℝ → EuclideanSpace ℂ κ, (∀ i, Measurable (F i)) →
      (∀ᵐ z ∂(volume.prod volume).restrict G, ∀ i,
        ‖F i z‖ ≤ L^C*((T i).weight (L^A1) d z)^8) →
      IntegrableOn (fun z => ‖(∑ i, F i z)-(∑ i, (T i).mask L A z • F i z)‖) G
        (volume.prod volume) ∧
      (∫ z in G, ‖(∑ i, F i z)-(∑ i, (T i).mask L A z • F i z)‖ ∂volume.prod volume) ≤
        2*L^(-H)*(2*4^d*(Ccount/(α:ℝ))*Real.sqrt (∑ i, (T i).area)*R^3)*
          Real.sqrt ((volume.prod volume).real G) := by
  obtain ⟨Ccount,hCcount,hcount⟩ := popular_top_count_weak_two hLL
  obtain ⟨A,L0,hA,hL0,hmask⟩ := exists_slope_mask_integral C H A1 d hC hH (by linarith)
  refine ⟨Ccount,A,L0,hCcount,hA,hL0,?_⟩
  intro L hL ι κ _ _ T l r R hR hPR hs u K α hu hα hα1 hlength E hEmeas hdisj hE
    hclose hsize hS G hG hGzero hGfin hGstrip F hFmeas hF
  let μ := (volume.prod volume).restrict G
  let B := 2*4^d*(Ccount/(α:ℝ))*Real.sqrt (∑ i, (T i).area)*R^3
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith : 0 < L0) hL
  have hP : 0 < L^A1 := Real.rpow_pos_of_pos hLpos _
  have hB : 0 < B := by
    dsimp [B]
    exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (by positivity))
      (div_pos hCcount hα)) (Real.sqrt_pos.mpr hS)) (pow_pos (by linarith) _)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hGfin
  have hμ : μ univ ≠ 0 := by simpa only [μ, Measure.restrict_apply_univ] using hGzero
  have hweak (s : ℝ) (hspos : 0 < s) :
      μ {z | s < ∑ i, (T i).weight (L^A1) d z} ≤ ENNReal.ofReal (B^2/s^2) := by
    have hm : Measurable (fun z => ∑ i, (T i).weight (L^A1) d z) :=
      Finset.measurable_sum _ (fun i _ => ((T i).weight_continuous _ d hP).measurable)
    change ((volume.prod volume).restrict G) _ ≤ _
    rw [Measure.restrict_apply (measurableSet_lt measurable_const hm)]
    apply (measure_mono (show {z | s < ∑ i, (T i).weight (L^A1) d z} ∩ G ⊆
      {z | z.1 ∈ Icc l r} ∩ {z | s < ∑ i, (T i).weight (L^A1) d z} from
        fun z hz => ⟨hGstrip z hz.2,hz.1⟩)).trans
    exact hcount ι T l r R hR hs u K α hu hα hα1 hlength E hEmeas hdisj hE hclose hsize
      (L^A1) d hP hPR hd s hspos
  have hm := hmask L hL ι κ μ hμ T F hFmeas hF B hB hweak
  simpa only [μ, Measure.restrict_apply_univ, B, IntegrableOn, Measure.real] using hm

end LipschitzHilbert

end

end OAI
