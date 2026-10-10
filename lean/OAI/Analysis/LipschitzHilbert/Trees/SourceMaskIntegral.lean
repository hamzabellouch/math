import OAI.Analysis.LipschitzHilbert.Estimates.MaskNormalization
import OAI.Analysis.LipschitzHilbert.Estimates.PopularTopCountPowers

namespace OAI

/-! The source-normalized mask error. The weak count is derived from
the actual popular witnesses, and the area relation removes its square
root factors. The mask scale is fixed before all finite families. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert

theorem source_mask_integral (hLL : LaceyLiInput) (C H a aw s d : ℝ)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (haw : 0 ≤ aw) (hs : 0 ≤ s) (hd : 4 ≤ d) :
    ∃ A L0 : ℝ, a < A ∧ 2 < A ∧ 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
        (T : ι → SlopeBox) (l r : ℝ), (∀ i, |(T i).slope| ≤ 1) →
      ∀ (u : Plane → ℝ) (lip : ℝ≥0), LipschitzWith lip u →
      300*((2*lip:ℝ≥0):ℝ)*(r-l) ≤ 1 →
      ∀ E : ι → Set (ℝ × ℝ), (∀ i, MeasurableSet (E i)) →
      (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ (T i).radius z ≤ L^aw) →
      (∀ i z, z ∈ E i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal (L^(-aw)*(T i).length*(T i).width) ≤
        (volume.prod volume) (E i)) → 0 < ∑ i, (T i).area →
      ∀ (ratio : ℝ) (F G : Set (ℝ × ℝ)), 0 ≤ ratio →
      (volume.prod volume) F ≠ ∞ → MeasurableSet G → G ⊆ F →
      (∀ z ∈ G, z.1 ∈ Icc l r) →
      (∑ i, (T i).area) ≤ L^s*ratio^2*(volume.prod volume).real F →
      ∀ V : ι → ℝ × ℝ → EuclideanSpace ℂ κ, (∀ i, Measurable (V i)) →
      (∀ᵐ z ∂(volume.prod volume).restrict G, ∀ i,
        ‖V i z‖ ≤ L^C*((T i).weight (L^a) d z)^8) →
      IntegrableOn (fun z => ‖(∑ i, V i z)-(∑ i, (T i).mask L A z • V i z)‖) G
        (volume.prod volume) ∧
      (∫ z in G, ‖(∑ i, V i z)-(∑ i, (T i).mask L A z • V i z)‖ ∂volume.prod volume) ≤
        L^(-H)*ratio*(volume.prod volume).real F := by
  obtain ⟨Cc,hCc,hcount⟩ := popular_top_count_powers hLL aw a d haw hd
  let e := aw+3*max a aw
  have he : 0 ≤ e := by dsimp [e]; linarith [le_max_right a aw]
  obtain ⟨A,Lm,haA,hA,hLm,hmask⟩ := exists_slope_mask_integral_above C (H+e+s/2+2) a d a
    hC (by positivity) (by linarith)
  refine ⟨A,max Lm (max 1 (2*Cc)),haA,hA,hLm.trans (le_max_left _ _),?_⟩
  intro L hL ι κ _ _ T l r hslopes u lip hu hlength E hE hdisj hinside hclose hsize hSpos
    ratio F G hratio hFfin hG hGF hGstrip hS V hV hpoint
  have hLmL : Lm ≤ L := (le_max_left _ _).trans hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have hCcL : 2*Cc ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hCcL2 : 2*Cc ≤ L^2 := hCcL.trans (by nlinarith)
  have hGfin : (volume.prod volume) G ≠ ∞ := ne_top_of_le_ne_top hFfin (measure_mono hGF)
  by_cases hGzero : (volume.prod volume) G = 0
  · simp only [IntegrableOn, Measure.restrict_eq_zero.mpr hGzero, integrable_zero_measure,
      integral_zero_measure, true_and]
    positivity
  let μ := (volume.prod volume).restrict G
  let B := Cc*L^e*Real.sqrt (∑ i, (T i).area)
  have hB : 0 < B := mul_pos (mul_pos hCc (Real.rpow_pos_of_pos hLpos _))
    (Real.sqrt_pos.mpr hSpos)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hGfin
  have hμ : μ univ ≠ 0 := by simpa only [μ, Measure.restrict_apply_univ] using hGzero
  have hweak (t : ℝ) (ht : 0 < t) :
      μ {z | t < ∑ i, (T i).weight (L^a) d z} ≤ ENNReal.ofReal (B^2/t^2) := by
    have hm : Measurable (fun z => ∑ i, (T i).weight (L^a) d z) :=
      Finset.measurable_sum _ (fun i _ =>
        ((T i).weight_continuous _ d (Real.rpow_pos_of_pos hLpos _)).measurable)
    change ((volume.prod volume).restrict G) _ ≤ _
    rw [Measure.restrict_apply (measurableSet_lt measurable_const hm)]
    apply (measure_mono (show {z | t < ∑ i, (T i).weight (L^a) d z} ∩ G ⊆
      {z | z.1 ∈ Icc l r} ∩ {z | t < ∑ i, (T i).weight (L^a) d z} from
        fun z hz => ⟨hGstrip z hz.2,hz.1⟩)).trans
    exact hcount L hL1 ι T l r hslopes u lip hu hlength E hE hdisj hinside hclose hsize t ht
  obtain ⟨hint,hintbound⟩ := hmask L hLmL ι κ μ hμ T V hV hpoint B hB hweak
  refine ⟨hint,?_⟩
  have hnorm := mask_error_normalization L Cc e s H ratio
    ((volume.prod volume).real F) ((volume.prod volume).real G) (∑ i, (T i).area)
    hLpos hCc.le hCcL2 hratio measureReal_nonneg
    (measureReal_mono hGF hFfin) hS
  apply le_trans ?_ hnorm
  simpa only [μ, Measure.restrict_apply_univ, B, Measure.real] using hintbound

end LipschitzHilbert

end

end OAI
