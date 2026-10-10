import OAI.MeasureTheory.Falconer.Radial.UnitHeavyPlateCover
import OAI.MeasureTheory.Falconer.Radial.PlateZoom

namespace OAI

/-! # Removing the unit-ball normalization from the published heavy-plate cover -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem bounded_heavy_plate_cover (hpublished : PublishedHeavyHyperplanes)
    {d : ℕ} (hd : 3 ≤ d) (μ : ProbabilityMeasure (Space d)) {M s C : ℝ}
    (hM : 0 ≤ M) (hs : 1/2 < s-((d-2:ℕ):ℝ)) (hs' : s-((d-2:ℕ):ℝ) < 1)
    (hC : 0 ≤ C) (hbounded : ∀ᵐ x ∂(μ : Measure (Space d)), ‖x‖ ≤ M)
    (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ S : Finset (Space d × ℝ), (∀ p ∈ S, ‖p.1‖ = 1) ∧
        (S.card:ℝ) ≤ K*δ^(-heavyPlateExponent (s-((d-2:ℕ):ℝ))) ∧
        ∀ w : Space d, ‖w‖ = 1 → ∀ t : ℝ,
          ENNReal.ofReal (δ^(heavyPlateExponent (s-((d-2:ℕ):ℝ)))) ≤
            (μ : Measure (Space d)) {x | |inner ℝ w x-t| ≤ δ} →
          ∃ p ∈ S, ∀ x : Space d, ‖x‖ ≤ M → |inner ℝ w x-t| ≤ δ →
            |inner ℝ p.1 x-p.2| ≤ K*δ^(1/4:ℝ) := by
  classical
  let c : ℝ := 1/(2*(M+1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by dsimp [c]; apply (div_le_iff₀ (by positivity)).mpr; linarith only [hM]
  have hcM : c*M < 1 := by
    dsimp [c]
    rw [one_div_mul_eq_div]
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith only [hM]
  let e := radialZoom c hc.ne' (0:Space d)
  let μ' : ProbabilityMeasure (Space d) := μ.map e
  have hbound' : ∀ᵐ y ∂(μ' : Measure (Space d)), ‖y‖ < 1 := by
    change ∀ᵐ y ∂Measure.map e (μ : Measure (Space d)), ‖y‖ < 1
    rw [ae_map_iff e.measurable.aemeasurable (measurableSet_lt measurable_norm measurable_const)]
    filter_upwards [hbounded] with x hx
    have he : ‖e x‖ = c*‖x‖ := by simpa only [sub_zero] using radialZoom_norm hc (0:Space d) x
    rw [he]
    exact (mul_le_mul_of_nonneg_left hx hc.le).trans_lt hcM
  have hfrost' : FrostmanBallBound (μ' : Measure (Space d)) s (C*c^(-s)) :=
    radialZoom_full_frostman (μ : Measure (Space d)) hc (0:Space d) hfrost
  obtain ⟨K,hK,hcover⟩ := unit_heavy_plate_cover hpublished hd μ' hs hs'
    (mul_nonneg hC (Real.rpow_nonneg hc.le _)) hbound' hfrost'
  let b := heavyPlateExponent (s-((d-2:ℕ):ℝ))
  have hb : 0 < b := heavyPlateExponent_pos (by linarith only [hs])
  let L := max 1 (max (K*c^(-b)) (K*c^(1/4:ℝ)/c))
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLK : K*c^(-b) ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hLW : K*c^(1/4:ℝ)/c ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨L,hL1,?_⟩
  intro δ hδ hδ1
  obtain ⟨S,hunit,hcard,hcoverS⟩ := hcover (c*δ) (mul_pos hc hδ)
    ((mul_le_mul_of_nonneg_right hc1 hδ.le).trans (by simpa only [one_mul] using hδ1))
  let S' := S.image (fun p => (p.1,p.2/c))
  refine ⟨S',?_,?_,?_⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact hunit q hq
  · have hcard' : (S'.card:ℝ) ≤ (S.card:ℝ) := Nat.cast_le.mpr Finset.card_image_le
    apply hcard'.trans (hcard.trans ?_)
    rw [Real.mul_rpow hc.le hδ.le]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hLK (Real.rpow_nonneg hδ.le (-b))
  · intro w hw t hheavy
    have hheavy' : ENNReal.ofReal ((c*δ)^b) ≤
        (μ' : Measure (Space d)) {y | |inner ℝ w y-c*t| ≤ c*δ} := by
      change ENNReal.ofReal ((c*δ)^b) ≤ Measure.map (radialZoom c hc.ne' (0:Space d))
        (μ : Measure (Space d)) {y | |inner ℝ w y-c*t| ≤ c*δ}
      rw [radialZoom_zero_slab (μ : Measure (Space d)) hc w t δ]
      apply le_trans (ENNReal.ofReal_le_ofReal ?_) hheavy
      exact Real.rpow_le_rpow (mul_nonneg hc.le hδ.le)
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hδ.le) hb.le
    obtain ⟨p,hp,hpcover⟩ := hcoverS w hw (c*t) hheavy'
    refine ⟨(p.1,p.2/c),Finset.mem_image.mpr ⟨p,hp,rfl⟩,?_⟩
    intro x hx hxw
    have hcx : ‖c • x‖ < 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hc]
      exact (mul_le_mul_of_nonneg_left hx hc.le).trans_lt hcM
    have hxw' : |inner ℝ w (c • x)-c*t| ≤ c*δ := by
      rw [inner_smul_right,show c*inner ℝ w x-c*t = c*(inner ℝ w x-t) by ring,
        abs_mul,abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left hxw hc.le
    apply (pullback_affine_slab hc p.1 x (hpcover (c • x) hcx hxw')).trans
    rw [Real.mul_rpow hc.le hδ.le]
    have hh := mul_le_mul_of_nonneg_right hLW (Real.rpow_nonneg hδ.le (1/4:ℝ))
    convert hh using 1
    ring

end Falconer

end OAI
