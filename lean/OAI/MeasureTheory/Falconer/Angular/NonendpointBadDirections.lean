import OAI.MeasureTheory.Falconer.Radial.NonendpointTubeGain
import OAI.MeasureTheory.Falconer.Angular.BadDirectionSelection
import OAI.MeasureTheory.Falconer.Incidence.PowerIncidenceMass
import OAI.MeasureTheory.Falconer.Estimates.EndpointDyadicScale

namespace OAI

/-! # A universal Borel bad-direction envelope in the nonendpoint regime -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem nonendpoint_bad_direction_envelope (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {t q C : ℝ} (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2)
    (hqt : q < t) (ht : t-(h:ℝ) < 1) (hC : 0 ≤ C) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ : Measure (Space (h+2))) [IsProbabilityMeasure μ],
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) →
      (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      ∃ B : Set (Sphere (h+2)), MeasurableSet B ∧
        {w : Sphere (h+2) | ∃ S : Finset (Space (h+2)), (S.card:ℝ) ≤ (1/(2:ℝ)^N)^(-q-b) ∧
          ENNReal.ofReal ((1/(2:ℝ)^N)^b) ≤
            μ {x | ∃ v ∈ S, ‖perpendicularPart (w:Space (h+2)) (x-v)‖ ≤ C*(1/(2:ℝ)^N)}} ⊆ B ∧
        ∀ (ν : Measure (Sphere (h+2))) [IsFiniteMeasure ν], ν univ ≤ 1 →
          (∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N → ν (Metric.ball w (1/(2:ℝ)^j)) ≤
            ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
          ν B ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^b) := by
  classical
  obtain ⟨ε₀,c,δ₀,hε₀,hc,hδ₀,hgain⟩ := nonendpoint_dyadic_tube_gain hpublished hq hq' hqt ht
    (by linarith : 0 ≤ 2*C+1)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    (dyadic_inverse_tendsto.eventually (Ioo_mem_nhdsGT hδ₀))
  let ε : ℝ := ε₀/2
  let b : ℝ := min ε (c/3)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hb : 0 < b := lt_min hε (by positivity)
  have hεle : ε ≤ ε₀ := by dsimp [ε]; linarith
  have hble : b ≤ ε₀ := (min_le_left _ _).trans hεle
  have hbc : 2*b ≤ c := by have hh := min_le_right ε (c/3); dsimp [b]; linarith
  refine ⟨ε,b,hε,hb,N₀,?_⟩
  intro N hN μ _ hμ hμball
  let δ : ℝ := 1/(2:ℝ)^N
  let count : ℕ := Nat.floor (δ^(-q-b))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1)
      (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) : (1:ℝ) ≤ (2:ℝ)^N)
  have hL : δ^(-ε) ≤ δ^(-ε₀) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hεle)
  obtain ⟨G,hG,hnet⟩ := exists_bounded_anchor_net (d := h+2) (1/4) hδ
  let B := finiteBadDirections μ G count (1/4) ((2*C+1)*δ) (ENNReal.ofReal (δ^b))
  refine ⟨B,finiteBadDirections_measurable μ G count _ _ _,?_,?_⟩
  · rintro w ⟨S,hS,hmass⟩
    have hh := original_bad_direction_mem_envelope μ G count (ENNReal.ofReal (δ^b))
      hμ hnet w S (Nat.le_floor hS) hmass
    have he : 2*(C*δ)+δ = (2*C+1)*δ := by ring
    change w ∈ finiteBadDirections μ G count (1/4) (2*(C*δ)+δ) (ENNReal.ofReal (δ^b)) at hh
    rw [he] at hh
    exact hh
  · intro ν _ hνmass hνball
    obtain ⟨J,F,hF,hJ,hJmeas,hFb,hcover,hlower⟩ :=
      exists_finite_bad_incidence μ G count (1/4) ((2*C+1)*δ) (ENNReal.ofReal (δ^b))
    have hcount : (count:ℝ) ≤ δ^(-q-ε₀) :=
      (Nat.floor_le (Real.rpow_nonneg hδ.le _)).trans
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
    have hupper := hgain N μ ν F (hN₀ N hN).2 hμ (by simp) hνmass
      (fun x j hj => (hμball x j hj).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (show 0 ≤ 1/(2:ℝ)^j by positivity) t))))
      (fun w j hj => (hνball w j hj).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (show 0 ≤ 1/(2:ℝ)^j by positivity) q))))
      hF hFb (by
          intro w
          refine ⟨J w,?_,?_⟩
          · exact (show ((J w).card:ℝ) ≤ count by exact_mod_cast (hJ w).2).trans hcount
          · intro x hx
            exact hcover (x,w) hx)
    exact ennreal_mass_of_power_incidence hδ hδ1 hbc (ν B) ((hlower ν).trans hupper)

end Falconer

end OAI
