import OAI.MeasureTheory.Falconer.Radial.NonendpointRadialBadDirections
import OAI.MeasureTheory.Falconer.Radial.MiddleRadialPruning
import OAI.MeasureTheory.Falconer.Radial.HeavyCoverCount

namespace OAI

/-! # Quantitative middle-interval improvement from the published planar input -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem nonendpoint_middle_radial_pruning (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {t q : ℝ} (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2)
    (hqt : q < t) (ht : t-(h:ℝ) < 1) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ ν : Measure (Space (h+2)))
        [IsProbabilityMeasure μ] [IsFiniteMeasure ν], ν univ ≤ 1 →
      ∀ (_w₀ : Sphere (h+2)) (G : Set (Space (h+2) × Space (h+2))), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → z ≠ x ∧ ‖z‖ ≤ 1/4) →
      (∀ᵐ z ∂μ, ‖z‖ ≤ 1/4) →
      (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ᵐ z ∂μ, ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
      ∀ r H θ : ℝ, 0 < r → 8*(1/4:ℝ)^2/r ≤ 1/(2:ℝ)^N →
      H*θ ≤ 1/(2:ℝ)^N →
      (∀ x, (∃ z, (z,x) ∈ G) → r ≤ ‖(0:Space (h+2))-x‖ ∧
        ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal ((1/(2:ℝ)^N)^b) ∧
        ∀ p ∈ G', radialCollisionMass μ θ p ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(q+b/2)) := by
  let C : ℝ := 2*((h+2:ℕ):ℝ)+2
  let L : ℕ := h+5
  let K : ℕ := (2*L+1)^(h+2)
  obtain ⟨ε,b,hε,hb,N₁,hN₁⟩ := nonendpoint_radial_bad_directions hpublished hq hq' hqt ht
    (show 0 ≤ C by dsimp [C]; positivity)
  obtain ⟨N₂,hN₂⟩ := eventually_heavy_cover_card (q := q) (K := (K:ℝ)) hb (by positivity)
  refine ⟨ε,b,hε,hb,max N₁ N₂,?_⟩
  intro N hN μ ν _ _ hν w₀ G hG hgeom hμ hballs hcaps r H θ hr hfreeze hwidth hpin
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Bad,hBad,hcontains,hbadmass⟩ := hN₁ N ((le_max_left _ _).trans hN) μ ν hν
    w₀ G hG (fun z x hx => (hgeom z x hx).1.symm) hμ hballs hcaps
  have hL : 1+1+((h+1+1:ℕ):ℝ)+1/2 ≤ (L:ℝ) := by dsimp [L]; push_cast; linarith
  have hrobust : (2*((h+1+1:ℕ):ℝ)+1)*δ+2*(2*(1/4)/r)*(1/4+1/4) ≤ C*δ := by
    have he : 2*(2*(1/4:ℝ)/r)*(1/4+1/4) = 8*(1/4:ℝ)^2/r := by ring
    rw [he]
    dsimp [C]
    change 8*(1/4:ℝ)^2/r ≤ δ at hfreeze
    nlinarith
  have henv (v : Sphere (h+2)) (S : Finset (Space (h+2)))
      (hc : (S.card:ℝ≥0∞)*ENNReal.ofReal (δ^(q+b/2)) ≤
        ((2*L+1)^(h+1+1):ℕ)*μ univ)
      (hm : ENNReal.ofReal (δ^b) ≤
        μ {z | ∃ a ∈ S, ‖perpendicularPart (v:Space (h+2)) (z-a)‖ ≤ C*δ}) : v ∈ Bad := by
    apply hcontains
    refine ⟨S,?_,hm⟩
    apply hN₂ N ((le_max_right _ _).trans hN) S.card
    simpa only [measure_univ,mul_one,ENNReal.ofReal_natCast] using hc
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := middle_radial_pruning (θ := θ) (n := h+1) μ ν w₀ G hG
    Bad hBad 0 hr hδ hfreeze (by simpa only [sub_zero] using hμ) hμ
    (fun z x hx => ⟨(hgeom z x hx).1,by simpa only [sub_zero] using (hgeom z x hx).2,
      (hgeom z x hx).2⟩) hpin (by simpa only [one_mul] using hwidth) hrobust (ENNReal.ofReal (δ^(q+b/2)))
    (ENNReal.ofReal (δ^b)) (ENNReal.ofReal (δ^b)) L hL henv hbadmass
  refine ⟨G',hG',hsub,hdel.trans ?_,hbound⟩
  calc
    _ ≤ ENNReal.ofReal (δ^b)+ENNReal.ofReal (δ^b)*1 :=
      add_le_add le_rfl (mul_le_mul' le_rfl hν)
    _ = 2*ENNReal.ofReal (δ^b) := by ring

end Falconer

end OAI
