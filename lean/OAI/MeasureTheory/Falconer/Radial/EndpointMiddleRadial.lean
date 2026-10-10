import OAI.MeasureTheory.Falconer.Radial.EndpointRadialBadDirections
import OAI.MeasureTheory.Falconer.Radial.MiddleRadialPruning
import OAI.MeasureTheory.Falconer.Radial.HeavyCoverCount

namespace OAI

/-! # Quantitative middle-interval improvement from finite Loomis–Whitney -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem endpoint_middle_radial_pruning (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ : ℝ} (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2)
    (hζ : 0 < ζ) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ ν : Measure (Space (h+3)))
        [IsProbabilityMeasure μ] [IsFiniteMeasure ν], ν univ ≤ 1 →
      ∀ (_w₀ : Sphere (h+3)) (G : Set (Space (h+3) × Space (h+3))), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → z ≠ x ∧ ‖z‖ ≤ 1/4) →
      (∀ᵐ z ∂μ, ‖z‖ ≤ 1/4) →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ᵐ z ∂μ,
        (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N →
          ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+3)) < 1/(2:ℝ)^j} ≤
            ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) ∧
        (∀ w : Sphere (h+3), ∀ u : ℝ, 1/(2:ℝ)^N ≤ u → u ≤ 1 →
          ν {x | (z,x) ∈ G ∧ |inner ℝ (w:Space (h+3)) (normalize (x-z))| ≤ u} ≤
            ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*u^ζ))) →
      ∀ r H θ : ℝ, 0 < r → 8*(1/4:ℝ)^2/r ≤ 1/(2:ℝ)^N →
      H*θ ≤ 1/(2:ℝ)^N →
      (∀ x, (∃ z, (z,x) ∈ G) → r ≤ ‖(0:Space (h+3))-x‖ ∧
        ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) →
      ∃ G' : Set (Space (h+3) × Space (h+3)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal ((1/(2:ℝ)^N)^b) ∧
        ∀ p ∈ G', radialCollisionMass μ θ p ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^((h+1:ℝ)+b/2)) := by
  let C : ℝ := 2*((h+3:ℕ):ℝ)+2
  let L : ℕ := h+6
  let K : ℕ := (2*L+1)^(h+3)
  obtain ⟨ε,b,hε,hb,N₁,hN₁⟩ := endpoint_radial_bad_directions hLW ht ht' hζ
    (show 0 ≤ C by dsimp [C]; positivity)
  obtain ⟨N₂,hN₂⟩ := eventually_heavy_cover_card (q := (h+1:ℝ)) (K := (K:ℝ)) hb (by positivity)
  refine ⟨ε,b,hε,hb,max N₁ N₂,?_⟩
  intro N hN μ ν _ _ hν w₀ G hG hgeom hμ hballs hcaps r H θ hr hfreeze hwidth hpin
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Bad,hBad,hcontains,hbadmass⟩ := hN₁ N ((le_max_left _ _).trans hN) μ ν hν
    w₀ G hG (fun z x hx => (hgeom z x hx).1.symm) hμ hballs hcaps
  have hL : 1+1+((h+2+1:ℕ):ℝ)+1/2 ≤ (L:ℝ) := by dsimp [L]; push_cast; linarith
  have hrobust : (2*((h+2+1:ℕ):ℝ)+1)*δ+2*(2*(1/4)/r)*(1/4+1/4) ≤ C*δ := by
    have he : 2*(2*(1/4:ℝ)/r)*(1/4+1/4) = 8*(1/4:ℝ)^2/r := by ring
    rw [he]
    dsimp [C]
    change 8*(1/4:ℝ)^2/r ≤ δ at hfreeze
    nlinarith
  have henv (v : Sphere (h+3)) (S : Finset (Space (h+3)))
      (hc : (S.card:ℝ≥0∞)*ENNReal.ofReal (δ^((h+1:ℝ)+b/2)) ≤
        ((2*L+1)^(h+2+1):ℕ)*μ univ)
      (hm : ENNReal.ofReal (δ^b) ≤
        μ {z | ∃ a ∈ S, ‖perpendicularPart (v:Space (h+3)) (z-a)‖ ≤ C*δ}) : v ∈ Bad := by
    apply hcontains
    refine ⟨S,?_,hm⟩
    apply hN₂ N ((le_max_right _ _).trans hN) S.card
    simpa only [measure_univ,mul_one,ENNReal.ofReal_natCast] using hc
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := middle_radial_pruning (θ := θ) (n := h+2) μ ν w₀ G hG
    Bad hBad 0 hr hδ hfreeze (by simpa only [sub_zero] using hμ) hμ
    (fun z x hx => ⟨(hgeom z x hx).1,by simpa only [sub_zero] using (hgeom z x hx).2,
      (hgeom z x hx).2⟩) hpin (by simpa only [one_mul] using hwidth) hrobust (ENNReal.ofReal (δ^((h+1:ℝ)+b/2)))
    (ENNReal.ofReal (δ^b)) (ENNReal.ofReal (δ^b)) L hL henv hbadmass
  refine ⟨G',hG',hsub,hdel.trans ?_,hbound⟩
  calc
    _ ≤ ENNReal.ofReal (δ^b)+ENNReal.ofReal (δ^b)*1 :=
      add_le_add le_rfl (mul_le_mul' le_rfl hν)
    _ = 2*ENNReal.ofReal (δ^b) := by ring

end Falconer

end OAI
