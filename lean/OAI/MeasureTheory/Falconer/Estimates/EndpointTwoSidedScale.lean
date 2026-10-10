import OAI.MeasureTheory.Falconer.Radial.TwoSidedRadialIntersection
import OAI.MeasureTheory.Falconer.Estimates.EndpointOneScale

namespace OAI

/-! # Both orientations of the endpoint one-scale preparation estimate -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem endpoint_two_sided_one_scale (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {α t q ζ C D s : ℝ}
    (hq : q = (h:ℝ)+1) (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2)
    (hζ : 0 < ζ) (htα : t < α) (hC : 0 ≤ C)
    (Q : DyadicCube (h+3)) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (h+3:ℕ) ≤ D) (hs : 0 < s) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ ν : Measure (Space (h+3))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        μ Q.carrierᶜ = 0 → ν Q.carrierᶜ = 0 →
        (∀ y : Space (h+3), ∀ r > 0, μ (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
        (∀ y : Space (h+3), ∀ r > 0, ν (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
      ∀ A P : Set (Space (h+3)), MeasurableSet A → MeasurableSet P →
        μ Aᶜ = 0 → ν Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ A ∪ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space (h+3) × Space (h+3)), MeasurableSet G →
        (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+3), ‖u‖ = 1 →
            ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^q)) →
        (∀ᵐ z ∂μ, ∀ u : Space (h+3), ‖u‖ = 1 → ∀ r : ℝ,
          1/(2:ℝ)^N ≤ r → r ≤ 1 →
            ν {x | (z,x) ∈ G ∧ |inner ℝ u (normalize (x-z))| ≤ r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) →
        (∀ᵐ x ∂ν, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+3), ‖u‖ = 1 →
            μ {z | (z,x) ∈ G ∧ dist (normalize (z-x)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^q)) →
        (∀ᵐ x ∂ν, ∀ u : Space (h+3), ‖u‖ = 1 → ∀ r : ℝ,
          1/(2:ℝ)^N ≤ r → r ≤ 1 →
            μ {z | (z,x) ∈ G ∧ |inner ℝ u (normalize (z-x))| ≤ r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) →
      ∃ G' : Set (Space (h+3) × Space (h+3)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        (∀ x u : Space (h+3), μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-q-c))) ∧
        (∀ z u : Space (h+3), ν {x | (z,x) ∈ G' ∧ ‖normalize (x-z)-u‖ ≤ 1/(2:ℝ)^N} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-q-c))) := by
  obtain ⟨ε,c,hε,hc,N₀,hscale⟩ := endpoint_one_scale_gain hLW hq ht ht' hζ htα hC
    Q hQ hD hDdim hs
  refine ⟨ε,c,hε,hc,N₀,?_⟩
  intro N hN μ ν _ _ hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hcap hslab hcap' hslab'
  obtain ⟨H,hH,hHG,hHcost,hHcap⟩ := hscale N hN μ ν hμroot hμfrost A P hA hP hμA hνP
    hsep (fun y hy x hx => hpin y hy x (Or.inr hx)) G hG hcap hslab
  obtain ⟨K,hK,hKG,hKcost,hKcap⟩ := hscale N hN ν μ hνroot hνfrost P A hP hA hνP hμA
    (fun x hx z hz => by simpa only [norm_sub_rev] using hsep z hz x hx)
    (fun y hy x hx => hpin y hy x (Or.inl hx)) (Prod.swap ⁻¹' G) (hG.preimage measurable_swap)
    (by simpa only [mem_preimage,Prod.swap_prod_mk] using hcap')
    (by simpa only [mem_preimage,Prod.swap_prod_mk] using hslab')
  obtain ⟨G',hG',hsub,hdel,hcaps⟩ := intersect_radial_orientations μ ν G H K hG hH hK hHG hKG
    hHcost hKcost hHcap hKcap
  refine ⟨G',hG',hsub,?_,hcaps⟩
  simpa only [two_mul] using hdel

end Falconer.Regularization

end OAI
