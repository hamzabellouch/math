import OAI.MeasureTheory.Falconer.Estimates.NonendpointTwoSidedScale
import OAI.MeasureTheory.Falconer.Radial.FiniteRadialRefinement
import OAI.MeasureTheory.Falconer.Radial.RadialScaleWindow

namespace OAI

/-! # The same original pair set can be improved throughout a dyadic scale window -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators

theorem nonendpoint_scale_window_gain (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {α t q C D s : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t)
    (ht : t-(h:ℝ) < 1) (htα : t < α) (hC : 0 ≤ C)
    (Q : DyadicCube (h+2)) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (h+2:ℕ) ≤ D) (hs : 0 < s) :
    ∃ ε gain : ℝ, 0 < ε ∧ 0 < gain ∧ ∀ K : ℕ, 0 < K →
      ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ ν : Measure (Space (h+2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        μ Q.carrierᶜ = 0 → ν Q.carrierᶜ = 0 →
        (∀ y : Space (h+2), ∀ r > 0, μ (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
        (∀ y : Space (h+2), ∀ r > 0, ν (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
      ∀ A P : Set (Space (h+2)), MeasurableSet A → MeasurableSet P →
        μ Aᶜ = 0 → ν Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ A ∪ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G →
        (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+2), ‖u‖ = 1 →
            ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^q)) →
        (∀ᵐ x ∂ν, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+2), ‖u‖ = 1 →
            μ {z | (z,x) ∈ G ∧ dist (normalize (z-x)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^q)) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        ∀ j : ℕ, N/K ≤ j → j ≤ N →
          (∀ x u : Space (h+2), μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^j} ≤
            ENNReal.ofReal ((1/(2:ℝ)^j)^(q+gain))) ∧
          (∀ z u : Space (h+2), ν {x | (z,x) ∈ G' ∧ ‖normalize (x-z)-u‖ ≤ 1/(2:ℝ)^j} ≤
            ENNReal.ofReal ((1/(2:ℝ)^j)^(q+gain))) := by
  obtain ⟨ε,gain,hε,hgain,Ns,hscale⟩ := nonendpoint_two_sided_one_scale hpublished hq hq' hqt
    ht htα hC Q hQ hD hDdim hs
  refine ⟨ε,gain,hε,hgain,?_⟩
  intro K hK
  obtain ⟨c,hc,Nc,hcost⟩ := radial_scale_window_cost K hK hgain
  refine ⟨c,hc,max (K*Ns) (max (2*K) Nc),?_⟩
  intro N hN μ ν _ _ hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hcap hcap'
  simp only [max_le_iff] at hN
  obtain ⟨hNs,hNK,hNc⟩ := hN
  have hstart : Ns ≤ N/K := (Nat.le_div_iff_mul_le hK).mpr (by simpa only [Nat.mul_comm] using hNs)
  have hcapSwap : ∀ᵐ z ∂ν, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space (h+2), ‖u‖ = 1 →
        μ {x | (z,x) ∈ Prod.swap ⁻¹' G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^q) := by
    simpa only [mem_preimage,Prod.swap_prod_mk] using hcap'
  obtain ⟨H,hH,hsub,hdel,hbounds⟩ := finite_radial_refinement μ ν G hG (Finset.Icc (N/K) N)
    (fun j => 2*ENNReal.ofReal (((2:ℝ)^j)^(-gain)))
    (fun j => ENNReal.ofReal ((1/(2:ℝ)^j)^(q+gain))) (fun j => 1/(2:ℝ)^j) (by
      intro j hj
      obtain ⟨hjlo,hjhi⟩ := Finset.mem_Icc.mp hj
      have hloss := radial_scale_window_loss hK hNK hjlo hε.le
      have hc₁ := reverse_caps_all_radii μ μ ν Measure.AbsolutelyContinuous.rfl
        (Subset.rfl (s := G)) hjhi hloss hcap
      have hc₂ := reverse_caps_all_radii ν ν μ Measure.AbsolutelyContinuous.rfl
        (Subset.rfl (s := Prod.swap ⁻¹' G)) hjhi hloss hcapSwap
      obtain ⟨H,hH,hsub,hdel,hbounds⟩ := hscale j (hstart.trans hjlo) μ ν
        hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hc₁
        (by simpa only [mem_preimage,Prod.swap_prod_mk] using hc₂)
      refine ⟨H,hH,hsub,hdel,?_⟩
      have he : ((2:ℝ)^j)^(-q-gain) = (1/(2:ℝ)^j)^(q+gain) := by
        rw [one_div,Real.inv_rpow (by positivity),← Real.rpow_neg (by positivity)]
        congr 1
        ring
      simpa only [he] using hbounds)
  refine ⟨H,hH,hsub,?_,fun j hjlo hjhi => hbounds j (Finset.mem_Icc.mpr ⟨hjlo,hjhi⟩)⟩
  apply hdel.trans
  rw [← Finset.mul_sum]
  exact mul_le_mul' le_rfl (hcost N hNc)

end Falconer.Regularization

end OAI
