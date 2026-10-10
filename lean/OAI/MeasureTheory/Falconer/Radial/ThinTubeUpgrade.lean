import OAI.MeasureTheory.Falconer.Estimates.NonendpointAvailabilityGain
import OAI.MeasureTheory.Falconer.Estimates.EndpointAvailabilityGain

namespace OAI

/-! # The thin-tube upgrade in the original pair measures

Proposition `prep:thin-upgrade`: the integer exponent improves to the adjacent
half-integer. The endpoint and nonendpoint gains below are proved geometric
inputs, not extra hypotheses about availability.
-/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem thin_tube_upgrade (hpublished : PublishedPlanarFurstenberg)
    (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {α ζ C D s Cplate : ℝ}
    (hα : (h:ℝ)+3/2 < α) (hα' : α < (h:ℝ)+2) (hζ : 0 < ζ) (hC : 0 ≤ C)
    (Q : DyadicCube (h+3)) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (h+3:ℕ) ≤ D) (hs : 0 < s)
    (μ ν : ProbabilityMeasure (Space (h+3)))
    (hμroot : (μ : Measure (Space (h+3))) Q.carrierᶜ = 0)
    (hνroot : (ν : Measure (Space (h+3))) Q.carrierᶜ = 0)
    (hμfrost : ∀ y : Space (h+3), ∀ r > 0, (μ : Measure (Space (h+3))) (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α))
    (hνfrost : ∀ y : Space (h+3), ∀ r > 0, (ν : Measure (Space (h+3))) (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α))
    (A P : Set (Space (h+3))) (hA : MeasurableSet A) (hP : MeasurableSet P)
    (hμA : (μ : Measure (Space (h+3))) Aᶜ = 0) (hνP : (ν : Measure (Space (h+3))) Pᶜ = 0)
    (hsep : ∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖)
    (hpin : ∀ y ∈ Q.carrier, ∀ x ∈ A ∪ P, ‖y-x‖ ≤ D)
    (Γ : ℕ → Set (Space (h+3) × Space (h+3))) (hΓ : ∀ N, MeasurableSet (Γ N))
    (hslab : ∀ N : ℕ, ∀ᵐ z ∂(μ : Measure (Space (h+3))),
      ∀ u : Space (h+3), ‖u‖ = 1 → ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        (ν : Measure (Space (h+3))) {x | (z,x) ∈ Γ N ∧ |inner ℝ u (normalize (x-z))| ≤ r} ≤
          ENNReal.ofReal (Cplate*r^ζ))
    (hslab' : ∀ N : ℕ, ∀ᵐ x ∂(ν : Measure (Space (h+3))),
      ∀ u : Space (h+3), ‖u‖ = 1 → ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        (μ : Measure (Space (h+3))) {z | (z,x) ∈ Γ N ∧ |inner ℝ u (normalize (z-x))| ≤ r} ≤
          ENNReal.ofReal (Cplate*r^ζ))
    (hstart : CapAvailable μ ν Γ ((h:ℝ)+1)) :
    CapAvailable μ ν Γ ((h:ℝ)+3/2) := by
  let t := (α+((h:ℝ)+3/2))/2
  have htt : (h:ℝ)+3/2 < t := by dsimp [t]; linarith only [hα]
  have htα : t < α := by dsimp [t]; linarith only [hα]
  have ht' : t < (h:ℝ)+2 := htα.trans hα'
  have hbase : ((h+2:ℕ):ℝ)-1 = (h:ℝ)+1 := by push_cast; ring
  have htop : ((h+2:ℕ):ℝ)-1/2 = (h:ℝ)+3/2 := by push_cast; ring
  have hresult := capAvailable_half_integer (h+2) μ ν Γ (by simpa only [hbase] using hstart) (by
    intro q hlow hu havail
    have hlo : (h:ℝ)+1 ≤ q := by simpa only [hbase] using hlow
    have hupper : q < (h:ℝ)+3/2 := by simpa only [htop] using hu
    have hex : ∃ r : ℝ, q < r ∧ CapAvailable μ ν Γ r := by
      by_cases heq : q = (h:ℝ)+1
      · exact CapAvailable.endpoint_improve hLW heq htt ht' hζ htα hC Q hQ hD hDdim hs μ ν
          hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin Γ hΓ hslab hslab' havail
      · have hq : ((h+1:ℕ):ℝ) < q := by push_cast; exact lt_of_le_of_ne hlo (Ne.symm heq)
        have hq' : q-((h+1:ℕ):ℝ) ≤ 1/2 := by push_cast; linarith only [hupper]
        have hqt : q < t := hupper.trans htt
        have ht : t-((h+1:ℕ):ℝ) < 1 := by push_cast; linarith only [ht']
        exact CapAvailable.nonendpoint_improve hpublished hq hq' hqt ht htα hC Q hQ hD hDdim hs μ ν
          hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin Γ hΓ havail
    obtain ⟨r,hqr,hr⟩ := hex
    refine ⟨min r (((h+2:ℕ):ℝ)-1/2),lt_min hqr hu,min_le_right _ _,?_⟩
    exact hr.mono (min_le_left _ _))
  simpa only [htop] using hresult

end Falconer

end OAI
