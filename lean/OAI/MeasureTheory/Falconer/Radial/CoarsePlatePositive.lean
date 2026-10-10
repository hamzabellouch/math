import OAI.MeasureTheory.Falconer.Radial.DyadicHeavyCover
import OAI.MeasureTheory.Falconer.Radial.InitialPlateLoss
import OAI.MeasureTheory.Falconer.Radial.LatePlateTail
import OAI.MeasureTheory.Falconer.Radial.CoarsePlateLimit

namespace OAI

/-! # Positive limiting mass of the actual coarse dyadic plate filter -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem coarse_plate_positive_limit (hpublished : PublishedHeavyHyperplanes)
    {d : ℕ} (hd : 3 ≤ d) (μ ν : ProbabilityMeasure (Space d))
    (Q : DyadicCube d) (hQ : 0 < Q.side) {M s C : ℝ}
    (hM : 0 ≤ M) (hroot : ∀ x ∈ Q.carrier, ‖x‖ ≤ M)
    (hs : 1/2 < s-((d-2:ℕ):ℝ)) (hs' : s-((d-2:ℕ):ℝ) < 1) (hC : 0 ≤ C)
    (hμbounded : ∀ᵐ x ∂(μ : Measure (Space d)), ‖x‖ ≤ M)
    (hνbounded : ∀ᵐ x ∂(ν : Measure (Space d)), ‖x‖ ≤ M)
    (hμfrost : FrostmanBallBound (μ : Measure (Space d)) s C)
    (hνfrost : FrostmanBallBound (ν : Measure (Space d)) s C)
    (hμroot : (μ : Measure (Space d)) Q.carrier = 1)
    (hνroot : (ν : Measure (Space d)) Q.carrier = 1)
    (hzero : ∀ w : Space d, ‖w‖ = 1 → ∀ t : ℝ,
      ((μ : Measure (Space d))+(ν : Measure (Space d))) {x | inner ℝ w x = t} = 0) :
    ∃ j₀ : ℕ, 0 < ((μ : Measure (Space d)).prod (ν : Measure (Space d)))
      (⋂ J : ℕ, coarsePlateFilter ((μ : Measure (Space d))+(ν : Measure (Space d)))
        Q j₀ J plateScale (fun j => 2*(plateScale j)^(heavyPlateExponent (s-((d-2:ℕ):ℝ))))) := by
  classical
  let ρ := (μ : Measure (Space d))+(ν : Measure (Space d))
  let b := heavyPlateExponent (s-((d-2:ℕ):ℝ))
  let E := dyadicPlateExclusions ρ Q b
  obtain ⟨A,hA,hS⟩ := dyadic_heavy_plate_covers hpublished hd μ ν Q hQ hM hroot
    hs hs' hC hμbounded hνbounded hμfrost hνfrost
  choose S hunit hcard hcover using hS
  have hνle : (ν : Measure (Space d)) ≤ ρ := by
    intro t
    change (ν : Measure (Space d)) t ≤ (μ : Measure (Space d)) t+(ν : Measure (Space d)) t
    exact le_add_left le_rfl
  have hρbounded : ∀ᵐ x ∂ρ, ‖x‖ ≤ M := ae_add_measure_iff.mpr ⟨hμbounded,hνbounded⟩
  have ha : 0 < s-((d-2:ℕ):ℝ) := by linarith only [hs]
  obtain ⟨hb,hgap,hgap'⟩ := plate_exponent_gaps ha
  have ha16 : 0 < (s-((d-2:ℕ):ℝ))/16 := by positivity
  have hinit := eventually_initial_plate_loss (μ : Measure (Space d)) (ν : Measure (Space d)) ρ
    E (fun j => measurableSet_dyadicPlateExclusions ρ Q b j) S hA hb hM hC
    (ha16.trans hgap') hνle hμbounded hνbounded hρbounded hμfrost hzero hunit hcard hcover
  have hlate := eventually_late_plate_tail (μ : Measure (Space d)) (ν : Measure (Space d)) ρ
    Q S hA hb hM hC (ha16.trans hgap) hνle hμbounded hνbounded hμfrost hunit hcard hcover
  obtain ⟨j₀,hi,hl⟩ := (hinit.and hlate).exists
  have hu := union_exclusion_mass ((μ : Measure (Space d)).prod (ν : Measure (Space d)))
    (fun i => E (j₀+i)) (63*j₀)
    (fun n => ((μ : Measure (Space d)).prod (ν : Measure (Space d)))
      (firstExclusion (fun i => E (j₀+i)) (63*j₀+n))) hi (fun _ => le_rfl)
  have hu' : ((μ : Measure (Space d)).prod (ν : Measure (Space d))) (⋃ i : ℕ, E (j₀+i)) ≤
      ENNReal.ofReal (1/2:ℝ) := by
    apply hu.trans ((add_le_add le_rfl hl).trans_eq ?_)
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  refine ⟨j₀,coarsePlateFilter_limit_pos _ ρ Q j₀ plateScale (fun j => 2*(plateScale j)^b) ?_ ?_⟩
  · rw [Measure.prod_prod,hμroot,hνroot,one_mul]
  · exact hu'.trans_lt (by norm_num)

end Falconer

end OAI
