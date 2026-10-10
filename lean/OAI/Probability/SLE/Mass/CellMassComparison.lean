import OAI.Probability.SLE.Mass.InverseMassDilation
import OAI.Probability.SLE.Mass.CanonicalMassContinuity

namespace OAI

/-! At a fixed conformal-radius level the normalized disk mass bounds the
mass of a small cell and is bounded by the mass of a larger physical ball. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Multipoint

lemma Multipoint.ContinuousMassPath.zero_on_surviving
    {γ : ℝ≥0 → ℂ} {μ : ℚ → Measure upperHalfPlane} {ν : Measure upperHalfPlane}
    {N : ℝ≥0 → Measure upperHalfPlane} (hp : ContinuousMassPath γ μ ν N)
    (t : ℝ≥0) : N t (Subtype.val ⁻¹' survivingDomain γ t)=0 := by
  have h := hp.increment_support 0 t (show 0 ≤ t from zero_le)
  rw [hp.zero,Measure.sub_zero] at h
  apply le_zero_iff.mp
  apply (measure_mono ?_).trans_eq h
  intro z hz
  rintro ⟨s,hs,he⟩
  apply hz.1.2
  refine ⟨s.toNNReal,⟨zero_le,?_⟩,he⟩
  simpa only [Real.toNNReal_coe] using Real.toNNReal_mono hs.2

lemma Multipoint.ContinuousMassPath.zero_on_surviving_subset
    {γ : ℝ≥0 → ℂ} {μ : ℚ → Measure upperHalfPlane} {ν : Measure upperHalfPlane}
    {N : ℝ≥0 → Measure upperHalfPlane} (hp : ContinuousMassPath γ μ ν N)
    (t : ℝ≥0) (A : Set ℂ) (hA : A ⊆ survivingDomain γ t) :
    N t (Subtype.val ⁻¹' A)=0 :=
  le_zero_iff.mp ((measure_mono (preimage_mono hA)).trans_eq (hp.zero_on_surviving t))

lemma measure_sub_apply_of_zero
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X) [SigmaFinite μ]
    (hle : μ ≤ ν) (A : Set X) (hz : μ A=0) : (ν-μ) A=ν A := by
  have he := congrArg (fun ρ : Measure X => ρ A) (sigmaFinite_sub_add_cancel_of_le hle)
  simpa only [Measure.add_apply,hz,add_zero] using he

lemma IsCapacityTwoWitness.cell_mass_comparison
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hgrowth : PublishedDiskUnivalentGrowth)
    (κ : ℝ) (hκ : 0<κ) (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t)
    (r : ℝ) (hr : 0<r) (hR : fullRadius G t z=(2048*Real.pi)*r)
    (a : ℝ≥0) (ha : 0<a)
    (he : G t z=(U t:ℂ)+(a:ℂ)*Complex.exp (θ*Complex.I))
    (μ : Measure upperHalfPlane) [IsFiniteMeasureOnCompacts μ] :
    let ν := weightedImageMass (fun w : upperHalfPlane => F t ((w:ℂ)+(U t:ℂ)))
      (fun w : upperHalfPlane => ENNReal.ofReal
        (‖deriv (F t) ((w:ℂ)+(U t:ℂ))‖^dimension κ)) (dilationMass κ a ha μ)
    let L := ENNReal.ofReal (compactWeightedMass (Target.diskMassWeight κ θ hθ)
      (Target.diskSourceHalfPlane θ) μ)
    ENNReal.ofReal (((128*Real.pi)*r)^dimension κ)*L ≤
        ν (closedBall z ((4096*Real.pi)*r)) ∧
      ∀ A : Set ℂ, A ⊆ closedBall z (2*r) →
        ν A ≤ ENNReal.ofReal (((32768*Real.pi)*r)^dimension κ)*L := by
  let f := physicalDiskChart id F G t z
  have hRp : 0<fullRadius G t z := by rw [hR]; positivity
  obtain ⟨_,hinner,houter,_,_⟩ := hw.quarter_disk_chart_bounds hgrowth t z hz hRp
  have hb := hw.physical_quarter_mass_bounds hgrowth κ hκ θ hθ t z hz a he μ
  have hi : fullRadius G t z/(1024*Real.pi)=2*r := by
    rw [hR]
    field_simp
    ring
  have ho : 2*fullRadius G t z=(4096*Real.pi)*r := by rw [hR]; ring
  have hl : fullRadius G t z/16=(128*Real.pi)*r := by rw [hR]; ring
  have hu : 16*fullRadius G t z=(32768*Real.pi)*r := by rw [hR]; ring
  change ENNReal.ofReal ((fullRadius G t z/16)^dimension κ)*_ ≤ _ ∧
    _ ≤ ENNReal.ofReal ((16*fullRadius G t z)^dimension κ)*_ at hb
  rw [hl,hu] at hb
  rw [hi] at hinner
  rw [ho] at houter
  dsimp only
  rw [hw.inverse_mass_dilation κ hκ t a ha μ]
  refine ⟨hb.1.trans (measure_mono houter),?_⟩
  intro A hA
  exact (measure_mono (hA.trans hinner)).trans hb.2

end SLEExactGauge

end

end OAI
