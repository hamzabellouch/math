import OAI.Geometry.RCD.Sobolev.ContinuousSobolevTestOrder

namespace OAI

/-! # From bounds on compact Sobolev pairings to pointwise bounds -/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
  (Q : QuadraticCheegerEnergy μ)

theorem continuous_sub_le_of_sobolev_pairings {Ω A : Set X}
    (hΩ : IsOpen Ω) (hA : IsCompact A) (hΩA : Ω ⊆ A)
    (f g : X → ℝ) (hf : ContinuousOn f A) (hg : ContinuousOn g A) (C : ℝ)
    (htest : ∀ φ : SobolevSpace μ Q,
      (∀ᵐ x ∂μ, x ∉ A → SobolevSpace.toLp μ Q φ x = 0) →
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q φ x| ≤ 1) →
      (∫ x in A, SobolevSpace.toLp μ Q φ x*f x ∂μ) -
        (∫ x in A, SobolevSpace.toLp μ Q φ x*g x ∂μ) ≤
          C * ∫ x in A, |SobolevSpace.toLp μ Q φ x| ∂μ) :
    ∀ x ∈ Ω, f x-g x ≤ C := by
  have hnonpos := continuous_nonpos_of_sobolev_tests μ Q hΩ hΩA
    ((hf.sub hg).sub continuousOn_const |>.mono hΩA) (f := fun x => f x-g x-C) ?_
  · intro x hx
    have hh := hnonpos x hx
    linarith
  intro φ hφs hφ0 hφ1
  let Φ := SobolevSpace.toLp μ Q φ
  have hsA : ∀ᵐ x ∂μ, x ∉ A → Φ x = 0 := by
    filter_upwards [hφs] with x hx hnot
    exact hx (fun hxΩ => hnot (hΩA hxΩ))
  have hiΦ : IntegrableOn Φ A μ := lp_integrableOn_of_finite μ Φ A hA.measure_lt_top.ne
  obtain ⟨M,hM⟩ := hA.exists_bound_of_continuousOn hf
  obtain ⟨N,hN⟩ := hA.exists_bound_of_continuousOn hg
  have hiF : IntegrableOn (fun x => Φ x*f x) A μ :=
    hiΦ.mul_bdd (hf.aestronglyMeasurable hA.measurableSet)
      (by filter_upwards [ae_restrict_mem hA.measurableSet] with x hx; exact hM x hx)
  have hiG : IntegrableOn (fun x => Φ x*g x) A μ :=
    hiΦ.mul_bdd (hg.aestronglyMeasurable hA.measurableSet)
      (by filter_upwards [ae_restrict_mem hA.measurableSet] with x hx; exact hN x hx)
  have habs : (∫ x in A, |Φ x| ∂μ) = ∫ x in A, Φ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hφ0] with x hx
    exact abs_of_nonneg hx
  have hh := htest φ hsA hφ1
  rw [habs] at hh
  have he : (∫ x in A, Φ x*(f x-g x-C) ∂μ) =
      (∫ x in A, Φ x*f x ∂μ) - (∫ x in A, Φ x*g x ∂μ) -
        C*(∫ x in A, Φ x ∂μ) := by
    calc
      _ = ∫ x in A, (Φ x*f x-Φ x*g x)-C*Φ x ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = _ := by
        have he1 := integral_sub (hiF.sub hiG) (hiΦ.const_mul C)
        have he2 := integral_sub hiF hiG
        simp only [Pi.sub_apply] at he1 he2
        rw [he1,he2,integral_const_mul]
  change (∫ x in A, Φ x*(f x-g x-C) ∂μ) ≤ 0
  rw [he]
  linarith

theorem continuous_abs_sub_le_of_sobolev_pairings {Ω A : Set X}
    (hΩ : IsOpen Ω) (hA : IsCompact A) (hΩA : Ω ⊆ A)
    (f g : X → ℝ) (hf : ContinuousOn f A) (hg : ContinuousOn g A) (C : ℝ)
    (htest : ∀ φ : SobolevSpace μ Q,
      (∀ᵐ x ∂μ, x ∉ A → SobolevSpace.toLp μ Q φ x = 0) →
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q φ x| ≤ 1) →
      |(∫ x in A, SobolevSpace.toLp μ Q φ x*f x ∂μ) -
        (∫ x in A, SobolevSpace.toLp μ Q φ x*g x ∂μ)| ≤
          C * ∫ x in A, |SobolevSpace.toLp μ Q φ x| ∂μ) :
    ∀ x ∈ Ω, |f x-g x| ≤ C := by
  have hu := continuous_sub_le_of_sobolev_pairings μ Q hΩ hA hΩA f g hf hg C
    (fun φ hs hb => (le_abs_self _).trans (htest φ hs hb))
  have hl := continuous_sub_le_of_sobolev_pairings μ Q hΩ hA hΩA g f hg hf C
    (fun φ hs hb => (le_abs_self _).trans (by simpa only [abs_sub_comm] using htest φ hs hb))
  intro x hx
  exact abs_sub_le_iff.mpr ⟨hu x hx,hl x hx⟩

end RegularPointCoordinates

end

end OAI
