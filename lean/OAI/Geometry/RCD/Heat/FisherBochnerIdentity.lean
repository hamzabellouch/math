import OAI.Geometry.RCD.Heat.FisherSourceCancellation
import OAI.Geometry.RCD.Heat.FisherEnergyCancellation

namespace OAI

/-! # The exact identity between Fisher variation and logarithmic Bochner

Every cancellation uses an actual bounded Sobolev test. Both Laplacian
sources may be unbounded L² functions.
-/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
private theorem shifted_product_coe (u w : SobolevSpace μ hQ) (ε : ℝ) (A C : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x|≤A)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x|≤C) :
    SobolevSpace.toLp μ hQ (ε • w+SobolevSpace.product μ hQ u w A C) =ᵐ[μ]
      fun x => (ε+SobolevSpace.toLp μ hQ u x)*SobolevSpace.toLp μ hQ w x := by
  filter_upwards [SobolevSpace.product_coe μ hQ u w A C hu hw,
    Lp.coeFn_add (ε • SobolevSpace.toLp μ hQ w)
      (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ u w A C)),
    Lp.coeFn_smul ε (SobolevSpace.toLp μ hQ w)] with x hp ha hs
  change (ε • SobolevSpace.toLp μ hQ w+
    SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ u w A C)) x = _
  simp only [ha,Pi.add_apply,hs,Pi.smul_apply,smul_eq_mul,hp]
  ring

theorem fisher_bochner_identity (u d w ℓ S H : SobolevSpace μ hQ)
    (e : Lp ℝ 2 μ) (K : ℝ)
    (hd : IsWeakLaplacian μ hQ u (SobolevSpace.toLp μ hQ d))
    (he : IsWeakLaplacian μ hQ w e)
    (hS : IsWeakLaplacian μ hQ ℓ (SobolevSpace.toLp μ hQ S))
    {ε : ℝ} (hε : 0<ε) (A C B L M : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ u x∈Icc 0 (A:ℝ))
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x|≤C)
    (hH : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ H x|≤B)
    (hLu : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ u x≤L)
    (hLℓ : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ ℓ x≤M)
    (hℓ : SobolevSpace.toLp μ hQ ℓ =ᵐ[μ]
      fun x => Real.log (ε+SobolevSpace.toLp μ hQ u x)-Real.log ε)
    (hHr : SobolevSpace.toLp μ hQ H =ᵐ[μ] fun x => localGamma μ hQ u u x /
      (ε+SobolevSpace.toLp μ hQ u x)^2)
    (hSr : SobolevSpace.toLp μ hQ S =ᵐ[μ] fun x =>
      SobolevSpace.toLp μ hQ d x/(ε+SobolevSpace.toLp μ hQ u x)-SobolevSpace.toLp μ hQ H x) :
    ∃ (R : SobolevSpace μ hQ) (N : ℝ≥0),
      (SobolevSpace.toLp μ hQ R =ᵐ[μ] fun x =>
        (ε+SobolevSpace.toLp μ hQ u x)*SobolevSpace.toLp μ hQ w x) ∧
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ R x|≤N) ∧
      (∫ x, e x*localGamma μ hQ u u x/(ε+SobolevSpace.toLp μ hQ u x) ∂μ)+
        (∫ x, SobolevSpace.toLp μ hQ w x*SobolevSpace.toLp μ hQ d x*
          localGamma μ hQ u u x/(ε+SobolevSpace.toLp μ hQ u x)^2 ∂μ)-
        2*(∫ x, SobolevSpace.toLp μ hQ w x*localGamma μ hQ u d x /
          (ε+SobolevSpace.toLp μ hQ u x) ∂μ) =
      2*(bochnerTestForm μ hQ (-K) H R-weightedGamma μ hQ (SobolevSpace.toLp μ hQ R) ℓ S)+
        2*K*(∫ x, SobolevSpace.toLp μ hQ w x*localGamma μ hQ u u x /
          (ε+SobolevSpace.toLp μ hQ u x) ∂μ) := by
  obtain ⟨R,N,hRr,hRb,hcancel⟩ := fisher_source_cancellation μ hQ u d w ℓ S H hd
    hε A C B L M hu hw hH hLu hLℓ hℓ hHr hSr
  have huA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x|≤A :=
    hu.mono fun x hx => (abs_of_nonneg hx.1).trans_le hx.2
  have hRc : R=ε • w+SobolevSpace.product μ hQ u w A C := by
    apply Subtype.ext
    exact Lp.ext (hRr.trans (shifted_product_coe μ hQ u w ε A C huA hw).symm)
  let Z := ε • H+SobolevSpace.product μ hQ u H A B
  have hZr := shifted_product_coe μ hQ u H ε A B huA hH
  change SobolevSpace.toLp μ hQ Z =ᵐ[μ] _ at hZr
  have henergy := fisher_energy_source_cancellation μ hQ u w H
    (SobolevSpace.toLp μ hQ d) hd ε A C B huA hw hH
  rw [←hRc] at henergy
  have hboch := bochner_source_square μ hQ ℓ S H R (-K) N M hRb hLℓ hS
  have hI : inner ℝ (SobolevSpace.toLp μ hQ R) (SobolevSpace.toLp μ hQ H) =
      ∫ x, SobolevSpace.toLp μ hQ w x*localGamma μ hQ u u x /
        (ε+SobolevSpace.toLp μ hQ u x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hRr,hHr,hu] with x hr hh hx
    simp only [Real.inner_apply,hr,hh]
    have hz : ε+SobolevSpace.toLp μ hQ u x≠0 :=
      (add_pos_of_pos_of_nonneg hε hx.1).ne'
    field_simp [hz]
  have hZ : inner ℝ e (SobolevSpace.toLp μ hQ Z) =
      ∫ x, e x*localGamma μ hQ u u x/(ε+SobolevSpace.toLp μ hQ u x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hZr,hHr,hu] with x hz hh hx
    simp only [Real.inner_apply,hz,hh]
    have hz' : ε+SobolevSpace.toLp μ hQ u x≠0 :=
      (add_pos_of_pos_of_nonneg hε hx.1).ne'
    field_simp [hz']
  have hfirst : (∫ x, e x*localGamma μ hQ u u x /
      (ε+SobolevSpace.toLp μ hQ u x) ∂μ) = -energyForm μ hQ w Z := by
    have htest := he Z
    rw [hZ] at htest
    linarith only [htest]
  have hsecond : (∫ x, SobolevSpace.toLp μ hQ w x*SobolevSpace.toLp μ hQ d x*
      localGamma μ hQ u u x/(ε+SobolevSpace.toLp μ hQ u x)^2 ∂μ) =
      ∫ x, SobolevSpace.toLp μ hQ w x*SobolevSpace.toLp μ hQ H x*
        SobolevSpace.toLp μ hQ d x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hHr] with x hx
    rw [hx]
    ring
  rw [hI] at hboch
  refine ⟨R,N,hRr,hRb,?_⟩
  rw [hfirst,hsecond]
  change energyForm μ hQ H R-energyForm μ hQ w Z+_+_=0 at henergy
  linarith only [henergy,hboch,hcancel]

end RegularPointCoordinates

end

end OAI
