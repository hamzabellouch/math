import OAI.Geometry.SurfaceImmersion.Primitive.CircularFamilyProfile
import OAI.Geometry.SurfaceImmersion.Primitive.ActualProfileCrossing

namespace OAI

/-! A fixed transverse-turn threshold suffices for both ordered crossing
invariants, for every later sufficiently accurate exact realization. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame VelocityFrame RealModes SmallModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_circular_actual_crossings {Q X Y C e₁ e₂ : E → Vec} {R : E → ℝ}
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hQ : ContDiffOn ℝ ∞ Q U) (hX : ContDiffOn ℝ ∞ X U)
    (hY : ContDiffOn ℝ ∞ Y U) (hC : ContDiffOn ℝ ∞ C U)
    (hR : ContDiffOn ℝ ∞ R U) (h₁ : ContDiffOn ℝ ∞ e₁ U) (h₂ : ContDiffOn ℝ ∞ e₂ U)
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0)
    (hframe : ∀ x ∈ U, e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (hRpos : ∀ x ∈ U, 0 < R x) (d : E) (B T : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ α : E × ℝ → ℝ,
      ContDiffOn ℝ ∞ α (U ×ˢ univ) →
      (∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, fderiv ℝ α (x,t) (0,1) = 0 →
        Λ < fderiv ℝ α (x,t) (d,0)) →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℝ, 0 < z → z < η →
      ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ F : RField 4, ContDiff ℝ ∞ F →
      ∀ p : SmallModes.Base, ‖realBoundaryProfile F z p-
        circularFamilyProfile Q X Y C R e₁ e₂ α d (x,t)‖ < η →
      ∀ κ : ℝ,
      coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p =
        κ*gramDet (coordDeriv dx F p) (coordDeriv dy F p) →
      -B ≤ coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p →
      ∀ a b : ℝ, |a| ≤ T → |b| ≤ T →
        0 < orderedCrossing F (1,a) (1,b) p κ ∧
        0 < orderedCrossing F (1,b) (1,a) p κ := by
  let Z : Set (E × ℝ) := K ×ˢ Icc (0 : ℝ) 1
  let : CompactSpace Z := isCompact_iff_compactSpace.mp (hK.prod isCompact_Icc)
  obtain ⟨sLo,sHi,D,hsLo,hsHi,hD0,hbounds⟩ := compact_circular_profile_threshold
    hU hK hKU hQ hX hY hC hR h₁ h₂ hD hframe hRpos d
  obtain ⟨H,hH,hcross⟩ := compact_actual_profile_crossings (X := Z)
    sLo sHi B D T hsLo hsHi hB hD0 hT
  obtain ⟨Λ,hΛ,hprofile⟩ := hbounds H hH.le
  refine ⟨Λ,hΛ,?_⟩
  intro α hα hturn
  let J : Z → BoundaryProfile := fun z => circularFamilyProfile Q X Y C R e₁ e₂ α d z.1
  have hJ : Continuous J := by
    change Continuous (Z.domRestrict (circularFamilyProfile Q X Y C R e₁ e₂ α d))
    apply ContinuousOn.domRestrict
    exact (circularFamilyProfile_smoothOn hU hQ hX hY hC hR h₁ h₂ hα hD d).continuousOn.mono
      (fun z hz => ⟨hKU hz.1,mem_univ _⟩)
  have hdata (z : Z) : J z ∈ regularBoundaryProfiles ∧
      sLo ≤ profileCoefficients (J z) 0 ∧ profileCoefficients (J z) 0 ≤ sHi ∧
      |profileCoefficients (J z) 1| ≤ D ∧
      (profileCoefficients (J z) 3 = 0 → H+2 < |profileCoefficients (J z) 2|) := by
    let x := z.1.1
    let t := z.1.2
    have hx : x ∈ U := hKU z.2.1
    have hαat := (hα.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hx,mem_univ t⟩)).differentiableAt (by simp)
    have hαslice : DifferentiableAt ℝ (fun y => α (y,t)) x :=
      hαat.comp x (differentiableAt_id.prodMk (differentiableAt_const t))
    have heq : J z = circularSpatialProfile Q X Y C R e₁ e₂ (fun y => α (y,t))
        (fderiv ℝ α (x,t) (0,1)) x d :=
      circularFamilyProfile_spatial
        ((hQ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
        ((hR.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
        ((h₁.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
        ((h₂.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) hαat d
    rw [heq]
    obtain ⟨hreg,hlo,hhi,hd,hlarge⟩ := hprofile (fun y => α (y,t)) x z.2.1 hαslice
      (fderiv ℝ α (x,t) (0,1))
    refine ⟨hreg,hlo,hhi,hd,?_⟩
    intro hzero
    have hf := hframe x hx
    have hβ : fderiv ℝ α (x,t) (0,1) = 0 :=
      (circularBoundaryProfile_turn_iff (hD x hx) (hRpos x hx).ne'
        hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2.2).mp hzero
    apply hlarge
    rw [fderiv_slice_first hαat]
    exact hturn x z.2.1 t z.2.2 hβ
  obtain ⟨η,hη,hactual⟩ := hcross J hJ (fun z => (hdata z).1)
    (fun z => (hdata z).2.1) (fun z => (hdata z).2.2.1)
    (fun z => (hdata z).2.2.2.1) (fun z => (hdata z).2.2.2.2)
  refine ⟨η,hη,?_⟩
  intro z hz hzη x hx t ht F hF p herr κ hκ hcurv a b ha hb
  exact hactual z hz hzη ⟨(x,t),hx,ht⟩ F hF p herr κ hκ hcurv a b ha hb

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
