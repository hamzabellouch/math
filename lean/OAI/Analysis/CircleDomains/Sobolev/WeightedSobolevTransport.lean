import OAI.Analysis.CircleDomains.Sobolev.PlanarSobolevTransport

namespace OAI

/-! Preserve a common pointwise derivative bound when transporting rectangle
weak derivatives into the Euclidean Sobolev witness. -/

open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

theorem exists_bounded_rectangle_sobolev_witness
    {f Gx Gy r : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hf : MemLp f 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hx : MemLp Gx 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hy : MemLp Gy 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hbound : ∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d),
      |Gx p| ≤ r p ∧ |Gy p| ≤ r p)
    (hweak : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ioo c d →
      (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (1, 0)) =
        -(∫p in Icc a b ×ˢ Icc c d, Gx p * φ p) ∧
      (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (0, 1)) =
        -(∫p in Icc a b ×ˢ Icc c d, Gy p * φ p)) :
    ∃H : DeGiorgi.MemW1pWitness 2 (f ∘ euclideanPlaneCoordinates)
        (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)),
      ∀i : Fin 2, ∀ᵐ x ∂volume.restrict
        (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)),
        |H.weakGrad x i| ≤ r (euclideanPlaneCoordinates x) := by
  let W := Ioo a b ×ˢ Ioo c d
  have hmp := euclideanPlaneCoordinates_measurePreserving.restrict_preimage (s := W)
    (isOpen_Ioo.prod isOpen_Ioo).measurableSet
  have hf' : MemLp f 2 (volume.restrict W) := by rwa [rectangle_restrict_Ioo_eq_Icc]
  have hx' : MemLp Gx 2 (volume.restrict W) := by rwa [rectangle_restrict_Ioo_eq_Icc]
  have hy' : MemLp Gy 2 (volume.restrict W) := by rwa [rectangle_restrict_Ioo_eq_Icc]
  have hb' : ∀ᵐ p ∂volume.restrict W, |Gx p| ≤ r p ∧ |Gy p| ≤ r p := by
    rwa [rectangle_restrict_Ioo_eq_Icc]
  let G : EuclideanPlane → EuclideanPlane := fun x =>
    WithLp.toLp 2 fun i => if i = 0 then Gx (euclideanPlaneCoordinates x)
      else Gy (euclideanPlaneCoordinates x)
  let H : DeGiorgi.MemW1pWitness 2 (f ∘ euclideanPlaneCoordinates)
      (euclideanPlaneCoordinates ⁻¹' W) := {
    memLp := hf'.comp_measurePreserving hmp
    weakGrad := G
    weakGrad_component_memLp := by
      intro i
      fin_cases i
      · exact hx'.comp_measurePreserving hmp
      · exact hy'.comp_measurePreserving hmp
    isWeakGrad := by
      intro i
      fin_cases i
      · exact weakPartial_of_planar_identity 0 (1, 0) euclideanPlaneCoordinates_single_zero
          (fun φ hφ hs hsub => (hweak φ hφ hs hsub).1)
      · exact weakPartial_of_planar_identity 1 (0, 1) euclideanPlaneCoordinates_single_one
          (fun φ hφ hs hsub => (hweak φ hφ hs hsub).2) }
  refine ⟨H, ?_⟩
  intro i
  have hb := hmp.quasiMeasurePreserving.ae hb'
  filter_upwards [hb] with x hx
  fin_cases i
  · exact hx.1
  · exact hx.2

end CircleDomainRigidity

end

end OAI
