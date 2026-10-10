import OAI.Analysis.LipschitzHilbert.Packets.JointPacketAverage
import OAI.Analysis.LipschitzHilbert.Estimates.ShearedLatticePeriodization

namespace OAI

/-! The complete finite length/direction sum can use one product
probability average of the actual translated lattices. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lattice_periodization_integrable {l W theta : ℝ} (hl : 0<l) (hW : 0<W)
    (F : ℝ×ℝ → ℂ) (hF : Integrable F planeMeasure) :
    Integrable (fun z => ∑' n : ℤ×ℤ, F (latticeHom l W theta n+z))
      (latticeAverage l W theta) := by
  let G := (latticeHom l W theta).range
  let e : (ℤ×ℤ) ≃+ G :=
    AddMonoidHom.ofInjective (latticeHom_injective (theta := theta) hl.ne' hW.ne')
  let : Countable G := Countable.of_equiv (ℤ×ℤ) e.toEquiv
  have hm (n : ℤ×ℤ) : AEMeasurable (fun z => F (latticeHom l W theta n+z))
      (planeMeasure.restrict (latticeCell l W theta)) :=
    ((hF.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_add_left planeMeasure (latticeHom l W theta n))).restrict).aemeasurable
  have hmg (g : G) : AEMeasurable (fun z => ‖F (g+ᵥz)‖ₑ)
      (planeMeasure.restrict (latticeCell l W theta)) :=
    ((hF.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_add_left planeMeasure (g:ℝ×ℝ))).restrict).enorm
  have hfinite : (∫⁻ z in latticeCell l W theta,
      ∑' n : ℤ×ℤ, ‖F (latticeHom l W theta n+z)‖ₑ ∂planeMeasure) < ∞ := by
    have heq (z : ℝ×ℝ) : (∑' n : ℤ×ℤ, ‖F (latticeHom l W theta n+z)‖ₑ) =
        ∑' g : G, ‖F (g+ᵥz)‖ₑ :=
      e.toEquiv.tsum_eq (fun g : G => ‖F (g+ᵥz)‖ₑ)
    simp_rw [heq]
    rw [lintegral_tsum hmg, ← (latticeCell_fundamental (theta := theta) hl hW).lintegral_eq_tsum'' (fun z => ‖F z‖ₑ)]
    exact hF.hasFiniteIntegral
  have hi : Integrable (fun z => ∑' n : ℤ×ℤ, F (latticeHom l W theta n+z))
      (planeMeasure.restrict (latticeCell l W theta)) := by
    refine ⟨(AEMeasurable.tsum hm).aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt (lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)) hfinite
  exact hi.smul_measure (by
    exact ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos hl hW))))

theorem joint_lattice_average_bound {ι : Type*} [Fintype ι]
    (l W theta : ι → ℝ) (hl : ∀ i, 0<l i) (hW : ∀ i, 0<W i)
    (F : ι → (ℝ×ℝ) → ℂ) (hF : ∀ i, Integrable (F i) planeMeasure)
    (C : ℝ)
    (hfinite : ∀ z : ι → (ℝ×ℝ), ∀ S : Finset (ι×(ℤ×ℤ)),
      ‖∑ p ∈ S, ((l p.1*W p.1:ℝ):ℂ)⁻¹*
        F p.1 (latticeHom (l p.1) (W p.1) (theta p.1) p.2+z p.1)‖ ≤ C) :
    ‖∑ i, (((l i*W i:ℝ):ℂ)^2)⁻¹ * ∫ z, F i z ∂planeMeasure‖ ≤ C := by
  let μ := fun i => latticeAverage (l i) (W i) (theta i)
  let value := fun i z => ∑' n : ℤ×ℤ, ((l i*W i:ℝ):ℂ)⁻¹*
    F i (latticeHom (l i) (W i) (theta i) n+z)
  let term := fun i z n => ((l i*W i:ℝ):ℂ)⁻¹*
    F i (latticeHom (l i) (W i) (theta i) n+z)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => latticeAverage_probability (hl i) (hW i)
  have hvalue (i : ι) : Integrable (value i) (μ i) := by
    dsimp only [value, μ]
    simp_rw [tsum_mul_left]
    exact (lattice_periodization_integrable (hl i) (hW i) (F i) (hF i)).const_mul _
  have hseries (i : ι) : ∀ᵐ z ∂μ i,
      Summable (fun n => ‖term i z n‖) ∧ (∑' n, term i z n) = value i z := by
    filter_upwards [sheared_lattice_summable (hl i) (hW i) (F i) (hF i)] with z hz
    refine ⟨?_, rfl⟩
    simpa only [term, norm_mul] using hz.mul_left ‖((l i*W i:ℝ):ℂ)⁻¹‖
  have h := joint_packet_average_bound μ value hvalue term hseries C hfinite
  have heq (i : ι) : (∫ z, value i z ∂μ i) =
      (((l i*W i:ℝ):ℂ)^2)⁻¹ * ∫ z, F i z ∂planeMeasure := by
    dsimp only [μ, value]
    rw [integral_latticeAverage (hl i) (hW i)]
    simp_rw [tsum_mul_left]
    rw [integral_const_mul, ← sheared_lattice_periodization (hl i) (hW i) (F i) (hF i)]
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul, pow_two, mul_inv_rev]
    ring
  simpa only [heq] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
