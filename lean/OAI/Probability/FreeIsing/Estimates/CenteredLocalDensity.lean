import OAI.Probability.FreeIsing.Estimates.FiniteCoordinateRepresentation
import OAI.Probability.FreeIsing.Spectral.KoopmanInvolutions

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367

theorem dense_centered_finite_coordinate
    {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ] :
    Dense {f : centeredL2 μ | ∃ (s : Finset ι) (g : (∀ i : s, X i) → ℝ),
      Measurable g ∧ (fun x => (f : Lp ℝ 2 μ) x) =ᵐ[μ] g ∘ s.restrict} := by
  apply Metric.dense_iff.mpr
  intro f ε hε
  obtain ⟨s, g, hgm, hgLp, hint, happrox⟩ :=
    exists_finite_coordinate_Lp_approx μ (by norm_num : 1 ≤ (2 : ENNReal))
      (by norm_num : (2 : ENNReal) ≠ ⊤) (Lp.memLp (f : Lp ℝ 2 μ))
      (ENNReal.ofReal_pos.mpr hε)
  let gLp : Lp ℝ 2 μ := hgLp.toLp (g ∘ s.restrict)
  have hcenter : gLp ∈ centeredL2 μ := by
    rw [mem_centeredL2_iff]
    calc
      (∫ x, gLp x ∂μ) = ∫ x, g (s.restrict x) ∂μ :=
        integral_congr_ae hgLp.coeFn_toLp
      _ = ∫ x, (f : Lp ℝ 2 μ) x ∂μ := hint
      _ = 0 := (mem_centeredL2_iff _).mp f.property
  refine ⟨⟨gLp, hcenter⟩, ?_, s, g, hgm, hgLp.coeFn_toLp⟩
  change dist gLp (f : Lp ℝ 2 μ) < ε
  rw [dist_comm, Lp.dist_def]
  apply ENNReal.toReal_lt_of_lt_ofReal
  rw [eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hgLp.coeFn_toLp)]
  exact happrox

end Problem367

end

end OAI
