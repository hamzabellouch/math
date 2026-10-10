import OAI.MeasureTheory.Falconer.Measures.RootNormalizedError
import OAI.MeasureTheory.Falconer.Estimates.RootWeightedDistance

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter

noncomputable def rootNormalizedF (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (n : ℕ) (U V : DyadicSquare) (r : ℝ) : ℂ :=
  ∫ z, rootNormalizedKernel d e N sig n r (sourceConeCircle (sourceParentAxis U V)) z ∂d.ρ.prod e.ρ

theorem rootNormalizedF_error_of_pointwise (d e : RootEndpointData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (N : ℕ) (sig : ℝ)
    (n : ℕ) (U V : DyadicSquare) (r ε : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ᵐ z ∂d.ρ.prod e.ρ, δ ≤ dist z.1 z.2)
    (herr : ∀ᵐ z ∂d.ρ.prod e.ρ,
      ‖(rootSpatialWeight d e N sig z:ℂ)*Complex.exp (Complex.I*((r*dist z.1 z.2:ℝ):ℂ)) -
        rootNormalizedKernel d e N sig n r (sourceConeCircle (sourceParentAxis U V)) z‖ ≤ ε) :
    Integrable (rootNormalizedKernel d e N sig n r (sourceConeCircle (sourceParentAxis U V)))
      (d.ρ.prod e.ρ) ∧
    ‖charFun (rootWeightedDistance d e N sig) r - rootNormalizedF d e N sig n U V r‖ ≤
      (d.ρ.prod e.ρ).real univ * ε := by
  let μ := d.ρ.prod e.ρ
  let ψ := sourceConeCircle (sourceParentAxis U V)
  let K := rootNormalizedKernel d e N sig n r ψ
  let f := fun z : Plane × Plane =>
    (rootSpatialWeight d e N sig z:ℂ)*Complex.exp (Complex.I*((r*dist z.1 z.2:ℝ):ℂ))
  have hfm : Measurable f := by
    apply Measurable.mul (Complex.measurable_ofReal.comp (rootSpatialWeight_measurable d e N sig))
    fun_prop
  have hfb : ∀ᵐ z ∂μ, ‖f z‖ ≤ δ^(-(1/2:ℝ)) := by
    filter_upwards [hsep] with z hz
    have hw := rootSpatialWeight_le d e hd he N sig hδ hz
    have hw0 := rootSpatialWeight_nonneg d e hd he N sig z
    simpa [f,norm_mul,Complex.norm_exp,Complex.mul_re,Complex.mul_im,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw0] using hw
  have hfi : Integrable f μ := Integrable.of_bound hfm.aestronglyMeasurable _ hfb
  have hkm : Measurable K := (rootNormalizedKernel_measurable d e N sig n ψ
    (measurable_sourceConeCircle _)).comp (f := fun z : Plane × Plane => (r,z))
      (measurable_const.prodMk measurable_id)
  have hki : Integrable K μ := by
    refine Integrable.of_bound hkm.aestronglyMeasurable (ε+δ^(-(1/2:ℝ))) ?_
    filter_upwards [herr,hfb] with z hz hb
    calc
      ‖K z‖ = ‖(K z-f z)+f z‖ := by rw [sub_add_cancel]
      _ ≤ ‖K z-f z‖+‖f z‖ := norm_add_le _ _
      _ ≤ ε+δ^(-(1/2:ℝ)) := add_le_add (by simpa only [norm_sub_rev] using hz) hb
  refine ⟨hki,?_⟩
  rw [rootWeightedDistance_fourier d e hd he N sig r,rootNormalizedF]
  change ‖(∫ z, f z ∂μ)-(∫ z, K z ∂μ)‖ ≤ _
  rw [← integral_sub hfi hki]
  exact (norm_integral_le_of_norm_le_const herr).trans_eq (mul_comm _ _)

theorem rootNormalizedF_measurable (d e : RootEndpointData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ] (N : ℕ) (sig : ℝ)
    (n : ℕ) (U V : DyadicSquare) : Measurable (rootNormalizedF d e N sig n U V) :=
  (rootNormalizedKernel_measurable d e N sig n _ (measurable_sourceConeCircle _)).stronglyMeasurable.integral_prod_right'.measurable

theorem root_pair_ae_patches (d e : RootEndpointData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ] (U V : DyadicSquare)
    (hU : ∀ᵐ x ∂d.ρ, x ∈ U.carrier) (hV : ∀ᵐ y ∂e.ρ, y ∈ V.carrier) :
    ∀ᵐ z ∂d.ρ.prod e.ρ, z.1 ∈ U.carrier ∧ z.2 ∈ V.carrier :=
  (Measure.quasiMeasurePreserving_fst.ae hU).and (Measure.quasiMeasurePreserving_snd.ae hV)

end PlanarFalconer

end OAI
