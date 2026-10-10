import OAI.Probability.ProjectionMoments.Frames

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[fun_prop] lemma measurable_coordinateMap (m : ℕ) :
    Measurable (fun z : (Fin m → E) × E => coordinateMap z.1 z.2) := by
  apply Measurable.of_eval
  intro i
  simp only [coordinateMap_apply]
  fun_prop

def projectionKernel (ν : Measure E) [SFinite ν] (m : ℕ) : Kernel (Fin m → E) (Fin m → ℝ) where
  toFun A := ν.map (coordinateMap A)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have he (A : Fin m → E) : (ν.map (coordinateMap A)) s =
        ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) (coordinateMap A x) ∂ν := by
      rw [← lintegral_map (measurable_const.indicator hs) (by fun_prop)]
      simp [lintegral_indicator hs]
    simp_rw [he]
    apply Measurable.lintegral_prod_right
    exact (measurable_const.indicator hs).comp (measurable_coordinateMap m)

instance projectionKernel_finite (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ) :
    IsFiniteKernel (projectionKernel ν m) := by
  refine ⟨ν Set.univ, measure_lt_top _ _, ?_⟩
  intro A
  change (ν.map (coordinateMap A)) Set.univ ≤ _
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ]

lemma projectionKernel_compProd (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ) :
    (Measure.pi (fun _ : Fin m => stdGaussian E)) ⊗ₘ projectionKernel ν m =
      NoiselessRegression.projectionLaw ν m := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_compProd hf, NoiselessRegression.projectionLaw,
    lintegral_map hf (by fun_prop), lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro A
  change (∫⁻ y, f (A,y) ∂ν.map (coordinateMap A)) = _
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  apply congrArg f
  exact Prod.ext (by rfl) (funext fun i => coordinateMap_apply A x i)

lemma ae_projection_ac (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (h : NoiselessRegression.projectionLaw ν m ≪ NoiselessRegression.matrixLabelReference (E := E) m) :
    ∀ᵐ A : Fin m → E ∂Measure.pi (fun _ => stdGaussian E),
      ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ)) := by
  let γ : Measure (Fin m → E) := Measure.pi (fun _ => stdGaussian E)
  let η : Measure (Fin m → ℝ) := volume.toFinite
  have hh : γ ⊗ₘ projectionKernel ν m ≪ γ ⊗ₘ Kernel.const (Fin m → E) η := by
    rw [projectionKernel_compProd, Measure.compProd_const]
    exact h.trans (Measure.AbsolutelyContinuous.refl γ |>.prod (absolutelyContinuous_toFinite volume))
  filter_upwards [hh.kernel_of_compProd] with A hA
  exact hA.trans (toFinite_absolutelyContinuous volume)

lemma sphere_ae_projection_ac [Nontrivial E] {m : ℕ} (hm : m+2 ≤ Module.finrank ℝ E) :
    ∀ᵐ A : Fin m → E ∂Measure.pi (fun _ => stdGaussian E),
      NoiselessRegression.ambientSphereLaw.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ)) := by
  apply ae_projection_ac
  apply NoiselessRegression.projectionLaw_absolutelyContinuous (a := m+1) (n := 1)
    (C := ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E))
  · intro z r hr
    exact NoiselessRegression.ambientSphereLaw_closedBall z hr (m+1) (by omega)
  · positivity
  · exact ENNReal.ofReal_ne_top
  · exact NoiselessRegression.ambientSphereLaw_support.trans Metric.sphere_subset_closedBall
  · omega
  · omega

lemma linearEquiv_preserves_ac {m : ℕ} (T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ))
    {μ : Measure (Fin m → ℝ)} (hμ : μ ≪ volume) : μ.map T ≪ volume := by
  exact (T.toHomeomorph.toMeasurableEquiv.measurableEmbedding.absolutelyContinuous_map hμ).trans
    (Measure.LinearMap.quasiMeasurePreserving volume T.toLinearEquiv.toLinearMap
      (LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero).absolutelyContinuous

lemma sphere_projection_rotation [Nontrivial E] {m : ℕ} (O : Rotation E) (A : Fin m → E) :
    NoiselessRegression.ambientSphereLaw.map (coordinateMap (rotateRows O A)) =
      NoiselessRegression.ambientSphereLaw.map (coordinateMap A) := by
  have hfun : (coordinateMap (rotateRows O A) : E → (Fin m → ℝ)) =
      coordinateMap A ∘ (Unitary.linearIsometryEquiv O).symm :=
    funext (coordinateMap_rotateRows O A)
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
    (NoiselessRegression.ambientSphereLaw_isometry (Unitary.linearIsometryEquiv O).symm).map_eq]

theorem sphere_frame_ac [Nontrivial E] {m : ℕ} (hm : m+2 ≤ Module.finrank ℝ E)
    {u : Fin m → E} (hu : Orthonormal ℝ u) :
    NoiselessRegression.ambientSphereLaw.map (coordinateMap u) ≪ (volume : Measure (Fin m → ℝ)) := by
  obtain ⟨B,hB,hac⟩ := ((gaussian_rows_ae_linearIndependent m (by omega)).and
    (sphere_ae_projection_ac hm)).exists
  obtain ⟨v,hv,T,hT,hvol⟩ := rows_factor B hB
  have he : (NoiselessRegression.ambientSphereLaw.map (coordinateMap B)).map T.symm =
      NoiselessRegression.ambientSphereLaw.map (coordinateMap v) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    simp only [Function.comp_apply, hT, T.symm_apply_apply]
  have hvac := linearEquiv_preserves_ac T.symm hac
  rw [he] at hvac
  obtain ⟨O,hO⟩ := rotation_transitive hv hu
  have heu : rotateRows O v = u := funext hO
  rw [← heu, sphere_projection_rotation]
  exact hvac

theorem sphere_fullRank_ac [Nontrivial E] {m : ℕ} (hm : m+2 ≤ Module.finrank ℝ E)
    {A : Fin m → E} (hA : LinearIndependent ℝ A) :
    NoiselessRegression.ambientSphereLaw.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ)) := by
  obtain ⟨u,hu,T,hT,hvol⟩ := rows_factor A hA
  have he : NoiselessRegression.ambientSphereLaw.map (coordinateMap A) =
      (NoiselessRegression.ambientSphereLaw.map (coordinateMap u)).map T := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    exact funext hT
  rw [he]
  exact linearEquiv_preserves_ac T (sphere_frame_ac hm hu)

end ProjectionMoments
end

end

end OAI
