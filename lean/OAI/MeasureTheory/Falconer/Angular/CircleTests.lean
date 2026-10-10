import OAI.MeasureTheory.Falconer.Measures.ExtendedDensityNorm

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

instance unitCircle_compactSpace : CompactSpace UnitCircle := by
  apply isCompact_iff_compactSpace.mp
  have he : (fun z : Plane => ‖z‖ = 1) = (sphere (0 : Plane) 1 : Set Plane) := by
    funext z
    simp [Metric.sphere, dist_zero_right, Set.ofPred]
  rw [he]
  exact isCompact_sphere (0 : Plane) 1

theorem sourceTestNorm_eq_continuous_tests (γ : Measure UnitCircle) (q : ℝ) :
    sourceTestNorm q γ =
      ⨆ (F : C(UnitCircle, ℝ)) (_ : eLpNorm F (ENNReal.ofReal q) sourceArcLength ≤ 1),
        ENNReal.ofReal ‖∫ x, F x ∂γ‖ := by
  apply le_antisymm
  · apply iSup_le; intro F; apply iSup_le; intro hF
    exact le_iSup_of_le F.toContinuousMap (le_iSup_of_le hF le_rfl)
  · apply iSup_le; intro F; apply iSup_le; intro hF
    exact le_iSup_of_le (BoundedContinuousFunction.mkOfCompact F) (le_iSup_of_le hF le_rfl)

theorem sourceTestNorm_mono (γ δ : Measure UnitCircle) [IsFiniteMeasure δ]
    (hγδ : γ ≤ δ) (q : ℝ) : sourceTestNorm q γ ≤ sourceTestNorm q δ := by
  apply iSup_le; intro F; apply iSup_le; intro hF
  let G : BoundedContinuousFunction UnitCircle ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun x => |F x|, F.continuous.abs⟩
  have hG : eLpNorm G (ENNReal.ofReal q) sourceArcLength ≤ 1 := by
    have he : eLpNorm G (ENNReal.ofReal q) sourceArcLength = eLpNorm F (ENNReal.ofReal q) sourceArcLength :=
      eLpNorm_congr_norm_ae G.continuous.aestronglyMeasurable
        F.continuous.aestronglyMeasurable
        (Eventually.of_forall (fun x => by simp [G, Real.norm_eq_abs]))
    rwa [he]
  have hi : Integrable G δ := (G.memLp_top (μ := δ)).integrable le_top
  have he : ENNReal.ofReal ‖∫ x, G x ∂δ‖ = ∫⁻ x, ‖F x‖ₑ ∂δ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun x => abs_nonneg (F x))),
      ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x => abs_nonneg (F x)))]
    apply lintegral_congr
    intro x
    exact ofReal_norm (F x)
  calc
    ENNReal.ofReal ‖∫ x, F x ∂γ‖ ≤ ∫⁻ x, ‖F x‖ₑ ∂γ := by
      simpa only [ofReal_norm] using enorm_integral_le_lintegral_enorm (μ := γ) (fun x => F x)
    _ ≤ ∫⁻ x, ‖F x‖ₑ ∂δ := lintegral_mono' hγδ le_rfl
    _ = ENNReal.ofReal ‖∫ x, G x ∂δ‖ := he.symm
    _ ≤ sourceTestNorm q δ := le_iSup_of_le G (le_iSup_of_le hG le_rfl)

theorem sourceTestNorm_smul_le (γ : Measure UnitCircle) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (q : ℝ) : sourceTestNorm q (c • γ) ≤ c * sourceTestNorm q γ := by
  apply iSup_le; intro F; apply iSup_le; intro hF
  rw [integral_smul_measure, norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hc]
  have hb : ENNReal.ofReal ‖∫ x, F x ∂γ‖ ≤ sourceTestNorm q γ :=
    le_iSup_of_le F (le_iSup_of_le hF le_rfl)
  exact mul_le_mul_right hb c

end PlanarFalconer

end OAI
