import OAI.Probability.SLE.Angle.TargetDiskPotential
import OAI.Probability.SLE.Geometry.WeightedCompactTerminal
import OAI.Probability.SLE.Geometry.RestartHalfPlaneGreen

namespace OAI

/-! The exact compact and continuous conformal weight whose canonical
mass has the source-prescribed disk Green potential. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

def diskSourceHalfPlane (θ : ℝ) : Set upperHalfPlane :=
  Subtype.val ⁻¹' diskSourceCompact θ

lemma diskSourceHalfPlane_compact {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    IsCompact (diskSourceHalfPlane θ) := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have he : Subtype.val '' diskSourceHalfPlane θ=diskSourceCompact θ := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro hz
      exact ⟨⟨z,diskSourceCompact_subset hθ hz⟩,hz,rfl⟩
  rw [he]
  exact diskSourceCompact_compact θ

lemma diskMap_deriv_continuous {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    Continuous (fun z : upperHalfPlane => deriv (diskMap θ) z) := by
  have he : (fun z : upperHalfPlane => deriv (diskMap θ) z)=
      (fun z : upperHalfPlane => (Complex.exp (θ*Complex.I)-Complex.exp (-θ*Complex.I))/
        ((z:ℂ)-Complex.exp (-θ*Complex.I))^2) :=
    funext (fun z => (diskMap_hasDerivAt hθ z.property).deriv)
  rw [he]
  exact continuous_const.div ((continuous_subtype_val.sub continuous_const).pow 2)
    (fun z => pow_ne_zero _ (diskMap_denominator_ne hθ z.property))

def diskMassWeight (κ θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) : C(upperHalfPlane,ℝ≥0) where
  toFun z := (‖deriv (diskMap θ) z‖^dimension κ).toNNReal
  continuous_toFun := continuous_real_toNNReal.comp
    ((diskMap_deriv_continuous hθ).norm.rpow_const
      (fun z => Or.inl (diskMap_deriv_pos hθ z.property).ne'))

@[simp] lemma diskMassWeight_coe (κ θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    (z : upperHalfPlane) :
    (diskMassWeight κ θ hθ z:ℝ)=‖deriv (diskMap θ) z‖^dimension κ := by
  exact Real.coe_toNNReal _ (Real.rpow_nonneg (norm_nonneg _) _)

lemma diskMassWeight_ennreal (κ θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    (z : upperHalfPlane) :
    (diskMassWeight κ θ hθ z:ℝ≥0∞)=ENNReal.ofReal (‖deriv (diskMap θ) z‖^dimension κ) := by
  rw [← ENNReal.ofReal_coe_nnreal,diskMassWeight_coe]

theorem potential_eq_weighted_green
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ) (hUc : Continuous U)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (T : ℝ≥0) :
    potential κ θ b (κ*T)=
      ∫⁻ z in diskSourceHalfPlane θ, (diskMassWeight κ θ hθ z:ℝ≥0∞)
        ∂(volume.withDensity (fun z => ENNReal.ofReal (greenDensity κ U γ G T z))).comap Subtype.val := by
  have hK := diskSourceHalfPlane_compact hθ
  rw [← lintegral_indicator hK.measurableSet,
    Multipoint.halfPlane_realDensity_lintegral _ (Multipoint.currentGreen_measurable hw hUc hκ T)]
  rw [potential_eq_source_green_integral κ hκ b U hUc γ G F hw hU θ hθ T]
  symm
  calc
    _ = ∫⁻ z in upperHalfPlane, (diskSourceCompact θ).indicator
        (fun z => ENNReal.ofReal (‖deriv (diskMap θ) z‖^dimension κ)*
          ENNReal.ofReal (greenDensity κ U γ G T z)) z := by
      apply setLIntegral_congr_fun isOpen_upperHalfPlane.measurableSet
      intro z hz
      simp only [Multipoint.extendHalfPlaneENN,dite_eq_left hz]
      by_cases hzk : z ∈ diskSourceCompact θ
      · rw [Set.indicator_of_mem (show (⟨z,hz⟩:upperHalfPlane) ∈ diskSourceHalfPlane θ from hzk),
          Set.indicator_of_mem hzk,diskMassWeight_ennreal]
      · rw [Set.indicator_of_notMem (show (⟨z,hz⟩:upperHalfPlane) ∉ diskSourceHalfPlane θ from hzk),
          Set.indicator_of_notMem hzk,zero_mul]
    _ = _ := by
      rw [lintegral_indicator (diskSourceCompact_compact θ).measurableSet,
        Measure.restrict_restrict (diskSourceCompact_compact θ).measurableSet,
        inter_eq_left.mpr (diskSourceCompact_subset hθ)]

theorem potential_toReal_eq_compactWeightedMass
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ) (hUc : Continuous U)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (T : ℝ≥0) :
    (potential κ θ b (κ*T)).toReal = Multipoint.compactWeightedMass
      (diskMassWeight κ θ hθ) (diskSourceHalfPlane θ)
      ((volume.withDensity (fun z => ENNReal.ofReal (greenDensity κ U γ G T z))).comap Subtype.val) := by
  rw [potential_eq_weighted_green κ hκ b U hUc γ G F hw hU θ hθ T,
    Multipoint.compactWeightedMass_eq_lintegral]

end SLEExactGauge.Target

end

end OAI
