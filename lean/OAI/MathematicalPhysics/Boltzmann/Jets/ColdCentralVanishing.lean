import OAI.MathematicalPhysics.Boltzmann.Approximation.CapColdAverages
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapDilationCompactness
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotUndamped
import OAI.MathematicalPhysics.Boltzmann.Approximation.SubcapColdControl
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdGaussianFamily
import OAI.MathematicalPhysics.Boltzmann.Jets.PeriodicJetFamilies

namespace OAI

section

/-! # Compact cold cylinders and their exhaustion away from the axis -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

def coldCylinderVolume (a A R : ℝ) : Measure (ℝ × JetPrototype.Space) :=
  (volume.restrict (Icc a A)).prod (JetPrototype.spaceVolume.restrict
    (Metric.closedBall (0 : VelocityWeight.Transverse) R ×ˢ Icc (-R) R))

instance coldCylinderVolume_finite (a A R : ℝ) : IsFiniteMeasure (coldCylinderVolume a A R) := by
  let _ : IsFiniteMeasure (JetPrototype.spaceVolume.restrict
      (Metric.closedBall (0 : VelocityWeight.Transverse) R ×ˢ Icc (-R) R)) :=
    isFiniteMeasure_restrict.mpr ((isCompact_closedBall (0 : VelocityWeight.Transverse) R).prod
      isCompact_Icc).measure_lt_top.ne
  exact inferInstanceAs (IsFiniteMeasure ((volume.restrict (Icc a A)).prod _))

def coldAxisCutoff (m : ℕ) : Set (ℝ × JetPrototype.Space) :=
  {z | 1/((m:ℝ)+1) ≤ ‖z.2.1‖}

def coldTransverseAnnulus (R : ℝ) (m : ℕ) : Set VelocityWeight.Transverse :=
  Metric.closedBall 0 R ∩ {y | 1/((m:ℝ)+1) ≤ ‖y‖}

theorem coldTransverseAnnulus_compact (R : ℝ) (m : ℕ) :
    IsCompact (coldTransverseAnnulus R m) :=
  (isCompact_closedBall (0 : VelocityWeight.Transverse) R).inter_right
    (isClosed_le continuous_const continuous_norm)

theorem coldAxisCutoff_measurable (m : ℕ) : MeasurableSet (coldAxisCutoff m) :=
  measurableSet_le measurable_const (measurable_snd.fst.norm)

theorem coldCylinderVolume_restrict_axis (a A R : ℝ) (m : ℕ) :
    (coldCylinderVolume a A R).restrict (coldAxisCutoff m) =
      (volume.restrict (Icc a A)).prod (JetPrototype.spaceVolume.restrict
        (coldTransverseAnnulus R m ×ˢ Icc (-R) R)) := by
  have hs : MeasurableSet {x : JetPrototype.Space | 1/((m:ℝ)+1) ≤ ‖x.1‖} :=
    measurableSet_le measurable_const measurable_fst.norm
  have he : coldAxisCutoff m = (univ : Set ℝ) ×ˢ {x : JetPrototype.Space | 1/((m:ℝ)+1) ≤ ‖x.1‖} := by
    ext z
    simp [coldAxisCutoff]
  rw [coldCylinderVolume,he,← Measure.prod_restrict,Measure.restrict_univ,Measure.restrict_restrict hs]
  congr 2
  ext x
  simp only [coldTransverseAnnulus,mem_inter_iff,mem_ofPred_eq,mem_prod]
  tauto

theorem coldAxisCutoff_exhausts (a A R : ℝ) :
    ∀ᵐ z ∂coldCylinderVolume a A R, ∀ᶠ m in atTop, z ∈ coldAxisCutoff m := by
  have hx : ∀ᵐ x ∂JetPrototype.spaceVolume, x.1 ≠ 0 :=
    Measure.quasiMeasurePreserving_fst.ae (volume.ae_ne (0 : VelocityWeight.Transverse))
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_of_ae hx)] with z hz
  have hp : 0 < ‖z.2.1‖ := norm_pos_iff.mpr hz
  exact (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hp)).mono
    (fun _ hm => hm.le)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Restriction from the hot windows to the compact cold cylinders -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

theorem coldCylinderVolume_le_hotBaseWindowVolume {a A R : ℝ} (ha : 0 ≤ a) :
    coldCylinderVolume a A R ≤ hotBaseWindowVolume A R := by
  apply Measure.prod_mono
  · exact Measure.restrict_mono (Icc_subset_Icc ha le_rfl) le_rfl
  · apply Measure.restrict_mono _ le_rfl
    intro x hx
    have hy : ‖x.1‖ ≤ R := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hx.1
    have hz : |x.2| ≤ R := abs_le.mpr hx.2
    change dist x 0 ≤ R
    rw [dist_zero_right]
    change max ‖x.1‖ ‖x.2‖ ≤ R
    exact max_le hy (by simpa only [Real.norm_eq_abs] using hz)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The cold cylinders are measurable restrictions of the hot windows -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

theorem cold_spatial_box_eq_ball (R : ℝ) :
    (Metric.closedBall (0 : VelocityWeight.Transverse) R ×ˢ Icc (-R) R) =
      Metric.closedBall (0 : JetPrototype.Space) R := by
  ext x
  simp only [mem_prod,Metric.mem_closedBall,dist_zero_right,mem_Icc]
  change (‖x.1‖ ≤ R ∧ -R ≤ x.2 ∧ x.2 ≤ R) ↔ max ‖x.1‖ ‖x.2‖ ≤ R
  rw [max_le_iff,Real.norm_eq_abs,abs_le]

def coldCylinderSet (a A R : ℝ) : Set HotKineticPhase :=
  (Icc a A ×ˢ Metric.closedBall (0 : JetPrototype.Space) R) ×ˢ univ

theorem coldCylinderSet_measurable (a A R : ℝ) : MeasurableSet (coldCylinderSet a A R) :=
  (measurableSet_Icc.prod measurableSet_closedBall).prod MeasurableSet.univ

theorem coldCylinderVolume_eq (a A R : ℝ) :
    (coldCylinderVolume a A R).prod (volume : Measure Velocity) =
      (volume : Measure HotKineticPhase).restrict (coldCylinderSet a A R) := by
  rw [coldCylinderVolume,cold_spatial_box_eq_ball,
    show JetPrototype.spaceVolume = (volume : Measure JetPrototype.Space) from
      (Measure.volume_eq_prod VelocityWeight.Transverse ℝ).symm,
    Measure.prod_restrict,← Measure.volume_eq_prod,
    Measure.restrict_prod_eq_prod_univ,← Measure.volume_eq_prod]
  rfl

theorem coldCylinderVolume_eq_hot_restrict {a A R : ℝ} (ha : 0 ≤ a) :
    (coldCylinderVolume a A R).prod (volume : Measure Velocity) =
      (hotWindowVolume A R).restrict {z | a ≤ z.1.1} := by
  rw [coldCylinderVolume_eq,hotWindowVolume_eq,
    Measure.restrict_restrict (measurableSet_le measurable_const measurable_fst.fst)]
  congr 1
  ext z
  simp only [coldCylinderSet,hotWindowSet,mem_prod,mem_Icc,mem_univ,and_true,
    mem_inter_iff,mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hat,htA⟩,hx⟩
    exact ⟨hat,⟨⟨ha.trans hat,htA⟩,hx⟩⟩
  · rintro ⟨hat,⟨⟨_,htA⟩,hx⟩⟩
    exact ⟨⟨hat,htA⟩,hx⟩

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem HotLimitExtraction.physical_weak_cylinder (S : AttainedCapSequence F)
    (E : HotLimitExtraction S) (hs₀ : 0 < s₀) {a A : ℝ} (ha : 0 ≤ a)
    (hA : ENNReal.ofReal A < E.horizon) (R : ℝ) :
    Published.WeakL1Converges ((coldCylinderVolume a A R).prod volume)
      (fun n => S.physicalHotDensity (E.indices n)) E.hotLimit := by
  rw [coldCylinderVolume_eq_hot_restrict ha]
  exact (E.physical_weak S hs₀ hA R).restrict
    (measurableSet_le measurable_const measurable_fst.fst)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A uniform central-cube bound for the actual cold components -/
noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetLattice
namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem Approximation.cold_central_bound {s₀ η K α γ d₀ q T ε : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32) (hε : 0 < ε)
    {t : ℝ} (ht : t ∈ Ioc 0 T) {x v : Velocity}
    (hx : x ∈ TorusChart.cube) (hv : ε ≤ ‖transverse v‖) :
    H q v*F.coldTotal (t,(JetPeriodicDatum.spatialMap x,v)) ≤
      JetSupersolution.transverseDecayConstant K d₀ ε*‖transverse x‖^9+
      H q v*(JetEscapedEnvelope.constant s₀ η α K d₀
        (JetEscapedEnvelope.exponent 2)*t^(2:ℝ)) := by
  have hc := JetSupersolution.transverseDecayConstant_nonneg (ε := ε) hK hd₀.le
  have hesc := F.escapedTotal_bound_global hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq hT hTmax 2 (z := ((t,x),v)) ht
  have hesc' := mul_le_mul_of_nonneg_left hesc (H_nonneg q v)
  by_cases hm : ∃ i : Label, i.annulus < N ∧ x ∈ spatialEnlargement s₀ η t i
  · obtain ⟨i,hi,hxi⟩ := hm
    have hs : 0 < JetGeometry.jetScale s₀ η i.annulus := DatumBounds.scale_pos hs₀ _
    have hsx := enlargement_central_shell hs₀ hsmax hη (ht.2.trans hTmax) hx hxi
    have hscale : JetGeometry.jetScale s₀ η i.annulus ≤ ‖transverse x‖ := hsx.1.le
    have heps := JetEscapedEnvelope.epsilon_small hK hd₀.le hs
      (JetEscapedTotal.scale_bound hs₀ hη _) hsmall
    have hb := F.cold_free_majorant_at_main hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall
      hq hT hTmax ((t,x),v) ht i hi hxi
    have hu := JetSupersolution.off_axis_small_scale hK hs hd₀ ht.1
      ((ht.2.trans hTmax).trans (by norm_num)) hε hα hγ heps η i.positive
      (WeightedTranslation.shift (displacement i.lattice) (JetPeriodicDatum.spatialMap x,v)).1 v hv
    change _ ≤ JetSupersolution.U η K α γ _ _ t i.positive _+
      H q v*F.escapedTotal ((t,x),v) at hb
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le hscale 9) hc
    exact hb.trans (add_le_add (hu.trans hp) hesc')
  · have hn : ∀ i : Label, i.annulus < N → x ∉ spatialEnlargement s₀ η t i :=
      fun i hi hxi => hm ⟨i,hi,hxi⟩
    rw [F.coldTotal_eq_escaped_of_no_main hs₀ hsmax hη hηmax hK hd₀.le hq hT ((t,x),v) hn]
    exact hesc'.trans (le_add_of_nonneg_left (mul_nonneg hc (pow_nonneg (norm_nonneg _) _)))

end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

end OAI
