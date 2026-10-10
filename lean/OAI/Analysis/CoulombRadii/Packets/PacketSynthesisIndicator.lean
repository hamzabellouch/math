import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.PacketFrame
import OAI.Analysis.CoulombRadii.Packets.PacketStateJointSquareIntegrable
import OAI.Analysis.CoulombRadii.Packets.PacketSynthesis
import OAI.Analysis.CoulombRadii.FormDomain.L2KernelIntegral

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
namespace Coulomb
lemma packetSynthesis_indicator_eq (g : 𝓢(Space,ℂ)) (A : Set (Space × Space))
    (hA : MeasurableSet A) (c : Space × Space → ℂ) (x : Space) :
    packetSynthesis g (A.indicator c) x =
      ∫ yp : Space × Space, c yp * packetState g yp.1 yp.2 x ∂(volume.restrict A) := by
  rw [← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards [] with yp
  by_cases hy : yp ∈ A <;> simp [packetState_apply, hy]

lemma packetState_joint_continuous (g : 𝓢(Space,ℂ)) :
    Continuous (fun z : (Space × Space) × Space => packetState g z.1.1 z.1.2 z.2) := by
  simp only [packetState_apply]
  fun_prop

lemma compactPhase_finite (A : Set (Space × Space)) (K : Set Space) (hK : IsCompact K)
    (P : ℝ) (hAK : ∀ yp ∈ A, yp.1 ∈ K) (hAP : ∀ yp ∈ A, ‖yp.2‖ ≤ P) :
    IsFiniteMeasure ((volume : Measure (Space × Space)).restrict A) := by
  constructor
  rw [Measure.restrict_apply_univ]
  have hs : A ⊆ K ×ˢ closedBall 0 P := by
    intro yp hy
    exact ⟨hAK yp hy, by simpa only [mem_closedBall, dist_zero_right] using hAP yp hy⟩
  exact (measure_mono hs).trans_lt ((hK.prod (isCompact_closedBall (0 : Space) P)).measure_lt_top)

lemma packetFrame_smooth_range (g : 𝓢(Space,ℂ)) (hgc : HasCompactSupport (g : Space → ℂ))
    (A : Set (Space × Space)) (hA : MeasurableSet A)
    (K : Set Space) (hK : IsCompact K) (P : ℝ)
    (hAK : ∀ yp ∈ A, yp.1 ∈ K) (hAP : ∀ yp ∈ A, ‖yp.2‖ ≤ P)
    (u : Lp ℂ 2 (volume : Measure Space)) :
    ∃ F : Space → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
      (packetFrame g (volume.restrict A) u : Space → ℂ) =ᵐ[volume] F := by
  let μ : Measure (Space × Space) := volume.restrict A
  let := compactPhase_finite A K hK P hAK hAP
  let c : Space × Space → ℂ := fun yp => inner ℂ ((packetState g yp.1 yp.2).toLp 2 volume) u
  have hc : Continuous c := (packetState_toL2_continuous g).inner continuous_const
  let C : ℝ := ‖g.toLp 2 volume‖ * ‖u‖
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hcb (yp : Space × Space) : ‖c yp‖ ≤ C := by
    calc
      _ ≤ ‖(packetState g yp.1 yp.2).toLp 2 volume‖ * ‖u‖ := norm_inner_le_norm _ _
      _ = C := by rw [packetState_toL2_norm]
  let f := A.indicator c
  have hf : LocallyIntegrable f volume := by
    apply (locallyIntegrable_const C).mono (hc.aestronglyMeasurable.indicator hA)
    filter_upwards [] with yp
    rw [Real.norm_of_nonneg hC]
    by_cases hy : yp ∈ A
    · simpa [f, hy] using hcb yp
    · simp [hy, hC]
  have hpf (yp : Space × Space) (hy : f yp ≠ 0) : ‖yp.2‖ ≤ P := by
    apply hAP yp
    by_contra hn
    exact hy (by simp [f, hn])
  have hfk (yp : Space × Space) (hy : yp.1 ∉ K) : f yp = 0 := by
    have hn : yp ∉ A := by intro h; exact hy (hAK yp h)
    simp [f, hn]
  let F := packetSynthesis g f
  have hFs : ContDiff ℝ (⊤ : ℕ∞) F := packetSynthesis_contDiff g (g.smooth ⊤) hgc f hf P hpf
  have hFc : HasCompactSupport F := packetSynthesis_compactSupport g hgc f K hK hfk
  have he (x : Space) : F x = ∫ yp, c yp * packetState g yp.1 yp.2 x ∂μ :=
    packetSynthesis_indicator_eq g A hA c x
  have hFm : MemLp (fun x => ∫ yp, c yp * packetState g yp.1 yp.2 x ∂μ) 2 volume := by
    simpa only [← he] using hFs.continuous.memLp_of_hasCompactSupport hFc (p := (2:ℝ≥0∞))
  have hK2 : MemLp (fun z : (Space × Space) × Space => packetState g z.1.1 z.1.2 z.2) 2 (μ.prod volume) :=
    (memLp_two_iff_integrable_sq_norm (packetState_joint_continuous g).aestronglyMeasurable).mpr
      (packetState_joint_square_integrable g μ)
  have hEq := l2_kernel_integral (fun yp : Space × Space => (packetState g yp.1 yp.2).toLp 2 volume)
    (packetState_toL2_memLp g μ) (fun yp x => packetState g yp.1 yp.2 x)
    (fun yp => (packetState g yp.1 yp.2).coeFn_toLp 2 volume) hK2 c hc.aestronglyMeasurable C hcb hFm
  refine ⟨F, hFs, hFc, ?_⟩
  change (frameOperator μ (fun yp : Space × Space => (packetState g yp.1 yp.2).toLp 2 volume) u : Space → ℂ) =ᵐ[volume] F
  have hOp := (frameOperator_apply (packetState_toL2_memLp g μ) u).trans hEq
  rw [hOp]
  filter_upwards [hFm.coeFn_toLp] with x hx
  exact hx.trans (he x).symm

lemma packetFrame_eigen_smooth (g : 𝓢(Space,ℂ)) (hgc : HasCompactSupport (g : Space → ℂ))
    (A : Set (Space × Space)) (hA : MeasurableSet A)
    (K : Set Space) (hK : IsCompact K) (P : ℝ)
    (hAK : ∀ yp ∈ A, yp.1 ∈ K) (hAP : ∀ yp ∈ A, ‖yp.2‖ ≤ P)
    (u : Lp ℂ 2 (volume : Measure Space)) (lam : ℂ) (hlam : lam ≠ 0)
    (hu : packetFrame g (volume.restrict A) u = lam • u) :
    ∃ F : Space → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
      (u : Space → ℂ) =ᵐ[volume] F := by
  obtain ⟨F,hFs,hFc,hF⟩ := packetFrame_smooth_range g hgc A hA K hK P hAK hAP u
  refine ⟨fun x => lam⁻¹*F x, contDiff_const.mul hFs, hFc.mul_left, ?_⟩
  rw [hu] at hF
  filter_upwards [hF, Lp.coeFn_smul lam u] with x hx hy
  rw [hy] at hx
  change lam * u x = F x at hx
  rw [← hx, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]

open scoped Pointwise
lemma packetSynthesis_zero_of_notMem_region (g : Space → ℂ)
    (f : Space × Space → ℂ) (K : Set Space)
    (hfK : ∀ yp, yp.1 ∉ K → f yp = 0) (x : Space)
    (hx : x ∉ K + tsupport g) : packetSynthesis g f x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with yp
  by_cases hy : yp.1 ∈ K
  · have hz : x-yp.1 ∉ tsupport g := by
      intro hz
      exact hx ⟨yp.1, hy, x-yp.1, hz, by abel_nf⟩
    simp [image_eq_zero_of_notMem_tsupport hz]
  · simp [hfK yp hy]
lemma packetFrame_smooth_range_supported (g : 𝓢(Space,ℂ)) (hgc : HasCompactSupport (g : Space → ℂ))
    (A : Set (Space × Space)) (hA : MeasurableSet A)
    (K : Set Space) (hK : IsCompact K) (P : ℝ)
    (hAK : ∀ yp ∈ A, yp.1 ∈ K) (hAP : ∀ yp ∈ A, ‖yp.2‖ ≤ P)
    (u : Lp ℂ 2 (volume : Measure Space)) :
    ∃ F : Space → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
      (packetFrame g (volume.restrict A) u : Space → ℂ) =ᵐ[volume] F ∧
      (∀ x, x ∉ K + tsupport (g : Space → ℂ) → F x = 0) := by
  let μ : Measure (Space × Space) := volume.restrict A
  let := compactPhase_finite A K hK P hAK hAP
  let c : Space × Space → ℂ := fun yp => inner ℂ ((packetState g yp.1 yp.2).toLp 2 volume) u
  have hc : Continuous c := (packetState_toL2_continuous g).inner continuous_const
  let C : ℝ := ‖g.toLp 2 volume‖ * ‖u‖
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hcb (yp : Space × Space) : ‖c yp‖ ≤ C := by
    calc
      _ ≤ ‖(packetState g yp.1 yp.2).toLp 2 volume‖ * ‖u‖ := norm_inner_le_norm _ _
      _ = C := by rw [packetState_toL2_norm]
  let f := A.indicator c
  have hf : LocallyIntegrable f volume := by
    apply (locallyIntegrable_const C).mono (hc.aestronglyMeasurable.indicator hA)
    filter_upwards [] with yp
    rw [Real.norm_of_nonneg hC]
    by_cases hy : yp ∈ A
    · simpa [f, hy] using hcb yp
    · simp [hy, hC]
  have hpf (yp : Space × Space) (hy : f yp ≠ 0) : ‖yp.2‖ ≤ P := by
    apply hAP yp
    by_contra hn
    exact hy (by simp [f, hn])
  have hfk (yp : Space × Space) (hy : yp.1 ∉ K) : f yp = 0 := by
    have hn : yp ∉ A := by intro h; exact hy (hAK yp h)
    simp [f, hn]
  let F := packetSynthesis g f
  have hFs : ContDiff ℝ (⊤ : ℕ∞) F := packetSynthesis_contDiff g (g.smooth ⊤) hgc f hf P hpf
  have hFc : HasCompactSupport F := packetSynthesis_compactSupport g hgc f K hK hfk
  have he (x : Space) : F x = ∫ yp, c yp * packetState g yp.1 yp.2 x ∂μ :=
    packetSynthesis_indicator_eq g A hA c x
  have hFm : MemLp (fun x => ∫ yp, c yp * packetState g yp.1 yp.2 x ∂μ) 2 volume := by
    simpa only [← he] using hFs.continuous.memLp_of_hasCompactSupport hFc (p := (2:ℝ≥0∞))
  have hK2 : MemLp (fun z : (Space × Space) × Space => packetState g z.1.1 z.1.2 z.2) 2 (μ.prod volume) :=
    (memLp_two_iff_integrable_sq_norm (packetState_joint_continuous g).aestronglyMeasurable).mpr
      (packetState_joint_square_integrable g μ)
  have hEq := l2_kernel_integral (fun yp : Space × Space => (packetState g yp.1 yp.2).toLp 2 volume)
    (packetState_toL2_memLp g μ) (fun yp x => packetState g yp.1 yp.2 x)
    (fun yp => (packetState g yp.1 yp.2).coeFn_toLp 2 volume) hK2 c hc.aestronglyMeasurable C hcb hFm
  refine ⟨F, hFs, hFc, ?_, packetSynthesis_zero_of_notMem_region g f K hfk⟩
  change (frameOperator μ (fun yp : Space × Space => (packetState g yp.1 yp.2).toLp 2 volume) u : Space → ℂ) =ᵐ[volume] F
  have hOp := (frameOperator_apply (packetState_toL2_memLp g μ) u).trans hEq
  rw [hOp]
  filter_upwards [hFm.coeFn_toLp] with x hx
  exact hx.trans (he x).symm

lemma packetFrame_eigen_smooth_supported (g : 𝓢(Space,ℂ)) (hgc : HasCompactSupport (g : Space → ℂ))
    (A : Set (Space × Space)) (hA : MeasurableSet A)
    (K : Set Space) (hK : IsCompact K) (P : ℝ)
    (hAK : ∀ yp ∈ A, yp.1 ∈ K) (hAP : ∀ yp ∈ A, ‖yp.2‖ ≤ P)
    (u : Lp ℂ 2 (volume : Measure Space)) (lam : ℂ) (hlam : lam ≠ 0)
    (hu : packetFrame g (volume.restrict A) u = lam • u) :
    ∃ F : Space → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
      (u : Space → ℂ) =ᵐ[volume] F ∧
      (∀ x, x ∉ K + tsupport (g : Space → ℂ) → F x = 0) := by
  obtain ⟨F,hFs,hFc,hF,hFS⟩ := packetFrame_smooth_range_supported g hgc A hA K hK P hAK hAP u
  refine ⟨fun x => lam⁻¹*F x, contDiff_const.mul hFs, hFc.mul_left, ?_, fun x hx => by change lam⁻¹*F x = 0; rw [hFS x hx,mul_zero]⟩
  rw [hu] at hF
  filter_upwards [hF, Lp.coeFn_smul lam u] with x hx hy
  rw [hy] at hx
  change lam * u x = F x at hx
  rw [← hx, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff

end

end OAI
