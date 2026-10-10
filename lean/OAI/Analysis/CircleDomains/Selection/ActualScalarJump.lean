import OAI.Analysis.CircleDomains.Topology.PlanarFilledJump
import OAI.Analysis.CircleDomains.Sobolev.LocalGradientMajorant
import OAI.Analysis.CircleDomains.Transfer.FilledScalarLineData
import OAI.Analysis.CircleDomains.Sobolev.FilledScalarTestIntegrals

namespace OAI

/-! The horizontal distributional jump bound for the actual retained scalar
models. All geometric, integrability and cluster hypotheses are constructed. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 theorem eventually_filled_horizontal_jump (i : Fin m) :
    ∀ᶠ n in atTop, ∀ F : R.HoleFilling i n, ∀ φ : ℂ → ℝ,
      ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ C : ℝ, 0 ≤ C → (∀ z, |φ z| ≤ C) →
      |(∫ z, F.filled z * fderiv ℝ φ z 1) + (∫ z, fderiv ℝ F.filled z 1 * φ z)| ≤
      4 * C * ∑' s, F.radius s * terminalOscillation ((R.model.stages n).terminals.H s)
        ((R.model.stages n).functions (prefixIndex (R.index i) n)) := by
  filter_upwards [R.eventually_energy i, R.eventually_filled_test_integrals i] with n hn htest
  intro F φ hφ hs C hC hbound
  let : Fintype (R.model.stages n).indices := (R.model.stages n).finite_indices.fintype
  let U := (⋃ s, closedBall (F.center s) (F.radius s))ᶜ
  have hU : IsOpen U := (isClosed_iUnion_of_finite (fun _ => isClosed_closedBall)).isOpen_compl
  have he : IntegrableOn (euclideanGradientEnergy (R.transferred i n)) U := by
    simpa only [F.complement] using hn.1
  have hv : ContDiffOn ℝ 1 (R.transferred i n) U := by
    simpa only [F.complement] using (R.transferred_contDiffOn i n).of_le (by simp)
  have hc : IsCompact (tsupport φ ∪ ⋃ s, closedBall (F.center s) (F.radius s)) :=
    hs.union (isCompact_iUnion (fun _ => isCompact_closedBall _ _))
  obtain ⟨L, hL, hBL⟩ := hc.isBounded.exists_pos_norm_lt
  have hsub (s : (R.model.stages n).indices) : closedBall (F.center s) (F.radius s) ⊆ ball 0 L := by
    intro z hz
    exact mem_ball_zero_iff.mpr (hBL z (Or.inr (mem_iUnion.mpr ⟨s, hz⟩)))
  have hsL : tsupport φ ⊆ ball 0 L := fun z hz =>
    mem_ball_zero_iff.mpr (hBL z (Or.inl hz))
  obtain ⟨ρ, hρ, hmajor⟩ := exists_integrable_gradient_majorant_on_square hU he hL.le
  rw [tsum_fintype]
  apply planar_filled_horizontal_jump_of_density F.center F.radius F.value
    (fun s => terminalOscillation ((R.model.stages n).terminals.H s)
      ((R.model.stages n).functions (prefixIndex (R.index i) n)))
    F.radius_nonneg (fun _ => Metric.diam_nonneg) F.disjoint hL hsub hv hρ hmajor
  · intro z hz
    apply F.filled_on_domain
    change z ∈ ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain
    rw [F.complement]
    exact hz
  · exact fun s z hz => F.filled_on_hole s hz
  · intro s z t hz ht
    apply F.cluster_error s t
    apply planar_mapClusterPt_mem_componentClusterValues
    · rw [F.component]
      exact mem_image_of_mem _ hz
    · simpa only [F.complement, RetainedRealCircleModel.transferred] using ht
  · exact F.horizontal_derivative_ae
  · exact hφ
  · exact hsL
  · exact (htest F φ hφ hs).1
  · exact (htest F φ hφ hs).2.1
  · exact hC
  · exact hbound

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
