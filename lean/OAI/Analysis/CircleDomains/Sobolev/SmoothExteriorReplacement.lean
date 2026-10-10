import OAI.Analysis.CircleDomains.Sobolev.LocalComplexWitness
import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevSmoothing

namespace OAI

/-! A local Sobolev scalar smooth off a compact set can be replaced by a
smooth scalar without changing it near an exterior boundary. The removed
part is an actual compactly supported global Sobolev function. -/
open Set Filter Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_smooth_exterior_replacement {K : Set EuclideanPlane} (hK : IsCompact K)
    {R : ℝ} (hKR : K ⊆ Metric.ball 0 R) {u : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u (Metric.ball 0 R))
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ) :
    ∃ (v e : EuclideanPlane → ℝ) (_ : DeGiorgi.MemW1pWitness 2 e univ),
      ContDiff ℝ (⊤ : ℕ∞) v ∧ HasCompactSupport e ∧
      tsupport e ⊆ Metric.ball 0 R ∧ (∀ x, u x = v x + e x) ∧ EqOn v u (Metric.ball 0 R)ᶜ := by
  obtain ⟨η, V, hη, hsη, _hunit, hηsub, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK Metric.isOpen_ball hKR
  let v : EuclideanPlane → ℝ := fun x => (1-η x) * u x
  let e : EuclideanPlane → ℝ := fun x => η x * u x
  obtain ⟨he⟩ := exists_global_compact_cutoff_witness Metric.isOpen_ball hu.memW1p hη hsη hηsub
  refine ⟨v, e, he, ?_, hsη.mul_right, tsupport_mul_subset_left.trans hηsub, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ K
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hV.mem_nhds (hKV hx)] with y hy
      change (1-η y) * u y = 0
      rw [hone y hy, sub_self, zero_mul]
    · exact (contDiffAt_const.sub hη.contDiffAt).mul
        (hsmooth.contDiffAt (hK.isClosed.isOpen_compl.mem_nhds hx))
  · intro x
    dsimp only [v, e]
    ring
  · intro x hx
    have hz : η x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hηsub ht))
    change (1-η x) * u x = u x
    rw [hz, sub_zero, one_mul]

end CircleDomainRigidity

end

end OAI
