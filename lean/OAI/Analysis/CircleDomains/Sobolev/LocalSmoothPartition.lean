import OAI.Analysis.CircleDomains.Topology.EuclideanPlaneCoordinates
import Mathlib.Geometry.Manifold.PartitionOfUnity

namespace OAI

/-! Compact smooth partition functions on an open planar domain. The
family is locally finite in the domain, allowing accumulation at its boundary. -/

open Set Function Filter TopologicalSpace
open scoped Topology Manifold

noncomputable section

namespace CircleDomainRigidity

structure OpenPlanePartition (Ω : Opens EuclideanPlane) (ι : Type*) where
  weight : ι → EuclideanPlane → ℝ
  smooth : ∀i, ContDiff ℝ (⊤ : ℕ∞) (weight i)
  compact : ∀i, HasCompactSupport (weight i)
  inside : ∀i, tsupport (weight i) ⊆ Ω
  locallyFinite : LocallyFinite (fun i => Subtype.val ⁻¹' Function.support (weight i) :
    ι → Set Ω)
  nonneg : ∀i x, 0 ≤ weight i x
  sum_one : ∀x : Ω, ∑ᶠ i, weight i x = 1

theorem exists_openPlanePartition
    (Ω : Opens EuclideanPlane) (U : Ω → Set Ω) (hU : ∀x, U x ∈ 𝓝 x) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : OpenPlanePartition Ω ι) (c : ι → Ω),
      ∀i, tsupport (ρ.weight i) ⊆ Subtype.val '' U (c i) := by
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  obtain ⟨ι, b, hb⟩ := SmoothBumpCovering.exists_isSubordinate
    (𝓘(ℝ, EuclideanPlane)) (M := Ω) isClosed_univ (fun x _ => hU x)
  let : Encodable ι := b.locallyFinite.encodable (fun i => (b i).nonempty_support)
  let ρ := b.toSmoothPartitionOfUnity
  have hc (i : ι) : HasCompactSupport (ρ i) :=
    (b i).hasCompactSupport.of_isClosed_subset isClosed_closure
      (closure_mono (b.support_toSmoothPartitionOfUnity_subset i))
  let ψ : ι → EuclideanPlane → ℝ := fun i => Subtype.val.extend (ρ i) 0
  have hon (i : ι) (x : Ω) : ψ i x = ρ i x :=
    congrFun (Function.extend_comp Subtype.val_injective (ρ i) 0) x
  have hsub (i : ι) : tsupport (ψ i) ⊆ Subtype.val '' U (b.c i) := by
    apply ((hc i).tsupport_extend_zero_subset continuous_subtype_val).trans
    exact image_mono (hb.toSmoothPartitionOfUnity i)
  have hin (i : ι) : tsupport (ψ i) ⊆ Ω :=
    (hsub i).trans (image_subset_iff.mpr (fun x _ => x.property))
  have hsmooth (i : ι) : ContDiff ℝ (⊤ : ℕ∞) (ψ i) := by
    apply contMDiff_iff_contDiff.mp
    exact ContMDiff.extend_zero (hc i) (ρ i).contMDiff
  have hloc : LocallyFinite (fun i => Subtype.val ⁻¹' Function.support (ψ i) :
      ι → Set Ω) := by
    have heq : (fun i => Subtype.val ⁻¹' Function.support (ψ i) : ι → Set Ω) =
        fun i => Function.support (ρ i) := by
      funext i
      ext x
      simp only [mem_preimage, Function.mem_support, hon]
    rw [heq]
    exact ρ.locallyFinite
  have hn (i : ι) (x : EuclideanPlane) : 0 ≤ ψ i x := by
    by_cases hx : x ∈ Ω
    · rw [show x = ((⟨x, hx⟩ : Ω) : EuclideanPlane) from rfl, hon]
      exact ρ.nonneg i _
    · have hz : ψ i x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hin i h))
      rw [hz]
  refine ⟨ι, inferInstance, ⟨ψ, hsmooth,
    fun i => (hc i).extend_zero continuous_subtype_val, hin, hloc, hn, ?_⟩, b.c, hsub⟩
  intro x
  simp only [hon]
  exact ρ.sum_eq_one (mem_univ x)

end CircleDomainRigidity

end

end OAI
