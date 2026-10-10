import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompletedIdentity
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedIdentityScalar
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteGroupSyzygyScalar
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SubgroupResolution
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BoundedLocallyFiniteKernel

namespace OAI

/-! # Torsion of the complete identity bounds all finite subgroup orders

The annihilator is kept as an explicit premise. In particular, the theorem
below does not claim that FP-infinity by itself supplies an annihilator.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem normalizedStableScalar_restrict_descend (H : Subgroup G) [Fintype H]
    (n : ℕ) (m : ℤ)
    (h : stableRepresentationClass
      (Rep.res H.subtype ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)))
      (Rep.res H.subtype ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)))
      (m • 𝟙 _) = 0) :
    stableRepresentationClass (trivialIntegral H) (trivialIntegral H)
      (m • 𝟙 _) = 0 := by
  induction n with
  | zero => exact h
  | succ n ih =>
    apply ih
    let F : Rep.{0} ℤ G ⥤ Rep.{0} ℤ H := Rep.resFunctor H.subtype
    let S := normalizedSyzygySequence ((iteratedNormalizedSyzygy n).obj (trivialIntegral G))
    let : Projective ((S.map F).X₂) := by
      change Projective (F.obj (normalizedFreeRepresentation
        ((iteratedNormalizedSyzygy n).obj (trivialIntegral G))))
      exact (Rep.resFunctor (k := ℤ) H.subtype).projective_obj_of_projective inferInstance
    let : Module.Projective ℤ ((S.map F).X₃) := by
      change Module.Projective ℤ ((iteratedNormalizedSyzygy n).obj (trivialIntegral G))
      infer_instance
    exact stableScalar_descend (S.map F)
      ((normalizedSyzygySequence_shortExact _).map_of_exact F) m h

theorem finite_subgroup_order_dvd_of_completedIdentity_annihilator
    (H : Subgroup G) [Fintype H] (m : ℤ) (hm : m • completedIdentity G = 0) :
    (Fintype.card H : ℤ) ∣ m := by
  have hz : Module.DirectLimit.of ℤ ℕ _ (normalizedCohomologyForward (trivialIntegral G)) 0
      (m • normalizedGroupIdentityClass G 0) = 0 := by
    rw [map_zsmul]
    exact hm
  obtain ⟨j, hj, he⟩ := Module.DirectLimit.of.zero_exact hz
  rw [map_zsmul, normalizedCohomologyForward_identity] at he
  have hs : m • normalizedGroupIdentityClass G (j + 1) = 0 := by
    have hd := congrArg (fun x => normalizedSyzygyConnecting (trivialIntegral G) j x) he
    simpa only [map_zsmul, normalizedSyzygyConnecting_identity, map_zero] using hd
  have hc : m • normalizedIdentityClass (trivialIntegral G) (j + 1) = 0 := by
    have hd := congrArg (fun x => (coefficientNaturalCohomologyIso
      (normalizedProjectiveResolution (trivialIntegral G))
      ((iteratedNormalizedSyzygy (j + 1)).obj (trivialIntegral G)) (j + 1)).hom x) hs
    simp only [map_zsmul, normalizedGroupIdentityClass_comparison, map_zero] at hd
    exact hd
  have hstable := normalizedIdentityClass_scalar_zero_stable (trivialIntegral G) j m hc
  obtain ⟨P, hP, u, v, huv⟩ :=
    (stableRepresentationClass_eq_zero_iff_projective_factor _).mp hstable
  let := hP
  let F : Rep.{0} ℤ G ⥤ Rep.{0} ℤ H := Rep.resFunctor H.subtype
  have hres : stableRepresentationClass
      (F.obj ((iteratedNormalizedSyzygy (j + 1)).obj (trivialIntegral G)))
      (F.obj ((iteratedNormalizedSyzygy (j + 1)).obj (trivialIntegral G))) (m • 𝟙 _) = 0 := by
    apply (stableRepresentationClass_eq_zero_iff_projective_factor _).mpr
    refine ⟨F.obj P, (Rep.resFunctor (k := ℤ) H.subtype).projective_obj_of_projective hP,
      F.map u, F.map v, ?_⟩
    rw [← F.map_comp, huv, F.map_zsmul, F.map_id]
  exact (stableTrivialScalar_eq_zero_iff m).mp
    (normalizedStableScalar_restrict_descend H (j + 1) m hres)

theorem boundedFiniteSubgroupOrders_of_completedIdentity_torsion
    (m : ℤ) (hm0 : m ≠ 0) (hm : m • completedIdentity G = 0) :
    HasBoundedFiniteSubgroupOrders G := by
  refine ⟨m.natAbs, fun H hH => ?_⟩
  let := hH
  let := Fintype.ofFinite H
  have hd := finite_subgroup_order_dvd_of_completedIdentity_annihilator H m hm
  have hn : Fintype.card H ∣ m.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  rw [Nat.card_eq_fintype_card]
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hm0) hn

end PolycyclicRecognition

end

end OAI
