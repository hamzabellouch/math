import OAI.Analysis.CircleDomains.Rigidity.FiniteMatchedField
import OAI.Analysis.CircleDomains.Rigidity.SmoothMatchedScalar

namespace OAI

/-! One compact smooth coordinate test agrees with the actual coordinate
on all fibers over a prescribed compact source set and on all target
complementary components. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem compact_relation_image (hf : IsConformalEquivalence f G (f '' G))
    {K : Set ℂ} (hK : IsCompact K) :
    IsCompact {p : Sphere | ∃ z ∈ K, D.planeRelation z p} := by
  have h := ((hK.prod (isCompact_univ : IsCompact (univ : Set Sphere))).inter_right
    (D.planeRelation_closed hf)).image continuous_snd
  convert h using 1
  ext p
  simp only [mem_image,mem_inter_iff,mem_prod,mem_univ,and_true,Prod.exists]
  constructor
  · rintro ⟨z,hz,hr⟩
    exact ⟨z,p,⟨hz,hr⟩,rfl⟩
  · rintro ⟨z,q,⟨hz,hr⟩,rfl⟩
    exact ⟨z,hz,hr⟩

 theorem exists_compact_relation_coordinate_test
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsOpen (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {K : Set ℂ} (hK : IsCompact K) (k : Fin 2) :
    ∃ Φ : EuclideanPlane → ℝ, ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧
      (∀ p ∈ (f '' G)ᶜ, sphereFromPlaneFunction Φ p =
        (complexPlaneCoordinates.symm (finiteCoord p)) k) ∧
      ∀ z ∈ K, ∀ p, D.planeRelation z p → sphereFromPlaneFunction Φ p =
        (complexPlaneCoordinates.symm (finiteCoord p)) k := by
  let L : Set Sphere := {p | ∃ z ∈ K, D.planeRelation z p} ∪ (f '' G)ᶜ
  have hL : IsClosed L := (D.compact_relation_image hf hK).isClosed.union hH.isClosed_compl
  have hLinf : OnePoint.infty ∉ L := by
    rintro (⟨z,_,hz⟩ | hz)
    · exact D.planeRelation_ne_infty hG hinf hf hfix hz rfl
    · exact hz hinf'
  obtain ⟨Φ,hΦ,hs,hcoord⟩ := exists_smooth_compact_coordinate_test hL.isOpen_compl hLinf k
  have hc (p : Sphere) (hp : p ∈ L) : sphereFromPlaneFunction Φ p =
      (complexPlaneCoordinates.symm (finiteCoord p)) k := by
    cases p using OnePoint.rec with
    | infty => exact (hLinf hp).elim
    | coe z => simpa only [finiteCoord_coe] using hcoord z (not_not.mpr hp)
  exact ⟨Φ,hΦ,hs,fun p hp => hc p (Or.inr hp),fun z hz p hr => hc p (Or.inl ⟨z,hz,hr⟩)⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
