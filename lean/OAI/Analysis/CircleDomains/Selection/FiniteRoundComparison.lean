import OAI.Analysis.CircleDomains.Reflection.FiniteAnalyticBeltrami
import OAI.Analysis.CircleDomains.Reflection.RoundDiskReflection

namespace OAI

/-! Exact labeled spherical exterior correspondence for the constructed
smooth finite rounding. -/
open Set Function Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma rounding_round_disks_disjoint {I : Type*} (C : FiniteJordanConfiguration I)
    (P : ℂ ≃ₜ ℂ) (c : I → ℂ) (r : I → ℝ)
    (hp : ∀i,P '' closure (jordanInterior (C.hole i))=closedBall (c i) (r i)) :
    Pairwise (fun i j => Disjoint (((↑) : ℂ → Sphere) '' closedBall (c i) (r i))
      (((↑) : ℂ → Sphere) '' closedBall (c j) (r j))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro p ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
  have hyx : y=x := OnePoint.coe_injective he
  subst y
  rw [←hp i] at hx
  rw [←hp j] at hy
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,he⟩ := hy
  have hba : b=a := P.injective he
  exact Set.disjoint_left.mp (C.disjoint hij) ha (hba ▸ hb)

lemma rounding_spherical_cap_image {I : Type*} (C : FiniteJordanConfiguration I)
    (P : ℂ ≃ₜ ℂ) (c : I → ℂ) (r : I → ℝ)
    (hp : ∀i,P '' closure (jordanInterior (C.hole i))=closedBall (c i) (r i)) (i : I) :
    P.onePointCongr '' closedTerminalCap (C.hole i)=
      ((↑) : ℂ → Sphere) '' closedBall (c i) (r i) := by
  rw [closedTerminalCap,CannonSphereReflection.onePoint_image,hp]

lemma rounding_spherical_exterior_image {I : Type*} [Finite I] (C : FiniteJordanConfiguration I)
    (P : ℂ ≃ₜ ℂ) (c : I → ℂ) (r : I → ℝ)
    (hp : ∀i,P '' closure (jordanInterior (C.hole i))=closedBall (c i) (r i)) :
    P.onePointCongr '' C.region=(⋃i,((↑) : ℂ → Sphere) '' closedBall (c i) (r i))ᶜ := by
  change P.onePointCongr '' (⋃i,closedTerminalCap (C.hole i))ᶜ=_
  rw [P.onePointCongr.image_compl,image_iUnion]
  simp_rw [rounding_spherical_cap_image C P c r hp]

end CircleDomainRigidity

end

end OAI
