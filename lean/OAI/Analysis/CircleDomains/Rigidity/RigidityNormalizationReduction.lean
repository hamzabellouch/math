import OAI.Analysis.CircleDomains.Rigidity.RemovabilityMobiusTransport
import OAI.Analysis.CircleDomains.Modulus.PrincipalNormalization

namespace OAI

/-! The principal identity statement implies the exact, unnormalized
removability-to-rigidity statement. All normalizers are explicit Möbius maps. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem circleDomainRemovabilityRigidity_of_principal_identity
    (hidentity : ∀ {G : Set Sphere} {f : Sphere → Sphere}, IsCircleDomain G →
      OnePoint.infty ∈ G → IsConformalEquivalence f G (f '' G) →
      IsPrincipalNormalized f → IsCircleDomain (f '' G) →
      IsConformallyRemovable (frontier G) → ∀ p ∈ G, f p = p) :
    CircleDomainRemovabilityRigidity := by
  intro U V f hU hV hrem hf
  obtain ⟨p,hp⟩ := hU.2.1.nonempty
  let A := pointToInfinity p
  let B := pointToInfinity (f p)
  let U' := A '' U
  have hA : IsConformalEquivalence A.symm U' U := by
    refine ⟨fun q _ => isConformalAt_pointToInfinity_symm p q,?_,A,
      fun q _ => isConformalAt_pointToInfinity p q,?_,?_,?_⟩
    · rintro q ⟨x,hx,rfl⟩
      simpa only [A.symm_apply_apply] using hx
    · exact mapsTo_image _ _
    · exact fun q _ => A.apply_symm_apply q
    · exact fun q _ => A.symm_apply_apply q
  let f₀ := B ∘ f ∘ A.symm
  have hf₀ : IsConformalEquivalence f₀ U' (B '' V) :=
    hA.trans (hf.trans (isConformalEquivalence_pointToInfinity (f p) V))
  have hU' : IsCircleDomain U' := pointToInfinity_preserves_circleDomain p hU
  have hinf : OnePoint.infty ∈ U' := by
    rw [← pointToInfinity_apply_self p]
    exact mem_image_of_mem A hp
  have hAi : A.symm OnePoint.infty = p := by
    rw [← pointToInfinity_apply_self p]
    exact A.symm_apply_apply p
  have hfix : f₀ OnePoint.infty = OnePoint.infty := by
    dsimp only [f₀,Function.comp_apply]
    rw [hAi]
    exact pointToInfinity_apply_self (f p)
  obtain ⟨a,b,ha,hnorm⟩ := principal_normalize_at_infty hU'.1 hf₀.1 hf₀.bijOn.injOn hinf hfix
  let C := affineSphere a b ha
  let f₁ := C ∘ f₀
  have hC : IsConformalEquivalence C (B '' V) (C '' (B '' V)) :=
    isConformalEquivalence_of_homeomorph C _ (fun q _ => isConformalAt_affineSphere a b ha q)
      (fun q _ => isConformalAt_affineSphere_symm a b ha q)
  have hf₁ : IsConformalEquivalence f₁ U' (C '' (B '' V)) := hf₀.trans hC
  have hc : IsCircleDomain (C '' (B '' V)) :=
    isCircleDomain_image_mobius (pointToInfinity_preserves_circleDomain (f p) hV)
      (affineMobius a b ha) C (affineSphere_eq_smul a b ha)
  have hrem' : IsConformallyRemovable (frontier U') := hrem.frontier_pointToInfinity p
  have he := hf₁.bijOn.image_eq
  have hid := hidentity hU' hinf (he.symm ▸ hf₁) hnorm (he.symm ▸ hc) hrem'
  refine ⟨(affineMobius a b ha * pointToInfinityMobius (f p))⁻¹ * pointToInfinityMobius p,?_⟩
  intro q hq
  have hh := hid (A q) (mem_image_of_mem A hq)
  change C (B (f (A.symm (A q)))) = A q at hh
  rw [A.symm_apply_apply] at hh
  change affineSphere a b ha (pointToInfinity (f p) (f q)) = pointToInfinity p q at hh
  have hh' : (affineMobius a b ha * pointToInfinityMobius (f p)) • f q =
      pointToInfinityMobius p • q := by
    simpa only [affineSphere_eq_smul,pointToInfinity_eq_smul,mul_smul] using hh
  have hh'' := congrArg (fun x : Sphere =>
    (affineMobius a b ha * pointToInfinityMobius (f p))⁻¹ • x) hh'
  rw [inv_smul_smul] at hh''
  simpa only [mul_smul] using hh''

end CircleDomainRigidity

end

end OAI
