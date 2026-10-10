import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAutomorphicSections
import Mathlib.Topology.ContinuousMap.CompactlySupported

namespace OAI

/-! Compactly supported seeds produce actual continuous automorphic
sections by a locally finite sum with the cubic multiplier. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators CompactlySupported
namespace CubicFirstMoment

lemma cubicTheta_compact_translates_locallyFinite {K : Set CubicThetaPoint} (hK : IsCompact K) :
    LocallyFinite (fun g : cubicThetaPrincipalGroup => (fun p => g • p) ⁻¹' K) := by
  intro p
  obtain ⟨L,hL,hLp⟩ := exists_compact_mem_nhds p
  refine ⟨L,hLp,?_⟩
  apply (finite_disjoint_inter_image (Γ:=cubicThetaPrincipalGroup) hL hK).subset
  rintro g ⟨q,hq,hqL⟩
  exact ⟨g • q,⟨q,hqL,rfl⟩,hq⟩

def cubicThetaPoincareTerm (ψ : C_c(CubicThetaPoint,ℂ))
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) : ℂ :=
  star (cubicThetaKubotaValue g)*ψ (g • p)

lemma cubicThetaPoincareTerm_locallyFinite (ψ : C_c(CubicThetaPoint,ℂ)) :
    LocallyFinite (fun g : cubicThetaPrincipalGroup => Function.support (cubicThetaPoincareTerm ψ g)) := by
  apply (cubicTheta_compact_translates_locallyFinite ψ.hasCompactSupport).subset
  intro g p hp
  apply subset_tsupport ψ
  intro hz
  exact hp (by simp [cubicThetaPoincareTerm,hz])

lemma cubicThetaPoincareTerm_continuous (ψ : C_c(CubicThetaPoint,ℂ))
    (g : cubicThetaPrincipalGroup) : Continuous (cubicThetaPoincareTerm ψ g) :=
  continuous_const.mul (ψ.continuous.comp (continuous_const_smul g))

lemma cubicThetaPoincareTerm_translate (ψ : C_c(CubicThetaPoint,ℂ))
    (g h : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    cubicThetaPoincareTerm ψ g (h • p)=
      cubicThetaKubotaValue h*cubicThetaPoincareTerm ψ (g*h) p := by
  have hu : cubicThetaKubotaValue h*star (cubicThetaKubotaValue h)=1 := by
    rw [Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  calc
    _ = (cubicThetaKubotaValue h*star (cubicThetaKubotaValue h))*
      cubicThetaPoincareTerm ψ g (h • p) := by rw [hu,one_mul]
    _ = _ := by
      simp only [cubicThetaPoincareTerm,cubicThetaKubotaValue_mul,star_mul,mul_smul]
      ring

def cubicThetaPoincareSection (ψ : C_c(CubicThetaPoint,ℂ)) : CubicThetaSection :=
  ⟨⟨fun p => ∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p,
    continuous_finsum (cubicThetaPoincareTerm_continuous ψ) (cubicThetaPoincareTerm_locallyFinite ψ)⟩,by
    intro h p
    change (∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g (h • p))=
      cubicThetaKubotaValue h*(∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p)
    simp_rw [cubicThetaPoincareTerm_translate]
    change (∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaKubotaValue h • cubicThetaPoincareTerm ψ (g*h) p)=_
    rw [← smul_finsum]
    exact congrArg (fun z : ℂ => cubicThetaKubotaValue h • z)
      (finsum_comp_equiv (f:=fun g => cubicThetaPoincareTerm ψ g p) (Equiv.mulRight h))⟩

lemma cubicThetaPoincareSection_compact (ψ : C_c(CubicThetaPoint,ℂ)) :
    HasCompactSupport (cubicThetaSectionNorm (cubicThetaPoincareSection ψ)) := by
  have hc := ψ.hasCompactSupport.image cubicThetaQuotientMap_open.continuous
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hc.isClosed
  intro q hq
  let p := cubicThetaQuotientLift q
  have hn : (∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p)≠0 := by
    intro hz
    apply hq
    change ‖∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p‖=0
    simp [hz]
  have hex : ∃ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p≠0 := by
    by_contra! hn'
    exact hn (by simp [hn'])
  obtain ⟨g,hg⟩ := hex
  refine ⟨g • p,?_,?_⟩
  · apply subset_tsupport ψ
    intro hz
    exact hg (by simp [cubicThetaPoincareTerm,hz])
  · exact (cubicThetaQuotient_covering.map_smul g).trans (cubicThetaQuotientLift_map q)

end CubicFirstMoment

end

end OAI
