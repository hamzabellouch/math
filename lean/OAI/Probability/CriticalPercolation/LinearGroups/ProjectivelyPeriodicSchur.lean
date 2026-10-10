import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.SelbergSchur

namespace OAI

section
noncomputable section
open Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Group G]

def linearMatrixEquiv : (V ≃ₗ[K] V) ≃* GL (Fin (finrank K V)) K :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (Module.finBasis K V)).toMulEquiv)

lemma finite_range_of_torsion_linearEquiv [Group.FG G] (ρ : G →* (V ≃ₗ[K] V))
    (ht : ∀ g, IsOfFinOrder (ρ g)) : Finite ρ.range := by
  let τ := linearMatrixEquiv.toMonoidHom.comp ρ
  have ht' (g : G) : IsOfFinOrder (τ g) := by
    obtain ⟨m,hm,he⟩ := (ht g).exists_pow_eq_one
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨m,hm,?_⟩
    change (linearMatrixEquiv (ρ g))^m=1
    rw [←map_pow,he,map_one]
  let : Finite τ.range := finite_range_of_torsion τ ht'
  let f : ρ.range → τ.range := fun x => ⟨linearMatrixEquiv x.val,by
    obtain ⟨g,hg⟩ := x.property
    exact ⟨g,congrArg linearMatrixEquiv hg⟩⟩
  exact Finite.of_injective f (fun x y h => Subtype.ext
    (linearMatrixEquiv.injective (congrArg Subtype.val h)))

def conjugationRepresentation (ρ : G →* (V ≃ₗ[K] V)) : G →* (End K V ≃ₗ[K] End K V) where
  toFun g := (ρ g).conj
  map_one' := by ext f x; simp only [map_one]; rfl
  map_mul' g h := by ext f x; simp only [map_mul]; rfl

omit [CharZero K] [FiniteDimensional K V] in
lemma conjugation_eq_one_of_scalar (e : V ≃ₗ[K] V) (c : K)
    (hc : e.toLinearMap=c • (1:End K V)) : e.conj=1 := by
  have he (x : V) : e x=c • x := congrArg (fun f : End K V => f x) hc
  ext f x
  change e (f (e.symm x))=f x
  rw [he,←f.map_smul,←he,e.apply_symm_apply]

lemma exists_finiteIndex_comm_range_of_projectively_periodic [Group.FG G]
    (ρ : G →* (V ≃ₗ[K] V))
    (ht : ∀ g, ∃ m : ℕ, 0 < m ∧ ∃ c : K,
      ((ρ g).toLinearMap)^m=c • (1:End K V)) :
    ∃ H : Subgroup G, H.FiniteIndex ∧
      ∀ x y : (ρ.comp H.subtype).range, x*y=y*x := by
  let τ := conjugationRepresentation ρ
  have htτ (g : G) : IsOfFinOrder (τ g) := by
    obtain ⟨m,hm,c,hc⟩ := ht g
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨m,hm,?_⟩
    rw [←map_pow]
    apply conjugation_eq_one_of_scalar (ρ (g^m)) c
    rw [map_pow]
    change (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (ρ g^m))=_
    rw [map_pow]
    exact hc
  let : Finite τ.range := finite_range_of_torsion_linearEquiv τ htτ
  refine ⟨τ.ker,inferInstance,?_⟩
  intro x y
  obtain ⟨g,hg⟩ := x.property
  obtain ⟨h,hh⟩ := y.property
  apply Subtype.ext
  change x.val*y.val=y.val*x.val
  rw [←hg,←hh]
  have hconj : (ρ g.val).conj=1 := g.property
  ext v
  have he := congrArg (fun e : End K V ≃ₗ[K] End K V => e (ρ h.val).toLinearMap (ρ g.val v)) hconj
  change (ρ g.val) ((ρ h.val) v)=(ρ h.val) ((ρ g.val) v)
  change (ρ g.val) ((ρ h.val) ((ρ g.val).symm ((ρ g.val) v)))=(ρ h.val) ((ρ g.val) v) at he
  simpa only [LinearEquiv.conj_apply_apply,LinearEquiv.symm_apply_apply,
    LinearEquiv.coe_one,id_eq,LinearEquiv.mul_apply,MonoidHom.comp_apply,Subgroup.coe_subtype] using he

end CriticalPercolation.LinearGrowth
end
end

end OAI
