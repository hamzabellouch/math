import Mathlib
import OAI.Analysis.Commutator.FactorCorner
import OAI.Analysis.Commutator.NormalGNS
import OAI.Analysis.Commutator.TracialSequenceTrace

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology ComplexOrder

namespace Kadison.NormalGNS

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

lemma gns_injective (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) :
    Function.Injective τ.gnsStarAlgHom := by
  intro a b hab
  have hz : τ.gnsStarAlgHom (a-b)=0 :=
    (map_sub τ.gnsStarAlgHom a b).trans (sub_eq_zero.mpr hab)
  have hv : algebraVector τ (a-b)=0 := by
    have h := congrArg (fun T : τ.GNS →L[ℂ] τ.GNS => T (vacuum τ)) hz
    simpa only [left_vacuum,algebraVector_apply,zero_apply] using h
  apply sub_eq_zero.mp
  apply hfaith (a-b)
  rw [←inner_algebraVector,hv,inner_zero_left]

lemma gns_norm (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (a : M) :
    ‖τ.gnsStarAlgHom a‖=‖a‖ :=
  NonUnitalStarAlgHom.norm_map _ (gns_injective M τ hfaith) a

variable (hτ : ∀ a b : M, τ (a*b)=τ (b*a)) (hnormal : BoundedWOTContinuous M τ)

def algebra : VonNeumannAlgebra τ.GNS :=
  BicommutantRange.ofStarHom τ.gnsStarAlgHom (range_bicommutant M τ hτ hnormal)

@[simp] lemma mem_algebra (T : τ.GNS →L[ℂ] τ.GNS) :
    T∈algebra M τ hτ hnormal ↔ ∃ a : M, τ.gnsStarAlgHom a=T := Iff.rfl

def equivalence (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) :
    M ≃⋆ₐ[ℂ] algebra M τ hτ hnormal :=
  StarAlgEquiv.ofInjective τ.gnsStarAlgHom (gns_injective M τ hfaith)

@[simp] lemma equivalence_apply (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (a : M) :
    (equivalence M τ hτ hnormal hfaith a : τ.GNS →L[ℂ] τ.GNS)=τ.gnsStarAlgHom a := rfl

def trace : (τ.GNS →L[ℂ] τ.GNS) →ₚ[ℂ] ℂ := VectorFunctional.functional (vacuum τ)

@[simp] lemma trace_gns (a : M) : trace M τ (τ.gnsStarAlgHom a)=τ a := by
  change inner ℂ (vacuum τ) (τ.gnsStarAlgHom a (vacuum τ))=τ a
  rw [left_vacuum]
  exact inner_vacuum_algebraVector τ a

lemma trace_continuous : Continuous (fun T : τ.GNS →WOT[ℂ] τ.GNS => trace M τ T.toCLM) :=
  VectorFunctional.continuous_functional_wot (vacuum τ)

include hτ hnormal in
lemma trace_tracial : ∀ S∈algebra M τ hτ hnormal, ∀ T∈algebra M τ hτ hnormal,
    trace M τ (S*T)=trace M τ (T*S) := by
  rintro S ⟨a,rfl⟩ T ⟨b,rfl⟩
  change trace M τ (τ.gnsStarAlgHom a*τ.gnsStarAlgHom b)=
    trace M τ (τ.gnsStarAlgHom b*τ.gnsStarAlgHom a)
  calc
    trace M τ (τ.gnsStarAlgHom a*τ.gnsStarAlgHom b) =
        trace M τ (τ.gnsStarAlgHom (a*b)) :=
      congrArg (trace M τ) (τ.gnsStarAlgHom.map_mul' a b).symm
    _ = τ (a*b) := trace_gns M τ (a*b)
    _ = τ (b*a) := hτ a b
    _ = trace M τ (τ.gnsStarAlgHom (b*a)) := (trace_gns M τ (b*a)).symm
    _ = trace M τ (τ.gnsStarAlgHom b*τ.gnsStarAlgHom a) :=
      congrArg (trace M τ) (τ.gnsStarAlgHom.map_mul' b a)

include hτ hnormal in
lemma trace_faithful : ∀ T∈algebra M τ hτ hnormal, trace M τ (star T*T)=0 → T=0 := by
  intro T hT hz
  have hb : T∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom)) := by
    rw [range_bicommutant M τ hτ hnormal]
    exact hT
  apply bicommutant_vacuum_separating τ hτ hb
  rw [trace,VectorFunctional.functional_star_mul] at hz
  exact inner_self_eq_zero.mp hz

lemma trace_one : trace M τ 1=τ 1 := by
    exact (congrArg (trace M τ) τ.gnsStarAlgHom.map_one').symm.trans (trace_gns M τ 1)

include hτ hnormal in
theorem isFactor (hM : FactorCorner.IsFactor M)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) :
    FactorCorner.IsFactor (algebra M τ hτ hnormal) := by
  intro z hz hc
  obtain ⟨a,rfl⟩ := hz
  have hca : (a : H →L[ℂ] H)∈Set.centralizer (M : Set (H →L[ℂ] H)) := by
    intro b hb
    let b' : M := ⟨b,hb⟩
    have he : b'*a=a*b' := by
      apply gns_injective M τ hfaith
      exact (τ.gnsStarAlgHom.map_mul' b' a).trans
        ((hc (τ.gnsStarAlgHom b') ⟨b',rfl⟩).trans (τ.gnsStarAlgHom.map_mul' a b').symm)
    exact congrArg Subtype.val he
  obtain ⟨c,hc⟩ := hM a a.property hca
  have he : a=c • (1 : M) := Subtype.ext hc
  refine ⟨c,?_⟩
  change τ.gnsStarAlgHom a=c • (1 : τ.GNS →L[ℂ] τ.GNS)
  calc
    τ.gnsStarAlgHom a = τ.gnsStarAlgHom (c • (1 : M)) := congrArg τ.gnsStarAlgHom he
    _ = c • τ.gnsStarAlgHom 1 := τ.gnsStarAlgHom.toAlgHom.toLinearMap.map_smul c 1
    _ = c • (1 : τ.GNS →L[ℂ] τ.GNS) :=
      congrArg (fun T : τ.GNS →L[ℂ] τ.GNS => c • T) τ.gnsStarAlgHom.map_one'

end Kadison.NormalGNS

end

end
end

end OAI
