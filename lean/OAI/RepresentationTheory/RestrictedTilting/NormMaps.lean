import OAI.RepresentationTheory.RestrictedTilting.NormDefinitions
import OAI.RepresentationTheory.RestrictedTilting.RegularSplitting

namespace OAI

namespace FiberFunctorProof
open Representation
universe u
variable {k : Type u} [Field k] {G : Type u} [Group G] [Fintype G]
variable {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

 
def NormSurjective (ρ : Representation k G V) : Prop :=
  ∀ w : V, (∀ g, ρ g w = w) → ∃ v, ρ.norm v = w

lemma coinvariantNorm_surjective_iff (ρ : Representation k G V) :
    Function.Surjective (coinvariantNorm ρ) ↔ NormSurjective ρ := by
  constructor
  · intro h w hw
    obtain ⟨c,hc⟩ := h ⟨w,hw⟩
    obtain ⟨v,rfl⟩ := Coinvariants.mk_surjective ρ c
    exact ⟨v,congrArg Subtype.val hc⟩
  · intro h w
    obtain ⟨v,hv⟩ := h w w.property
    exact ⟨Coinvariants.mk ρ v, Subtype.ext hv⟩

lemma normSurjective_of_retract {ρ : Representation k G V} {σ : Representation k G W}
    (f : ρ.IntertwiningMap σ) (s : σ.IntertwiningMap ρ)
    (h : s.comp f = IntertwiningMap.id ρ) (hσ : NormSurjective σ) : NormSurjective ρ := by
  have hsf (v : V) : s (f v) = v := congr($(h) v)
  intro w hw
  obtain ⟨v,hv⟩ := hσ (f w) (fun g => by rw [← f.isIntertwining, hw g])
  exact ⟨s v, by rw [← intertwining_norm s, hv, hsf]⟩

lemma norm_bijective_of_retract {ρ : Representation k G V} {σ : Representation k G W}
    (f : ρ.IntertwiningMap σ) (s : σ.IntertwiningMap ρ)
    (h : s.comp f = IntertwiningMap.id ρ)
    (hσ : Function.Bijective (coinvariantNorm σ)) :
    Function.Bijective (coinvariantNorm ρ) := by
  classical
  have hsf (v : V) : s (f v) = v := congr($(h) v)
  constructor
  · intro a b hab
    obtain ⟨v,rfl⟩ := Coinvariants.mk_surjective ρ a
    obtain ⟨w,rfl⟩ := Coinvariants.mk_surjective ρ b
    have hvw : ρ.norm v = ρ.norm w := congrArg Subtype.val hab
    have hn : coinvariantNorm σ (Coinvariants.mk σ (f v)) =
        coinvariantNorm σ (Coinvariants.mk σ (f w)) := by
      apply Subtype.ext
      change σ.norm (f v) = σ.norm (f w)
      rw [← intertwining_norm f, ← intertwining_norm f, hvw]
    have hc := congrArg (Coinvariants.map σ ρ s) (hσ.1 hn)
    simpa only [Coinvariants.map_mk, hsf] using hc
  · exact (coinvariantNorm_surjective_iff ρ).2 (normSurjective_of_retract f s h
      ((coinvariantNorm_surjective_iff σ).1 hσ.2))
end FiberFunctorProof

end OAI
