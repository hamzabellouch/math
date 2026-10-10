import Mathlib

namespace OAI

namespace FiberFunctorProof
open Representation
universe u v
variable {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
variable {G : Type v} [Group G] [Finite G]
variable {V : Type u} [AddCommGroup V] [Module k V]

 

theorem pgroup_exists_invariant (hG : IsPGroup p G) (ρ : Representation k G V)
    (v : V) (hv : v ≠ 0) : ∃ w : V, w ≠ 0 ∧ ∀ g, ρ g w = w := by
  classical
  let : Algebra (ZMod p) k := ZMod.algebra k p
  let : Module (ZMod p) V := Module.compHom V (algebraMap (ZMod p) k)
  let : IsScalarTower (ZMod p) k V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let W : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range fun g : G => ρ g v)
  have hvW : v ∈ W := by
    apply Submodule.subset_span
    exact ⟨1, by simp⟩
  have hstable (g : G) : W ≤ W.comap ((ρ g).restrictScalars (ZMod p)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨h,rfl⟩
    change ρ g (ρ h v) ∈ W
    change (ρ g * ρ h) v ∈ W
    rw [← map_mul]
    exact Submodule.subset_span ⟨g*h,rfl⟩
  let σ : Representation (ZMod p) G W :=
    { toFun := fun g => ((ρ g).restrictScalars (ZMod p)).restrict (hstable g)
      map_one' := by ext w; simp
      map_mul' := by intro g h; ext w; simp [map_mul] }
  let : Module.Finite (ZMod p) W :=
    Module.Finite.of_fg (Submodule.fg_span (Set.finite_range _))
  let : Finite W := Module.finite_of_finite (ZMod p)
  have hnt : Nontrivial W := ⟨⟨⟨v,hvW⟩,0,fun h => hv (congrArg Subtype.val h)⟩⟩
  let := hnt
  let : MulAction G W := {
    smul g w := σ g w
    one_smul := by intro w; change σ 1 w = w; simp
    mul_smul := by intro g h w; change σ (g*h) w = σ g (σ h w); simp [map_mul] }
  have hpW : p ∣ Nat.card W := by
    let := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
    exact dvd_pow_self p (ne_of_gt (Module.finrank_pos (R := ZMod p) (M := W)))
  obtain ⟨w,hw,hne⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point W hpW
    (a := 0) (by intro g; change σ g 0 = 0; simp)
  refine ⟨w,?_,?_⟩
  · intro h
    apply hne
    exact Subtype.ext h.symm
  · intro g
    exact congrArg Subtype.val (hw g)
end FiberFunctorProof

end OAI
