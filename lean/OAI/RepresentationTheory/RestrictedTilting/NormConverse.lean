import OAI.RepresentationTheory.RestrictedTilting.NormMaps
import OAI.RepresentationTheory.RestrictedTilting.PGroupInvariants
import OAI.RepresentationTheory.RestrictedTilting.ProjectiveRegular
import OAI.RepresentationTheory.RestrictedTilting.SplitRepresentation

namespace OAI

namespace FiberFunctorProof
open CategoryTheory Representation
universe u
variable {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
variable {G : Type u} [Group G] [Fintype G]
variable {V : Type u} [AddCommGroup V] [Module k V]

 

lemma regular_map_injective (hG : IsPGroup p G) (ρ : Representation k G V)
    (f : (Representation.leftRegular k G).IntertwiningMap ρ)
    (hN : f ((Representation.leftRegular k G).norm (MonoidAlgebra.single 1 1)) ≠ 0) :
    Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  by_contra hx0
  have hxk : (⟨x,hx⟩ : f.ker.toSubmodule) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨z,hz,hfix⟩ := pgroup_exists_invariant hG f.ker.toRepresentation ⟨x,hx⟩ hxk
  have hval : (z : MonoidAlgebra k G) ≠ 0 := fun h => hz (Subtype.ext h)
  have hzN := regular_invariant_eq (z : MonoidAlgebra k G)
    (fun g => congrArg Subtype.val (hfix g))
  have hz0 : f (z : MonoidAlgebra k G) = 0 := z.property
  have hc : (z : MonoidAlgebra k G).coeff 1 = 0 := by
    rw [hzN, map_smul] at hz0
    exact (smul_eq_zero.mp hz0).resolve_right hN
  apply hval
  rw [hzN, hc, zero_smul]

 

theorem projective_of_normSurjective (hG : IsPGroup p G)
    [FiniteDimensional k V] (ρ : Representation k G V) (hρ : NormSurjective ρ) :
    Projective (Rep.of ρ) := by
  suffices H : ∀ n : ℕ, ∀ (M : Type u) [AddCommGroup M] [Module k M]
      [FiniteDimensional k M], Module.finrank k M = n →
      ∀ τ : Representation k G M, NormSurjective τ → Projective (Rep.of τ) by
    exact H _ V rfl ρ hρ
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro M _ _ _ hdim τ hτ
    cases subsingleton_or_nontrivial M with
    | inl hs =>
      let := hs
      constructor
      intro E X f e he
      refine ⟨0, ?_⟩
      rw [Limits.zero_comp]
      apply Rep.hom_ext
      apply IntertwiningMap.ext
      ext m
      rw [Subsingleton.elim m 0]
      simp
    | inr hnt =>
      let := hnt
      obtain ⟨v,hv⟩ := exists_ne (0 : M)
      obtain ⟨w,hw,hfix⟩ := pgroup_exists_invariant hG τ v hv
      obtain ⟨m,hm⟩ := hτ w hfix
      let f : (Representation.leftRegular k G).IntertwiningMap τ :=
        (Rep.leftRegularHom (Rep.of τ) m).hom
      have hfm : f (MonoidAlgebra.single 1 1) = m := by simp [f]
      have hfn : f ((Representation.leftRegular k G).norm (MonoidAlgebra.single 1 1)) ≠ 0 := by
        rw [intertwining_norm f, hfm, hm]
        exact hw
      have hf := regular_map_injective hG τ f hfn
      obtain ⟨s,hs⟩ := regular_split_of_injective τ f hf
      let κ := s.ker.toRepresentation
      have hκ : NormSurjective κ :=
        normSurjective_of_retract (kernelInclusion s)
          (splitKernelProjection f s hs) (splitKernelProjection_inclusion f s hs) hτ
      have hker : s.toLinearMap.ker ≠ ⊤ := by
        intro htop
        have hzero : s (f (MonoidAlgebra.single 1 1)) = 0 := by
          exact (show f (MonoidAlgebra.single 1 1) ∈ s.toLinearMap.ker by rw [htop]; trivial)
        have hsf : s (f (MonoidAlgebra.single 1 1)) = MonoidAlgebra.single 1 1 :=
          congr($(hs) (MonoidAlgebra.single 1 1))
        rw [hsf] at hzero
        have hh := congrArg (fun v : MonoidAlgebra k G => v.coeff 1) hzero
        simp at hh
      have hlt : Module.finrank k s.ker.toSubmodule < n := by
        rw [← hdim]
        exact Submodule.finrank_lt hker
      have hK : Projective (Rep.of κ) := ih _ hlt _ rfl κ hκ
      exact projective_of_split_kernel f s hs (rep_leftRegular_projective k G) hK
end FiberFunctorProof

end OAI
