import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralQuotientKernel
import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentCyclicKernelCompletion

namespace OAI

/-! # Completing every nilpotent extension of a real kernel by an integral lattice

The quotient rank induction removes an actual coordinate, completes its
kernel, and constructs the next real cyclic direction. The section relations
and all maps are retained through the group isomorphisms.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K G : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [LieRing.IsNilpotent K]
  [Group G] [Group.IsNilpotent G]

theorem nilpotent_integral_kernel_completion_with_dimension {n : ℕ}
    (E : GroupExtension K G (IntegralLatticeGroup n))
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, K)) ∞ (E.conjAct g)) :
    ∃ C : NilpotentKernelCompletion E.inl, C.dimension = Module.finrank ℝ K + n := by
  have main : ∀ m : ℕ, ∀ (H : Type) [Group H] [Group.IsNilpotent H],
      ∀ (S : GroupExtension K H (IntegralLatticeGroup m)),
      (∀ h : H, ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, K)) ∞ (S.conjAct h)) →
      ∃ C : NilpotentKernelCompletion S.inl, C.dimension = Module.finrank ℝ K + m := by
    intro m
    induction m with
    | zero =>
      intro H _ _ S _
      simpa only [Nat.add_zero] using
        NilpotentKernelCompletion.exists_of_bijective_kernel_with_dimension S.inl (by
          refine ⟨S.inl_injective, ?_⟩
          intro h
          have hh : h ∈ S.inl.range := by
            rw [S.range_inl_eq_ker_rightHom]
            change S.rightHom h = 1
            exact Subsingleton.elim _ _
          exact hh)
    | succ m ih =>
      intro H _ _ S hS
      let q := integralLastMap S
      let T := integralKernelExtension S
      have hT (h : q.ker) : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, K)) ∞ (T.conjAct h) := by
        convert hS (h : H) using 1
        ext x
        exact integralKernelExtension_conjAct S h x
      obtain ⟨C, hC⟩ := ih q.ker T hT
      have hq : Function.Surjective q := (integralQuotientLast_surjective m).comp S.rightHom_surjective
      obtain ⟨t, ht⟩ := hq (Multiplicative.ofAdd 1)
      have hnormal (g : H) (x : K) :
          MulAut.conjNormal (H := q.ker) g (T.inl x) = T.inl (S.conjAct g x) := by
        apply Subtype.ext
        exact (S.inl_conjAct_comm (e := g) (n := x)).symm
      have hact (g : H) : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
          ((C.embed.comp (MulAut.conjNormal (H := q.ker) g).toMonoidHom).comp T.inl) := by
        have heq : ((C.embed.comp (MulAut.conjNormal (H := q.ker) g).toMonoidHom).comp
            T.inl : K → C.carrier) = fun x => C.embed (T.inl (S.conjAct g x)) := by
          funext x
          exact congrArg C.embed (hnormal g x)
        rw [heq]
        exact C.kernel_smooth.comp (hS g)
      have hai : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
          ((C.embed.comp (MulAut.conjNormal (H := q.ker) t).symm.toMonoidHom).comp T.inl) := by
        have hi : (MulAut.conjNormal (H := q.ker) t).symm =
            MulAut.conjNormal (H := q.ker) t⁻¹ := (map_inv _ t).symm
        rw [hi]
        exact hact t⁻¹
      obtain ⟨D, hD⟩ := nilpotent_cyclic_kernel_completion_with_dimension q t ht T.inl C (hact t) hai
      change NilpotentKernelCompletion S.inl at D
      exact ⟨D, hD.trans (by rw [hC, Nat.add_assoc])⟩
  exact main n G E hsmooth

theorem nilpotent_integral_kernel_completion {n : ℕ}
    (E : GroupExtension K G (IntegralLatticeGroup n))
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, K)) ∞ (E.conjAct g)) :
    Nonempty (NilpotentKernelCompletion E.inl) := by
  obtain ⟨C, _⟩ := nilpotent_integral_kernel_completion_with_dimension E hsmooth
  exact ⟨C⟩

end PolycyclicRecognition

end

end OAI
