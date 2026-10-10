import Mathlib
import OAI.GroupTheory.PeriodicGroups.Homology.KernelStability

namespace OAI

namespace SourceBurnside.ConcreteSource
noncomputable section
open Classical Stability Stability.RationalKernel
open scoped IsMulCommutative

theorem kernel_torsion_rank {n : ℕ} (hn : 12≤n) (u : Steinberg n R)
    (hu : Elementary.representation u=1) : ∃ m : ℕ, 0 < m ∧ u ^ m = 1 := by
  let j : J (R := R) n := ⟨u,Subtype.ext hu⟩
  let : IsMulCommutative (J (R := R) n) := ⟨⟨fun a b =>
    Subtype.ext ((central matrix_nil_kernel n (by omega) a.property).comm b.val).eq⟩⟩
  have hj : IsOfFinOrder j := by
    apply RationalDetection.finite_of_characters_vanish
    intro φ
    obtain ⟨q,hnq,m,hm,he⟩ := kernel_standard_stable_torsion (by omega) u hu
    obtain ⟨ψ,hψ⟩ := restriction_cast_surjective augmentation matrix_nil_kernel hn hnq φ
    have hfin : IsOfFinOrder (kernelCast augmentation hnq j) := by
      refine isOfFinOrder_iff_pow_eq_one.mpr ⟨m,hm,?_⟩
      exact Subtype.ext he
    have hz := RationalDetection.character_finite_eq_one ψ hfin
    have hx := DFunLike.congr_fun hψ j
    change ψ (kernelCast augmentation hnq j)=φ j at hx
    exact hx.symm.trans hz
  obtain ⟨m,hm,he⟩ := hj.exists_pow_eq_one
  exact ⟨m,hm,congrArg Subtype.val he⟩

theorem kernel_torsion (u : Steinberg 12 R) (hu : Elementary.representation u=1) :
    ∃ m : ℕ, 0 < m ∧ u ^ m = 1 := kernel_torsion_rank (by decide) u hu

theorem steinberg_periodic_rank {n : ℕ} (hn : 12≤n) : Periodic (Steinberg n R) := by
  intro g
  obtain ⟨a,ha,hea⟩ := matrix_periodic n (Elementary.representation g)
  have hker : Elementary.representation (g^a)=1 := by rw [map_pow,hea]
  obtain ⟨b,hb,heb⟩ := kernel_torsion_rank hn (g^a) hker
  exact ⟨a*b,Nat.mul_pos ha hb,by rw [pow_mul,heb]⟩

theorem steinberg_periodic : Periodic (Steinberg 12 R) := steinberg_periodic_rank (by decide)

theorem main : Infinite (Steinberg 12 R) ∧
    Group.IsFinitelyPresented (Steinberg 12 R) ∧ Periodic (Steinberg 12 R) :=
  ⟨steinberg_infinite,steinberg_finitely_presented,steinberg_periodic⟩

theorem main_statement : MainStatement := ⟨R,inferInstance,inferInstance,main⟩

theorem exists_infinite_finitely_presented_periodic_group :
    ∃ (G : Type) (hG : Group G), Infinite G ∧
      @Group.IsFinitelyPresented G hG ∧ @Periodic G hG :=
  ⟨Steinberg 12 R,inferInstance,main⟩

theorem burnside_statement : BurnsideStatement := exists_infinite_finitely_presented_periodic_group

end
end SourceBurnside.ConcreteSource

end OAI
