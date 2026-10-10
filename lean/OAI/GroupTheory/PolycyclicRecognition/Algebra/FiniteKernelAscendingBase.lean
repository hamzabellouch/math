import OAI.GroupTheory.PolycyclicRecognition.Analysis.AscendingBaseTransport
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteKernelSolvable
import OAI.GroupTheory.PolycyclicRecognition.Algebra.Nilpotent

namespace OAI

/-! # Lifting an ascending base across a finite kernel

Finite kernels preserve the concrete ascending-base property. They also
preserve virtual nilpotence: intersect with the centralizer of the finite
kernel, then use the central-extension criterion for nilpotence.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G Q : Type} [Group G] [Group Q]

theorem fg_preimage_of_finite_kernel (q : G →* Q) (hq : Function.Surjective q)
    [Finite q.ker] (B : Subgroup Q) (hB : B.FG) : (B.comap q).FG := by
  let C := B.comap q
  let f : C →* B := (q.comp C.subtype).codRestrict B (fun c => c.property)
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨g, hg⟩ := hq b
    exact ⟨⟨g, by change q g ∈ B; rw [hg]; exact b.property⟩, Subtype.ext hg⟩
  let k : f.ker → q.ker := fun c => ⟨((c : C) : G), by
    change q ((c : C) : G) = 1
    exact congrArg (fun b : B => (b : Q)) c.property⟩
  have hk : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : q.ker => (c : G)) hab
  let : Finite f.ker := Finite.of_injective k hk
  let : Group.FG B := (Group.fg_iff_subgroup_fg B).mpr hB
  let : Group.FG C := CriticalPercolation.fg_of_kernel_quotient f hf
  exact (Group.fg_iff_subgroup_fg C).mp inferInstance

theorem HasFinitelyGeneratedAscendingBase.of_finite_kernel
    (q : G →* Q) (hq : Function.Surjective q) [Finite q.ker]
    (α : MulAut G) (β : MulAut Q) (heq : ∀ g, q (α g) = β (q g))
    (hβ : HasFinitelyGeneratedAscendingBase β) :
    HasFinitelyGeneratedAscendingBase α := by
  obtain ⟨B, hBfg, hBstable, hBcover⟩ := hβ
  refine ⟨B.comap q, fg_preimage_of_finite_kernel q hq B hBfg, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    change q (α g) ∈ B
    rw [heq]
    exact hBstable ⟨q g, hg, rfl⟩
  · intro g
    obtain ⟨n, hn⟩ := hBcover (q g)
    refine ⟨n, (mem_automorphismStage_iff _ _ _ _).mpr ?_⟩
    change q ((α ^ n) g) ∈ B
    rw [automorphism_pow_equivariant q α β heq]
    exact (mem_automorphismStage_iff _ _ _ _).mp hn

theorem virtuallyNilpotent_of_finite_kernel (q : G →* Q)
    [Finite q.ker] [Group.IsNilpotent Q] : Group.IsVirtuallyNilpotent G := by
  let C := Subgroup.centralizer (q.ker : Set G)
  let : C.FiniteIndex := finiteIndex_centralizer_of_finite_normal q.ker
  let f := q.comp C.subtype
  have hk : f.ker ≤ Subgroup.center C := by
    intro a ha
    apply Subgroup.mem_center_iff.mpr
    intro b
    apply Subtype.ext
    exact (b.property (a : G) ha).symm
  have hC : Group.IsNilpotent C := Subgroup.isNilpotent_of_ker_le_center f hk
  exact ⟨C, hC, inferInstance⟩

theorem virtuallyNilpotent_preimage_of_finite_kernel (q : G →* Q)
    [Finite q.ker] (B : Subgroup Q) [Group.IsNilpotent B] :
    Group.IsVirtuallyNilpotent (B.comap q) := by
  let C := B.comap q
  let f : C →* B := (q.comp C.subtype).codRestrict B (fun c => c.property)
  let k : f.ker → q.ker := fun c => ⟨((c : C) : G), by
    change q ((c : C) : G) = 1
    exact congrArg (fun b : B => (b : Q)) c.property⟩
  have hk : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : q.ker => (c : G)) hab
  let : Finite f.ker := Finite.of_injective k hk
  exact virtuallyNilpotent_of_finite_kernel f

theorem virtuallyNilpotent_of_finiteIndex (H : Subgroup G) [H.FiniteIndex]
    (hH : Group.IsVirtuallyNilpotent H) : Group.IsVirtuallyNilpotent G := by
  obtain ⟨N, hNnil, hNindex⟩ := hH
  let := hNnil
  let := hNindex
  let P := N.map H.subtype
  let e : N ≃* P := N.equivMapOfInjective H.subtype H.subtype_injective
  have hPindex : P.FiniteIndex := ⟨by
    change (N.map H.subtype).index ≠ 0
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hNindex.index_ne_zero (inferInstance : H.FiniteIndex).index_ne_zero⟩
  exact ⟨P, Group.nilpotent_of_mulEquiv e, hPindex⟩

theorem virtuallyNilpotent_of_finite_kernel_of_virtuallyNilpotent (q : G →* Q)
    [Finite q.ker] (hQ : Group.IsVirtuallyNilpotent Q) : Group.IsVirtuallyNilpotent G := by
  obtain ⟨N, hNnil, hNindex⟩ := hQ
  let := hNnil
  let := hNindex
  exact virtuallyNilpotent_of_finiteIndex (N.comap q)
    (virtuallyNilpotent_preimage_of_finite_kernel q N)

theorem virtuallyNilpotent_preimage_of_finite_kernel_of_virtuallyNilpotent
    (q : G →* Q) [Finite q.ker] (B : Subgroup Q)
    (hB : Group.IsVirtuallyNilpotent B) : Group.IsVirtuallyNilpotent (B.comap q) := by
  let C := B.comap q
  let f : C →* B := (q.comp C.subtype).codRestrict B (fun c => c.property)
  let k : f.ker → q.ker := fun c => ⟨((c : C) : G), by
    change q ((c : C) : G) = 1
    exact congrArg (fun b : B => (b : Q)) c.property⟩
  have hk : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : q.ker => (c : G)) hab
  let : Finite f.ker := Finite.of_injective k hk
  exact virtuallyNilpotent_of_finite_kernel_of_virtuallyNilpotent f hB

end PolycyclicRecognition

end

end OAI
