import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SmallControlTransfer
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.InvariantPatching

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ControlledPatching
variable {α H ι : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

theorem controlled_cell_normalizes (L : Finset α → Subgroup H)
    (c : alternatingGroup α →* H)
    (hc : ∀ σ I, ∀ x ∈ L I, c σ*x*(c σ)⁻¹ ∈ L (I.map σ.val.toEmbedding))
    (hd : ∀ I J, Disjoint I J → ∀ x ∈ L I, ∀ y ∈ L J, Commute x y)
    (hα : 20 ≤ Fintype.card α)
    (F p v : ι → TrackStar α →* H) (j k : TrackStar α →* H)
    (hp : ∀ i, SmallSupported L (p i)) (hv : ∀ i, SmallSupported L (v i))
    (hj : SmallSupported L j) (hpc : ∀ i, SmallControlled c (p i) j)
    (hvc : ∀ i, SmallControlled c (v i) k)
    (hjk : ∀ s t, Commute (j s) (k t))
    (hsplit : ∀ i s, F i s=p i s*v i s) :
    ∀ i s, F i s ∈ Subgroup.normalizer ((⨆ i, (p i).range : Subgroup H) : Set H) := by
  have hcomm (i i' : ι) (s t : TrackStar α) : Commute (p i s) (v i' t) :=
    small_control_disjoint L c hc hd hα _ _ _ _ (hp i) (hv i') hj
      (hpc i) (hvc i') hjk s t
  have ho (i : ι) (s : TrackStar α) :
      v i s ∈ Subgroup.centralizer ((⨆ i, (p i).range : Subgroup H) : Set H) := by
    have hle : (⨆ i, (p i).range : Subgroup H) ≤ Subgroup.centralizer ({v i s} : Set H) := by
      apply iSup_le
      rintro i' x ⟨t,rfl⟩ y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact (hcomm i' i t s).eq.symm
    intro x hx
    exact (hle hx _ rfl).symm
  intro i s
  exact normalizes_of_cell_split _ _ _ _ (hsplit i s)
    ((le_iSup (fun i => (p i).range) i) ⟨s,rfl⟩) (ho i s)

theorem sameActionOn_iSup {D : Type*} (f g : D → H) (P : ι → Subgroup H)
    (h : ∀ i, SameActionOn f g (P i)) : SameActionOn f g (⨆ i, P i) := by
  intro d x hx
  let F : H →* H := (MulAut.conj (f d)).toMonoidHom
  let J : H →* H := (MulAut.conj (g d)).toMonoidHom
  have hle : (⨆ i, P i) ≤ F.eqLocus J := by
    apply iSup_le
    intro i y hy
    exact h i d y hy
  exact hle hx

end ControlledPatching

end SimpleAmenable
end
end

end OAI
