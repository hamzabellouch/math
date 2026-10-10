import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.NestedCutCalculus

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section InvariantPatching
variable {G D α ι : Type*} [Group G] [Group D]

theorem normalizes_of_cell_split (P : Subgroup G) (x y z : G)
    (hx : x=y*z) (hy : y ∈ P) (hz : z ∈ Subgroup.centralizer (P : Set G)) :
    x ∈ (Subgroup.normalizer (P : Set G)) := by
  rw [hx]
  exact (Subgroup.normalizer (P : Set G)).mul_mem (Subgroup.le_normalizer hy)
    (Subgroup.centralizer_le_normalizer _ hz)

theorem sameActionOn_free_lift (P : Subgroup G) (f g : α → G)
    (hf : ∀ i, f i ∈ (Subgroup.normalizer (P : Set G))) (hg : ∀ i, g i ∈ (Subgroup.normalizer (P : Set G)))
    (h : SameActionOn f g P) :
    SameActionOn (FreeGroup.lift f) (FreeGroup.lift g) P := by
  let F : FreeGroup α →* (Subgroup.normalizer (P : Set G)) := FreeGroup.lift (fun i => ⟨f i,hf i⟩)
  let J : FreeGroup α →* (Subgroup.normalizer (P : Set G)) := FreeGroup.lift (fun i => ⟨g i,hg i⟩)
  have hF : (Subgroup.normalizer (P : Set G)).subtype.comp F = FreeGroup.lift f := by
    apply FreeGroup.ext_hom
    intro i
    simp [F]
  have hJ : (Subgroup.normalizer (P : Set G)).subtype.comp J = FreeGroup.lift g := by
    apply FreeGroup.ext_hom
    intro i
    simp [J]
  have he : P.normalizerMonoidHom.comp F = P.normalizerMonoidHom.comp J := by
    apply FreeGroup.ext_hom
    intro i
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simpa [F,J] using h i x.val x.property
  intro w x hx
  have hh := congrArg (fun k : FreeGroup α →* MulAut P => ((k w) ⟨x,hx⟩).val) he
  change (F w).val*x*(F w).val⁻¹ = (J w).val*x*(J w).val⁻¹ at hh
  have hf' : (F w).val = FreeGroup.lift f w := DFunLike.congr_fun hF w
  have hg' : (J w).val = FreeGroup.lift g w := DFunLike.congr_fun hJ w
  simpa only [hf',hg'] using hh

theorem normalizes_of_same_action (P : Subgroup G) (x y : G)
    (hx : x ∈ (Subgroup.normalizer (P : Set G))) (h : ∀ z ∈ P, x*z*x⁻¹=y*z*y⁻¹) :
    y ∈ (Subgroup.normalizer (P : Set G)) := by
  intro z
  constructor
  · intro hz
    rw [← h z hz]
    exact (hx z).mp hz
  · intro hz
    have hu : x⁻¹*(y*z*y⁻¹)*x ∈ P := by
      have hu' := ((Subgroup.normalizer (P : Set G)).inv_mem hx (y*z*y⁻¹)).mp hz
      rw [inv_inv] at hu'
      exact hu'
    have hh := h _ hu
    have he : x*(x⁻¹*(y*z*y⁻¹)*x)*x⁻¹ = y*z*y⁻¹ := by group
    rw [he] at hh
    have hv : z=x⁻¹*(y*z*y⁻¹)*x := by
      have ht := congrArg (fun q => y⁻¹*q*y) hh
      simpa only [mul_assoc,inv_mul_cancel,inv_mul_cancel_left,mul_inv_cancel_left,mul_one] using ht
    rwa [← hv] at hu

theorem patching_centrality (f : α → G) (P : ι → Subgroup G)
    (hgen : (FreeGroup.lift f).range ≤ ⨆ i, P i)
    (hinv : ∀ i j, f j ∈ (Subgroup.normalizer (P i : Set G)))
    (w : FreeGroup α)
    (hlocal : ∀ i, ∃ g : α → G, SameActionOn f g (P i) ∧
      FreeGroup.lift g w ∈ Subgroup.centralizer (P i : Set G)) :
    ∀ x ∈ (FreeGroup.lift f).range, Commute (FreeGroup.lift f w) x := by
  have hc : ∀ i, FreeGroup.lift f w ∈ Subgroup.centralizer (P i : Set G) := by
    intro i
    obtain ⟨g,hg,hgw⟩ := hlocal i
    have hact := sameActionOn_free_lift (P i) f g (hinv i)
      (fun j => normalizes_of_same_action (P i) _ _ (hinv i j) (hg j)) hg
    intro x hx
    have he := hact w x hx
    have he' : FreeGroup.lift g w*x*(FreeGroup.lift g w)⁻¹=x := by
      rw [← hgw x hx]; group
    rw [he'] at he
    have ht := congrArg (fun z => z*FreeGroup.lift f w) he
    exact (by simpa only [mul_assoc,inv_mul_cancel,mul_one] using ht :
      FreeGroup.lift f w*x=x*FreeGroup.lift f w).symm
  have hs : (⨆ i, P i) ≤ Subgroup.centralizer {FreeGroup.lift f w} := by
    apply iSup_le
    intro i x hx y hy
    obtain rfl : y=FreeGroup.lift f w := Set.mem_singleton_iff.mp hy
    exact (hc i x hx).symm
  intro x hx
  exact show FreeGroup.lift f w*x=x*FreeGroup.lift f w from hs (hgen hx) _ rfl

end InvariantPatching

end SimpleAmenable
end
end

end OAI
