import Mathlib
import OAI.RepresentationTheory.PartialPermutation.SpechtModules
import OAI.RepresentationTheory.PartialPermutation.CrossTableaux

namespace OAI

section
namespace PartialPermutation.YoungTabloid
noncomputable section
open Finset
open scoped Classical

lemma polytabloid_specht_sign (μ : YoungDiagram) (c : columnGroup μ) :
    spechtRep μ c.1 ⟨polytabloid μ,polytabloid_mem_specht μ⟩ =
      signC c.1 • (⟨polytabloid μ,polytabloid_mem_specht μ⟩ : (spechtSub μ).toSubmodule) := by
  apply Subtype.ext
  apply PiLp.ext
  intro r
  change polytabloid μ (relabel μ c.1⁻¹ r)=signC c.1 * polytabloid μ r
  simpa using polytabloid_alternating μ c⁻¹ r

lemma cross_transversal_of_specht_map (μ ν : YoungDiagram) (e : μ.cells ≃ ν.cells)
    (L : (spechtSub μ).toSubmodule →ₗ[ℂ] (spechtSub ν).toSubmodule)
    (hL : Function.Injective L)
    (hcomm : ∀ g x, L (spechtRep μ g x)=spechtRep ν (e.permCongrHom g) (L x)) :
    ∃ r : Tabloid ν, CrossTransversal μ (fun x => r.1 (e x)) := by
  let v : (spechtSub μ).toSubmodule := ⟨polytabloid μ,polytabloid_mem_specht μ⟩
  have hv : v≠0 := fun h => polytabloid_ne_zero μ (congrArg Subtype.val h)
  have hf : (L v).val ≠ 0 := by
    intro h
    exact hv (hL (by simpa using (show L v=0 from Subtype.ext h)))
  obtain ⟨r,hr⟩ : ∃ r : Tabloid ν, (L v).val r≠0 := by
    by_contra hh
    push Not at hh
    exact hf (PiLp.ext hh)
  refine ⟨r,?_⟩
  intro x y hc he
  by_contra hxy
  let c : columnGroup μ := ⟨Equiv.swap x y,swap_mem_column μ x y hc⟩
  have hsg : signC c.1 = -1 := signC_swap x y hxy
  have hswap : e.permCongrHom c.1=Equiv.swap (e x) (e y) := by
    apply Equiv.ext
    intro z
    change e (Equiv.swap x y (e.symm z))=Equiv.swap (e x) (e y) z
    by_cases hx : e.symm z=x
    · have hz : z=e x := by simpa using congrArg e hx
      simp [hz]
    by_cases hy : e.symm z=y
    · have hz : z=e y := by simpa using congrArg e hy
      simp [hz]
    have hx' : z≠e x := by intro h; exact hx (by simp [h])
    have hy' : z≠e y := by intro h; exact hy (by simp [h])
    simp [Equiv.swap_apply_of_ne_of_ne hx hy,Equiv.swap_apply_of_ne_of_ne hx' hy']
  have h := hcomm c.1 v
  rw [polytabloid_specht_sign,map_smul,hsg,hswap] at h
  have hh := congrArg (fun w : (spechtSub ν).toSubmodule => w.val r) h
  change (-1 : ℂ) * (L v).val r = (L v).val (relabel ν (Equiv.swap (e x) (e y))⁻¹ r) at hh
  rw [Equiv.swap_inv,relabel_swap_fix ν r (e x) (e y) he] at hh
  apply hr
  linear_combination -hh / 2

lemma specht_map_rowMoment_le (μ ν : YoungDiagram) (e : μ.cells ≃ ν.cells)
    (L : (spechtSub μ).toSubmodule →ₗ[ℂ] (spechtSub ν).toSubmodule)
    (hL : Function.Injective L)
    (hcomm : ∀ g x, L (spechtRep μ g x)=spechtRep ν (e.permCongrHom g) (L x)) :
    rowMoment μ ≤ rowMoment ν := by
  obtain ⟨r,hr⟩ := cross_transversal_of_specht_map μ ν e L hL hcomm
  exact cross_rowMoment_le μ ν e r hr

theorem specht_equiv_shape_eq (μ ν : YoungDiagram) (e : μ.cells ≃ ν.cells)
    (L : (spechtSub μ).toSubmodule ≃ₗ[ℂ] (spechtSub ν).toSubmodule)
    (hcomm : ∀ g x, L (spechtRep μ g x)=spechtRep ν (e.permCongrHom g) (L x)) : μ=ν := by
  have hrev : ∀ g x, L.symm (spechtRep ν g x)=spechtRep μ (e.symm.permCongrHom g) (L.symm x) := by
    intro g x
    apply L.injective
    have he : e.permCongrHom (e.symm.permCongrHom g)=g := e.permCongrHom.apply_symm_apply g
    simpa only [he,L.apply_symm_apply] using (hcomm (e.symm.permCongrHom g) (L.symm x)).symm
  have hm := le_antisymm (specht_map_rowMoment_le μ ν e L.toLinearMap L.injective hcomm)
    (specht_map_rowMoment_le ν μ e.symm L.symm.toLinearMap L.symm.injective hrev)
  obtain ⟨r,hr⟩ := cross_transversal_of_specht_map μ ν e L.toLinearMap L.injective hcomm
  exact cross_equal_moment_shape_eq μ ν e r hr hm

end
end PartialPermutation.YoungTabloid

end

end OAI
