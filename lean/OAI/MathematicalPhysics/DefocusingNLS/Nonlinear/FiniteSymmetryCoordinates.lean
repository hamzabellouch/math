import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FiniteSymmetryDecomposition
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! Product coordinates for the neutral, time, and translation eigenspaces. -/

namespace DefocusingNLS
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

abbrev SymmetryCoordinates (G : V →L[ℂ] V) :=
  Module.End.eigenspace G.toLinearMap 0 ×
    (Module.End.eigenspace G.toLinearMap 1 × Module.End.eigenspace G.toLinearMap (1/2))

def symmetryCoordinateSum (G : V →L[ℂ] V) : SymmetryCoordinates G →ₗ[ℂ] V where
  toFun u := u.1.val+u.2.1.val+u.2.2.val
  map_add' := by intros; simp only [Prod.fst_add,Prod.snd_add,Submodule.coe_add]; abel
  map_smul' := by intros; simp only [Prod.smul_fst,Prod.smul_snd,Submodule.coe_smul,smul_add,RingHom.id_apply]

theorem symmetry_eigenvectors_independent (G : V →L[ℂ] V) (x₀ x₁ xh : V)
    (h0 : G x₀=0) (h1 : G x₁=x₁) (hh : G xh=(1/2 : ℂ) • xh)
    (hsum : x₀+x₁+xh=0) : x₀=0 ∧ x₁=0 ∧ xh=0 := by
  have ha : x₁+(1/2 : ℂ) • xh=0 := by
    simpa only [map_add,h0,h1,hh,map_zero,zero_add] using congrArg G hsum
  have hb : x₁+(1/4 : ℂ) • xh=0 := by
    have he := congrArg G ha
    simpa only [map_add,map_smul,h1,hh,map_zero,smul_smul,
      show (1/2 : ℂ)*(1/2)=1/4 by norm_num] using he
  have hxh : xh=0 := by
    calc
      xh = (4 : ℂ) • ((x₁+(1/2 : ℂ) • xh)-(x₁+(1/4 : ℂ) • xh)) := by module
      _ = 0 := by rw [ha,hb,sub_self,smul_zero]
  have hx1 : x₁=0 := by simpa only [hxh,smul_zero,add_zero] using ha
  exact ⟨by simpa only [hx1,hxh,add_zero] using hsum,hx1,hxh⟩

theorem symmetryCoordinateSum_bijective (G : V →L[ℂ] V)
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam)=⊤)
    (hspec : ∀ (lam : ℂ) (w : V), w ≠ 0 → G w=lam • w → lam=0 ∨ lam=1 ∨ lam=1/2) :
    Function.Bijective (symmetryCoordinateSum G) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro u hu
    obtain ⟨h0,h1,hh⟩ := symmetry_eigenvectors_independent G u.1 u.2.1 u.2.2
      (by simpa only [zero_smul,ContinuousLinearMap.coe_coe] using Module.End.mem_eigenspace_iff.mp u.1.property)
      (by simpa only [one_smul,ContinuousLinearMap.coe_coe] using Module.End.mem_eigenspace_iff.mp u.2.1.property)
      (Module.End.mem_eigenspace_iff.mp u.2.2.property) hu
    exact Prod.ext (Subtype.ext h0) (Prod.ext (Subtype.ext h1) (Subtype.ext hh))
  · intro x
    obtain ⟨x₀,x₁,xh,hx,h0,h1,hh⟩ := symmetry_eigenvector_decomposition G.toLinearMap hspan hspec x
    refine ⟨(⟨x₀,?_⟩,(⟨x₁,?_⟩,⟨xh,?_⟩)),hx.symm⟩
    · exact Module.End.mem_eigenspace_iff.mpr (by simpa only [zero_smul] using h0)
    · exact Module.End.mem_eigenspace_iff.mpr (by simpa only [one_smul] using h1)
    · exact Module.End.mem_eigenspace_iff.mpr hh

noncomputable def symmetryCoordinateEquiv [FiniteDimensional ℂ V] (G : V →L[ℂ] V)
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam)=⊤)
    (hspec : ∀ (lam : ℂ) (w : V), w ≠ 0 → G w=lam • w → lam=0 ∨ lam=1 ∨ lam=1/2) :
    SymmetryCoordinates G ≃L[ℂ] V :=
  (LinearEquiv.ofBijective (symmetryCoordinateSum G)
    (symmetryCoordinateSum_bijective G hspan hspec)).toContinuousLinearEquiv

end DefocusingNLS

end OAI
