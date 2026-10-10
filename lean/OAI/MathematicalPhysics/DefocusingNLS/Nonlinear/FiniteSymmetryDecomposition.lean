import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FiniteGeneratorNoJordan

namespace OAI

/-! The three actual symmetry eigenvalues give a concrete decomposition. -/

namespace DefocusingNLS
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem symmetry_eigenspaces_sup_eq_top (G : Module.End ℂ V)
    (hspan : (⨆ lam : ℂ, G.eigenspace lam)=⊤)
    (hspec : ∀ (lam : ℂ) (w : V), w ≠ 0 → G w=lam • w → lam=0 ∨ lam=1 ∨ lam=1/2) :
    (G.eigenspace 0 ⊔ G.eigenspace 1) ⊔ G.eigenspace (1/2)=⊤ := by
  apply top_unique
  rw [← hspan]
  refine iSup_le fun lam x hx => ?_
  by_cases hz : x=0
  · subst x
    exact Submodule.zero_mem _
  rcases hspec lam x hz (Module.End.mem_eigenspace_iff.mp hx) with rfl | rfl | rfl
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left hx)
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right hx)
  · exact Submodule.mem_sup_right hx

theorem symmetry_eigenvector_decomposition (G : Module.End ℂ V)
    (hspan : (⨆ lam : ℂ, G.eigenspace lam)=⊤)
    (hspec : ∀ (lam : ℂ) (w : V), w ≠ 0 → G w=lam • w → lam=0 ∨ lam=1 ∨ lam=1/2)
    (x : V) : ∃ x₀ x₁ xh : V, x=x₀+x₁+xh ∧ G x₀=0 ∧ G x₁=x₁ ∧ G xh=(1/2 : ℂ) • xh := by
  have hx : x ∈ (G.eigenspace 0 ⊔ G.eigenspace 1) ⊔ G.eigenspace (1/2) := by
    rw [symmetry_eigenspaces_sup_eq_top G hspan hspec]
    trivial
  obtain ⟨y,hy,xh,hh,hxy⟩ := Submodule.mem_sup.mp hx
  obtain ⟨x₀,h0,x₁,h1,hyx⟩ := Submodule.mem_sup.mp hy
  refine ⟨x₀,x₁,xh,?_,?_,?_,Module.End.mem_eigenspace_iff.mp hh⟩
  · rw [← hxy,← hyx]
  · simpa only [zero_smul] using Module.End.mem_eigenspace_iff.mp h0
  · simpa only [one_smul] using Module.End.mem_eigenspace_iff.mp h1

theorem symmetry_polynomial_annihilates (G : Module.End ℂ V)
    (hspan : (⨆ lam : ℂ, G.eigenspace lam)=⊤)
    (hspec : ∀ (lam : ℂ) (w : V), w ≠ 0 → G w=lam • w → lam=0 ∨ lam=1 ∨ lam=1/2) :
    G * (G-(1/2 : ℂ) • 1) * (G-1)=0 := by
  ext x
  obtain ⟨x₀,x₁,xh,rfl,h0,h1,hh⟩ := symmetry_eigenvector_decomposition G hspan hspec x
  simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.one_apply,map_add,map_sub,map_smul,h0,h1,hh,map_zero,LinearMap.zero_apply,smul_zero,sub_self,add_zero]

end DefocusingNLS

end OAI
