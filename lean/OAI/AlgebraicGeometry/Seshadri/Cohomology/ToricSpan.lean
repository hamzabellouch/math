import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.ToricPresentation

namespace OAI


                                   
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

def monomialSpan {ι : Type*} (S : Set (ℤ × ℤ)) (g : ι → M) : Submodule K M :=
  Submodule.span K {v | ∃ i z, z ∈ S ∧ v = T (K := K) z • g i}

lemma shift_span_mem {ι : Type*} (S U : Set (ℤ × ℤ)) (g : ι → M)
    (z : ℤ × ℤ) (hz : ∀ w ∈ S, z+w ∈ U) (x : M) (hx : x ∈ monomialSpan (K := K) S g) :
    T (K := K) z • x ∈ monomialSpan (K := K) U g := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,w,hw,rfl⟩ := hx
    rw [← mul_smul,← T_add]
    exact Submodule.subset_span ⟨i,z+w,hz w hw,rfl⟩
  | zero => simp
  | add x y hx hy ih ih' => simpa only [smul_add] using (monomialSpan (K := K) U g).add_mem ih ih'
  | smul a x hx ih =>
    rw [smul_comm]
    exact (monomialSpan (K := K) U g).smul_mem a ih

omit [IsScalarTower K (LaurentPlane.Ring K) M] in
lemma monomialSpan_le {ι : Type*} (S : Set (ℤ × ℤ)) (g : ι → M)
    (V : Submodule K M) (hg : ∀ i, g i ∈ V)
    (h : ∀ z ∈ S, ∀ x ∈ V, T (K := K) z • x ∈ V) : monomialSpan (K := K) S g ≤ V := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,z,hz,rfl⟩
  exact h z hz _ (hg i)

omit [IsScalarTower K (LaurentPlane.Ring K) M] in
lemma generator_mem_span {ι : Type*} (S : Set (ℤ × ℤ)) (hS : (0 : ℤ × ℤ) ∈ S)
    (g : ι → M) (i : ι) : g i ∈ monomialSpan (K := K) S g := by
  exact Submodule.subset_span ⟨i,0,hS,by simp⟩

theorem finite_monomial_generators {σ N : Type*} [AddCommGroup N] [Module K N]
    [Module (MvPolynomial σ K) N] [IsScalarTower K (MvPolynomial σ K) N]
    [Module.Finite (MvPolynomial σ K) N]
    (i : Fin 3) (v : σ → Fin 3) (F : N →ₗ[K] M)
    (stable : ∀ z ∈ vertexCone i, ∀ x ∈ F.range, T (K := K) z • x ∈ F.range)
    (hvars : ∀ j n, F ((MvPolynomial.X j : MvPolynomial σ K) • n) = T (K := K) (weight (v j)-weight i) • F n) :
    ∃ d : ℕ, ∃ g : Fin d → M, (∀ a, g a ∈ F.range) ∧
      F.range = monomialSpan (K := K) (vertexCone i) g := by
  obtain ⟨d,g,hg⟩ := Module.Finite.exists_fin (R := MvPolynomial σ K) (M := N)
  let W := monomialSpan (K := K) (vertexCone i) (fun a => F (g a))
  have hzero : (0 : ℤ × ℤ) ∈ vertexCone i := by simpa using direction_mem i i 0
  have hstable : ∀ j x, x ∈ W → T (K := K) (weight (v j)-weight i) • x ∈ W := by
    intro j x hx
    apply shift_span_mem _ _ _ _ _ x hx
    intro w hw
    exact vertexCone_add i (by simpa using direction_mem i (v j) 1) hw
  have hpoly (p : MvPolynomial σ K) (n : N) (hn : F n ∈ W) : F (p • n) ∈ W := by
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq,IsScalarTower.algebraMap_smul,map_smul]
      exact W.smul_mem a hn
    | add p q hp hq => simpa only [add_smul,map_add] using W.add_mem hp hq
    | mul_X p j hp =>
      rw [mul_comm,mul_smul,hvars]
      exact hstable j _ hp
  refine ⟨d,fun a => F (g a),fun a => ⟨g a,rfl⟩,le_antisymm ?_ ?_⟩
  · rintro _ ⟨n,rfl⟩
    have hn : n ∈ Submodule.span (MvPolynomial σ K) (Set.range g) := hg ▸ Submodule.mem_top
    induction hn using Submodule.span_induction with
    | mem n hn =>
      obtain ⟨a,rfl⟩ := hn
      exact generator_mem_span _ hzero _ a
    | zero => simp
    | add n m hn hm ih ih' => simpa only [map_add] using W.add_mem ih ih'
    | smul p n hn ih => exact hpoly p n ih
  · exact monomialSpan_le _ _ F.range (fun a => ⟨g a,rfl⟩) stable

theorem localized_span {ι : Type*} (S U : Set (ℤ × ℤ)) (g : ι → M)
    (A : Submodule K M) (hg : ∀ a, g a ∈ A)
    (stable : ∀ z ∈ U, ∀ x ∈ A, T (K := K) z • x ∈ A)
    (clear : ∀ x ∈ A, ∃ z : ℤ × ℤ,
      T (K := K) z • x ∈ monomialSpan (K := K) S g ∧ ∀ w ∈ S, -z+w ∈ U) :
    A = monomialSpan (K := K) U g := by
  apply le_antisymm
  · intro x hx
    obtain ⟨z,hz,hshift⟩ := clear x hx
    have hm := shift_span_mem S U g (-z) hshift _ hz
    rw [← mul_smul,← T_add,neg_add_cancel,T_zero,one_smul] at hm
    exact hm
  · exact monomialSpan_le U g A hg stable

end
end MaximalSeshadri.PlaneCech

end


end OAI
