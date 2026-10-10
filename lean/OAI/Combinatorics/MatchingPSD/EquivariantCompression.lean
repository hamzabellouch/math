import OAI.Combinatorics.MatchingPSD.SpectralContraction

namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
namespace Pairing
variable {V : Type u_1}

lemma act_pointwise_mul (p : Equiv.Perm V) (f g : Pairing V → ℝ) :
    act p (f * g) = act p f * act p g := rfl

lemma act_pointwise_one (p : Equiv.Perm V) : act p (1 : Pairing V → ℝ) = 1 := rfl

lemma act_edgeCoord (p : Equiv.Perm V) (e : V × V) :
    act p (edgeCoord e) = edgeCoord (p e.1, p e.2) := by
  classical
  ext M
  simp only [act_apply, edgeCoord, relabel_apply, inv_inv]
  congr 1
  exact propext p.symm_apply_eq

lemma lowDegree_invariant (p : Equiv.Perm V) (d : ℕ)
    (f : Pairing V → ℝ) (hf : f ∈ lowDegree edgeCoord d) :
    act p f ∈ lowDegree edgeCoord d := by
  apply Submodule.span_induction (p := fun f _ => act p f ∈ lowDegree edgeCoord d)
    _ _ _ _ hf
  · rintro f ⟨l, hl, rfl⟩
    have hprod : act p ((l.map edgeCoord).prod) =
        ((l.map (fun e => (p e.1, p e.2))).map edgeCoord).prod := by
      clear hl
      induction l with
      | nil => exact act_pointwise_one p
      | cons e l ih =>
        simp only [List.map_cons, List.prod_cons, act_pointwise_mul,
          act_edgeCoord, ih]
    rw [hprod]
    exact Submodule.subset_span ⟨_, by simpa, rfl⟩
  · simp
  · intro f g _ _ hf hg
    simpa only [map_add] using (lowDegree edgeCoord d).add_mem hf hg
  · intro c f _ hf
    simpa only [map_smul] using (lowDegree edgeCoord d).smul_mem c hf

end Pairing

open scoped RealInnerProductSpace
section EuclideanPermutations
variable {X : Type u_2} [Fintype X]

noncomputable def permIso (e : Equiv.Perm X) :
    EuclideanSpace ℝ X ≃ₗᵢ[ℝ] EuclideanSpace ℝ X :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

@[simp] lemma permIso_apply (e : Equiv.Perm X) (v : EuclideanSpace ℝ X) (x : X) :
    permIso e v x = v (e.symm x) := rfl

lemma matrix_equivariant [DecidableEq X] (A : Matrix X X ℝ) (e : Equiv.Perm X)
    (hA : ∀ x y, A (e x) (e y) = A x y) (v : EuclideanSpace ℝ X) :
    A.toEuclideanLin (permIso e v) = permIso e (A.toEuclideanLin v) := by
  ext x
  change (∑ y, A x y * v (e.symm y)) = ∑ y, A (e.symm x) y * v y
  rw [← Equiv.sum_comp e (fun y => A x y * v (e.symm y))]
  apply Finset.sum_congr rfl
  intro y _
  rw [e.symm_apply_apply, ← hA (e.symm x) y, e.apply_symm_apply]

lemma matrix_trace_square [DecidableEq X] (A : Matrix X X ℝ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ X) (A.toEuclideanLin * A.toEuclideanLin) =
      Matrix.trace (A * A) := by
  simp only [Matrix.toLpLin_eq_toLin, Module.End.mul_eq_comp,
    ← Matrix.toLin_mul, Matrix.trace_toLin_eq]

end EuclideanPermutations

section CompressionEquivariance
variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma invariant_map_eq (W : Submodule ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (h : ∀ x, x ∈ W → e x ∈ W) (hi : ∀ x, x ∈ W → e.symm x ∈ W) :
    W.map e.toLinearEquiv.toLinearMap = W := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · intro x hx
    exact ⟨e.symm x, hi x hx, e.apply_symm_apply x⟩

omit [FiniteDimensional ℝ E] in
lemma invariant_orthogonal (W : Submodule ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (hi : ∀ x, x ∈ W → e.symm x ∈ W) (x : E) (hx : x ∈ Wᗮ) :
    e x ∈ Wᗮ := by
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro y hy
  rw [← e.apply_symm_apply y, e.inner_map_map]
  exact hx (e.symm y) (hi y hy)

lemma starProjection_equivariant (W : Submodule ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (h : ∀ x, x ∈ W → e x ∈ W) (hi : ∀ x, x ∈ W → e.symm x ∈ W)
    (x : E) : e (W.starProjection x) = W.starProjection (e x) := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact h _ (W.orthogonalProjectionOnto x).property
  · intro y hy
    rw [← e.apply_symm_apply y, ← e.map_sub, e.inner_map_map]
    exact W.starProjection_inner_eq_zero x (e.symm y) (hi y hy)

lemma compression_eigenspace_invariant (A : Module.End ℝ E) (W : Submodule ℝ E)
    (e : E ≃ₗᵢ[ℝ] E) (h : ∀ x, x ∈ W → e x ∈ W)
    (hi : ∀ x, x ∈ W → e.symm x ∈ W)
    (hA : ∀ x, A (e x) = e (A x)) (c : ℝ) (x : E)
    (hx : x ∈ (Module.End.eigenspace (compression A W) c).map W.subtype) :
    e x ∈ (Module.End.eigenspace (compression A W) c).map W.subtype := by
  rcases hx with ⟨x, hx, rfl⟩
  refine ⟨⟨e x, h x x.2⟩, ?_, rfl⟩
  simp only [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hx ⊢
  apply Subtype.ext
  have he := congrArg (fun y : W => (y : E)) hx
  change W.starProjection (A x) = c • (x : E) at he
  change W.starProjection (A (e (x : E))) = c • e (x : E)
  rw [hA, ← starProjection_equivariant W e h hi, he, map_smul]

end CompressionEquivariance
end MatchingSmoothing

end OAI
