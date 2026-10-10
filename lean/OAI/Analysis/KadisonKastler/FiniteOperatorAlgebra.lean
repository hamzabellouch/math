import OAI.Analysis.KadisonKastler.DiffuseInfiniteDimensional
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Logic.Equiv.Set

namespace OAI

/-! # Finiteness of all operators forces finite Hilbert dimension

An infinite Hilbert basis admits a proper shift. The associated orthogonal
sum is an isometry whose range misses one basis vector.
-/

namespace KadisonKastler

noncomputable section

private theorem exists_injective_avoiding (ι : Type*) [Infinite ι] :
    ∃ (j : ι → ι) (i₀ : ι), Function.Injective j ∧ ∀ i, j i ≠ i₀ := by
  classical
  let e := Infinite.natEmbedding ι
  let d : (ℕ ⊕ ↥((Set.range e)ᶜ)) ≃ ι :=
    (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range e))
  let f : ℕ ⊕ ↥((Set.range e)ᶜ) → ℕ ⊕ ↥((Set.range e)ᶜ) := Sum.map Nat.succ id
  have hf : Function.Injective f := Sum.map_injective.mpr ⟨Nat.succ_injective, Function.injective_id⟩
  refine ⟨fun i => d (f (d.symm i)), d (Sum.inl 0),
    d.injective.comp (hf.comp d.symm.injective), ?_⟩
  intro i hi
  have hh := d.injective hi
  rcases h : d.symm i with n | x <;> simp [f, h] at hh

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finiteDimensional_of_all_isometries_coisometric
    (hfinite : ∀ v : H →L[ℂ] H, star v * v = 1 → v * star v = 1) :
    FiniteDimensional ℂ H := by
  classical
  obtain ⟨I, b, _⟩ := exists_hilbertBasis ℂ H
  by_cases hI : Finite I
  · let := hI
    let := Fintype.ofFinite I
    exact b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  have : Infinite I := not_finite_iff_infinite.mp hI
  obtain ⟨j, i₀, hj, hmiss⟩ := exists_injective_avoiding I
  have ho := b.orthonormal.comp j hj
  let V : H →ₗᵢ[ℂ] H := ho.orthogonalFamily.linearIsometry.comp b.repr.toLinearIsometry
  let v : H →L[ℂ] H := V.toContinuousLinearMap
  have hv : star v * v = 1 := V.adjoint_comp_self
  have hv' := hfinite v hv
  have horth (x : H) : inner ℂ (b i₀) (v x) = 0 := by
    have hsum := (ho.orthogonalFamily.hasSum_linearIsometry (b.repr x)).mapL
      (innerSL ℂ (b i₀))
    have hz (i : I) : inner ℂ (b i₀)
        (LinearIsometry.toSpanSingleton ℂ H (ho.1 i) (b.repr x i)) = 0 := by
      rw [LinearIsometry.toSpanSingleton_apply, inner_smul_right]
      change (b.repr x i) * inner ℂ (b i₀) (b (j i)) = 0
      rw [b.orthonormal.inner_eq_zero (Ne.symm (hmiss i)), mul_zero]
    have he : (fun i : I => innerSL ℂ (b i₀)
        (LinearIsometry.toSpanSingleton ℂ H (ho.1 i) (b.repr x i))) = fun _ => 0 := by
      funext i
      exact hz i
    rw [he] at hsum
    exact hsum.unique hasSum_zero
  have hx : v (star v (b i₀)) = b i₀ :=
    congrArg (fun T : H →L[ℂ] H => T (b i₀)) hv'
  have hzero := horth (star v (b i₀))
  have hone : inner ℂ (b i₀) (b i₀) = 1 := by
    simpa using (orthonormal_iff_ite.mp b.orthonormal i₀ i₀)
  rw [hx, hone] at hzero
  exact False.elim (one_ne_zero hzero)

end

end KadisonKastler

end OAI
