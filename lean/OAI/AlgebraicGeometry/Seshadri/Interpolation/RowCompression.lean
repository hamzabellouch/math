import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Interpolation.CompressionRanks

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
abbrev RowIndex {Q : Type*} (n : Q → ℕ) := (q : Q) × Fin (n q + 1)

theorem compression_column_mem_span {Q : Type*} [Fintype Q]
    (q : Q → ℤ) (B n : Q → ℕ) (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (s : ℂ) (hs : s ≠ 0) (i : RowIndex n) :
    finiteJetColumn r m points (fun u z => u ^ q i.1 *
      ((1 + s * z) ^ B i.1 * z ^ (i.2 : ℕ))) ∈
      Submodule.span ℂ (Set.range fun j : RowIndex n => finiteJetColumn r m points
        (fun u z => u ^ q j.1 * (1 + s * z) ^ (B j.1 + (j.2 : ℕ)))) := by
  let L := (polynomialJetMap r m points (q i.1)).comp (compressionRowMap s (B i.1))
  have hp := polynomial_image_mem_span L
    ((Polynomial.C s⁻¹ * (Polynomial.X - 1)) ^ (i.2 : ℕ)) (n i.1)
    ((compression_inverse_degree s i.2).trans (by omega))
  have hv : L ((Polynomial.C s⁻¹ * (Polynomial.X - 1)) ^ (i.2 : ℕ)) =
      finiteJetColumn r m points (fun u z => u ^ q i.1 *
        ((1 + s * z) ^ B i.1 * z ^ (i.2 : ℕ))) := by
    dsimp only [L, LinearMap.comp_apply]
    rw [compressionRowMap_inverse s hs, polynomialJetMap_eq]
    congr 1
    funext u z
    simp
  rw [hv] at hp
  apply (Submodule.span_mono ?_) hp
  rintro _ ⟨j, rfl⟩
  refine ⟨⟨i.1, j⟩, ?_⟩
  dsimp only [L, LinearMap.comp_apply]
  rw [compressionRowMap_pow, polynomialJetMap_eq]
  congr 1
  funext u z
  simp

theorem compression_rank_to_powers {Q : Type*} [Fintype Q]
    (q : Q → ℤ) (B n : Q → ℕ) (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (s : ℂ) (hs : s ≠ 0)
    (h : LinearIndependent ℂ (fun i : RowIndex n => finiteJetColumn r m points
      (fun u z => u ^ q i.1 * ((1 + s * z) ^ B i.1 * z ^ (i.2 : ℕ))))) :
    LinearIndependent ℂ (fun i : RowIndex n => finiteJetColumn r m points
      (fun u z => u ^ q i.1 * (1 + s * z) ^ (B i.1 + (i.2 : ℕ)))) := by
  apply linearIndependent_of_span_le _ _ h
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact compression_column_mem_span q B n r m points s hs i

theorem iteratedDeriv_affine_pow (s : ℂ) (b N : ℕ) :
    iteratedDeriv b (fun z : ℂ => (1 + s * z) ^ N) =
      fun z => s ^ b * iteratedDeriv b (fun z : ℂ => z ^ N) (1 + s * z) := by
  have hd : ContDiff ℂ (b : ℕ∞ω) (fun z : ℂ => (1 + z) ^ N) := by fun_prop
  rw [show (fun z : ℂ => (1 + s * z) ^ N) =
    (fun z : ℂ => (fun y : ℂ => (1 + y) ^ N) (s * z)) by rfl,
    iteratedDeriv_comp_const_mul hd s]
  funext z
  congr 1
  exact congrFun (iteratedDeriv_comp_const_add b (fun z : ℂ => z ^ N) 1) (s * z)

noncomputable def verticalJetScale (r m : ℕ) (s : ℂ) :
    (JetIndex r m → ℂ) →ₗ[ℂ] (JetIndex r m → ℂ) :=
  LinearMap.pi fun j => (s ^ (j.2.2 : ℕ)) • LinearMap.proj j

theorem verticalJetScale_column (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (s : ℂ) (q : ℤ) (N : ℕ) :
    verticalJetScale r m s
      (finiteJetColumn r m (fun i => ((points i).1, 1 + s * (points i).2))
        (fun u z => u ^ q * z ^ N)) =
      finiteJetColumn r m points (fun u z => u ^ q * (1 + s * z) ^ N) := by
  funext j
  simp only [verticalJetScale, LinearMap.pi_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, finiteJetColumn]
  split_ifs
  · simp only [mixed_deriv_separated, iteratedDeriv_affine_pow]
    ring
  · exact mul_zero _

theorem compression_powers_to_original {Q : Type*} [Fintype Q]
    (q : Q → ℤ) (B n : Q → ℕ) (r m : ℕ) (points : Fin r → ℂ × ℂ) (s : ℂ)
    (h : LinearIndependent ℂ (fun i : RowIndex n => finiteJetColumn r m points
      (fun u z => u ^ q i.1 * (1 + s * z) ^ (B i.1 + (i.2 : ℕ))))) :
    LinearIndependent ℂ (fun i : RowIndex n =>
      finiteJetColumn r m (fun i => ((points i).1, 1 + s * (points i).2))
        (fun u z => u ^ q i.1 * z ^ (B i.1 + (i.2 : ℕ)))) := by
  apply LinearIndependent.of_comp (verticalJetScale r m s)
  simpa only [Function.comp_def, verticalJetScale_column] using h

theorem affine_vertical_tuple_injective {r : ℕ} (points : Fin r → ℂ × ℂ)
    (hi : Function.Injective points) (s : ℂ) (hs : s ≠ 0) :
    Function.Injective (fun i => ((points i).1, 1 + s * (points i).2)) := by
  intro i j hij
  apply hi
  apply Prod.ext
  · simpa only using congrArg (fun p : ℂ × ℂ => p.1) hij
  · have h := congrArg Prod.snd hij
    exact (mul_left_cancel₀ hs) (add_left_cancel h)

theorem compression_exists_tuple {Q : Type*} [Fintype Q]
    (q : Q → ℤ) (B n : Q → ℕ) (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (hi : Function.Injective points) (hnz : ∀ i, (points i).1 ≠ 0)
    (h₀ : LinearIndependent ℂ (fun i : RowIndex n => finiteJetColumn r m points
      (fun u z => u ^ q i.1 * z ^ (i.2 : ℕ)))) :
    ∃ p : Fin r → ℂ × ℂ, Function.Injective p ∧
      (∀ i, (p i).1 ≠ 0 ∧ (p i).2 ≠ 0) ∧
      LinearIndependent ℂ (fun i : RowIndex n => finiteJetColumn r m p
        (fun u z => u ^ q i.1 * z ^ (B i.1 + (i.2 : ℕ)))) := by
  have hrank := compression_finite_rank (fun i : RowIndex n => q i.1)
    (fun i => B i.1) (fun i => (i.2 : ℕ)) r m points h₀
  have hn : ∀ᶠ s : ℂ in 𝓝 0, ∀ i, 1 + s * (points i).2 ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    have ht : Tendsto (fun s : ℂ => 1 + s * (points i).2) (𝓝 0) (𝓝 1) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℂ => (1 : ℂ)) (𝓝 0) (𝓝 1)).add
        ((tendsto_id : Tendsto (id : ℂ → ℂ) (𝓝 0) (𝓝 0)).mul_const (points i).2)
    exact ht.eventually_ne one_ne_zero
  have he : ∀ᶠ s : ℂ in 𝓝[≠] 0, s ≠ 0 := eventually_mem_nhdsWithin
  obtain ⟨s, hs, hrank, hn⟩ := (he.and
    ((hrank.and hn).filter_mono nhdsWithin_le_nhds)).exists
  refine ⟨(fun i => ((points i).1, 1 + s * (points i).2)),
    affine_vertical_tuple_injective points hi s hs, ?_, ?_⟩
  · intro i
    exact ⟨hnz i, hn i⟩
  · exact compression_powers_to_original q B n r m points s
      (compression_rank_to_powers q B n r m points s hs hrank)


end MaximalSeshadri.Interpolation
end

end OAI
