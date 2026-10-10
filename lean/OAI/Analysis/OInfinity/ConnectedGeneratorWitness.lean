import OAI.Analysis.OInfinity.TailCancellationWitness
import OAI.Analysis.OInfinity.CentralBufferImage

namespace OAI

/-! # Connected finite conjugacy of the two actual O∞ images

The first buffer is constructed from the two commuting images. The entire
tail cancellation takes place in its closed commutant and the second norm
ultrapower. Two connected-unitary descents give the original finite witness.
-/

noncomputable section
open Filter Topology
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

private lemma generatorWitness_quotient_nontrivial [Nontrivial E] (U : Ultrafilter ℕ) :
    Nontrivial (NormUltra.QuotientAlgebra (fun _ : ℕ => E) U) := by
  have hnorm : ‖(1 : NormUltra.QuotientAlgebra (fun _ : ℕ => E) U)‖ = 1 := by
    change ‖NormUltra.QuotientAlgebra.mk U (DirectComparison.boundedDiagonal (1 : E))‖ = 1
    rw [NormUltra.QuotientAlgebra.norm_mk_eq_limsup]
    change limsup (fun _ : ℕ => ‖(1 : E)‖) (U : Filter ℕ) = 1
    rw [norm_one, Filter.limsup_const]
  exact nontrivial_of_ne 0 1 (by
    intro he
    rw [← he, norm_zero] at hnorm
    exact zero_ne_one hnorm)

local instance generatorWitnessCentralizerClosed (R : ℕ → E) :
    IsClosed (StarSubalgebra.centralizer ℂ (Set.range R) : Set E) :=
  Set.isClosed_centralizer _

/-- All buffers, complement matching, and connected coordinate lifts are
constructed from the two given commuting unital images. -/
theorem oInfinity_connected_generator_conjugacy [Nontrivial E]
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]
    (f g : OInfinity →⋆ₐ[ℂ] E) (hfg : ∀ x y, Commute (f x) (g y))
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : unitary E, Joined 1 v ∧
      ∀ i < n, ‖(v : E) * f (oInfinityIsometry i) * star (v : E) -
        g (oInfinityIsometry i)‖ < ε := by
  classical
  let Q := NormUltra.QuotientAlgebra (fun _ : ℕ => E) U
  let : Nontrivial Q := generatorWitness_quotient_nontrivial U
  let d := NormUltra.QuotientAlgebra.diagonalHom (A := E) U
  obtain ⟨R, hR, hf, hg⟩ := exists_normUltrapower_factor_buffer U f g hfg
  let C := StarSubalgebra.centralizer ℂ (Set.range R)
  let fC : OInfinity →⋆ₐ[ℂ] C := (d.comp f).codRestrict C hf
  let gC : OInfinity →⋆ₐ[ℂ] C := (d.comp g).codRestrict C hg
  let s : ℕ → C := fun i => fC (oInfinityIsometry i)
  let t : ℕ → C := fun i => gC (oInfinityIsometry i)
  have hs (i j : ℕ) : star (s i) * s j = if i = j then 1 else 0 := by
    change star (fC (oInfinityIsometry i)) * fC (oInfinityIsometry j) = _
    rw [← map_star, ← map_mul, oInfinityIsometry_relations]
    split_ifs <;> simp only [map_one, map_zero]
  have ht (i j : ℕ) : star (t i) * t j = if i = j then 1 else 0 := by
    change star (gC (oInfinityIsometry i)) * gC (oInfinityIsometry j) = _
    rw [← map_star, ← map_mul, oInfinityIsometry_relations]
    split_ifs <;> simp only [map_one, map_zero]
  have hC (a b : OInfinity) : Commute (fC a) (gC b) := by
    apply Subtype.ext
    change d (f a) * d (g b) = d (g b) * d (f a)
    simpa only [map_mul] using congrArg d (hfg a b).eq
  have hst : bergRowsCommute s t := by
    intro i j
    refine ⟨hC _ _, ?_⟩
    change Commute (fC (oInfinityIsometry i)) (star (gC (oInfinityIsometry j)))
    simpa only [map_star] using hC (oInfinityIsometry i) (star (oInfinityIsometry j))
  obtain ⟨v₂, hv₂, hv₂i⟩ :=
    exists_buffered_commuting_rows_conjugacy U R hR s t hs ht hst n ε hε
  let P₁ : Finset (Q × Q) := Finset.univ.image
    (fun i : Fin (n + 1) => ((s i : Q), (t i : Q)))
  have hP₁ : ∀ p ∈ P₁,
      ‖(v₂ : NormUltra.QuotientAlgebra (fun _ : ℕ => Q) U) *
        NormUltra.QuotientAlgebra.diagonalHom U p.1 * star (v₂ :
          NormUltra.QuotientAlgebra (fun _ : ℕ => Q) U) -
        NormUltra.QuotientAlgebra.diagonalHom U p.2‖ < ε := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hv₂i i
  obtain ⟨v₁, hv₁, hv₁i⟩ := connected_finite_conjugacy_of_ultrapower U P₁ v₂ hv₂ hP₁
  let P₀ : Finset (E × E) := Finset.univ.image
    (fun i : Fin (n + 1) => (f (oInfinityIsometry i), g (oInfinityIsometry i)))
  have hP₀ : ∀ p ∈ P₀,
      ‖(v₁ : Q) * d p.1 * star (v₁ : Q) - d p.2‖ < ε := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    have hi := hv₁i ((s i : Q), (t i : Q))
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    exact hi
  obtain ⟨v, hv, hvi⟩ := connected_finite_conjugacy_of_ultrapower U P₀ v₁ hv₁ hP₀
  refine ⟨v, hv, fun i hi => ?_⟩
  exact hvi (f (oInfinityIsometry i), g (oInfinityIsometry i))
    (Finset.mem_image.mpr ⟨⟨i, by omega⟩, Finset.mem_univ _, rfl⟩)

end WeakPureInfiniteness

end

end OAI
