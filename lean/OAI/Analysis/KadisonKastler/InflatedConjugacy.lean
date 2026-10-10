import OAI.Analysis.KadisonKastler.InfiniteCornerInflation
import OAI.Analysis.FactorGeneration.OperatorLimits

namespace OAI

/-! # Recovering the full algebra from its common matrix corners -/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem extension_matrixEntry (T : H →L[ℂ] H) (i j : ℕ) :
    cornerExtension E (F.matrixEntry T i j) = F.entry 0 i * T * F.entry j 0 := by
  have he : F.matrixEntry T i j =
      cornerCompression E (F.entry 0 i * T * F.entry j 0) := by
    apply ContinuousLinearMap.ext
    intro x
    exact F.matrixEntry_apply T i j x
  rw [he, cornerExtension_compression, ← F.zero_zero]
  calc
    F.entry 0 0 * (F.entry 0 i * T * F.entry j 0) * F.entry 0 0 =
        (F.entry 0 0 * F.entry 0 i) * T * (F.entry j 0 * F.entry 0 0) := by
      noncomm_ring
    _ = _ := by rw [F.mul_entry, F.mul_entry]; simp

def partialDiagonal (s : Finset ℕ) : H →L[ℂ] H := ∑ i ∈ s, F.entry i i

theorem partialDiagonal_star (s : Finset ℕ) :
    star (F.partialDiagonal s) = F.partialDiagonal s := by
  simp only [partialDiagonal, star_sum, F.star_entry]

theorem partialDiagonal_tendsto (x : H) :
    Tendsto (fun s : Finset ℕ => F.partialDiagonal s x) atTop (𝓝 x) := by
  simpa only [HasSum, SummationFilter.unconditional, partialDiagonal, sum_apply] using
    F.total x

/-- Membership of every transported matrix entry determines membership of
the whole operator. The proof uses actual finite compressions and WOT closure. -/
theorem mem_of_matrixEntries (N : VonNeumannAlgebra H)
    (hF : ∀ i j, F.entry i j ∈ N) (T : H →L[ℂ] H)
    (hT : ∀ i j, cornerExtension E (F.matrixEntry T i j) ∈ N) : T ∈ N := by
  have hterm (i j : ℕ) : F.entry i i * T * F.entry j j ∈ N := by
    have h := N.mul_mem (N.mul_mem (hF i 0) (hT i j)) (hF 0 j)
    rw [F.extension_matrixEntry] at h
    have he : F.entry i 0 * (F.entry 0 i * T * F.entry j 0) * F.entry 0 j =
        F.entry i i * T * F.entry j j := by
      calc
        _ = (F.entry i 0 * F.entry 0 i) * T * (F.entry j 0 * F.entry 0 j) := by
          noncomm_ring
        _ = _ := by rw [F.mul_entry, F.mul_entry]; simp
    rwa [he] at h
  have hmem (s : Finset ℕ) : F.partialDiagonal s * T * F.partialDiagonal s ∈ N := by
    simp only [partialDiagonal, Finset.sum_mul, Finset.mul_sum]
    exact N.sum_mem (fun i _ => N.sum_mem (fun j _ => hterm j i))
  let a (s : Finset ℕ) : Algebra N :=
    ⟨F.partialDiagonal s * T * F.partialDiagonal s, hmem s⟩
  apply Generator.Tracial.weak_operator_limit_mem (l := atTop) N a T
  intro x y
  have ht := (F.partialDiagonal_tendsto y).inner (𝕜 := ℂ)
    (T.continuous.continuousAt.tendsto.comp (F.partialDiagonal_tendsto x))
  have he (s : Finset ℕ) :
      inner ℂ (F.partialDiagonal s y) (T (F.partialDiagonal s x)) =
        inner ℂ y ((F.partialDiagonal s * T * F.partialDiagonal s) x) := by
    rw [mul_apply_eq_comp, mul_apply_eq_comp]
    rw [← ContinuousLinearMap.adjoint_inner_left (F.partialDiagonal s)
      (T (F.partialDiagonal s x)) y]
    simp only [← ContinuousLinearMap.star_eq_adjoint, F.partialDiagonal_star]
  exact ht.congr he

/-- A conjugacy of the common initial corners inflates to a conjugacy of
the original algebras, retaining the corner displacement bound. -/
theorem conjugates_inflateUnitary (M N : VonNeumannAlgebra H)
    (hM : ∀ i j, F.entry i j ∈ M) (hN : ∀ i j, F.entry i j ∈ N)
    (v : unitary (E →L[ℂ] E))
    (hv : Conjugates v
      (representedCorner E M (F.zero_zero ▸ hM 0 0))
      (representedCorner E N (F.zero_zero ▸ hN 0 0))) :
    Conjugates (F.inflateUnitary v) M N := by
  have hdir (P Q : VonNeumannAlgebra H)
      (hP : ∀ i j, F.entry i j ∈ P) (hQ : ∀ i j, F.entry i j ∈ Q)
      (w : unitary (E →L[ℂ] E))
      (hw : Conjugates w
        (representedCorner E P (F.zero_zero ▸ hP 0 0))
        (representedCorner E Q (F.zero_zero ▸ hQ 0 0)))
      (T : H →L[ℂ] H) (hT : T ∈ P) :
      unitaryConj (F.inflateUnitary w) T ∈ Q := by
    apply F.mem_of_matrixEntries Q hQ
    intro i j
    rw [F.matrixEntry_unitaryConj]
    have he : F.matrixEntry T i j ∈ representedCorner E P (F.zero_zero ▸ hP 0 0) := by
      rw [mem_representedCorner, F.extension_matrixEntry]
      exact P.mul_mem (P.mul_mem (hP 0 i) hT) (hP j 0)
    have hq : unitaryConj w (F.matrixEntry T i j) ∈
        representedCorner E Q (F.zero_zero ▸ hQ 0 0) := by
      change unitaryConj w (F.matrixEntry T i j) ∈
        (representedCorner E Q (F.zero_zero ▸ hQ 0 0) : Set (E →L[ℂ] E))
      rw [← hw]
      exact ⟨F.matrixEntry T i j, he, rfl⟩
    exact hq
  apply Set.Subset.antisymm
  · rintro _ ⟨T, hT, rfl⟩
    exact hdir M N hM hN v hv T hT
  · intro T hT
    have hs : F.inflateUnitary (star v) = star (F.inflateUnitary v) := by
      apply Subtype.ext
      exact map_star F.inflateHom (v : E →L[ℂ] E)
    refine ⟨unitaryConj (star (F.inflateUnitary v)) T, ?_, ?_⟩
    · change unitaryConj (star (F.inflateUnitary v)) T ∈ M
      simpa only [hs] using hdir N M hN hM (star v) hv.symm T hT
    · simpa only [star_star] using unitaryConj_star_unitaryConj
        (star (F.inflateUnitary v)) T

end FullMatrixCorner

end

end KadisonKastler

end OAI
