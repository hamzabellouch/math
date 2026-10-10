import OAI.Analysis.MarkovType.C00FiniteCoordinates
import Mathlib.Data.Finset.Union
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

theorem finite_coordinate_factorization
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (S : E →ₗ[ℝ] C00) :
    ∃ m : ℕ, ∃ R : E →ₗ[ℝ] (Fin m → ℝ),
      ∀ z : E, C00.ofArray (R z) = S z := by
  classical
  let b := Module.finBasis ℝ E
  let t : Finset ℕ := Finset.univ.biUnion (fun i => (S (b i)).support)
  let m := (t.sup id).succ
  have hbzero (i : Fin (Module.finrank ℝ E)) (n : ℕ) (hn : m ≤ n) :
      S (b i) n = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    have hnt : n ∈ t :=
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hmem⟩
    have hlt : n < m :=
      Finset.mem_range.mp (Finset.subset_range_sup_succ t hnt)
    exact (Nat.not_lt_of_ge hn) hlt
  have hzero (z : E) (n : ℕ) (hn : m ≤ n) : S z n = 0 := by
    have hmap : (Finsupp.lapply n : C00 →ₗ[ℝ] ℝ).comp S = 0 := by
      apply b.ext
      intro i
      change S (b i) n = 0
      exact hbzero i n hn
    have hz := congrArg (fun L : E →ₗ[ℝ] ℝ => L z) hmap
    exact hz
  let R : E →ₗ[ℝ] (Fin m → ℝ) :=
    LinearMap.pi (fun i : Fin m => (Finsupp.lapply i.val : C00 →ₗ[ℝ] ℝ).comp S)
  refine ⟨m, R, ?_⟩
  intro z
  change C00.ofArray (fun i : Fin m => S z i.val) = S z
  exact C00.ofArray_of_vanishes (S z) m (hzero z)

end MarkovSuperreflexivity

end

end OAI
