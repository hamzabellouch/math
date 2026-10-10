import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Selection.GreedyPivots
import OAI.NumberTheory.SiegelZeros.Structure.EvalOneInvariantJetMonomial

namespace OAI

namespace SiegelZeros

section
open Module Submodule

namespace WeightedTorusJets.Geometry

theorem finrank_span_algebraMap_image {K L n : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype n] (s : Set (n → K)) :
    finrank L (span L ((fun v : n → K => algebraMap K L ∘ v) '' s)) =
      finrank K (span K s) := by
  obtain ⟨b, _, hbspan, hbind⟩ := Submodule.exists_fun_fin_finrank_span_eq K s
  have hbL : LinearIndependent L (fun i => algebraMap K L ∘ b i) :=
    linearIndependent_algebraMap_comp_iff.mpr hbind
  let φ := Pi.algebraMap n K L
  have hmap := congrArg (fun p : Submodule K (n → K) => p.map φ) hbspan
  simp only [Submodule.map_span, ← Set.range_comp] at hmap
  have hspan := congrArg (fun p : Submodule K (n → L) => span L (p : Set (n → L))) hmap
  simp only [Submodule.span_span_of_tower] at hspan
  change span L (Set.range (fun i => algebraMap K L ∘ b i)) =
    span L ((fun v : n → K => algebraMap K L ∘ v) '' s) at hspan
  rw [← hspan, finrank_span_eq_card hbL, Fintype.card_fin]



theorem eval_source_jet_monomial_eq_map_row {K : Type*} [Field K]
    (φ : K →+* ℂ) (u : Fin 4 → K) (σ τ : K →+* K)
    (n : Fin 4 → ℕ) (a : Fin 3 → ℕ) :
    MvPolynomial.eval (fun _ => 1)
      (invariantJet (fun j i => φ (![u, (fun i => σ (u i)),
        (fun i => (σ.comp τ) (u i))] j i)) a
        (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm n) 1)) =
    φ ((∑ i, (n i : K) * u i) ^ a 0 *
      σ (∑ i, (n i : K) * u i) ^ a 1 *
      (σ.comp τ) (∑ i, (n i : K) * u i) ^ a 2) := by
  simp [eval_one_invariantJet_monomial, map_sum, mul_comm]

theorem finrank_span_source_jet_rows_eq {K κ : Type*} [Field K] [Fintype κ]
    (φ : K →+* ℂ) (u : Fin 4 → K) (σ τ : K →+* K)
    (n : κ → Fin 4 → ℕ) (s : Set (Fin 3 → ℕ)) :
    Module.finrank ℂ (Submodule.span ℂ
      ((fun a : Fin 3 → ℕ => fun j => MvPolynomial.eval (fun _ => 1)
        (invariantJet (fun k i => φ (![u, (fun i => σ (u i)),
          (fun i => (σ.comp τ) (u i))] k i)) a
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (n j)) 1))) '' s)) =
    Module.finrank K (Submodule.span K
      ((fun a : Fin 3 → ℕ => fun j =>
        (∑ i, (n j i : K) * u i) ^ a 0 *
        σ (∑ i, (n j i : K) * u i) ^ a 1 *
        (σ.comp τ) (∑ i, (n j i : K) * u i) ^ a 2) '' s)) := by
  let : Algebra K ℂ := φ.toAlgebra
  have h := finrank_span_algebraMap_image (L := ℂ)
    (((fun a : Fin 3 → ℕ => fun j =>
      (∑ i, (n j i : K) * u i) ^ a 0 *
      σ (∑ i, (n j i : K) * u i) ^ a 1 *
      (σ.comp τ) (∑ i, (n j i : K) * u i) ^ a 2)) '' s)
  have hr := funext fun a => funext fun j =>
    eval_source_jet_monomial_eq_map_row φ u σ τ (n j) a
  rw [hr]
  rw [Set.image_image] at h
  exact h

end WeightedTorusJets.Geometry

end

namespace WeightedTorusJets

theorem greedyPivots_eq_global_retained_set {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (v : ℕ → V) (T : ℕ)
    (hspan : Submodule.span K (v '' (Finset.range T : Set ℕ)) = ⊤) :
    (greedyPivots K v T : Set ℕ) =
      {i | v i ∉ Submodule.span K (v '' (Finset.range i : Set ℕ))} := by
  ext i
  constructor
  · intro hi
    exact ((mem_greedyPivots_iff v i T).mp hi).2
  · intro hi
    have hmem : i ∈ greedyPivots K v (max T (i + 1)) :=
      (mem_greedyPivots_iff v i (max T (i + 1))).mpr
        ⟨(Nat.lt_succ_self i).trans_le (le_max_right T (i + 1)), hi⟩
    rw [← greedyPivots_eq_of_span_eq_top v (le_max_left T (i + 1)) hspan] at hmem
    exact hmem

end WeightedTorusJets



end SiegelZeros

end OAI
