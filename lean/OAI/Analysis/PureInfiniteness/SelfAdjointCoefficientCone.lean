import OAI.Analysis.Nuclearity.UnitizedConeMembership
import OAI.Analysis.WeakInfiniteness.CPSchwarz
import OAI.Analysis.JiangSu.Nuclearity.NuclearNormApproximation

namespace OAI

/-! Finite self-adjoint evaluations of the actual coefficient cone. The
Hahn--Banach step uses the existing finite seminorm separation theorem. -/

noncomputable section
open scoped BigOperators
open Complex selfAdjoint

namespace WeakPureInfiniteness

variable {A B I : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [Fintype I]
  (U : Ultrafilter ℕ)

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

def selfAdjointCoefficientTuple (x : I → selfAdjoint B) :
    (B → N) →ₗ[ℝ] (I → selfAdjoint N) where
  toFun S i := realPart (S (x i))
  map_add' S T := by
    funext i
    exact map_add (realPart : N →ₗ[ℝ] selfAdjoint N) (S (x i)) (T (x i))
  map_smul' c S := by
    funext i
    exact map_smul (realPart : N →ₗ[ℝ] selfAdjoint N) c (S (x i))

omit [Fintype I] in
lemma selfAdjointCoefficientTuple_cp (x : I → selfAdjoint B) (T : B →L[ℂ] N)
    (hT : CompletelyPositive T) (i : I) :
    ((selfAdjointCoefficientTuple U x T i : selfAdjoint N) : N) = T (x i) := by
  apply IsSelfAdjoint.coe_realPart
  change star (T (x i)) = T (x i)
  rw [← completelyPositive_map_star hT, (x i).property]

omit [PartialOrder B] [StarOrderedRing B] [Fintype I] in
lemma selfAdjointCoefficientTuple_hom (x : I → selfAdjoint B) (β : B →⋆ₙₐ[ℂ] N) (i : I) :
    ((selfAdjointCoefficientTuple U x β i : selfAdjoint N) : N) = β (x i) :=
  ((x i).property.map β).coe_realPart

variable [TopologicalSpace.SeparableSpace B] [Fact ((U : Filter ℕ) ≤ Filter.atTop)]

theorem finite_coefficient_approximation_of_functionals (hP : MainGap.PropertyP A)
    (β : B →⋆ₙₐ[ℂ] N) (x : I → selfAdjoint B)
    (hdual : ∀ l : I → selfAdjoint N →L[ℝ] ℝ,
      (∀ T : B →L[ℂ] N, CompletelyPositive T →
        (T : B → N) ∈ finiteUnitizedAbelianCoefficientCone U β →
          0 ≤ ∑ i, l i (realPart (T (x i)))) →
      0 ≤ ∑ i, l i (realPart (β (x i))))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : B →L[ℂ] N, CompletelyPositive T ∧
      (T : B → N) ∈ finiteUnitizedAbelianCoefficientCone U β ∧
      ‖(fun i => β (x i)) - (fun i => T (x i))‖ < ε := by
  classical
  let C := (unitizedCoefficientCone U β).map (selfAdjointCoefficientTuple U x)
  let b := selfAdjointCoefficientTuple U x β
  have hzero : (0 : I → selfAdjoint N) ∈ C :=
    ⟨0, finiteUnitizedAbelianCoefficientCone_zero U β, map_zero _⟩
  have hscale : ∀ t : ℝ, 0 ≤ t → ∀ y ∈ C, t • y ∈ C := by
    intro t ht y hy
    rcases ht.eq_or_lt with rfl | ht
    · simpa only [zero_smul] using hzero
    · exact C.smul_mem ht hy
  have hbound (L : (I → selfAdjoint N) →L[ℝ] ℝ)
      (_ : ∃ c : ℝ, 0 ≤ c ∧ ∀ y, |L y| ≤ c * normSeminorm ℝ (I → selfAdjoint N) y)
      (hL : ∀ y ∈ C, L y ≤ 0) : L b ≤ 0 := by
    let l (i : I) := -(L.comp (ContinuousLinearMap.single ℝ (fun _ : I => selfAdjoint N) i))
    have he (y : I → selfAdjoint N) : ∑ i, l i (y i) = -L y := by
      change (∑ i, -(L (Pi.single i (y i)))) = -L y
      rw [Finset.sum_neg_distrib, ← map_sum]
      exact congrArg (fun z => -L z) (Finset.univ_sum_single y)
    have hb := hdual l (by
      intro T hT hTC
      have hm : selfAdjointCoefficientTuple U x T ∈ C := ⟨T, hTC, rfl⟩
      change 0 ≤ ∑ i, l i (selfAdjointCoefficientTuple U x T i)
      rw [he]
      exact neg_nonneg.mpr (hL _ hm))
    change 0 ≤ ∑ i, l i (b i) at hb
    rw [he] at hb
    exact neg_nonneg.mp hb
  obtain ⟨y, hy, hclose⟩ := NuclearTrace.seminorm_cone_approximation_of_dual
    (normSeminorm ℝ (I → selfAdjoint N)) continuous_norm C C.convex hzero hscale b hbound hε
  obtain ⟨S, hS, rfl⟩ := hy
  obtain ⟨T, hTS, hT⟩ := finiteUnitizedAbelianCoefficientCone_has_cp_map U hP β hS
  refine ⟨T, hT, ?_, ?_⟩
  · have he : (T : B → N) = S := funext hTS
    rwa [he]
  · change ‖(fun i => β (x i)) - (fun i => T (x i))‖ < ε
    have heval : (fun i => ((b - selfAdjointCoefficientTuple U x S) i : N)) =
        (fun i => β (x i) - T (x i)) := by
      funext i
      change (realPart (β (x i)) : N) - (realPart (S (x i)) : N) = _
      rw [← hTS]
      exact congrArg₂ (· - ·) (selfAdjointCoefficientTuple_hom U x β i)
        (selfAdjointCoefficientTuple_cp U x T hT i)
    have hn : ‖(fun i => ((b - selfAdjointCoefficientTuple U x S) i : N))‖ =
        ‖b - selfAdjointCoefficientTuple U x S‖ := rfl
    rw [heval] at hn
    exact hn.trans_lt hclose

end WeakPureInfiniteness

end

end OAI
