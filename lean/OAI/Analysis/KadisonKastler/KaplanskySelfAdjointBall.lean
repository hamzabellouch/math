import OAI.Analysis.KadisonKastler.KaplanskyRational
import OAI.Analysis.KadisonKastler.NormClosureUnitBall
import OAI.Analysis.KadisonKastler.Algebra

namespace OAI

/-! # Bounded density at self-adjoint elements

The rational preimage lies in the same bicommutant. Its unbounded
self-adjoint approximants become contractions under the rational map.
A final norm approximation returns to the original star algebra.
-/

namespace KadisonKastler

open Generator Filter
open scoped Topology BigOperators

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Contractions from the norm closure approximate a self-adjoint
bicommutant contraction strongly on any finite set of vectors. -/
theorem selfAdjoint_bicommutant_closureBall_approx
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (hsa : IsSelfAdjoint T) (hn : ‖T‖ ≤ 1) (V : Finset H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ b ∈ A.topologicalClosure, ‖b‖ ≤ 1 ∧ ∀ x ∈ V, ‖T x - b x‖ < ε := by
  classical
  let M := generatedVonNeumannAlgebra A
  have hTM : T ∈ M.toStarSubalgebra := by
    change T ∈ (generatedVonNeumannAlgebra A : Set (H →L[ℂ] H))
    rwa [generatedVonNeumannAlgebra_coe]
  let : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_algebra M
  obtain ⟨S, rfl, hS, hST⟩ := exists_kaplanskyTransform_preimage T hsa hn
  have hSin : cfc kaplanskyInverse T ∈ Set.centralizer
      (Set.centralizer (A : Set (H →L[ℂ] H))) := by
    have hs : cfc kaplanskyInverse T ∈ M.toStarSubalgebra := cfc_mem _ hTM
    change cfc kaplanskyInverse T ∈
      (generatedVonNeumannAlgebra A : Set (H →L[ℂ] H)) at hs
    rwa [generatedVonNeumannAlgebra_coe] at hs
  obtain ⟨a, ha, halim⟩ := selfAdjoint_bicommutant_exists_strong_net A _ hSin hS
  have hlim (x : H) : Tendsto
      (fun i => cfc kaplanskyTransform (a i : H →L[ℂ] H) x) atTop (𝓝 (T x)) := by
    simpa only [hST] using tendsto_kaplanskyTransform_of_strong ha hS halim x
  have hevent : ∀ᶠ i in (atTop : Filter (Finset H × ℕ)),
      ∀ x ∈ V, ‖T x - cfc kaplanskyTransform (a i : H →L[ℂ] H) x‖ < ε := by
    rw [Filter.eventually_all_finset]
    intro x _
    have he := (tendsto_iff_norm_sub_tendsto_zero.mp (hlim x)).eventually (gt_mem_nhds hε)
    simpa only [norm_sub_rev] using he
  obtain ⟨i, hi⟩ := hevent.exists
  refine ⟨cfc kaplanskyTransform (a i : H →L[ℂ] H), ?_,
    norm_kaplanskyTransform_le_one _, hi⟩
  let : IsClosed (A.topologicalClosure : Set (H →L[ℂ] H)) := A.isClosed_topologicalClosure
  exact cfc_mem _ (A.le_topologicalClosure (a i).property)

/-- The original star algebra's unit ball is strongly dense at every
self-adjoint contraction in its bicommutant. -/
theorem selfAdjoint_bicommutant_unitBall_approx
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (hsa : IsSelfAdjoint T) (hn : ‖T‖ ≤ 1) (V : Finset H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, ‖(a : H →L[ℂ] H)‖ ≤ 1 ∧ ∀ x ∈ V, ‖T x - (a : H →L[ℂ] H) x‖ < ε := by
  classical
  obtain ⟨b, hb, hbn, hTb⟩ := selfAdjoint_bicommutant_closureBall_approx
    A T hT hsa hn V (half_pos hε)
  let R := 1 + ∑ x ∈ V, ‖x‖
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨a, han, hba⟩ := normClosure_unitBall_approx A hb hbn
    (div_pos hε (mul_pos (by norm_num : (0 : ℝ) < 2) hR))
  refine ⟨a, han, ?_⟩
  intro x hx
  have hxR : ‖x‖ ≤ R := by
    have hs := Finset.single_le_sum (fun y (_ : y ∈ V) => norm_nonneg y) hx
    dsimp [R]
    linarith
  have hdist : ‖b x - (a : H →L[ℂ] H) x‖ < ε / 2 := by
    have hlt : ‖b - (a : H →L[ℂ] H)‖ * R < ε / 2 := by
      have h := mul_lt_mul_of_pos_right hba hR
      have he : ε / (2 * R) * R = ε / 2 := by field_simp
      rwa [he] at h
    have hle := ContinuousLinearMap.le_opNorm (b - (a : H →L[ℂ] H)) x
    exact hle.trans_lt ((mul_le_mul_of_nonneg_left hxR (norm_nonneg _)).trans_lt hlt)
  have htriangle : ‖T x - (a : H →L[ℂ] H) x‖ ≤
      ‖T x - b x‖ + ‖b x - (a : H →L[ℂ] H) x‖ := by
    simpa only [dist_eq_norm] using dist_triangle (T x) (b x) ((a : H →L[ℂ] H) x)
  exact htriangle.trans_lt (by linarith [hTb x hx])

end

end KadisonKastler

end OAI
