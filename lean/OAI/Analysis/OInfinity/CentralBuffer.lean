import OAI.Analysis.OInfinity.CentralIsometries
import OAI.Analysis.OInfinity.MixedTower
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerMaps

namespace OAI

/-! # A third canonical row in the norm ultrapower

The representatives are the explicit approximately central canonical rows,
with tolerance `1/(n+1)` and the first `n+1` source generators tested. Their
norms are uniformly one; both Gram and commutation relations hold exactly
in the quotient. No commuting-buffer existence is assumed.
-/

noncomputable section
open Filter Topology
open scoped CStarAlgebra ENNReal

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E] [Nontrivial E]

/-- A concrete third row centralizing the two constant canonical families. -/
lemma exists_normUltrapower_central_cuntz_row
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]
    (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hc : bergRowsCommute s t) :
    ∃ R : ℕ → NormUltra.QuotientAlgebra (fun _ : ℕ => E) U,
      (∀ j k, star (R j) * R k = if j = k then 1 else 0) ∧
      (∀ j i, Commute (R j) (NormUltra.QuotientAlgebra.diagonalHom U (s i)) ∧
        Commute (R j) (star (NormUltra.QuotientAlgebra.diagonalHom U (s i)))) ∧
      ∀ j i, Commute (R j) (NormUltra.QuotientAlgebra.diagonalHom U (t i)) ∧
        Commute (R j) (star (NormUltra.QuotientAlgebra.diagonalHom U (t i))) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  choose r hr ha ht using fun n =>
    exists_approximately_central_cuntz_row s t hs hc (n + 1) (ε n) (hε n)
  have hn (n j : ℕ) : ‖r n j‖ ≤ 1 := by
    have h := congrArg norm (show star (r n j) * r n j = 1 by simpa only [ite_true] using hr n j j)
    rw [CStarRing.norm_star_mul_self, norm_one] at h
    nlinarith [norm_nonneg (r n j)]
  let x : ℕ → NormUltra.BoundedFamilies (fun _ : ℕ => E) := fun j =>
    ⟨fun n => r n j, memℓp_infty ⟨1, by rintro _ ⟨n, rfl⟩; exact hn n j⟩⟩
  let q := NormUltra.QuotientAlgebra.mkHom (A := fun _ : ℕ => E) (U := U)
  let d := NormUltra.QuotientAlgebra.diagonalHom (A := E) U
  have hεlim : Tendsto ε (U : Filter ℕ) (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left Fact.out
  have happ (j i : ℕ) (b : E)
      (hb : ∀ n, i < n + 1 → ‖r n j * b - b * r n j‖ < ε n) :
      Commute (q (x j)) (d b) := by
    change NormUltra.QuotientAlgebra.mk U (x j * DirectComparison.boundedDiagonal b) =
      NormUltra.QuotientAlgebra.mk U (DirectComparison.boundedDiagonal b * x j)
    apply (NormUltra.QuotientAlgebra.mk_eq_mk_iff _ _).mpr
    change Tendsto (fun n => ‖r n j * b - b * r n j‖) (U : Filter ℕ) (𝓝 0)
    apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hεlim
    filter_upwards [(eventually_ge_atTop i).filter_mono Fact.out] with n hn'
    exact (hb n (by omega)).le
  have hexact (j : ℕ) (b : E) (hb : ∀ n, Commute (r n j) b) :
      Commute (q (x j)) (d b) := by
    change NormUltra.QuotientAlgebra.mk U (x j * DirectComparison.boundedDiagonal b) =
      NormUltra.QuotientAlgebra.mk U (DirectComparison.boundedDiagonal b * x j)
    congr 1
    ext n
    exact (hb n).eq
  refine ⟨fun j => q (x j), ?_, ?_, ?_⟩
  · intro j k
    by_cases hjk : j = k
    · subst k
      rw [ite_eq_left rfl]
      change NormUltra.QuotientAlgebra.mk U (star (x j) * x j) =
        NormUltra.QuotientAlgebra.mk U (DirectComparison.boundedDiagonal (1 : E))
      congr 1
      ext n
      exact (hr n j j).trans (ite_eq_left rfl)
    · rw [ite_eq_right hjk]
      change NormUltra.QuotientAlgebra.mk U (star (x j) * x k) =
        NormUltra.QuotientAlgebra.mk U (0 : NormUltra.BoundedFamilies (fun _ : ℕ => E))
      congr 1
      ext n
      exact (hr n j k).trans (ite_eq_right hjk)
  · intro j i
    constructor
    · exact happ j i (s i) (fun n hni => (ha n j i hni).1)
    · rw [← map_star]
      exact happ j i (star (s i)) (fun n hni => (ha n j i hni).2)
  · intro j i
    constructor
    · exact hexact j (t i) (fun n => (ht n j i).1)
    · rw [← map_star]
      exact hexact j (star (t i)) (fun n => (ht n j i).2)

end WeakPureInfiniteness

end

end OAI
