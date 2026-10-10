import OAI.Analysis.PureInfiniteness.UltrapowerFiniteAbelianization
import OAI.Analysis.PureInfiniteness.FiniteUltrapowerSaturation
import OAI.Analysis.PureInfiniteness.ExactCompressionRelations

namespace OAI

/-! Exact finite spectral abelianization in the norm ultrapower. The witness
comes from polynomial norm conditions; multiplicativity is not inferred from
centrality of a completely positive map. -/

noncomputable section
open Filter Topology
open scoped ENNReal

namespace WeakPureInfiniteness

variable {A I : Type*} [NonUnitalCStarAlgebra A] [Fintype I] [DecidableEq I]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "L" => NormUltra.BoundedFamilies (fun _ : ℕ => A)

private def finiteAbelianizationTest (a : I → L) (b : L)
    (j : Unit ⊕ (Fin 3 × I)) (k : ℕ) (v : A) : ℝ :=
  match j with
  | .inl _ => max (‖v‖ - 1) 0
  | .inr (j, i) => match j.val with
    | 0 => ‖star v * a i k * v - a i k‖
    | 1 => ‖star v * (a i k * a i k) * v - a i k * a i k‖
    | _ => ‖a i k * (star v * b k * v) - (star v * b k * v) * a i k‖

omit [Fintype I] [DecidableEq I] in
private lemma finiteAbelianizationTest_nonneg (a : I → L) (b : L)
    (j : Unit ⊕ (Fin 3 × I)) (k : ℕ) (v : A) :
    0 ≤ finiteAbelianizationTest a b j k v := by
  rcases j with _ | ⟨j, i⟩
  · exact le_max_right _ _
  · fin_cases j <;> exact norm_nonneg _

theorem ultrapower_finite_abelianization_exact (hP : MainGap.PropertyP A)
    (a : I → N) (ha : ∀ i, 0 ≤ a i) (hc : ∀ i j, Commute (a i) (a j))
    (b : N) (hb : IsSelfAdjoint b) :
    ∃ v : N, ‖v‖ ≤ 1 ∧ ∀ i,
      star v * a i * v = a i ∧
      star v * (a i * a i) * v = a i * a i ∧
      a i * (star v * b * v) = (star v * b * v) * a i := by
  classical
  let q := NormUltra.QuotientAlgebra.mkHom (A := fun _ : ℕ => A) (U := U)
  choose α hα using fun i => NormUltra.QuotientAlgebra.mk_surjective (a i)
  obtain ⟨β, hβ⟩ := NormUltra.QuotientAlgebra.mk_surjective b
  let g := finiteAbelianizationTest α β
  have hs (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k in (U : Filter ℕ),
      ∃ v : A, ‖v‖ ≤ 2 ∧ ∀ j, g j k v < ε := by
    obtain ⟨v, hvn, hv⟩ := ultrapower_finite_abelianization_approx U hP a ha hc b hb
      (ε / 2) (half_pos hε)
    obtain ⟨x, hx, hxn⟩ := NormUltra.QuotientAlgebra.exists_norm_mk_lt v zero_lt_one
    have hn : ∀ᶠ k in (U : Filter ℕ), ‖x k‖ < 1 + ε :=
      NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U x (by rw [hx]; linarith)
    have h₁ (i : I) : ‖q (star x * α i * x - α i)‖ < ε := by
      change ‖star (q x) * q (α i) * q x - q (α i)‖ < ε
      rw [show q x = v from hx, show q (α i) = a i from hα i]
      exact ((hv i).1).trans (by linarith)
    have h₂ (i : I) : ‖q (star x * (α i * α i) * x - α i * α i)‖ < ε := by
      change ‖star (q x) * (q (α i) * q (α i)) * q x - q (α i) * q (α i)‖ < ε
      rw [show q x = v from hx, show q (α i) = a i from hα i]
      exact ((hv i).2.1).trans (by linarith)
    have h₃ (i : I) : ‖q (α i * (star x * β * x) - (star x * β * x) * α i)‖ < ε := by
      change ‖q (α i) * (star (q x) * q β * q x) -
        (star (q x) * q β * q x) * q (α i)‖ < ε
      rw [show q x = v from hx, show q (α i) = a i from hα i, show q β = b from hβ]
      exact ((hv i).2.2).trans (by linarith)
    have hj : ∀ j, ∀ᶠ k in (U : Filter ℕ), g j k (x k) < ε := by
      rintro (_ | ⟨j, i⟩)
      · filter_upwards [hn] with k hk
        exact max_lt (by linarith) hε
      · fin_cases j
        · exact NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U _ (h₁ i)
        · exact NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U _ (h₂ i)
        · exact NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U _ (h₃ i)
    filter_upwards [eventually_all.mpr hj] with k hk
    refine ⟨x k, ?_, hk⟩
    exact (NormUltra.BoundedFamilies.norm_coordinate_le x k).trans
      (hxn.le.trans (by linarith))
  obtain ⟨x, _, hx⟩ := NormUltra.bounded_epsilon_test_finite U Fact.out 2 (by norm_num)
    g (finiteAbelianizationTest_nonneg α β) hs
  refine ⟨q x, NormUltra.norm_mk_le_one_of_defect_tendsto U x (hx (.inl ())), ?_⟩
  intro i
  have h₁ := (NormUltra.QuotientAlgebra.mk_eq_mk_iff (star x * α i * x) (α i)).mpr
    (hx (.inr (0, i)))
  have h₂ := (NormUltra.QuotientAlgebra.mk_eq_mk_iff (star x * (α i * α i) * x)
    (α i * α i)).mpr (hx (.inr (1, i)))
  have h₃ := (NormUltra.QuotientAlgebra.mk_eq_mk_iff (α i * (star x * β * x))
    ((star x * β * x) * α i)).mpr (hx (.inr (2, i)))
  change star (q x) * q (α i) * q x = q (α i) at h₁
  change star (q x) * (q (α i) * q (α i)) * q x = q (α i) * q (α i) at h₂
  change q (α i) * (star (q x) * q β * q x) =
    (star (q x) * q β * q x) * q (α i) at h₃
  rw [show q (α i) = a i from hα i] at h₁ h₂ h₃
  rw [show q β = b from hβ] at h₃
  exact ⟨h₁, h₂, h₃⟩

/-- Relative support and commutation are consequences of preserving both
moments, not assumptions about the completely positive compression. -/
theorem ultrapower_finite_relative_abelianization (hP : MainGap.PropertyP A)
    (a : I → N) (ha : ∀ i, 0 ≤ a i) (hc : ∀ i j, Commute (a i) (a j))
    (b : N) (hb : IsSelfAdjoint b) :
    ∃ v : N, ‖v‖ ≤ 1 ∧ (∀ i, a i * v = v * a i ∧ (star v * v) * a i = a i) ∧
      ∀ i, Commute (a i) (star v * b * v) := by
  obtain ⟨v, hv, he⟩ := ultrapower_finite_abelianization_exact U hP a ha hc b hb
  exact ⟨v, hv, fun i => (selfAdjoint_fixed_compression_iff v (a i) hv
    (ha i).isSelfAdjoint).mp ⟨(he i).1, (he i).2.1⟩, fun i => (he i).2.2⟩

end WeakPureInfiniteness

end

end OAI
