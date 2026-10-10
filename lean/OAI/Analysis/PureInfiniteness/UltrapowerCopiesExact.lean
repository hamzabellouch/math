import OAI.Analysis.PureInfiniteness.UltrapowerCopiesApprox
import OAI.Analysis.PureInfiniteness.FiniteUltrapowerSaturation
import OAI.Analysis.PureInfiniteness.ExactCompressionRelations

namespace OAI

/-! The finite relative copies needed in KR02 Proposition 7.14. The relations
are imposed on the selected commuting positive elements, which is sufficient
for combining their coefficient compressions. -/

noncomputable section
open Filter Topology
open scoped ENNReal

namespace WeakPureInfiniteness

variable {A I M : Type*} [NonUnitalCStarAlgebra A]
  [Fintype I] [DecidableEq I] [Fintype M] [DecidableEq M]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "L" => NormUltra.BoundedFamilies (fun _ : ℕ => A)

private abbrev CopyTest := Unit ⊕ (M ⊕ ((I × M × M) ⊕ (I × M)))

private def copyTestValue (a : I → L) (t : CopyTest (I := I) (M := M)) (k : ℕ)
    (v : M → A) : ℝ :=
  match t with
  | .inl _ => 0
  | .inr (.inl j) => max (‖v j‖ - 1) 0
  | .inr (.inr (.inl (i, j, l))) =>
      ‖star (v j) * a i k * v l - (if j = l then a i k else 0)‖
  | .inr (.inr (.inr (i, j))) =>
      ‖star (v j) * (a i k * a i k) * v j - a i k * a i k‖

omit [Fintype I] [DecidableEq I] [Fintype M] in
private lemma copyTestValue_nonneg (a : I → L) (t : CopyTest (I := I) (M := M))
    (k : ℕ) (v : M → A) : 0 ≤ copyTestValue a t k v := by
  rcases t with _ | (j | (⟨i, j, l⟩ | ⟨i, j⟩))
  · exact le_rfl
  · exact le_max_right _ _
  · exact norm_nonneg _
  · exact norm_nonneg _

theorem ultrapower_copies_exact (hP : MainGap.PropertyP A)
    (a : I → N) (ha : ∀ i, 0 ≤ a i) (hc : ∀ i j, Commute (a i) (a j)) :
    ∃ v : M → N, (∀ j, ‖v j‖ ≤ 1) ∧ ∀ i,
      (∀ j k, star (v j) * a i * v k = if j = k then a i else 0) ∧
      (∀ j, star (v j) * (a i * a i) * v j = a i * a i) := by
  classical
  let q := NormUltra.QuotientAlgebra.mkHom (A := fun _ : ℕ => A) (U := U)
  choose α hα using fun i => NormUltra.QuotientAlgebra.mk_surjective (a i)
  let g := copyTestValue (M := M) α
  have hs (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k in (U : Filter ℕ),
      ∃ v : M → A, ‖v‖ ≤ 2 ∧ ∀ t, g t k v < ε := by
    obtain ⟨v, hvn, hv⟩ := ultrapower_copies_approx (M := M) U hP a ha hc
      (ε / 2) (half_pos hε)
    choose x hx hxn using fun j => NormUltra.QuotientAlgebra.exists_norm_mk_lt (v j) zero_lt_one
    have hn (j : M) : ∀ᶠ k in (U : Filter ℕ), ‖x j k‖ < 1 + ε :=
      NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U (x j) (by rw [hx]; linarith [hvn j])
    have h₁ (i : I) (j l : M) :
        ‖q (star (x j) * α i * x l - (if j = l then α i else 0))‖ < ε := by
      change ‖star (q (x j)) * q (α i) * q (x l) - q (if j = l then α i else 0)‖ < ε
      have he : q (if j = l then α i else 0) = if j = l then a i else 0 := by
        split_ifs <;> simp only [map_zero, show q (α i) = a i from hα i]
      rw [show q (x j) = v j from hx j, show q (x l) = v l from hx l,
        show q (α i) = a i from hα i, he]
      exact ((hv i).1 j l).trans (by linarith)
    have h₂ (i : I) (j : M) :
        ‖q (star (x j) * (α i * α i) * x j - α i * α i)‖ < ε := by
      change ‖star (q (x j)) * (q (α i) * q (α i)) * q (x j) - q (α i) * q (α i)‖ < ε
      rw [show q (x j) = v j from hx j, show q (α i) = a i from hα i]
      exact ((hv i).2 j).trans (by linarith)
    have hall (t : CopyTest (I := I) (M := M)) :
        ∀ᶠ k in (U : Filter ℕ), g t k (fun j => x j k) < ε := by
      rcases t with _ | (j | (⟨i, j, l⟩ | ⟨i, j⟩))
      · exact Eventually.of_forall fun _ => hε
      · filter_upwards [hn j] with k hk
        exact max_lt (by linarith) hε
      · have he := NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U _ (h₁ i j l)
        filter_upwards [he] with k hk
        by_cases hjl : j = l
        · subst l
          rw [ite_eq_left rfl] at hk
          change ‖star (x j k) * α i k * x j k - α i k‖ < ε at hk
          simpa only [g, copyTestValue, ite_eq_left rfl, ite_true] using hk
        · rw [ite_eq_right hjl] at hk
          change ‖star (x j k) * α i k * x l k - 0‖ < ε at hk
          simpa only [g, copyTestValue, ite_eq_right hjl] using hk
      · exact NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U _ (h₂ i j)
    filter_upwards [eventually_all.mpr hall] with k hk
    refine ⟨fun j => x j k, ?_, hk⟩
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
    intro j
    exact (NormUltra.BoundedFamilies.norm_coordinate_le (x j) k).trans
      ((hxn j).le.trans (by linarith [hvn j]))
  obtain ⟨x, hxn, hx⟩ := NormUltra.bounded_epsilon_test_finite U Fact.out 2 (by norm_num)
    g (copyTestValue_nonneg α) hs
  let y (j : M) : L := ⟨fun k => x k j, memℓp_infty ⟨2, by
    rintro _ ⟨k, rfl⟩
    exact (norm_le_pi_norm (x k) j).trans (hxn k)⟩⟩
  let v (j : M) := q (y j)
  refine ⟨v, ?_, ?_⟩
  · intro j
    exact NormUltra.norm_mk_le_one_of_defect_tendsto U (y j) (hx (.inr (.inl j)))
  · intro i
    refine ⟨?_, ?_⟩
    · intro j l
      have ht := hx (.inr (.inr (.inl (i, j, l))))
      have he := (NormUltra.QuotientAlgebra.mk_eq_mk_iff (U := U) (star (y j) * α i * y l)
        (if j = l then α i else 0)).mpr (by
          by_cases hjl : j = l
          · subst l
            rw [ite_eq_left rfl]
            change Tendsto (fun k => ‖star (x k j) * α i k * x k j - α i k‖)
              (U : Filter ℕ) (𝓝 0)
            simpa only [g, copyTestValue, ite_eq_left rfl, ite_true] using ht
          · rw [ite_eq_right hjl]
            change Tendsto (fun k => ‖star (x k j) * α i k * x k l - 0‖)
              (U : Filter ℕ) (𝓝 0)
            simpa only [g, copyTestValue, ite_eq_right hjl] using ht)
      change star (q (y j)) * q (α i) * q (y l) = q (if j = l then α i else 0) at he
      have heq : q (if j = l then α i else 0) = if j = l then a i else 0 := by
        split_ifs <;> simp only [map_zero, show q (α i) = a i from hα i]
      rw [show q (α i) = a i from hα i, heq] at he
      exact he
    · intro j
      have he := (NormUltra.QuotientAlgebra.mk_eq_mk_iff
        (star (y j) * (α i * α i) * y j) (α i * α i)).mpr
          (hx (.inr (.inr (.inr (i, j)))))
      change star (q (y j)) * (q (α i) * q (α i)) * q (y j) = q (α i) * q (α i) at he
      rwa [show q (α i) = a i from hα i] at he

theorem ultrapower_relative_copies (hP : MainGap.PropertyP A)
    (a : I → N) (ha : ∀ i, 0 ≤ a i) (hc : ∀ i j, Commute (a i) (a j)) :
    ∃ v : M → N, (∀ j, ‖v j‖ ≤ 1) ∧ (∀ i j, Commute (a i) (v j)) ∧
      ∀ i j k, (star (v j) * v k) * a i = if j = k then a i else 0 := by
  obtain ⟨v, hv, he⟩ := ultrapower_copies_exact (M := M) U hP a ha hc
  have hrel (i : I) (j : M) : a i * v j = v j * a i ∧ (star (v j) * v j) * a i = a i := by
    apply (selfAdjoint_fixed_compression_iff (v j) (a i) (hv j) (ha i).isSelfAdjoint).mp
    exact ⟨by simpa using (he i).1 j j, (he i).2 j⟩
  refine ⟨v, hv, fun i j => (hrel i j).1, ?_⟩
  intro i j k
  calc
    (star (v j) * v k) * a i = star (v j) * (v k * a i) := mul_assoc _ _ _
    _ = star (v j) * (a i * v k) := by rw [(hrel i k).1]
    _ = star (v j) * a i * v k := (mul_assoc _ _ _).symm
    _ = _ := (he i).1 j k

end WeakPureInfiniteness

end

end OAI
