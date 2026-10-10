import OAI.Analysis.PureInfiniteness.AbelianizationRelations
import OAI.Analysis.PureInfiniteness.CountableUltrapowerSaturation

namespace OAI

/-! Countable positive families admit a single abelian-range compression.
This is the saturation step of KR02 Proposition 7.13. -/

noncomputable section
open Filter Topology
open scoped ENNReal

namespace WeakPureInfiniteness

variable {A : Type*} [NonUnitalCStarAlgebra A]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "L" => NormUltra.BoundedFamilies (fun _ : ℕ => A)

private def countableAbelianizationTest (a b : ℕ → L)
    (j : Unit ⊕ AbelianizationRelation) (k : ℕ) (v : A) : ℝ :=
  match j with
  | .inl _ => max (‖v‖ - 1) 0
  | .inr j => ‖abelianizationRelation (fun i => a i k) (fun i => b i k) v j‖

private lemma countableAbelianizationTest_nonneg (a b : ℕ → L)
    (j : Unit ⊕ AbelianizationRelation) (k : ℕ) (v : A) :
    0 ≤ countableAbelianizationTest a b j k v := by
  cases j
  · exact le_max_right _ _
  · exact norm_nonneg _

theorem ultrapower_countable_positive_abelianization (hP : MainGap.PropertyP A)
    (a b : ℕ → N) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hc : ∀ i j, Commute (a i) (a j)) :
    ∃ v : N, ‖v‖ ≤ 1 ∧ (∀ i, star v * a i * v = a i) ∧
      (∀ i j, Commute (a i) (star v * b j * v)) ∧
      ∀ i j, Commute (star v * b i * v) (star v * b j * v) := by
  classical
  let q := NormUltra.QuotientAlgebra.mkHom (A := fun _ : ℕ => A) (U := U)
  choose α hα using fun i => NormUltra.QuotientAlgebra.mk_surjective (a i)
  choose β hβ using fun i => NormUltra.QuotientAlgebra.mk_surjective (b i)
  have hαfun : (fun i => q (α i)) = a := funext hα
  have hβfun : (fun i => q (β i)) = b := funext hβ
  let g := countableAbelianizationTest α β
  have hs (F : Finset (Unit ⊕ AbelianizationRelation)) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ k in (U : Filter ℕ), ∃ v : A, ‖v‖ ≤ 2 ∧ ∀ j ∈ F, g j k v < ε := by
    let m := F.sup (Sum.elim (fun _ : Unit => 0) abelianizationHeight)
    obtain ⟨v, hv, hfix, hcomm, hpair⟩ := ultrapower_finite_family_abelianization U hP
      (fun i : Fin (m + 1) => a i) (fun i => ha i) (fun i j => hc i j)
      (m + 1) (fun i => b i) (fun i => hb i)
    obtain ⟨x, hx, hxn⟩ := NormUltra.QuotientAlgebra.exists_norm_mk_lt v zero_lt_one
    have hn : ∀ᶠ k in (U : Filter ℕ), ‖x k‖ < 1 + ε :=
      NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U x (by rw [hx]; linarith)
    have hr (j : AbelianizationRelation) (hj : abelianizationHeight j ≤ m) :
        ∀ᶠ k in (U : Filter ℕ),
          ‖abelianizationRelation (fun i => α i k) (fun i => β i k) (x k) j‖ < ε := by
      have he : q (abelianizationRelation α β x j) = 0 := by
        rw [map_abelianizationRelation, hαfun, hβfun, show q x = v from hx]
        exact abelianizationRelation_eq_zero_of_finite a b v m hfix hcomm hpair j hj
      have he' := NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U
        (abelianizationRelation α β x j) (by change ‖q _‖ < ε; rw [he, norm_zero]; exact hε)
      rcases j with i | (⟨i, j⟩ | ⟨i, j⟩) <;> exact he'
    have hall : ∀ j : F, ∀ᶠ k in (U : Filter ℕ), g j.val k (x k) < ε := by
      intro j
      rcases hj : j.val with _ | r
      · filter_upwards [hn] with k hk
        change max (‖x k‖ - 1) 0 < ε
        exact max_lt (by linarith) hε
      · have hh : abelianizationHeight r ≤ m := by
          have h := Finset.le_sup (f := Sum.elim (fun _ : Unit => 0) abelianizationHeight) j.property
          simpa only [hj, Sum.elim_inr] using h
        simpa only [hj, g, countableAbelianizationTest] using hr r hh
    filter_upwards [eventually_all.mpr hall] with k hk
    refine ⟨x k, (NormUltra.BoundedFamilies.norm_coordinate_le x k).trans
      (hxn.le.trans (by linarith)), ?_⟩
    intro j hj
    exact hk ⟨j, hj⟩
  obtain ⟨x, _, hx⟩ := NormUltra.bounded_epsilon_test_countable U Fact.out 2 (by norm_num)
    g (countableAbelianizationTest_nonneg α β) hs
  have hrel (j : AbelianizationRelation) : abelianizationRelation a b (q x) j = 0 := by
    have hlim : Tendsto (fun k => ‖(abelianizationRelation α β x j) k‖)
        (U : Filter ℕ) (𝓝 0) := by
      have h := hx (.inr j)
      rcases j with i | (⟨i, j⟩ | ⟨i, j⟩) <;> exact h
    have he := (NormUltra.QuotientAlgebra.mk_eq_mk_iff (abelianizationRelation α β x j) 0).mpr
      (by
        change Tendsto (fun k => ‖(abelianizationRelation α β x j) k - 0‖) (U : Filter ℕ) (𝓝 0)
        simpa only [sub_zero] using hlim)
    change q (abelianizationRelation α β x j) = 0 at he
    rwa [map_abelianizationRelation, hαfun, hβfun] at he
  refine ⟨q x, NormUltra.norm_mk_le_one_of_defect_tendsto U x (hx (.inl ())), ?_, ?_, ?_⟩
  · intro i
    exact sub_eq_zero.mp (hrel (.inl i))
  · intro i j
    exact sub_eq_zero.mp (hrel (.inr (.inl (i, j))))
  · intro i j
    exact sub_eq_zero.mp (hrel (.inr (.inr (i, j))))

end WeakPureInfiniteness

end

end OAI
