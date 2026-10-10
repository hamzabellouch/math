import OAI.Analysis.SeparableQuotients.Positive.ContinuumMeasure

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Family
abbrev ContinuumIndex := Rows.ContinuumIndex
abbrev continuumMeasurableSpace : MeasurableSpace ContinuumIndex := Rows.continuumMeasurableSpace
abbrev ContinuumAdditive := Rows.ContinuumAdditive
alias small_null_union := Rows.small_null_union
alias small_set_null := Rows.small_set_null
alias continuum_regular := Rows.continuum_regular
end SeparableQuotient.Positive.Family

end

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal
universe u

namespace SeparableQuotient.Positive.Family

lemma exists_separated_cover {Y : Type u} [MetricSpace Y] (r : ℝ) (hr : 0 ≤ r) :
    ∃ S : Set Y, S.Pairwise (fun x y => r < dist x y) ∧
      ∀ y : Y, ∃ x ∈ S, dist y x ≤ r := by
  classical
  obtain ⟨S, hS⟩ := zorn_subset {S : Set Y | S.Pairwise (fun x y => r < dist x y)} (by
    intro c hc hchain
    refine ⟨⋃₀ c, hchain.pairwise_sUnion.mpr (fun s hs => hc hs), ?_⟩
    exact fun s hs => subset_sUnion_of_mem hs)
  refine ⟨S, hS.prop, fun y => ?_⟩
  by_contra! hy
  have hyS : y ∉ S := by
    intro h
    have := hy y h
    simpa using (lt_of_le_of_lt hr this : 0 < dist y y)
  have hins : (insert y S).Pairwise (fun x z => r < dist x z) := by
    intro x hx z hz hxz
    rcases hx with rfl | hx <;> rcases hz with rfl | hz
    · exact (hxz rfl).elim
    · exact hy z hz
    · simpa only [dist_comm] using hy x hx
    · exact hS.prop hx hz hxz
  have : insert y S ⊆ S := hS.2 hins (subset_insert y S)
  exact hyS (this (mem_insert y S))



theorem exists_large_separated_of_density {Y : Type u} [MetricSpace Y]
    {κ : Cardinal.{u}} (hκ : κ.IsRegular) (hunc : Cardinal.aleph0 < κ)
    (hdensity : ∀ S : Set Y, Dense S → κ ≤ Cardinal.mk S) :
    ∃ r : ℝ, 0 < r ∧ ∃ S : Set Y,
      S.Pairwise (fun x y => r < dist x y) ∧ κ ≤ Cardinal.mk S := by
  classical
  by_contra! h
  choose S hsep hcover using fun n : ULift.{u} ℕ =>
    exists_separated_cover (Y := Y) (1 / (n.down + 1 : ℝ)) (by positivity)
  have hsmall (n : ULift.{u} ℕ) : Cardinal.mk (S n) < κ :=
    h _ (by positivity) _ (hsep n)
  have hdense : Dense (⋃ n, S n) := by
    intro y
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨x, hx, hdist⟩ := hcover (ULift.up n) y
    exact ⟨x, mem_iUnion.mpr ⟨ULift.up n, hx⟩, lt_of_le_of_lt hdist hn⟩
  have hc : Cardinal.mk (⋃ n, S n) < κ :=
    (Cardinal.card_iUnion_lt_iff_forall_of_isRegular hκ (by simpa using hunc)).mpr hsmall
  exact (not_lt_of_ge (hdensity _ hdense)) hc

end SeparableQuotient.Positive.Family

end

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal
universe u

namespace SeparableQuotient.Positive.Family

local instance realSpaceRatSpace {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : NormedSpace ℚ E := NormedSpace.restrictScalars ℚ ℝ E

local instance realSpaceRatTower {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : IsScalarTower ℚ ℝ E where
  smul_assoc q r x := by
    change ((q : ℝ) * r) • x = (q : ℝ) • (r • x)
    exact mul_smul (q : ℝ) r x



lemma closure_rat_span_eq_real {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) :
    closure (Submodule.span ℚ S : Set E) = closure (Submodule.span ℝ S : Set E) := by
  let Q := (Submodule.span ℚ S).topologicalClosure
  let C : Submodule ℝ E :=
    { carrier := Q
      zero_mem' := Q.zero_mem
      add_mem' := Q.add_mem
      smul_mem' := by
        intro r x hx
        apply (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).induction_on (p := fun a : ℝ => a • x ∈ Q) r
        · exact (Submodule.span ℚ S).isClosed_topologicalClosure.preimage (continuous_id.smul continuous_const)
        · intro q
          simpa only [Rat.cast_smul_eq_qsmul] using Q.smul_mem q hx }
  have hreal : Submodule.span ℝ S ≤ C := Submodule.span_le.mpr
    (fun x hx => (Submodule.span ℚ S).le_topologicalClosure (Submodule.subset_span hx))
  have hrat : Submodule.span ℚ S ≤ (Submodule.span ℝ S).restrictScalars ℚ :=
    Submodule.span_le.mpr (fun x hx => Submodule.subset_span hx)
  apply subset_antisymm (closure_mono hrat)
  exact (Submodule.span ℝ S).topologicalClosure_minimal hreal isClosed_closure

lemma card_rat_span_le {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) :
    Cardinal.mk (Submodule.span ℚ S) ≤ max (Cardinal.mk S) Cardinal.aleph0 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  · let : Nonempty S := hS.to_subtype
    rw [Finsupp.span_eq_range_linearCombination]
    change Cardinal.mk (Set.range (Finsupp.linearCombination ℚ (fun x : S => (x : E)))) ≤ _
    exact Cardinal.mk_range_le.trans_eq (by simp)

end SeparableQuotient.Positive.Family

end

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal
universe u

namespace SeparableQuotient.Positive.Family

lemma large_separated_away_small_closure {E : Type u} [MetricSpace E]
    {κ : Cardinal.{u}} {S A : Set E} {δ : ℝ} (hδ : 0 < δ)
    (hsep : S.Pairwise (fun x y => δ < dist x y))
    (hS : κ ≤ Cardinal.mk S) (hA : Cardinal.mk A < κ) (hne : A.Nonempty) :
    ∃ y ∈ S, δ / 4 < Metric.infDist y (closure A) := by
  classical
  by_contra! h
  have hc (y : S) : ∃ a : A, dist y.val a.val < δ / 2 := by
    have hy := h y.val y.property
    rw [Metric.infDist_closure] at hy
    obtain ⟨a, ha, hya⟩ := (Metric.infDist_lt_iff hne).mp (show Metric.infDist y.val A < δ / 2 by linarith)
    exact ⟨⟨a, ha⟩, hya⟩
  choose a ha using hc
  have hinj : Function.Injective a := by
    intro y z hyz
    apply Subtype.ext
    by_contra hne'
    have hl := hsep y.property z.property hne'
    have hy := ha y
    have hz := ha z
    rw [← hyz] at hz
    have ht := dist_triangle y.val (a y).val z.val
    rw [dist_comm (a y).val z.val] at ht
    linarith
  exact (not_le_of_gt hA) (hS.trans (Cardinal.mk_le_of_injective hinj))



lemma exists_unit_dual_annihilating {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (M : Submodule ℝ E) (x : E) {r : ℝ}
    (hr : 0 < r) (hdist : r < Metric.infDist x (M : Set E)) :
    ∃ h : StrongDual ℝ E, ‖h‖ = 1 ∧
      (∀ m ∈ M, h m = 0) ∧ r < |h x| := by
  have hqx : r < ‖M.mkQL x‖ := by
    change r < ‖(QuotientAddGroup.mk x : E ⧸ M.toAddSubgroup)‖
    rwa [QuotientAddGroup.norm_mk]
  obtain ⟨g, hg, hgx⟩ := exists_dual_vector ℝ (M.mkQL x) (ne_of_gt (hr.trans hqx))
  let h₀ := g.comp M.mkQL
  have hq : ‖M.mkQL‖ ≤ 1 := by
    apply M.mkQL.opNorm_le_bound (by norm_num)
    intro y
    simpa using Submodule.Quotient.norm_mk_le M y
  have hh₀ : ‖h₀‖ ≤ 1 := by
    exact (g.opNorm_comp_le M.mkQL).trans (by simpa only [hg, one_mul] using hq)
  have hv : h₀ x = ‖M.mkQL x‖ := hgx
  have hx : r < |h₀ x| := by simpa only [hv, abs_of_nonneg (norm_nonneg _)] using hqx
  have hn : 0 < ‖h₀‖ := norm_pos_iff.mpr (by
    intro heq
    have : h₀ x = 0 := by rw [heq]; rfl
    rw [this, abs_zero] at hx
    linarith)
  refine ⟨‖h₀‖⁻¹ • h₀, ?_, ?_, ?_⟩
  · simp only [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  · intro m hm
    have hqm : M.mkQL m = 0 := (Submodule.Quotient.mk_eq_zero M).mpr hm
    simp [h₀, hqm]
  · have hinv : 1 ≤ ‖h₀‖⁻¹ := (one_le_inv₀ hn).mpr hh₀
    simp only [smul_apply, smul_eq_mul, abs_mul,
      abs_inv, abs_of_pos hn]
    exact hx.trans_le (le_mul_of_one_le_left (abs_nonneg _) hinv)

end SeparableQuotient.Positive.Family

end

end

end OAI
