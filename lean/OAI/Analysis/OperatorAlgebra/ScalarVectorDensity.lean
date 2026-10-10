import OAI.Analysis.OperatorAlgebra.ScalarVectorLp

namespace OAI

/-! Elementary scalar/vector functions detect all vector-valued L² operators. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure ℝ)

omit [CompleteSpace H] in
lemma scalarVectorLp_indicator {s : Set ℝ} (hs : MeasurableSet s) (hμ : μ s ≠ ⊤)
    (x : H) :
    scalarVectorLp μ (indicatorConstLp 2 hs hμ (1 : ℂ)) x = indicatorConstLp 2 hs hμ x := by
  apply Lp.ext
  filter_upwards [scalarVectorLp_ae μ (indicatorConstLp 2 hs hμ (1 : ℂ)) x,
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμ) (c := (1 : ℂ)),
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμ) (c := x)] with t h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  by_cases ht : t ∈ s <;> simp [ht]

omit [CompleteSpace H] in
theorem scalarVectorLp_induction (p : Lp H 2 μ → Prop)
    (hc : IsClosed {f | p f})
    (ha : ∀ f g, p f → p g → p (f + g))
    (he : ∀ f x, p (scalarVectorLp μ f x)) (f : Lp H 2 μ) : p f := by
  refine (Lp.simpleFunc.dense (E := H) (μ := μ) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).induction
    ?_ hc f
  intro g hg
  lift g to Lp.simpleFunc H 2 μ using hg
  induction g using Lp.simpleFunc.induction (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) with
  | indicatorConst x hs hμ =>
      change p (indicatorConstLp 2 hs hμ.ne x)
      rw [← scalarVectorLp_indicator μ hs hμ.ne x]
      exact he _ _
  | add hf hg hfg h₁ h₂ => exact ha _ _ h₁ h₂

omit [CompleteSpace H] in
lemma scalarVectorLp_inner_ext (f g : Lp H 2 μ)
    (h : ∀ a x, inner ℂ f (scalarVectorLp μ a x) = inner ℂ g (scalarVectorLp μ a x)) :
    f = g := by
  apply ext_inner_right ℂ
  intro y
  apply scalarVectorLp_induction μ (fun z => inner ℂ f z = inner ℂ g z)
    (isClosed_eq (by fun_prop) (by fun_prop))
    (fun a b ha hb => by rw [inner_add_right, inner_add_right, ha, hb]) h y

omit [CompleteSpace H] in
lemma scalarVectorLp_operator_ext
    (T R : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (h : ∀ f x g y, inner ℂ (T (scalarVectorLp μ f x)) (scalarVectorLp μ g y) =
      inner ℂ (R (scalarVectorLp μ f x)) (scalarVectorLp μ g y)) : T = R := by
  apply ContinuousLinearMap.ext
  intro z
  apply scalarVectorLp_induction μ (fun z => T z = R z)
    (isClosed_eq T.continuous R.continuous)
    (fun a b ha hb => by simp only [map_add, ha, hb])
    (fun f x => scalarVectorLp_inner_ext μ _ _ (h f x)) z

end WeakPureInfiniteness

end

end OAI
