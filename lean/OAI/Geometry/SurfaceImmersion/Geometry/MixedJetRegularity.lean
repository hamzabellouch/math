import OAI.Geometry.SurfaceImmersion.Correction.MixedJetPolynomial

namespace OAI

/-! Spatial order and smoothness of mixed jet expressions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

def order : MixedExpression → ℕ
  | .coeff _ => 2
  | .atom _ w _ e => max w.length e.order
  | .add e f => max e.order f.order

lemma order_ge_two (e : MixedExpression) : 2 ≤ e.order := by
  induction e with
  | coeff => rfl
  | atom _ _ _ _ ih => exact ih.trans (le_max_right _ _)
  | add _ _ ih _ => exact ih.trans (le_max_left _ _)

lemma order_sumList_le {ι : Type*} (l : List ι) (f : ι → MixedExpression) (N : ℕ)
    (hN : 2 ≤ N) (h : ∀ i ∈ l, (f i).order ≤ N) : (sumList l f).order ≤ N := by
  induction l with
  | nil => exact hN
  | cons i l ih =>
    exact max_le (h i (List.mem_cons_self ..))
      (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

lemma order_differentiate (j : Fin 3) (e : MixedExpression) :
    (e.differentiate j).order ≤ e.order := by
  induction e with
  | coeff c =>
    apply order_sumList_le _ _ 2 (le_refl 2)
    intro i _
    have hl : (lowWord i.1).length ≤ 2 := by
      obtain ⟨i, a⟩ := i
      fin_cases i <;> simp [lowWord]
    exact max_le hl (le_refl 2)
  | atom i w a e ih =>
    by_cases hi : i = 0
    · simp only [differentiate, hi, ↓reduceIte, order]
      omega
    · simp only [differentiate, hi, ↓reduceIte, order]
      omega
  | add e f ihe ihf =>
    simp only [differentiate, order]
    omega

lemma order_ofExpression (e : Expression) : (ofExpression e).order = e.order := by
  induction e with
  | coeff => rfl
  | atom _ _ _ ih => simp only [ofExpression, order, Expression.order, ih]
  | add _ _ ihe ihf => simp only [ofExpression, order, Expression.order, ihe, ihf]

lemma smoothCoeffs_ofExpression {O : Set LowJet} {e : Expression} (he : e.SmoothCoeffs O) :
    (ofExpression e).SmoothCoeffs O := by
  induction e with
  | coeff => exact he
  | atom _ _ _ ih => exact ih he
  | add _ _ ihe ihf => exact ⟨ihe he.1, ihf he.2⟩

theorem eval_smooth {O : Set LowJet} {U : Set Base} {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (hQ : Set.MapsTo (lowJet (G 0)) U O)
    {e : MixedExpression} (he : e.SmoothCoeffs O) :
    ContDiffOn ℝ ∞ (e.eval G) (U ×ˢ Set.univ) := by
  induction e with
  | coeff c =>
    exact he.comp (((lowJet_smooth (hG 0)).comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun z hz => ⟨hQ hz.1, hz.2⟩)
  | atom i w a e ih =>
    exact (((jet_smooth (hG i) w a).comp contDiff_fst).contDiffOn.mul (ih he))
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

lemma parameter_smooth {O : Set LowJet} {U : Set Base} {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (hQ : Set.MapsTo (lowJet (G 0)) U O)
    {e : MixedExpression} (he : e.SmoothCoeffs O) (t : ℝ) :
    ContDiffOn ℝ ∞ (fun p => e.eval G (p, t)) U :=
  (eval_smooth hG hQ he).comp (contDiffOn_id.prodMk contDiffOn_const)
    (fun _ hp => ⟨hp, Set.mem_univ t⟩)

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
