import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootCentralizer

namespace OAI

/-!
# Bounded diagonal returns in a root centralizer

A matrix centralizing one root can have entries outside the opposite-root
centralizer only in expanding directions of a suitable diagonal flow.
Bounded conjugates along arbitrarily late times therefore centralize both
roots. This is the matrix step in EKL (2006), Lemma 4.2.
-/

noncomputable section
open Filter Set Matrix MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma eq_zero_of_bounded_exp_mul
    {t : ℕ → ℝ} (ht : Tendsto t atTop atTop)
    {c : ℝ} (hc : 0 < c) (a B : ℝ)
    (hb : ∀ᶠ k in atTop, |Real.exp (c * t k) * a| ≤ B) : a = 0 := by
  by_contra ha
  have ha' : 0 < |a| := abs_pos.mpr ha
  have he := Real.tendsto_exp_atTop.comp (ht.const_mul_atTop hc)
  have hexp : Tendsto (fun k => |Real.exp (c * t k) * a|) atTop atTop := by
    simpa only [abs_mul, abs_of_pos (Real.exp_pos _), Function.comp_apply] using he.atTop_mul_const ha'
  exact (not_isBoundedUnder_of_tendsto_atTop hexp) ⟨B, eventually_map.mpr hb⟩

/-- Each strictly expanding matrix entry must vanish if the conjugates
remain bounded along a sequence of times tending to infinity. -/
lemma conjugation_expanding_entry_eq_zero {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0) (g : G n)
    {t : ℕ → ℝ} (ht : Tendsto t atTop atTop) (B : ℝ)
    (hb : ∀ᶠ k in atTop, ∀ r s,
      |(diagonalOneParameter ell hell (t k) * g *
        diagonalOneParameter ell hell (-t k)).val r s| ≤ B)
    {r s : Fin n} (hrs : ell s < ell r) : g.val r s = 0 := by
  apply eq_zero_of_bounded_exp_mul ht (sub_pos.mpr hrs) _ B
  filter_upwards [hb] with k hk
  simpa only [conjugation_entry] using hk r s

/-- With the two distinguished weights extremal, bounded conjugates in
one root centralizer belong to the common centralizer of opposite roots. -/
theorem rootPairCentralizer_of_bounded_conjugates {n : ℕ}
    {i j : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0)
    (hijw : ell j < ell i)
    (hmiddle : ∀ r, r ≠ i → r ≠ j → ell j < ell r ∧ ell r < ell i)
    (g : G n)
    (hg : g * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * g)
    {t : ℕ → ℝ} (ht : Tendsto t atTop atTop) (B : ℝ)
    (hb : ∀ᶠ k in atTop, ∀ r s,
      |(diagonalOneParameter ell hell (t k) * g *
        diagonalOneParameter ell hell (-t k)).val r s| ≤ B) :
    g ∈ rootPairCentralizer hij := by
  apply (mem_rootPairCentralizer hij g).mpr
  refine ⟨hg, (commutes_root_one_iff hij.symm g).mpr ?_⟩
  have hz {r s : Fin n} (h : ell s < ell r) : g.val r s = 0 :=
    conjugation_expanding_entry_eq_zero ell hell g ht B hb h
  obtain ⟨_, _, hd⟩ := (commutes_root_one_iff hij g).mp hg
  refine ⟨?_, ?_, hd.symm⟩
  · intro r hrj
    by_cases hri : r = i
    · subst r
      exact hz hijw
    · exact hz (hmiddle r hri hrj).1
  · intro s hsi
    by_cases hsj : s = j
    · subst s
      exact hz hijw
    · exact hz (hmiddle s hsi hsj).2

/-- Poincaré recurrence supplies the unbounded sequence needed by the
matrix criterion, even when conjugate bounds hold only on returns to a
measurable set. -/
theorem ae_rootPairCentralizer_of_recurrent_conjugates
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (E : Set Y) (hE : MeasurableSet E)
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0)
    (hijw : ell j < ell i)
    (hmiddle : ∀ r, r ≠ i → r ≠ j → ell j < ell r ∧ ell r < ell i)
    (g : Y → G n)
    (hg : ∀ x ∈ E, g x * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * g x)
    (B : ℝ)
    (hb : ∀ x ∈ E, ∀ k : ℕ, T^[k] x ∈ E → ∀ r s,
      |(diagonalOneParameter ell hell (k : ℝ) * g x *
        diagonalOneParameter ell hell (-(k : ℝ))).val r s| ≤ B) :
    ∀ᵐ x ∂μ, x ∈ E → g x ∈ rootPairCentralizer hij := by
  filter_upwards [hT.conservative.ae_mem_imp_frequently_image_mem hE.nullMeasurableSet]
    with x hx
  intro hxE
  obtain ⟨ns, hns, hret⟩ := extraction_of_frequently_atTop (hx hxE)
  apply rootPairCentralizer_of_bounded_conjugates hij ell hell hijw hmiddle
    (g x) (hg x hxE) (t := fun k => (ns k : ℝ))
    (tendsto_natCast_atTop_atTop.comp hns.tendsto_atTop) B
  exact Filter.Eventually.of_forall (fun k => hb x hxE (ns k) (hret k))

end DukePrimeDegree

end

end OAI
