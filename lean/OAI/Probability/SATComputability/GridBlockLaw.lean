import OAI.Probability.SATComputability.ClauseProcess

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

local instance gridBlockCandidateMeasurable (n : ℕ) :
    MeasurableSpace (DeletionCandidate n) := ⊤
local instance gridBlockCandidateSingleton (n : ℕ) :
    MeasurableSingletonClass (DeletionCandidate n) := ⟨fun _ => trivial⟩

theorem gridMaskLaw_pi_of_expect {A : Type*} [Fintype A] {n M : ℕ}
    (r : ℝ≥0) (mask : A → Finset (DeletionCandidate n))
    (Q : FiniteLaw (Finset (DeletionCandidate n)))
    (hQ : ∀ f, Q.expect f = ∫ c, f (countsMask mask c) ∂poissonCountLaw A r) :
    gridMaskLaw M r mask = FiniteLaw.pi (fun _ : Fin M => Q) := by
  classical
  let μ := poissonCountLaw A r
  have hsingle : finitePushforward μ (countsMask mask) (measurable_of_countable _) = Q := by
    apply finiteLaw_eq_of_expect
    intro f
    rw [finitePushforward_expect]
    exact (hQ f).symm
  apply finiteLaw_eq_of_expect
  intro f
  rw [gridMaskLaw_expect]
  have htranspose := poissonCountLaw_equiv (Equiv.prodComm (Fin M) A) r
    (fun c => f (maskGrid mask c))
  rw [← htranspose, ← poissonCountLaw_uncurry_integral]
  change (∫ c : Fin M → A → ℕ, f (fun j => countsMask mask (c j))
    ∂Measure.pi (fun _ : Fin M => μ)) = _
  rw [← finitePushforward_expect (Measure.pi (fun _ : Fin M => μ))
    (fun c j => countsMask mask (c j))
    (Measurable.of_eval (fun j => (measurable_of_countable (countsMask mask)).comp
      (measurable_pi_apply j))) f,
    finitePushforward_pi _ _ (fun _ => measurable_of_countable _)]
  simp only [hsingle]

theorem gridMaskLaw_equiv {A B : Type} [Fintype A] [Fintype B] {n M : ℕ}
    (e : A ≃ B) (r : ℝ≥0) (mask : B → Finset (DeletionCandidate n)) :
    gridMaskLaw M r (mask ∘ e) = gridMaskLaw M r mask := by
  apply finiteLaw_eq_of_expect
  intro f
  simp only [gridMaskLaw_expect]
  have he (c : A × Fin M → ℕ) :
      maskGrid (mask ∘ e) c = maskGrid mask (c ∘ (e.prodCongr (Equiv.refl (Fin M))).symm) := by
    funext j
    exact countsMask_equiv e mask (fun a => c (a,j))
  simp only [he]
  simpa only [Function.comp_def] using
    poissonCountLaw_equiv (e.prodCongr (Equiv.refl (Fin M))) r (fun c => f (maskGrid mask c))

theorem gridMaskLaw_clauses {n : ℕ} [NeZero n] (M k : ℕ) (r : ℝ≥0) :
    gridMaskLaw M r (clauseMask (n := n) (k := k)) =
      FiniteLaw.pi (fun _ : Fin M => candidateBlock
        (r*Fintype.card (Fin k → SignedLiteral n)) k Finset.univ) := by
  apply gridMaskLaw_pi_of_expect
  intro f
  rw [candidateBlock_counts]
  simp only [mul_div_cancel_right₀ _ (show
    (Fintype.card (Fin k → SignedLiteral n) : ℝ≥0) ≠ 0 by
      exact_mod_cast Fintype.card_ne_zero)]
  rfl

end FixedClauseThreshold.Computability

end OAI
