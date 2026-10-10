import OAI.NumberTheory.TwoPoint.Bounds.FiniteDesignationSum
import OAI.NumberTheory.TwoPoint.Bounds.CrudeTraceCatalog

namespace OAI

/-! The many-unlit bound for the actual full numerical word catalog. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def largeUnlitCatalog {R J : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (F : Finset (Fin R → SignedStep))
    (label : (Fin R → SignedStep) → Fin R × Fin J → ι) (L : ℝ) :
    Finset (Σ _w : Fin R → SignedStep, Finset (Fin R × Fin J)) :=
  F.sigma (fun w => (nonsingletonSlots (label w)).powerset.filter
    (fun U => L ^ (1 / 50 : ℝ) < (U.card : ℝ)))

noncomputable def designationExtra {τ ι : Type*} [Fintype τ] [Fintype ι] [DecidableEq ι]
    (label : τ → ι) (U : Finset τ) : ℕ :=
  ∑ a ∈ nonsingletonLabels label,
    extraReciprocalExponent (litOccurrences label (designationLit U) a).card
      (unlitOccurrences label (designationLit U) a).card

lemma twice_designationExtra {τ ι : Type*} [Fintype τ] [Fintype ι] [DecidableEq ι]
    (label : τ → ι) (U : Finset τ) (hU : U ⊆ nonsingletonSlots label) :
    U.card ≤ 2 * designationExtra label U :=
  designation_card_le_twice_extra label U hU

/-- All extra reciprocals, including a different exponent for every
word/designation pair, are summed here. No crude-catalog hypothesis remains. -/
theorem eventually_many_unlit_numerical_words (C Cexternal Csingle : ℝ)
    (hC : 0 ≤ C) (hCe : 0 ≤ Cexternal) (hCs : 0 ≤ Csingle) :
    ∀ᶠ L : ℝ in atTop, ∀ (R J T S : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (P Q : Finset ℕ)
      (F : Finset (Fin R → SignedStep))
      (label : (Fin R → SignedStep) → Fin R × Fin J → ι) (external H : ℝ),
      1 ≤ R → (R : ℝ) ≤ 2 * L →
      ((S + R * J : ℕ) : ℝ) ≤ Csingle * L * Real.log L →
      0 ≤ external → external ≤ Real.exp (Cexternal * L) →
      (T : ℝ) ≤ C * R * Real.log L →
      (T : ℝ) + 1 ≤ L ^ (2 : ℕ) → (R : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      primeHarmonicMass P ≤ L ^ (2 : ℕ) → primeHarmonicMass Q ≤ L ^ (2 : ℕ) →
      (∀ w ∈ F, Fintype.card (ActualPrimeSlot w) ≤ T) →
      (∀ w ∈ F, ∀ i, Squarefree (w i).tuple) →
      (∀ w ∈ F, ∀ i, Squarefree (w i).padding) →
      (∀ w ∈ F, ∀ i, (w i).tuple.primeFactors ⊆ P) →
      (∀ w ∈ F, ∀ i, (w i).padding.primeFactors ⊆ Q) →
      (∀ w ∈ F, ∀ i j, Disjoint (w i).tuple.primeFactors (w j).padding.primeFactors) →
      (∀ w ∈ F, ∀ i, ((w i).padding.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (∑ a ∈ largeUnlitCatalog F label L,
        (crudeTraceWeight R S (fun i => (a.1 i).padding) L external *
          ∏ p ∈ wordDivisorPrimeSupport (List.ofFn a.1), (p : ℝ)⁻¹) *
            (H⁻¹) ^ designationExtra (label a.1) a.2) ≤
        Real.exp (-L ^ (101 / 100 : ℝ)) := by
  let K := Cexternal + Csingle + 408 + 14 * C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_many_unlit_finsets K hK] with L hL hlog hdecay
  intro R J T S ι _ _ P Q F label external H hR hRscale hS hextpos hext hslots hT hRpoly
    hP hQ hactual ht hq htP hqQ hd hpad hH
  let weight (w : Fin R → SignedStep) :=
    crudeTraceWeight R S (fun i => (w i).padding) L external *
      ∏ p ∈ wordDivisorPrimeSupport (List.ofFn w), (p : ℝ)⁻¹
  have hw (w : Fin R → SignedStep) : 0 ≤ weight w := by
    exact mul_nonneg
      (crudeTraceWeight_nonneg R S _ L external (by linarith) hextpos) (by positivity)
  apply hdecay _ (largeUnlitCatalog F label L) (fun a => designationExtra (label a.1) a.2)
    H (fun a => weight a.1) (fun a _ => hw a.1) ?_ ?_ hH
  · apply (designation_catalog_weight F _ weight hw).trans
    have hbound := crude_trace_catalog_exp_bound R T (S + R * J) P Q F L C Cexternal Csingle
      external hR hL hlog hRscale hC hCe hS hext hslots hT hRpoly hP hQ
      hactual ht hq htP hqQ hd hpad
    convert hbound using 1
    rw [mul_sum]
    apply sum_congr rfl
    intro w _
    dsimp [weight, crudeTraceWeight]
    simp only [Fintype.card_prod, Fintype.card_fin, pow_add]
    ring
  · intro a ha
    have ha' := (mem_sigma.mp ha).2
    obtain ⟨hU, hlarge⟩ := mem_filter.mp ha'
    have hsub := mem_powerset.mp hU
    have he := twice_designationExtra (label a.1) a.2 hsub
    have he' : (a.2.card : ℝ) ≤ 2 * designationExtra (label a.1) a.2 := by exact_mod_cast he
    exact hlarge.le.trans he'

end TwoPointCorrelations

end OAI
