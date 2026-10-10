import OAI.NumberTheory.TwoPoint.Walks.ManyUnlitNumericalWords
import OAI.NumberTheory.TwoPoint.Bounds.WeightedDesignationBound

namespace OAI

/-! The many-unlit estimate for the actual weighted mixed-difference majorants. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem eventually_many_unlit_weighted_words
    (C Cexternal Csingle : ℝ) (hC : 0 ≤ C) (hCe : 0 ≤ Cexternal) (hCs : 0 ≤ Csingle) :
    ∀ᶠ L : ℝ in atTop, ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (R J T S B h : ℕ) (P Q : Finset ℕ)
      (F : Finset (Fin R → SignedStep))
      (label : (Fin R → SignedStep) → Fin R × Fin J → ι)
      (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
      (target : (Fin R → SignedStep) → Fin R × Fin J → Fin B) (base : ι → Fin B)
      (weight G : (Fin R → SignedStep) → (ι → Fin B) → ℝ)
      (cap : (Fin R → SignedStep) → ℝ) (external H : ℝ),
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
      Function.Injective p →
      (∀ w ∈ F, ∀ i ∈ nonsingletonLabels (label w), H ≤ p i) →
      (∀ w ∈ F, ∀ i ∈ univ.image (label w), p i ∈ wordDivisorPrimeSupport (List.ofFn w)) →
      (∀ w ∈ F, ∀ q ∈ wordDivisorPrimeSupport (List.ofFn w), ∃ i, p i = q) →
      (∀ w ∈ F, 0 ≤ cap w) →
      (∀ w ∈ F, ∀ x, 0 ≤ weight w x) →
      (∀ w ∈ F, ∀ x, weight w x ≤ cap w) →
      (∀ w ∈ F, ∀ x, |G w x| ≤ 1) →
      (∀ w ∈ F, ∀ x, weight w x ≠ 0 →
        RetainedMainTests p (univ.image (label w)) h B (List.ofFn w) x) →
      (∀ w ∈ F, cap w * 2 ^ (singletonLabels (label w)).card ≤
        crudeTraceWeight R S (fun i => (w i).padding) L external) →
      (∑ a ∈ largeUnlitCatalog F label L,
        if LitConsistent (nonsingletonSlots (label a.1) \ a.2) (label a.1) (target a.1) then
          designatedReciprocal p (singletonLabels (label a.1))
            (nonsingletonSlots (label a.1) \ a.2) a.2 (label a.1) *
          (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
            (fun x => weight a.1 x * |selectedMixedDifference (singletonLabels (label a.1))
              (singletonTarget (label a.1) (target a.1) base)
              (fun y => G a.1 (forceCoordinates ((nonsingletonSlots (label a.1) \ a.2).image (label a.1))
                (litForcedTarget (nonsingletonSlots (label a.1) \ a.2) (label a.1) (target a.1) base) y)) x|)
        else 0) ≤ Real.exp (-L ^ (101 / 100 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_many_unlit_numerical_words C Cexternal Csingle hC hCe hCs] with L hL hdecay
  intro ι _ _ R J T S B h P Q F label p hp hpB target base weight G cap external H
    hR hRscale hS hextpos hext hslots hT hRpoly hP hQ hactual ht hq htP hqQ hd hpad
    hH hinj hpH hseen hcover hcap hw hwcap hG hretain hcost
  have hHp : 0 < H := (Real.exp_pos _).trans_le hH
  apply le_trans _ (hdecay R J T S ι P Q F label external H
    hR hRscale hS hextpos hext hslots hT hRpoly hP hQ hactual ht hq htP hqQ hd hpad hH)
  apply sum_le_sum
  intro a ha
  have haw : a.1 ∈ F := (mem_sigma.mp ha).1
  have hau : a.2 ⊆ nonsingletonSlots (label a.1) :=
    mem_powerset.mp (mem_filter.mp (mem_sigma.mp ha).2).1
  split_ifs
  · have hb := weighted_designation_bound B h p hinj hp hpB (List.ofFn a.1)
      (label a.1) (target a.1) base a.2 hau H (cap a.1) hHp (hcap a.1 haw)
      (hpH a.1 haw) (hseen a.1 haw) (hcover a.1 haw) (weight a.1) (G a.1)
      (hw a.1 haw) (hwcap a.1 haw) (hG a.1 haw) (hretain a.1 haw)
    rw [designation_sdiff_decidable (fun a b => Classical.propDecidable (a = b))
      (inferInstance : DecidableEq (Fin R × Fin J)) _ _] at hb
    apply hb.trans
    change (cap a.1 * 2 ^ (singletonLabels (label a.1)).card) *
        H⁻¹ ^ designationExtra (label a.1) a.2 *
        (∏ q ∈ wordDivisorPrimeSupport (List.ofFn a.1), (q : ℝ)⁻¹) ≤ _
    calc
      _ = (cap a.1 * 2 ^ (singletonLabels (label a.1)).card) *
          ((∏ q ∈ wordDivisorPrimeSupport (List.ofFn a.1), (q : ℝ)⁻¹) *
            H⁻¹ ^ designationExtra (label a.1) a.2) := by ring
      _ ≤ crudeTraceWeight R S (fun i => (a.1 i).padding) L external *
          ((∏ q ∈ wordDivisorPrimeSupport (List.ofFn a.1), (q : ℝ)⁻¹) *
            H⁻¹ ^ designationExtra (label a.1) a.2) :=
        mul_le_mul_of_nonneg_right (hcost a.1 haw) (by positivity)
      _ = _ := by ring
  · have hc := crudeTraceWeight_nonneg R S (fun i => (a.1 i).padding) L external
      (by linarith) hextpos
    positivity

end TwoPointCorrelations

end OAI
