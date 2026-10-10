import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourcePolyDivTendsto
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FixedIsTagged

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical Filter
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

def usedPrimeReciprocal (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) : ℝ :=
  ∏ p : S.Index, if UsedPrime w 𝔏 p then (p : ℝ)⁻¹ else 1

lemma usedPrimeReciprocal_nonneg (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) :
    0 ≤ usedPrimeReciprocal w 𝔏 := by
  unfold usedPrimeReciprocal
  positivity

def traceIntegrationMajorant (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (R : AssignedRecord S ℓ) (T err : ℝ) : ℝ :=
  chargeConstant (S := S) w T (recordU w R.1) *
    Real.exp (-S.harmonicCore * bandDefect w betaC - S.harmonicCenter * bandDefect w betaZ +
      S.harmonicCore * betaC * (Real.exp kappa - 1) * (recordU w R.1).card + err) *
      usedPrimeReciprocal w 𝔏 * ∏ p : S.Index, recordTreeWeight w hh 𝔏 R p

lemma traceIntegrationMajorant_nonneg (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (R : AssignedRecord S ℓ) (T err : ℝ) :
    0 ≤ traceIntegrationMajorant w hh 𝔏 R T err := by
  unfold traceIntegrationMajorant chargeConstant
  exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    (usedPrimeReciprocal_nonneg w 𝔏)) (prod_nonneg (fun p _ => recordTreeWeight_nonneg w hh 𝔏 R p))

lemma traceIntegrationMajorant_mono (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (R : AssignedRecord S ℓ) (T : ℝ) {e₁ e₂ : ℝ}
    (he : e₁ ≤ e₂) :
    traceIntegrationMajorant w hh 𝔏 R T e₁ ≤ traceIntegrationMajorant w hh 𝔏 R T e₂ := by
  unfold traceIntegrationMajorant
  apply mul_le_mul_of_nonneg_right _ (prod_nonneg (fun p _ => recordTreeWeight_nonneg w hh 𝔏 R p))
  apply mul_le_mul_of_nonneg_right _ (usedPrimeReciprocal_nonneg w 𝔏)
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  linarith

theorem trace_integration_finite (w : ClosedLine h ℓ) (hh : 0 < h)
    {T : ℝ} (cut : S.Cutoffs T) (𝔏 : List (AttachedSpec w D L))
    (R : AssignedRecord S ℓ) (hlarge : ∀ p : S.Index, 2 * (ℓ+1) ≤ (p : ℕ)) :
    assignedKernelIntegral w cut 𝔏 (recordGroup w hh 𝔏 R) ≤
      traceIntegrationMajorant w hh 𝔏 R T (restorationError w 𝔏) := by
  by_cases hex : ∃ a, recordGroup w hh 𝔏 R a
  · obtain ⟨a,ha⟩ := hex
    change recordAt w hh 𝔏 a = R at ha
    subst R
    have hb := assignedKernelIntegral_restored w hh cut 𝔏 (recordAt w hh 𝔏 a).1
      (recordAt_compatible w hh 𝔏 a) (recordGroup w hh 𝔏 (recordAt w hh 𝔏 a))
      (fun b hb p => recordGroup_edges w hh 𝔏 (recordAt w hh 𝔏 a) b hb p) hlarge
    apply hb.trans
    have hp : (∏ p : S.Index, tokenPrimeFactor w 𝔏 (recordAt w hh 𝔏 a).1 p) ≤
        usedPrimeReciprocal w 𝔏 * ∏ p : S.Index, recordTreeWeight w hh 𝔏 (recordAt w hh 𝔏 a) p := by
      rw [usedPrimeReciprocal, ← prod_mul_distrib]
      exact prod_le_prod₀ (fun p _ => tokenPrimeFactor_nonneg w 𝔏 _ p)
        (fun p _ => record_tokenPrimeFactor_le w hh 𝔏 a p)
    simpa only [traceIntegrationMajorant,chargeConstant,mul_assoc] using
      mul_le_mul_of_nonneg_left hp (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  · have hfalse : ∀ a, ¬recordGroup w hh 𝔏 R a := not_exists.mp hex
    have hz : assignedKernelIntegral w cut 𝔏 (recordGroup w hh 𝔏 R) = 0 := by
      simp [assignedKernelIntegral,hfalse,avg]
    rw [hz]
    exact traceIntegrationMajorant_nonneg w hh 𝔏 R T _

theorem trace_integration_source (h : ℕ) (hh : 0 < h) (τ C₀ : ℝ)
    (hτ : 0 ≤ τ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop,
    ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (w : ClosedLine h (sourceLength B)),
    (∀ i, w.label i ∈ D.members) →
    ∀ {T : ℝ} (cut : (sourceSystem B).Cutoffs T)
      (𝔏 : List (AttachedSpec w D (pathLength B))),
    𝔏.length < listCutoff B →
    ∀ R : AssignedRecord (sourceSystem B) (sourceLength B),
    assignedKernelIntegral w cut 𝔏 (recordGroup w hh 𝔏 R) ≤
      traceIntegrationMajorant w hh 𝔏 R T (sourceErrorBound h τ C₀ B) := by
  filter_upwards [source_eventually_large h] with B hB
  intro D w hlabels T cut 𝔏 ht R
  have he := restorationError_source_bound w 𝔏 hlabels hB.1 hC₀ hτ
    (sourceLength_le B (by linarith [hB.1])) (pathLength_le B hB.1)
    ((by exact_mod_cast ht.le : (𝔏.length : ℝ) ≤ (listCutoff B : ℝ)).trans (listCutoff_le B hB.1))
    (fun p => (source_prime_lower B hB.1 p).le)
  exact (trace_integration_finite w hh cut 𝔏 R (fun p => (hB.2 p).1)).trans
    (traceIntegrationMajorant_mono w hh 𝔏 R T he)

lemma assignedKernelIntegral_mono (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (𝔏 : List (AttachedSpec w D L)) (G H : S.FixedResidues w → Prop)
    (hGH : ∀ a, G a → H a) :
    assignedKernelIntegral w cut 𝔏 G ≤ assignedKernelIntegral w cut 𝔏 H := by
  apply avg_mono
  intro a
  by_cases hg : G a
  · simp only [hg,hGH a hg,ite_true,le_refl]
  · simp only [hg,ite_false]
    split_ifs
    · exact abs_nonneg _
    · exact le_refl _

theorem trace_integration_retained (w : ClosedLine h ℓ) (hh : 0 < h)
    {T : ℝ} (cut : S.Cutoffs T) (𝔏 : List (AttachedSpec w D L))
    (R : AssignedRecord S ℓ) (retained : S.FixedResidues w → Prop)
    (hlarge : ∀ p : S.Index, 2 * (ℓ+1) ≤ (p : ℕ)) :
    assignedKernelIntegral w cut 𝔏 (fun a => retained a ∧ recordGroup w hh 𝔏 R a) ≤
      traceIntegrationMajorant w hh 𝔏 R T (restorationError w 𝔏) :=
  (assignedKernelIntegral_mono w cut 𝔏 _ _ (fun _ ha => ha.2)).trans
    (trace_integration_finite w hh cut 𝔏 R hlarge)

theorem source_active_graph_eventually (h : ℕ) (hh : 0 < h) :
    ∀ᶠ B : ℝ in atTop, ∀ (w : ClosedLine h (sourceLength B))
      (p : (sourceSystem B).Index) (a : ZMod (p : ℕ)) (u v : ℤ),
      (edgeGraph w hh (litEdges w p a)).Adj u v ↔
        (edgeGraph w hh w.treeSteps).Adj u v ∧
          a + (u : ZMod (p : ℕ)) = 0 ∧ a + (v : ZMod (p : ℕ)) = 0 := by
  filter_upwards [source_eventually_large h] with B hB
  intro w p a u v
  exact active_graph_exact w hh p (Nat.not_dvd_of_pos_of_lt hh (hB.2 p).2) a u v

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
