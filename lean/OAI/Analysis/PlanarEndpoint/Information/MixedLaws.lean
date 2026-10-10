import OAI.Analysis.PlanarEndpoint.Information.CountableCompactness
import OAI.Analysis.PlanarEndpoint.Information.FiniteLaws
import OAI.Analysis.PlanarEndpoint.Information.JointLaws
import OAI.Analysis.PlanarEndpoint.Information.Sampling
import OAI.Analysis.PlanarEndpoint.Information.TailBounds

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal Classical
namespace PlanarEndpoint.TransverseInformation

variable {S : Type} [Fintype S] {V Y : ℕ → Type}
  [∀ i, Fintype (V i)] [∀ i, Fintype (Y i)]

def mixedInformationVector (L : ℝ) (a : S → ℝ)
    (v : (i : ℕ) → S → V i) (y : (i : ℕ) → S → Y i)
    (z : ℕ → S → ℝ) (s : S) : (ℕ ⊕ ℕ) → ℝ :=
  Sum.elim (informationVector L a v y s) (fun i => z i s)

def mixedInformationLaw (L : ℝ) (a : S → ℝ) (ha : ∀ s, 0 ≤ a s)
    (ha1 : ∑ s, a s = 1) (v : (i : ℕ) → S → V i) (y : (i : ℕ) → S → Y i)
    (z : ℕ → S → ℝ) : ProbabilityMeasure ((ℕ ⊕ ℕ) → ℝ) :=
  finiteInformationLaw a ha ha1 (mixedInformationVector L a v y z)

lemma mixedInformationLaw_mass_tail_le (L : ℝ) (hL : 1 < L) (a : S → ℝ)
    (ha : ∀ s, 0 ≤ a s) (ha1 : ∑ s, a s = 1)
    (v : (i : ℕ) → S → V i) (y : (i : ℕ) → S → Y i)
    (z : ℕ → S → ℝ) (i : ℕ) (A : ℝ) :
    (mixedInformationLaw L a ha ha1 v y z : Measure ((ℕ ⊕ ℕ) → ℝ))
      {x | A < |x (.inl i)|} ≤ ENNReal.ofReal ((Fintype.card (Y i) : ℝ) * L ^ (-A)) := by
  change (finiteInformationLaw a ha ha1 (mixedInformationVector L a v y z) :
    Measure ((ℕ ⊕ ℕ) → ℝ)) _ ≤ _
  rw [finiteInformationLaw_apply a ha ha1 (mixedInformationVector L a v y z)
    {x | A < |x (.inl i)|}
    (isOpen_lt continuous_const (continuous_apply (Sum.inl i : ℕ ⊕ ℕ)).abs).measurableSet]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = ∑ s, if A < sampledInformation L a (v i) (y i) s then a s else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      change (if A < |sampledInformation L a (v i) (y i) s| then a s else 0) = _
      rw [abs_of_nonneg (sampledInformation_nonneg a ha (v i) (y i) hL s)]
    _ ≤ _ := sampledInformation_mass_tail_le a ha ha1 (v i) (y i) hL

omit [∀ index, Fintype (V index)] in
lemma mixedInformationLaw_aux_tail_zero (L : ℝ) (a : S → ℝ)
    (ha : ∀ s, 0 ≤ a s) (ha1 : ∑ s, a s = 1)
    (v : (i : ℕ) → S → V i) (y : (i : ℕ) → S → Y i)
    (z : ℕ → S → ℝ) (i : ℕ) {D : ℝ} (hz : ∀ s, |z i s| ≤ D) :
    (mixedInformationLaw L a ha ha1 v y z : Measure ((ℕ ⊕ ℕ) → ℝ))
      {x | D < |x (.inr i)|} = 0 := by
  change (finiteInformationLaw a ha ha1 (mixedInformationVector L a v y z) :
    Measure ((ℕ ⊕ ℕ) → ℝ)) _ = _
  rw [finiteInformationLaw_apply a ha ha1 (mixedInformationVector L a v y z)
    {x | D < |x (.inr i)|}
    (isOpen_lt continuous_const (continuous_apply (Sum.inr i : ℕ ⊕ ℕ)).abs).measurableSet]
  have hzero : (∑ s, if D < |z i s| then a s else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    rw [ite_eq_right (not_lt_of_ge (hz s))]
  change ENNReal.ofReal (∑ sample, if D < |z i sample| then a sample else 0) = 0
  rw [hzero, ENNReal.ofReal_zero]

section Varying
variable {S' : ℕ → Type} [∀ n, Fintype (S' n)] {V' Y' : ℕ → ℕ → Type}
  [∀ n i, Fintype (V' n i)] [∀ n i, Fintype (Y' n i)]
  (L : ℕ → ℝ) (a : (n : ℕ) → S' n → ℝ)
  (ha : ∀ n s, 0 ≤ a n s) (ha1 : ∀ n, ∑ s, a n s = 1)
  (v : (n i : ℕ) → S' n → V' n i) (y : (n i : ℕ) → S' n → Y' n i)
  (z : (n : ℕ) → ℕ → S' n → ℝ)

def mixedInformationLaws (n : ℕ) : ProbabilityMeasure ((ℕ ⊕ ℕ) → ℝ) :=
  mixedInformationLaw (L n) (a n) (ha n) (ha1 n) (v n) (y n) (z n)

theorem exists_mixed_information_limit (hL : ∀ n, 2 ≤ L n)
    (C D : ℕ → ℝ) (hcard : ∀ n i, (Fintype.card (Y' n i) : ℝ) ≤ (L n) ^ (C i))
    (hz : ∀ n i s, |z n i s| ≤ D i) :
    ∃ μ : ProbabilityMeasure ((ℕ ⊕ ℕ) → ℝ), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto ((mixedInformationLaws L a ha ha1 v y z) ∘ φ)
        atTop (𝓝 μ) := by
  apply exists_joint_weak_limit_countable
  intro j ε hε
  cases j with
  | inl i =>
    have ht : Tendsto (fun A : ℝ => ENNReal.ofReal ((2 : ℝ) ^ (C i-A))) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero] using
        ENNReal.tendsto_ofReal (polynomial_alphabet_mass_envelope_tendsto_zero (C i))
    obtain ⟨R, hRC, hRε⟩ := ((eventually_ge_atTop (C i)).and
      (ht.eventually (gt_mem_nhds hε))).exists
    refine ⟨R, fun n => ?_⟩
    exact ((mixedInformationLaw_mass_tail_le (L n) (by linarith [hL n]) (a n)
      (ha n) (ha1 n) (v n) (y n) (z n) i R).trans
        (ENNReal.ofReal_le_ofReal (polynomial_alphabet_mass_bound (hL n) (hcard n i) hRC))).trans hRε.le
  | inr i =>
    refine ⟨D i, fun n => ?_⟩
    change (mixedInformationLaw (L n) (a n) (ha n) (ha1 n) (v n) (y n) (z n) :
      Measure ((ℕ ⊕ ℕ) → ℝ)) _ ≤ ε
    rw [mixedInformationLaw_aux_tail_zero (L n) (a n) (ha n) (ha1 n) (v n) (y n) (z n) i (hz n i)]
    exact bot_le

end Varying
end PlanarEndpoint.TransverseInformation
end

end OAI
