import OAI.Geometry.SurfaceImmersion.Geometry.JetVariations

namespace OAI

/-! The weighted derivative bounds as actual seminorms on smooth fields
with fixed compact support, for finite derivative-loss parametrix iteration. -/
noncomputable section
open TopologicalSpace
open scoped Distributions NNReal

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev SupportedField (K : Compacts A) := ContDiffMapSupportedIn A F ⊤ K

def supportedWeightedSeminorm (K : Compacts A) (s : ℝ≥0) (m : ℕ) :
    Seminorm ℝ (SupportedField (F := F) K) :=
  (Finset.range (m + 1)).sup fun j =>
    s ^ j • ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j

lemma supportedWeightedSeminorm_component {K : Compacts A} (s : ℝ≥0) (m j : ℕ)
    (hj : j ≤ m) (f : SupportedField (F := F) K) :
    (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤
      supportedWeightedSeminorm K s m f := by
  let q : ℕ → Seminorm ℝ (SupportedField (F := F) K) :=
    fun j => s ^ j • ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j
  have h : q j f ≤ (Finset.range (m + 1)).sup q f :=
    Seminorm.le_finset_sup_apply (show j ∈ Finset.range (m + 1) by simpa using hj)
  simpa only [q, supportedWeightedSeminorm, smul_apply, NNReal.smul_def,
    NNReal.coe_pow, smul_eq_mul] using h

lemma weightedBound_of_supportedSeminorm {K : Compacts A} (s : ℝ≥0) (m : ℕ)
    (f : SupportedField (F := F) K) :
    WeightedBound Set.univ s m (supportedWeightedSeminorm K s m f) f := by
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  calc
    (s : ℝ) ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤
        (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f :=
      mul_le_mul_of_nonneg_left (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ)
        (pow_nonneg s.coe_nonneg _)
    _ ≤ _ := supportedWeightedSeminorm_component s m j hj f

lemma supportedSeminorm_le_of_weightedBound {K : Compacts A} {s : ℝ≥0} (hs : 0 < (s : ℝ))
    {m : ℕ} {C : ℝ} (hC : 0 ≤ C) (f : SupportedField (F := F) K)
    (hb : WeightedBound Set.univ s m C f) : supportedWeightedSeminorm K s m f ≤ C := by
  apply Seminorm.finset_sup_apply_le hC
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  change (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤ C
  have hn : ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤ C / (s : ℝ) ^ j := by
    apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (div_nonneg hC (pow_nonneg s.coe_nonneg _)) j f).2
    intro x _
    simpa only [iteratedFDerivWithin_univ] using hb.deriv_le hs hjm (Set.mem_univ x)
  calc
    _ ≤ (s : ℝ) ^ j * (C / (s : ℝ) ^ j) := mul_le_mul_of_nonneg_left hn (pow_nonneg s.coe_nonneg _)
    _ = C := by field_simp [ne_of_gt hs]

theorem supportedSeminorm_le_iff {K : Compacts A} {s : ℝ≥0} (hs : 0 < (s : ℝ))
    {m : ℕ} {C : ℝ} (hC : 0 ≤ C) (f : SupportedField (F := F) K) :
    supportedWeightedSeminorm K s m f ≤ C ↔ WeightedBound Set.univ s m C f := by
  constructor
  · exact fun h => (weightedBound_of_supportedSeminorm s m f).mono_const h
  · exact supportedSeminorm_le_of_weightedBound hs hC f

end ClosedSurfaceR4.JetPolynomial

end

end OAI
