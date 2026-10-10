import OAI.Analysis.FreeEntropy.EntropyIntegral

namespace OAI

universe u1

noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set
namespace FiniteEntropySeparation

 theorem lintegral_ofReal_finite {α : Type u1} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Integrable f μ) : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) < ∞ :=
  (lintegral_ofReal_le_lintegral_enorm _).trans_lt hf.hasFiniteIntegral

 theorem reciprocal_posPart_finite {n a : ℝ} (ha : 0 < a) :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (n/(1+s)) - ENNReal.ofReal (n/(a+s))) < ∞ := by
  have hh := lintegral_ofReal_finite ((reciprocalDifference_integrable ha).const_mul n)
  apply lt_of_le_of_lt _ hh
  apply setLIntegral_mono' measurableSet_Ioi
  intro s hs
  have hs : 0 < s := hs
  by_cases hn : 0 ≤ n
  · rw [← ENNReal.ofReal_sub _ (div_nonneg hn (by linarith : 0 ≤ a+s))]
    apply le_of_eq
    congr 1
    simp [reciprocalDifference, mul_sub, div_eq_mul_inv]
  · have hz : n / (1+s) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hn) (by linarith)
    rw [ENNReal.ofReal_of_nonpos hz, zero_tsub]
    exact bot_le

 theorem reciprocal_negPart_finite {n a : ℝ} (ha : 0 < a) :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (n/(a+s)) - ENNReal.ofReal (n/(1+s))) < ∞ := by
  have hh := lintegral_ofReal_finite (((reciprocalDifference_integrable ha).const_mul n).neg)
  apply lt_of_le_of_lt _ hh
  apply setLIntegral_mono' measurableSet_Ioi
  intro s hs
  have hs : 0 < s := hs
  by_cases hn : 0 ≤ n
  · rw [← ENNReal.ofReal_sub _ (div_nonneg hn (by linarith : 0 ≤ 1+s))]
    apply le_of_eq
    congr 1
    simp [reciprocalDifference, mul_sub, div_eq_mul_inv]
  · have hz : n / (a+s) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hn) (by linarith)
    rw [ENNReal.ofReal_of_nonpos hz, zero_tsub]
    exact bot_le

 theorem entropy_parts_finite {f : ℝ → ℝ≥0∞} {n a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hl : ∀ s, 0 < s → ENNReal.ofReal (n/(b+s)) ≤ f s)
    (hu : ∀ s, 0 < s → f s ≤ ENNReal.ofReal (n/(a+s))) :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (n/(1+s)) - f s) < ∞ ∧
    (∫⁻ s in Ioi (0 : ℝ), f s - ENNReal.ofReal (n/(1+s))) < ∞ := by
  constructor
  · apply lt_of_le_of_lt _ (reciprocal_posPart_finite (n := n) hb)
    exact setLIntegral_mono' measurableSet_Ioi (fun s hs => tsub_le_tsub_left (hl s hs) _)
  · apply lt_of_le_of_lt _ (reciprocal_negPart_finite (n := n) ha)
    exact setLIntegral_mono' measurableSet_Ioi (fun s hs => tsub_le_tsub_right (hu s hs) _)

 theorem finite_entropy_expression (c : ℝ) {P N : ℝ≥0∞} (hP : P < ∞) (hN : N < ∞) :
    ∃ r : ℝ, (c : EReal) + (1/2 : EReal) * P.toEReal - (1/2 : EReal) * N.toEReal = r := by
  refine ⟨c + (1/2 : ℝ) * P.toReal - (1/2 : ℝ) * N.toReal, ?_⟩
  rw [← EReal.coe_ennreal_toReal hP.ne, ← EReal.coe_ennreal_toReal hN.ne]
  norm_cast

namespace Model
 theorem chiStar_real (p : ℕ) [NeZero p] (hp : 2 ≤ p) (h : ℝ) (hh : 0 < h) :
    ∃ r : ℝ, chiStar (τ p) (X p h) (auxiliaryNoise p) = r := by
  have hb : 0 < h+4 := by linarith
  have hf := entropy_parts_finite (f := fun s => freeFisher (τ p) (doublyNoised p h s))
    (n := (p+1 : ℕ)) hh hb
    (fun s hs => by simpa [add_assoc, add_comm, add_left_comm] using
      doublyNoised_fisher_lower p hp h s hh.le hs.le (by linarith))
    (fun s hs => doublyNoised_fisher_le p h s hh.le hs.le (by linarith))
  exact finite_entropy_expression _ hf.1 hf.2

 theorem chiStar_finite (p : ℕ) [NeZero p] (hp : 2 ≤ p) (h : ℝ) (hh : 0 < h) :
    (⊥ : EReal) < chiStar (τ p) (X p h) (auxiliaryNoise p) ∧
    chiStar (τ p) (X p h) (auxiliaryNoise p) < ⊤ := by
  obtain ⟨r,hr⟩ := chiStar_real p hp h hh
  rw [hr]
  exact ⟨EReal.bot_lt_coe r, EReal.coe_lt_top r⟩
end Model
end FiniteEntropySeparation

end

end OAI
