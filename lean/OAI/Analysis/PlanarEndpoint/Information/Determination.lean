import OAI.Analysis.PlanarEndpoint.Information.Conditioning
import OAI.Analysis.PlanarEndpoint.Information.FiniteLaws
import OAI.Analysis.PlanarEndpoint.Information.FiniteTables
import OAI.Analysis.PlanarEndpoint.Information.Logarithms
import OAI.Analysis.PlanarEndpoint.Information.Sampling

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal Classical
namespace PlanarEndpoint.TransverseInformation

variable {S V Y : Type*} [Fintype S] [Fintype V] [Fintype Y]

omit [Fintype V] [Fintype Y] in
lemma sampledTable_mono {a b : S → ℝ} (hab : ∀ s, a s ≤ b s)
    (v : S → V) (y : S → Y) (c : V) (z : Y) :
    sampledTable a v y c z ≤ sampledTable b v y c z := by
  unfold sampledTable
  apply Finset.sum_le_sum
  intro s _
  split_ifs
  · exact hab s
  · exact le_rfl

omit [Fintype V] [Fintype Y] in
lemma sampledTable_restricted_zero (a : S → ℝ) (v : S → V) (y : S → Y)
    (E : S → Prop) (A : V → Finset Y) (hA : ∀ s, E s → y s ∈ A (v s))
    (b : V) (z : Y) (hz : z ∉ A b) :
    sampledTable (fun s => if E s then a s else 0) v y b z = 0 := by
  unfold sampledTable
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : E s
  · by_cases h : v s = b ∧ y s = z
    · exact (hz (by simpa only [h.1, h.2] using hA s hs)).elim
    · simp [h]
  · simp [hs]

lemma sampled_determination_exception_le (a : S → ℝ) (ha : ∀ s, 0 ≤ a s)
    (ha1 : ∑ s, a s = 1) (v : S → V) (y : S → Y)
    (E : S → Prop) (A : V → Finset Y) (hA : ∀ s, E s → y s ∈ A (v s))
    {M : ℝ} (hcard : ∀ b, ((A b).card : ℝ) ≤ M) {L t : ℝ} (hL : 1 < L) :
    (∑ s, if E s ∧ t < sampledInformation L a v y s then a s else 0) ≤
      M * L ^ (-t) := by
  let e : S → ℝ := fun s => if E s then a s else 0
  have he : ∀ s, 0 ≤ e s := fun s => by dsimp [e]; split_ifs; exact ha s; exact le_rfl
  have hea : ∀ s, e s ≤ a s := fun s => by dsimp [e]; split_ifs; exact le_rfl; exact ha s
  let q := sampledTable a v y
  let r := sampledTable e v y
  have heq : (∑ s, if E s ∧ t < sampledInformation L a v y s then a s else 0) =
      ∑ s, if t < information L (conditionalMass q (v s) (y s)) then e s else 0 := by
    apply Finset.sum_congr rfl
    intro s _
    by_cases hE : E s <;>
      by_cases ht : t < sampledInformation L a v y s <;>
      simp [e, q, sampledInformation] at ht ⊢ <;> simp_all
  rw [heq, ← sampledTable_event_mass e v y (fun b z => t < information L (conditionalMass q b z))]
  calc
    _ ≤ ∑ b, M * L ^ (-t) * rowMass q b := by
      apply Finset.sum_le_sum
      intro b _
      have h := conditional_determination_exception_le (q b) (r b) (A b)
        (sampledTable_nonneg a ha v y b)
        (fun z => ⟨sampledTable_nonneg e he v y b z, sampledTable_mono hea v y b z⟩)
        (fun z hz => sampledTable_restricted_zero a v y E A hA b z hz) hL (γ := t)
      exact h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hcard b) (Real.rpow_nonneg (by linarith) _))
        (rowMass_nonneg q (sampledTable_nonneg a ha v y) b))
    _ = _ := by
      rw [← Finset.mul_sum]
      have ht : (∑ b, rowMass q b) = 1 := by
        change (∑ b, ∑ z, sampledTable a v y b z) = 1
        rw [sampledTable_total, ha1]
      rw [ht, mul_one]

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

lemma finiteInformationLaw_determination_tail (a : S → ℝ) (ha : ∀ s, 0 ≤ a s)
    (ha1 : ∑ s, a s = 1) (v : S → V) (y : S → Y)
    (E : S → Prop) (A : V → Finset Y) (hA : ∀ s, E s → y s ∈ A (v s))
    {M : ℝ} (hcard : ∀ b, ((A b).card : ℝ) ≤ M) {L t : ℝ} (hL : 1 < L)
    (X : S → Ω) {d b : Ω → ℝ} (hd : Continuous d) (hb : Continuous b)
    (hrep : ∀ s, d (X s) = sampledInformation L a v y s ∧
      b (X s) = if E s then 1 else 0) :
    (finiteInformationLaw a ha ha1 X : Measure Ω) ({x | 1/2 < b x} ∩ {x | t < d x}) ≤
      ENNReal.ofReal (M * L ^ (-t)) := by
  rw [finiteInformationLaw_apply a ha ha1 X _
    ((isOpen_lt continuous_const hb).inter (isOpen_lt continuous_const hd)).measurableSet]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = ∑ s, if E s ∧ t < sampledInformation L a v y s then a s else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, (hrep s).1, (hrep s).2]
      by_cases hs : E s <;> norm_num [hs]
    _ ≤ _ := sampled_determination_exception_le a ha ha1 v y E A hA hcard hL

end PlanarEndpoint.TransverseInformation
end

end OAI
