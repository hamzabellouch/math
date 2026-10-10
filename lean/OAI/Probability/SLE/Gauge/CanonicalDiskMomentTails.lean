import OAI.Probability.SLE.Geometry.CanonicalDiskTails
import OAI.Probability.SLE.Geometry.FiniteLawTailENN

namespace OAI

/-! Summable tails for the exact prescribed moments, obtained from the actual
finite centered laws. The supremum is taken over finite radius levels. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)
  (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
  (h0 : ∀ ω, B 0 ω=0) (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
  (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)

include C hB hc h0 hκ hκ8 F hw hgrowth W hW in
lemma finiteMoment_nat_le_moment (n j : ℕ) :
    Target.finiteMoment κ W n j ≤ Target.moment κ W n := by
  apply ge_of_tendsto (C.finiteMoment_tendsto_moment hB hc h0 hκ hκ8 F hw hgrowth W hW n)
  filter_upwards [eventually_ge_atTop j] with k hk
  exact C.finiteMoment_mono hB hc h0 hκ hκ8 F hw hgrowth W hW n
    (by change (0:ℝ)≤(j:ℝ); exact Nat.cast_nonneg j)
    (by change (0:ℝ)≤(k:ℝ); exact Nat.cast_nonneg k) (Nat.cast_le.mpr hk)

include C hB hc h0 hκ hκ8 F hw hgrowth W hW in
lemma centeredDiskLaw_integrable_pow (ℓ : ℝ) (hℓ : 0≤ℓ) (n : ℕ) :
    Integrable (fun p : ℝ × Ω => C.diskAtRadius p.1 (4*ℓ/κ) p.2 ^ n)
      (centeredDiskLaw P κ B hc (4*ℓ/κ)) := by
  have hu : 0≤4*ℓ/κ := div_nonneg (mul_nonneg (by norm_num) hℓ) hκ.le
  have hm := (C.diskAtRadius_joint_measurable hc F hw _ hu).pow_const n
  have hnonneg : ∀ p : ℝ × Ω, 0≤C.diskAtRadius p.1 (4*ℓ/κ) p.2^n :=
    fun p => pow_nonneg (C.diskAtRadius_nonneg _ _ _) n
  apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Eventually.of_forall hnonneg)).mp
  simp_rw [ENNReal.ofReal_pow (C.diskAtRadius_nonneg _ _ _)]
  rw [C.centeredDiskLaw_moment hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ hℓ n]
  exact ENNReal.ofReal_ne_top

include C hB hc h0 hκ hκ8 F hw hgrowth W hW in
lemma centeredDiskLaw_integral_pow (ℓ : ℝ) (hℓ : 0≤ℓ) (n : ℕ) :
    (∫ p : ℝ × Ω, C.diskAtRadius p.1 (4*ℓ/κ) p.2 ^ n
      ∂centeredDiskLaw P κ B hc (4*ℓ/κ)) = Target.finiteMoment κ W n ℓ := by
  obtain ⟨M,_,hM⟩ := C.uniform_finiteMoment_bound hB hc h0 hκ hκ8 F hw hgrowth W hW n
  apply (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg (fun p => pow_nonneg (C.diskAtRadius_nonneg _ _ _) n))
    (hM ℓ hℓ).1).mp
  rw [ofReal_integral_eq_lintegral_ofReal
    (C.centeredDiskLaw_integrable_pow hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ hℓ n)
    (Eventually.of_forall (fun p => pow_nonneg (C.diskAtRadius_nonneg _ _ _) n))]
  simp_rw [ENNReal.ofReal_pow (C.diskAtRadius_nonneg _ _ _)]
  exact C.centeredDiskLaw_moment hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ hℓ n

def limitingDiskTail (hc : ∀ ω, Continuous (fun t => B t ω)) (b : ℝ) : ℝ≥0∞ :=
  ⨆ j : ℕ, C.centeredDiskTail hc b (4*(j:ℝ)/κ)

include C hB hc h0 hκ hκ8 F hw in
lemma centeredDiskTail_nat_mono (b : ℝ) :
    Monotone (fun j : ℕ => C.centeredDiskTail hc b (4*(j:ℝ)/κ)) := by
  intro i j hij
  apply C.centeredDiskTail_mono hB hc h0 hκ hκ8 F hw b
  · exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg i)) hκ.le
  · exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg j)) hκ.le
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hij) (by norm_num)) hκ.le

include C hB hc h0 hκ hκ8 F hw hgrowth W hW in
lemma limitingDiskTail_batch_bound {n : ℕ} (hn : 1≤n)
    (hm : 0<Target.moment κ W n) :
    (∑' k : ℤ, (Target.multiplicity κ W n k : ℝ≥0∞) *
      C.limitingDiskTail hc (16*MomentBatches.dyadic k)) ≤
        ENNReal.ofReal ((4:ℝ)^n/16^n/(1-(1/2:ℝ)^n)) := by
  let Q := fun j : ℕ => centeredDiskLaw P κ B hc (4*(j:ℝ)/κ)
  let X := fun j : ℕ => fun p : ℝ × Ω => C.diskAtRadius p.1 (4*(j:ℝ)/κ) p.2
  have hQ (j) : IsFiniteMeasure (Q j) := by
    let := centeredDiskLaw_isProbability hB hBm hc hκ hκ8 γ G F hw (4*(j:ℝ)/κ)
      (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg j)) hκ.le)
    infer_instance
  have hX (j) : Measurable (X j) := C.diskAtRadius_joint_measurable hc F hw _
    (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg j)) hκ.le)
  simp_rw [← MomentBatches.copies_eq_target]
  exact MomentBatches.limiting_upper_batch_bound Q hQ X hX
    (fun _ p => C.diskAtRadius_nonneg _ _ _)
    (fun b => C.centeredDiskTail_nat_mono hB hc h0 hκ hκ8 F hw b) hn hm
    (fun j => C.centeredDiskLaw_integrable_pow hB hc h0 hκ hκ8 F hw hgrowth W hW
      j (Nat.cast_nonneg j) n)
    (fun j => (C.centeredDiskLaw_integral_pow hB hc h0 hκ hκ8 F hw hgrowth W hW
      j (Nat.cast_nonneg j) n).trans_le
      (C.finiteMoment_nat_le_moment hB hc h0 hκ hκ8 F hw hgrowth W hW n j))

include C hB hc h0 hκ hκ8 F hw hgrowth W hW in
lemma limitingDiskTail_cleanup_bound :
    (∑' n : ℕ, C.limitingDiskTail hc (16*((n:ℝ)+1))) ≤
      ENNReal.ofReal (Target.moment κ W 1/16) := by
  let Q := fun j : ℕ => centeredDiskLaw P κ B hc (4*(j:ℝ)/κ)
  let X := fun j : ℕ => fun p : ℝ × Ω => C.diskAtRadius p.1 (4*(j:ℝ)/κ) p.2
  have hQ (j) : IsFiniteMeasure (Q j) := by
    let := centeredDiskLaw_isProbability hB hBm hc hκ hκ8 γ G F hw (4*(j:ℝ)/κ)
      (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg j)) hκ.le)
    infer_instance
  have hX (j) : Measurable (X j) := C.diskAtRadius_joint_measurable hc F hw _
    (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg j)) hκ.le)
  apply MomentBatches.limiting_cleanup_tail_bound Q hQ X hX
    (fun _ p => C.diskAtRadius_nonneg _ _ _)
    (fun b => C.centeredDiskTail_nat_mono hB hc h0 hκ hκ8 F hw b)
  · intro j
    simpa only [pow_one] using C.centeredDiskLaw_integrable_pow hB hc h0 hκ hκ8 F hw
      hgrowth W hW j (Nat.cast_nonneg j) 1
  · intro j
    simpa only [pow_one] using
      (C.centeredDiskLaw_integral_pow hB hc h0 hκ hκ8 F hw hgrowth W hW
        j (Nat.cast_nonneg j) 1).trans_le
        (C.finiteMoment_nat_le_moment hB hc h0 hκ hκ8 F hw hgrowth W hW 1 j)

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
