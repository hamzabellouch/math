import OAI.NumberTheory.DukePrimeDegree.Geometry.SeparatedControlledCuts
import OAI.NumberTheory.DukePrimeDegree.Geometry.ExponentialCutSize

namespace OAI

/-! # Exponential size control for separated covering cuts -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

lemma quotientNetBound_half_le {n : ℕ} (hn : 0 < n) (R : ℝ)
    {s : ℝ} (hs : 0 < s) :
    quotientNetBound n R (s/2) ≤ (2:ℝ)^(n*n)*quotientNetBound n R s := by
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  let A : ℝ := (s/(12*(n:ℝ)))/(4*(n:ℝ)*Real.exp (R+1))
  have hA : 0 < A := by dsimp [A]; positivity
  let D := min (1:ℝ) A
  let E := min (1:ℝ) (A/2)
  have hD : 0 < D := lt_min zero_lt_one hA
  have hE : 0 < E := lt_min zero_lt_one (by positivity)
  have hd : D/2 ≤ E := by
    apply le_min
    · have hh := min_le_left (1:ℝ) A
      dsimp [D]
      linarith
    · exact div_le_div_of_nonneg_right (min_le_right (1:ℝ) A) (by norm_num)
  have hp := pow_le_pow_left₀ (show 0 ≤ D/2 by positivity) hd (n*n)
  have he : ((s/2)/(12*(n:ℝ)))/(4*(n:ℝ)*Real.exp (R+1))=A/2 := by
    dsimp [A]
    ring
  unfold quotientNetBound
  rw [he]
  change (2*Real.exp (R+1)+2)^(n*n)/E^(n*n) ≤
    (2:ℝ)^(n*n)*((2*Real.exp (R+1)+2)^(n*n)/D^(n*n))
  calc
    _ ≤ (2*Real.exp (R+1)+2)^(n*n)/(D/2)^(n*n) :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos (by positivity : 0 < D/2) _) hp
    _ = _ := by rw [div_pow]; field_simp

lemma separatedCut_size_exponential {n : ℕ} (hn : 0 < n)
    {A B R₀ a : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hR₀ : 0 ≤ R₀)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ K > 0, ∃ C ≥ 0, ∀ m : ℕ,
      quotientNetBound n (A*(m:ℝ)+R₀) (Real.log (1+a*Real.exp (-B*(m:ℝ)))/8) *
        (48/Real.log (1+a*Real.exp (-B*(m:ℝ)))) ≤ K*Real.exp (C*(m:ℝ)) := by
  obtain ⟨K,hK,C,hC,hbound⟩ := distanceCut_size_exponential hn hA hB hR₀ ha ha1
  refine ⟨(2:ℝ)^(n*n)*K,by positivity,C,hC,?_⟩
  intro m
  let τ := Real.log (1+a*Real.exp (-B*(m:ℝ)))
  have hτ : 0 < τ := Real.log_pos (by have := Real.exp_pos (-B*(m:ℝ)); nlinarith)
  have hnB := quotientNetBound_half_le hn (A*(m:ℝ)+R₀) (show 0 < τ/4 by positivity)
  have he : τ/4/2=τ/8 := by ring
  rw [he] at hnB
  have hmul := mul_le_mul_of_nonneg_right hnB (show 0 ≤ 48/τ by positivity)
  have h := mul_le_mul_of_nonneg_left (hbound m) (show 0 ≤ (2:ℝ)^(n*n) by positivity)
  change quotientNetBound n (A*(m:ℝ)+R₀) (τ/8)*(48/τ) ≤ _
  calc
    _ ≤ (2:ℝ)^(n*n)*(quotientNetBound n (A*(m:ℝ)+R₀) (τ/4)*(48/τ)) := by
      convert hmul using 1; ring
    _ ≤ (2:ℝ)^(n*n)*(K*Real.exp (C*(m:ℝ))) := h
    _ = _ := by ring

theorem exists_separated_exponential_cut_family {n : ℕ} (hn : 0 < n)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    {A B R₀ a : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hR₀ : 0 ≤ R₀)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    let r := fun m : ℕ => a*Real.exp (-B*(m:ℝ))
    let τ := fun m => Real.log (1+r m)
    ∃ (N : ℕ → ℕ) (z : ∀ m, Fin (N m) → X n) (c : ∀ m, Fin (N m) → ℝ)
      (K C : ℝ), 0 < K ∧ 0 ≤ C ∧ ∀ m,
      ((N m:ℝ≥0∞)*ENNReal.ofReal (48/τ m) ≤
        ENNReal.ofReal (K*Real.exp (C*(m:ℝ)))) ∧
      (∀ i j, i ≠ j → τ m/8 < quotientLogDistance (z m i) (z m j)) ∧
      (∀ i, τ m/3 < c m i ∧ c m i < τ m/2 ∧
        μ {x | quotientLogDistance (z m i) x=c m i}=0 ∧
        ∀ k : ℕ, μ (realBoundaryStrip (quotientLogDistance (z m i)) (c m i) ((1/4:ℝ)^k)) ≤
          ENNReal.ofReal (48/τ m*(1/2:ℝ)^k)) ∧
      (∀ x, quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ A*(m:ℝ)+R₀ →
        ∃ i, quotientLogDistance (z m i) x < c m i) ∧
      ∀ i, ∀ x, quotientLogDistance (z m i) x < c m i →
        ∀ y, quotientLogDistance (z m i) y < c m i →
        ∃ g ∈ matrixBall n (r m), rightAction x g=y := by
  classical
  let r := fun m : ℕ => a*Real.exp (-B*(m:ℝ))
  let τ := fun m => Real.log (1+r m)
  have hr (m : ℕ) : 0 < r m := mul_pos ha (Real.exp_pos _)
  have hr1 (m : ℕ) : r m ≤ 1 := by
    have he : Real.exp (-B*(m:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr
      (by nlinarith [mul_nonneg hB (Nat.cast_nonneg (α := ℝ) m)])
    exact (mul_le_mul_of_nonneg_left he ha.le).trans (by simpa using ha1)
  have hτ (m : ℕ) : 0 < τ m := Real.log_pos (by linarith [hr m])
  have hex (m : ℕ) := exists_separated_controlled_distance_cuts hn μ
    (A*(m:ℝ)+R₀) (r m) (hr m) (hr1 m)
  choose N z c hN hsep hcut hcover hsmall using hex
  obtain ⟨K,hK,C,hC,hsize⟩ := separatedCut_size_exponential hn hA hB hR₀ ha ha1
  refine ⟨N,z,c,K,C,hK,hC,?_⟩
  intro m
  refine ⟨?_,hsep m,hcut m,hcover m,hsmall m⟩
  have hreal : (N m:ℝ)*(48/τ m) ≤ K*Real.exp (C*(m:ℝ)) :=
    (mul_le_mul_of_nonneg_right (hN m)
      (div_nonneg (by norm_num) (hτ m).le)).trans (hsize m)
  have H := ENNReal.ofReal_le_ofReal hreal
  rwa [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast] at H

end DukePrimeDegree

end

end OAI
