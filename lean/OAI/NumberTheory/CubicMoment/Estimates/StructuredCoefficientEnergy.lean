import OAI.NumberTheory.CubicMoment.Estimates.StructuredSupportBounds
import OAI.NumberTheory.CubicMoment.Estimates.PrimeConvolutionMoments
import OAI.NumberTheory.CubicMoment.Estimates.QuantitativeNoncube
import OAI.NumberTheory.CubicMoment.Estimates.FixedScalePowers

namespace OAI

/-! The coefficient energy needed by the noncube sieve follows from the
actual independent prime weights, including logarithmic weight families. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primeMomentCoefficient_norm_le (W : ι → ℝ → ℂ) (X M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hW : ∀ i x, ‖W i x‖ ≤ M i) (Z : ℝ) (z : Eisenstein) :
    ‖primeMomentCoefficient W X Z z‖ ≤
      ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  by_cases hz : Squarefree z
  · simpa only [primeMomentCoefficient,squarefreeConvolution,ite_eq_left hz] using
      orderedConvolution_norm_bound (coordinatePrimeSupport W X Z)
        (fun i n => W i (norm n/X i)) M (coordinatePrimeSupport_primary W X Z) hM
        (fun i p _ => hW i _) z
  · simpa only [primeMomentCoefficient,squarefreeConvolution,ite_eq_right hz,norm_zero] using
      mul_nonneg (Nat.cast_nonneg ((Fintype.card ι)^(Fintype.card ι)))
        (Finset.prod_nonneg (fun i _ => hM i))

lemma structuredCoefficient_energy_le (W : ι → ℝ → ℂ) (X M : ι → ℝ)
    (hX : ∀ i, 0 < X i) {R : ℝ} (hR : 0 ≤ R)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hM : ∀ i, 0 ≤ M i) (hW : ∀ i x, ‖W i x‖ ≤ M i) (Z : ℝ) :
    (∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Z),
      ‖primeMomentCoefficient W X Z z‖^2) ≤
      18*(R^(Fintype.card ι)*(∏ i, X i))*
        (((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 := by
  let S := orderedConvolutionSupport (coordinatePrimeSupport W X Z)
  have hcard : (S.card:ℝ) ≤ 18*(R^(Fintype.card ι)*(∏ i, X i)) :=
    primary_support_card_le S (mul_nonneg (pow_nonneg hR _)
      (Finset.prod_nonneg (fun i _ => (hX i).le))) (fun z hz =>
      ⟨orderedPrimarySupport_primary (coordinatePrimeSupport W X Z)
        (fun i p hp => (coordinatePrimeSupport_primary W X Z i p hp).1) hz,
        (coordinatePrimeProduct_norm_bounds W X hX hR hlo hhi Z z hz).2⟩)
  calc
    _ ≤ ∑ _z ∈ S, (((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 :=
      Finset.sum_le_sum (fun z _ => pow_le_pow_left₀ (_root_.norm_nonneg _)
        (primeMomentCoefficient_norm_le W X M hM hW Z z) 2)
    _ = (S.card:ℝ)*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)

lemma LogarithmicWeightFamily.subpower_norm {L : γ → ℝ} {W : γ → ℝ → ℂ}
    (h : LogarithmicWeightFamily L W) {s : ℝ} (hs : 0 < s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r x, ‖W r x‖ ≤ M*(L r)^s := by
  obtain ⟨M,hM,hbound⟩ := (h.normalize hs).norm_bound
  refine ⟨M,hM,?_⟩
  intro r x
  have hL : 0 < L r := zero_lt_one.trans_le (h.length_one r)
  have hb : (L r)^(-s)*‖W r x‖ ≤ M := by
    simpa only [normalizedLogWeight,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hL.le _)] using hbound r x
  calc
    _ = (L r)^s*((L r)^(-s)*‖W r x‖) := by
      rw [← mul_assoc,← Real.rpow_add hL]; simp
    _ ≤ (L r)^s*M := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hL.le _)
    _ = _ := mul_comm _ _

/-- Every specified logarithmic family has the actual subpower coefficient
energy required in the nonexceptional character sieve. -/
theorem logarithmic_structured_coefficient_energy {L : γ → ℝ}
    {W : γ → ι → ℝ → ℂ} (hW : LogarithmicWeightFamily
      (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) :
    ∃ T : ℝ, ∀ (r : γ) (X : ι → ℝ) (Z : ℝ), 1 ≤ L r → T ≤ L r →
      (∀ i, 0 < X i) → (∏ i, X i) = L r →
      (∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport (W r) X Z),
        ‖primeMomentCoefficient (W r) X Z z‖^2) ≤ (L r)^(1+ε) := by
  let k : ℕ := Fintype.card ι
  let s := ε/(4*((k:ℝ)+1))
  have hs : 0 < s := by dsimp [s]; positivity
  obtain ⟨M,hM,hbound⟩ := hW.subpower_norm hs
  let C := 18*R^k*((k^k:ℕ)*M^k)^2
  have he : 1+2*s*(k:ℝ) < 1+ε := by
    dsimp [s]
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
    have hd : (0:ℝ) < 4*((k:ℝ)+1) := by positivity
    have hh : s*(4*((k:ℝ)+1)) = ε := div_mul_cancel₀ _ hd.ne'
    nlinarith [mul_nonneg hs.le hk]
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_const_mul_rpow_le he C)
  refine ⟨T,?_⟩
  intro r X Z hL hT' hX hprod
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hb := structuredCoefficient_energy_le (W r) X (fun _ => M*(L r)^s) hX hR
    (hlo r) (hhi r) (fun _ => mul_nonneg hM (Real.rpow_nonneg hLp.le _))
    (fun i x => hbound (r,i) x) Z
  rw [hprod] at hb
  apply hb.trans
  calc
    _ = C*(L r)^(1+2*s*(k:ℝ)) := by
      simp only [Finset.prod_const,Finset.card_univ,mul_pow]
      rw [← Real.rpow_natCast ((L r)^s) k,← Real.rpow_mul hLp.le]
      dsimp [C,k]
      rw [mul_pow,← Real.rpow_natCast ((L r)^(s*(Fintype.card ι:ℝ))) 2,
        ← Real.rpow_mul hLp.le]
      rw [Real.rpow_add hLp,Real.rpow_one]
      have hexp : s*(Fintype.card ι:ℝ)*(2:ℝ) = 2*s*(Fintype.card ι:ℝ) := by ring
      norm_num only [Nat.cast_ofNat]
      rw [hexp]
      ring
    _ ≤ _ := hT (L r) hT'

end CubicFirstMoment

end

end OAI
