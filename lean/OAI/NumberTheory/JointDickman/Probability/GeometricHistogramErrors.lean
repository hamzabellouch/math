import OAI.NumberTheory.JointDickman.Amplification.SummedLocalErrors
import OAI.NumberTheory.JointDickman.Probability.CoarseKernelComparison

namespace OAI

/-! # The summed fine-histogram and residue losses in geometric boxes -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def geometricHistogramWindow (m B : ℕ) (t L U : ℝ) (k : ℤ) :
    Finset (Fin (channelFineCount m B)) :=
  histogramWindowCells (channelFineCount m B) (((k : ℝ)*t+L)/B) (((k : ℝ)*t+U)/B)

theorem geometric_histogram_error_sum
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ q : ℕ, [NeZero q] → q ≤ B →
      ∀ t L U : ℝ, 0 < t → L ≤ U → ∀ S : Finset ℤ,
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      ∀ M₁ M₂ L₁ L₂ : ℝ, 0 ≤ M₁ → 0 ≤ M₂ → 0 ≤ L₁ → 0 ≤ L₂ →
      let A := fun k => manuscriptAmplitudeEnergy m B q (geometricHistogramWindow m B t L U k)
      let R := fun k => manuscriptResidueEnergy m B q (geometricHistogramWindow m B t L U k) g
      let T := fun k => manuscriptResidueEnergy m B q (geometricHistogramWindow m B t L U k) h
      (∑ k ∈ S, (2*A k*channelMesh (channelFineCount m B)*(L₁*M₂+M₁*L₂)+
        M₁*M₂*(Real.sqrt (R k)*Real.sqrt (A k)+Real.sqrt (A k)*Real.sqrt (T k)))) ≤
      ((q : ℝ)/(q.totient : ℝ))*((U-L+2)/B)*C*((1+U-L)/t+1)*
        (2*channelMesh (channelFineCount m B)*(L₁*M₂+M₁*L₂)+
          2*M₁*M₂*(B : ℝ)^(-(1/80 : ℝ))) := by
  obtain ⟨C₁,hC₁,hamp⟩ := manuscript_geometric_box_energy hSD hSW hM hMP
  obtain ⟨C₂,hC₂,hres⟩ := manuscript_geometric_residue_energy hSD hSW hM hMP
  refine ⟨C₁+C₂,by positivity,?_⟩
  intro m hm
  filter_upwards [hamp m hm,hres m hm,eventually_ge_atTop 1] with B ha hr hB
  intro q _ hq t L U ht hLU S g h hg hh M₁ M₂ L₁ L₂ hM₁ hM₂ hL₁ hL₂
  dsimp only
  let A := fun k => manuscriptAmplitudeEnergy m B q (geometricHistogramWindow m B t L U k)
  let R := fun k => manuscriptResidueEnergy m B q (geometricHistogramWindow m B t L U k) g
  let T := fun k => manuscriptResidueEnergy m B q (geometricHistogramWindow m B t L U k) h
  let P := ((q : ℝ)/(q.totient : ℝ))*((U-L+2)/B)*((1+U-L)/t+1)
  let D := P*(C₁+C₂)
  let r := (B : ℝ)^(-(1/40 : ℝ))
  have hBpos : 0 < B := by omega
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hP : 0 ≤ P := by
    dsimp [P]
    have : 0 ≤ U-L+2 := by linarith
    have : 0 ≤ 1+U-L := by linarith
    positivity
  have hD : 0 ≤ D := mul_nonneg hP (by positivity)
  have hA : ∀ k ∈ S, 0 ≤ A k := fun k _ => manuscriptAmplitudeEnergy_nonneg hm hBpos _
  have hR : ∀ k ∈ S, 0 ≤ R k := fun k _ => manuscriptResidueEnergy_nonneg hm hBpos _ g
  have hT : ∀ k ∈ S, 0 ≤ T k := fun k _ => manuscriptResidueEnergy_nonneg hm hBpos _ h
  have hAt : ∑ k ∈ S, A k ≤ D := by
    have ha' : (∑ k ∈ S, A k) ≤ P*C₁ := (ha q hq t L U ht hLU S).trans_eq (by dsimp [P,A,geometricHistogramWindow]; ring)
    exact ha'.trans (mul_le_mul_of_nonneg_left (by linarith) hP)
  have hRt : ∑ k ∈ S, R k ≤ D*r := by
    have he := hr q hq t L U ht hLU S g
    have he' : (∑ k ∈ S, R k) ≤ P*C₂*r*(∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x^2) :=
      he.trans_eq (by dsimp [R,P,r,geometricHistogramWindow]; ring)
    calc
      _ ≤ P*C₂*r := (he'.trans (mul_le_mul_of_nonneg_left (fullPrimeMass_unit_energy B g hg) (by dsimp [r]; positivity))).trans_eq (mul_one _)
      _ ≤ D*r := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hP) (by dsimp [r]; positivity)
  have hTt : ∑ k ∈ S, T k ≤ D*r := by
    have he := hr q hq t L U ht hLU S h
    have he' : (∑ k ∈ S, T k) ≤ P*C₂*r*(∑ x, fullPrimeMass (auxiliaryPrimes B) x*h x^2) :=
      he.trans_eq (by dsimp [T,P,r,geometricHistogramWindow]; ring)
    calc
      _ ≤ P*C₂*r := (he'.trans (mul_le_mul_of_nonneg_left (fullPrimeMass_unit_energy B h hh) (by dsimp [r]; positivity))).trans_eq (mul_one _)
      _ ≤ D*r := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hP) (by dsimp [r]; positivity)
  have hsR : (∑ k ∈ S, Real.sqrt (R k)*Real.sqrt (A k)) ≤ D*Real.sqrt r := by
    simpa only [mul_comm] using sum_sqrt_product_of_totals S A R hA hR hD hAt hRt
  have hsT := sum_sqrt_product_of_totals S A T hA hT hD hAt hTt
  have hsqrt : Real.sqrt r = (B : ℝ)^(-(1/80 : ℝ)) := by
    dsimp [r]
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hB0.le]
    norm_num
  calc
    _ = (2*channelMesh (channelFineCount m B)*(L₁*M₂+M₁*L₂))*(∑ k ∈ S, A k)+
        M₁*M₂*((∑ k ∈ S, Real.sqrt (R k)*Real.sqrt (A k))+
          (∑ k ∈ S, Real.sqrt (A k)*Real.sqrt (T k))) := by
      simp only [mul_sum,sum_add_distrib]
      apply congrArg₂ (· + ·)
      · apply sum_congr rfl
        intro k _
        ring
      · simp only [A,R,T,mul_sum,sum_add_distrib,mul_add]
    _ ≤ (2*channelMesh (channelFineCount m B)*(L₁*M₂+M₁*L₂))*D+
        M₁*M₂*(D*Real.sqrt r+D*Real.sqrt r) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hAt (by unfold channelMesh; positivity))
        (mul_le_mul_of_nonneg_left (add_le_add hsR hsT) (mul_nonneg hM₁ hM₂))
    _ = _ := by rw [hsqrt]; dsimp [D,P]; ring

end JointDickman

end OAI
