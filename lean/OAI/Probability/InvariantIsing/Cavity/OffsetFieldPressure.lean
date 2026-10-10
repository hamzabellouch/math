import OAI.Probability.InvariantIsing.Cavity.OffsetBlockPrior
import OAI.Probability.InvariantIsing.Cavity.CavityAffineCounts
import OAI.Probability.InvariantIsing.Magnetic.RestrictedPressureMean

namespace OAI

/-! Exact field contributions in repeated blocks following a zero-field prefix. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology
namespace InvariantIsing

def offsetBlockField {n : ℕ} (r K : ℕ) (b : Fin n → ℝ) : Fin (r+K*n) → ℝ :=
  Fin.addCases (fun _ => 0) (consecutiveBlockField K b)

lemma fieldEnergy_offset_constraint {n K r : ℕ} (R : Finset (Spin r)) (C : Finset (Spin n))
    (b : Fin n → ℝ) (M : ℝ) (hM : ∀ σ ∈ C, fieldEnergy b σ=M)
    {σ : Spin (r+K*n)} (hσ : σ ∈ offsetBlockConstraint K R C) :
    fieldEnergy (offsetBlockField r K b) σ=(K : ℝ)*M := by
  have hs := (mem_cavityProductSlice R (consecutiveBlockConstraint n K C) σ).mp hσ
  have hh := fieldEnergy_consecutive_constraint C b M hM hs.2
  simpa only [fieldEnergy, offsetBlockField, Fin.sum_univ_add, Fin.addCases_left,
    Fin.addCases_right, zero_mul, Finset.sum_const_zero, zero_add, cavitySpinSplit_right] using hh

lemma offset_field_pressure_lower {n K r : ℕ} (_hN : 0 < r+K*n)
    (R : Finset (Spin r)) (hR : R.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (b : Fin n → ℝ) (M : ℝ) (hM : ∀ σ ∈ C, fieldEnergy b σ=M)
    (eig : Fin (r+K*n) → ℝ) (U : Rotation (r+K*n)) :
    restrictedRotatedPressure (offsetBlockConstraint K R C) eig U (fun _ => 0)+
      (K : ℝ)*M/(r+K*n) ≤ rotatedPressure eig U (offsetBlockField r K b) := by
  have hS := offsetBlockConstraint_nonempty (K := K) R hR C hC
  have hb := restrictedRotatedPressure_le_full (offsetBlockConstraint K R C)
    hS eig U (offsetBlockField r K b)
  have he : restrictedSpinLog (offsetBlockConstraint K R C)
      (fun σ => rotatedEnergy eig U σ+fieldEnergy (offsetBlockField r K b) σ)=
      restrictedSpinLog (offsetBlockConstraint K R C) (fun σ => rotatedEnergy eig U σ)+(K : ℝ)*M := by
    rw [← restrictedSpinLog_add_const _ hS]
    unfold restrictedSpinLog
    congr 2
    apply Finset.sum_congr rfl
    intro σ hσ
    dsimp only
    rw [fieldEnergy_offset_constraint R C b M hM hσ]
  rw [restrictedRotatedPressure, he] at hb
  convert hb using 1
  simp only [restrictedRotatedPressure,fieldEnergy,zero_mul,Finset.sum_const_zero,add_zero]
  simp only [Nat.cast_add,Nat.cast_mul]
  ring

lemma mean_offset_field_pressure_lower {n K r : ℕ} (hN : 0 < r+K*n)
    (μ : Measure (Orthogonal (r+K*n))) [IsProbabilityMeasure μ]
    (R : Finset (Spin r)) (hR : R.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (b : Fin n → ℝ) (M : ℝ) (hM : ∀ σ ∈ C, fieldEnergy b σ=M)
    (eig : Fin (r+K*n) → ℝ) :
    (∫ V, restrictedRotatedPressure (offsetBlockConstraint K R C) eig
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ)+(K : ℝ)*M/(r+K*n) ≤
    ∫ V, rotatedPressure eig (matrixRotation V⁻¹) (offsetBlockField r K b) ∂μ := by
  have hi := integrable_physicalRestrictedPressure hN μ _
    (offsetBlockConstraint_nonempty R hR C hC) eig (fun _ => 0)
  have hf := integrable_physicalPressure hN μ id measurable_id eig (offsetBlockField r K b)
  have hh := integral_mono (hi.add (integrable_const ((K : ℝ)*M/(r+K*n)))) hf
    (fun V => offset_field_pressure_lower hN R hR C hC b M hM eig (matrixRotation V⁻¹))
  simp only [Pi.add_apply,id_eq] at hh
  simpa only [integral_add hi (integrable_const _),integral_const,probReal_univ,one_smul] using hh

lemma offset_field_fraction_tendsto {n : ℕ} (hn : 0 < n) (r q : ℕ) (hq : 0 < q) (F : ℝ) :
    Tendsto (fun j : ℕ => ((q+j : ℕ) : ℝ)*(n : ℝ)*F/(r+(q+j)*n)) atTop (𝓝 F) := by
  have hh := (cavity_affine_ratio_tendsto n 0 n r q hn hq).mul_const F
  have hnz : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [Nat.add_zero, Nat.cast_mul, Nat.cast_add, div_self hnz, one_mul] at hh
  convert hh using 1
  funext j
  simp only [Nat.cast_add]
  ring

end InvariantIsing

end

end OAI
