import OAI.NumberTheory.JointDickman.Amplification.SingularSeriesTruncation
import OAI.NumberTheory.JointDickman.Probability.HistogramScaleDecay

namespace OAI

/-! # Summing the actual retained-denominator error weights -/

namespace JointDickman
open Finset Filter
open scoped Topology ArithmeticFunction.Moebius

theorem sum_positiveDenominators_Icc {E : Type*} [AddCommMonoid E] (Q : ℕ)
    (f : ℕ → E) :
    (∑ q ∈ positiveDenominators Q, f (q : ℕ)) = ∑ q ∈ Icc 1 Q, f q := by
  classical
  calc
    _ = ∑ q ∈ (range (Q+1)).filter (fun n => 0 < n), f q := sum_subtype_eq_sum_filter f
    _ = _ := by congr 1; ext n; simp; omega

noncomputable def retainedErrorSum (B j Q : ℕ) (E : ℕ+ → ℂ) : ℂ :=
  ((B : ℂ)/j)*∑ q ∈ positiveDenominators Q, ((μ (q : ℕ) : ℂ)/(q : ℕ).totient)*E q

theorem retainedErrorSum_bound (B j Q : ℕ) (E : ℕ+ → ℂ)
    {A : ℝ} (_hA : 0 ≤ A)
    (hE : ∀ q ∈ positiveDenominators Q,
      ‖E q‖ ≤ ((j*(q : ℕ) : ℕ)/(Nat.totient (j*(q : ℕ)) : ℝ))*A) :
    ‖retainedErrorSum B j Q E‖ ≤ ((B : ℝ)/j)*kernelDenominatorSum j Q*A := by
  have hw (q : ℕ+) : ‖(μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ)‖ ≤ 1/((q : ℕ).totient : ℝ) := by
    rw [norm_div,Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := (q : ℕ))
  have hs : (∑ q ∈ positiveDenominators Q, ‖((μ (q : ℕ) : ℂ)/(q : ℕ).totient)*E q‖) ≤
      kernelDenominatorSum j Q*A := by
    calc
      _ ≤ ∑ q ∈ positiveDenominators Q,
          (1/((q : ℕ).totient : ℝ))*(((j*(q : ℕ) : ℕ)/(Nat.totient (j*(q : ℕ)) : ℝ))*A) := by
        apply sum_le_sum
        intro q hq
        rw [norm_mul]
        exact mul_le_mul (hw q) (hE q hq) (norm_nonneg _) (by positivity)
      _ = kernelDenominatorSum j Q*A := by
        simp_rw [← mul_assoc]
        rw [← sum_mul,sum_positiveDenominators_Icc Q
          (fun n : ℕ => (1/(n.totient : ℝ))*((j*n : ℕ)/(Nat.totient (j*n) : ℝ)))]
        rfl
  unfold retainedErrorSum
  rw [norm_mul,norm_div,Complex.norm_natCast,Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans hs) (by positivity)).trans_eq (by ring)

theorem retainedErrorSum_vanishing
    (hMP : PublishedInputs.PrimeProductMertensInput) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ j Q : ℕ, 0 < j → 0 < Q → j*Q ≤ B^15 →
      ∀ T C : ℝ, 0 ≤ T → 0 ≤ C → η*T ≤ j → ∀ E : ℕ+ → ℂ,
      (∀ q ∈ positiveDenominators Q,
        ‖E q‖ ≤ ((j*(q : ℕ) : ℕ)/(Nat.totient (j*(q : ℕ)) : ℝ))*(C/B)*
          ((B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ)))) →
      T*‖retainedErrorSum B j Q E‖ ≤ C*ε B := by
  obtain ⟨ε,hε,he⟩ := histogram_residue_denominator_decay hMP hη
  refine ⟨ε,hε,?_⟩
  intro m hm
  filter_upwards [he m hm,eventually_ge_atTop 1] with B hb hB
  intro j Q hj hQ hscale T C hT hC hlag E hE
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlocal : ∀ q ∈ positiveDenominators Q,
      ‖E q‖ ≤ ((j*(q : ℕ) : ℕ)/(Nat.totient (j*(q : ℕ)) : ℝ))*
        ((C/B)*((B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ)))) := by
    intro q hq
    exact (hE q hq).trans_eq (by ring)
  have hbound := retainedErrorSum_bound B j Q E
    (show 0 ≤ (C/B)*((B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ))) by
      unfold channelMesh; positivity) hlocal
  calc
    _ ≤ T*(((B : ℝ)/j)*kernelDenominatorSum j Q*
        ((C/B)*((B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ))))) :=
      mul_le_mul_of_nonneg_left hbound hT
    _ = C*((T/j)*kernelDenominatorSum j Q*
        ((B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ)))) := by
      field_simp
    _ ≤ C*ε B := mul_le_mul_of_nonneg_left (hb j Q T hj hQ hT hlag hscale) hC

end JointDickman

end OAI
