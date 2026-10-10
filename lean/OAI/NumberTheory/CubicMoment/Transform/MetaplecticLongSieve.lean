import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLongDyads
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLogTail

namespace OAI

/-! The canonical finite dyads sum to the actual long inverse completion.
The squared estimate keeps the square of the number of active dyads. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplecticLongDyad_scale {C F : ℝ} (hF : 0 ≤ F) {j : ℕ}
    (hj : j ∈ metaplecticLongDyads C F) : (2:ℝ)^j ≤ F^2 := by
  obtain ⟨e,he,hj'⟩ := Finset.mem_image.mp hj
  have hmem : e ∈ metaplecticLongDyad C F j := Finset.mem_filter.mpr ⟨he,hj'⟩
  exact (metaplecticLongDyad_norm hmem).2.1.trans (metaplecticLongSupport_norm hF he)

lemma metaplectic_long_outer_partition (A : Finset Eisenstein)
    (α : Eisenstein → ℂ) (ℓ : ℤ) (W : Eisenstein → ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hF : B*U ≤ F)
    (hcut : ∀ r ∈ A, ∀ x : ℝ, B < x → W r x = 0) (C : ℝ) :
    (∑ r ∈ A, α r*metaplecticLongCompletion r ℓ (W r) U C F) =
      ∑ j ∈ metaplecticLongDyads C F, ∑ e ∈ metaplecticLongDyad C F j,
        ∑ r ∈ A, α r*metaplecticTailCoefficient r ℓ C F e*
          metaplecticAngularSmoothSum r ℓ (W r) (U/norm e^3) 0 := by
  calc
    _ = ∑ r ∈ A, ∑ j ∈ metaplecticLongDyads C F,
        ∑ e ∈ metaplecticLongDyad C F j, α r*metaplecticTailCoefficient r ℓ C F e*
          metaplecticAngularSmoothSum r ℓ (W r) (U/norm e^3) 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [metaplectic_long_completion_active r ℓ (W r) hU hB hF (hcut r hr) C,
        metaplectic_long_dyad_partition]
      simp only [Finset.mul_sum,mul_assoc]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]

lemma metaplectic_long_cutoff_ratio {C E U : ℝ}
    (hC : 0 < C) (hCE : C ≤ 2*E) (hU : 0 ≤ U) :
    U/E^3 ≤ 8*U/C^3 := by
  have hE : 0 < E := by linarith
  have hCE' : C/2 ≤ E := by linarith
  calc
    _ ≤ U/(C/2)^3 := div_le_div_of_nonneg_left hU (by positivity)
      (pow_le_pow_left₀ (by positivity) hCE' 3)
    _ = _ := by field_simp; ring

lemma metaplectic_long_dyad_power {F E ε : ℝ}
    (hF : 1 ≤ F) (hE : 0 ≤ E) (hEF : E ≤ F^2) (hε : 0 ≤ ε) :
    E^(2*ε) ≤ F^(4*ε) := by
  calc
    _ ≤ (F^2)^(2*ε) := Real.rpow_le_rpow hE hEF (by positivity)
    _ = _ := by
      rw [←Real.rpow_natCast F 2,←Real.rpow_mul (by linarith : 0 ≤ F)]
      congr 1
      ring

theorem LogarithmicWeightFamily.metaplectic_long_sieve
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
    (hW : LogarithmicWeightFamily Y W) {ε s : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1) (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : Eisenstein → γ) (A : Finset Eisenstein)
      (X N U B C F : ℝ), 1 ≤ X → 1 ≤ N → 0 < U → 0 ≤ B →
      0 < C → 1 ≤ F → B*U ≤ F →
      (∀ r ∈ A, primary r ∧ norm r ≤ N) →
      (∀ r ∈ A, Y (w r) ≤ X) →
      (∀ r ∈ A, ∀ x : ℝ, B < x → W (w r) x = 0) →
      ∀ (α : Eisenstein → ℂ) (ℓ : ℤ),
      ‖∑ r ∈ A, α r*metaplecticLongCompletion r ℓ (W (w r)) U C F‖^2 ≤
        K*((metaplecticLongDyads C F).card:ℝ)^2*X^(2*s)*(N*(B*U))^ε*(B*U)*F^(4*ε)*
          (N+8*B*U/C^3+(8*N*B*U/C^3)^(2/3:ℝ))*(∑ r ∈ A, ‖α r‖^2) := by
  obtain ⟨K,hK,hbound⟩ := hW.metaplectic_tail_dyad_sieve hε hεsmall hs
  refine ⟨K,hK,?_⟩
  intro w A X N U B C F hX hN hU hB hC hF hBU hA hY hcut α ℓ
  let J := metaplecticLongDyads C F
  let f : ℕ → ℂ := fun j => ∑ e ∈ metaplecticLongDyad C F j,
    ∑ r ∈ A, α r*metaplecticTailCoefficient r ℓ C F e*
      metaplecticAngularSmoothSum r ℓ (W (w r)) (U/norm e^3) 0
  let M : ℝ := K*X^(2*s)*(N*(B*U))^ε*(B*U)*F^(4*ε)*
    (N+8*B*U/C^3+(8*N*B*U/C^3)^(2/3:ℝ))*(∑ r ∈ A, ‖α r‖^2)
  have hb (j : ℕ) (hj : j ∈ J) : ‖f j‖^2 ≤ M := by
    have hE : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    have he := metaplectic_long_dyad_power hF (by positivity)
      (metaplecticLongDyad_scale (by linarith) hj) hε.le
    have hz := metaplectic_long_cutoff_ratio hC
      (metaplecticLongDyad_cutoff hj).le hU.le
    have hshape : N+B*(U/((2:ℝ)^j)^3)+
        (N*(B*(U/((2:ℝ)^j)^3)))^(2/3:ℝ) ≤
        N+8*B*U/C^3+(8*N*B*U/C^3)^(2/3:ℝ) := by
      have hz' : B*(U/((2:ℝ)^j)^3) ≤ 8*B*U/C^3 := by
        convert mul_le_mul_of_nonneg_left hz hB using 1
        ring
      have hn' : N*(B*(U/((2:ℝ)^j)^3)) ≤ 8*N*B*U/C^3 := by
        convert mul_le_mul_of_nonneg_left hz' (by linarith : 0 ≤ N) using 1
        ring
      exact add_le_add (add_le_add le_rfl hz')
        (Real.rpow_le_rpow (by positivity) hn' (by norm_num))
    have hh := hbound w A (metaplecticLongDyad C F j) X N U B C F ((2:ℝ)^j)
      hX hN hU hB hE hA (fun e he => metaplecticLongDyad_norm he) hY hcut α ℓ
    apply hh.trans
    dsimp [M]
    gcongr
  rw [metaplectic_long_outer_partition A α ℓ (fun r => W (w r)) hU hB hBU hcut C]
  change ‖∑ j ∈ J, f j‖^2 ≤ _
  have hCS : ‖∑ j ∈ J, f j‖^2 ≤ (J.card:ℝ)*(∑ j ∈ J, ‖f j‖^2) := by
    simpa using complex_bilinear_rows_sq J (fun _ => (1:ℂ)) f
  calc
    _ ≤ (J.card:ℝ)*(∑ j ∈ J, ‖f j‖^2) := hCS
    _ ≤ (J.card:ℝ)*(∑ _j ∈ J, M) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum hb) (Nat.cast_nonneg _)
    _ = _ := by simp [M,J]; ring

end CubicFirstMoment

end

end OAI
