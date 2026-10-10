import OAI.NumberTheory.CubicMoment.Estimates.UnrestrictedCubicSieve
import OAI.NumberTheory.CubicMoment.Estimates.RepeatedPrimeSupport
import OAI.NumberTheory.CubicMoment.Estimates.StructuredMeanValue
import OAI.NumberTheory.CubicMoment.Estimates.PrimePowerSupport

namespace OAI

/-! Sparse error terms in the first exceptional conductor configuration. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem unrestricted_mixed_product_sieve {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q H : Finset Eisenstein) (N Z : ℝ),
      1 ≤ N → 1 ≤ Z →
      (∀ p ∈ P, primary p ∧ Squarefree p ∧ norm p ≤ N) →
      (∀ q ∈ Q, primary q) → (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ Z) →
      ∀ v : Eisenstein → ℂ,
      (∑ q ∈ Q, ∑ p ∈ P, ‖∑ h ∈ H, v h*mixedCubic p q h‖^2) ≤
        (Q.card:ℝ)*C*(N*Z)^ε*(N*Z^(1/3:ℝ)+(N*Z)^(2/3:ℝ)+Z^(4/3:ℝ)+Z)*
          ∑ h ∈ H, ‖v h‖^2 := by
  obtain ⟨C,hC,hbound⟩ := unrestricted_cubic_sieve hε hε₁
  refine ⟨C,hC,?_⟩
  intro P Q H N Z hN hZ hP hQ hH v
  have hrow (q : Eisenstein) (hq : q ∈ Q) :
      (∑ p ∈ P, ‖∑ h ∈ H, v h*mixedCubic p q h‖^2) ≤
      C*(N*Z)^ε*(N*Z^(1/3:ℝ)+(N*Z)^(2/3:ℝ)+Z^(4/3:ℝ)+Z)*
        ∑ h ∈ H, ‖v h‖^2 := by
    have he (p : Eisenstein) : (∑ h ∈ H, v h*mixedCubic p q h) =
        ∑ h ∈ H, (v h*star (cubicSymbol q h))*cubicSymbol p h := by
      apply Finset.sum_congr rfl
      intro h hh
      unfold mixedCubic
      ring
    simp_rw [he]
    apply (hbound P H N Z hN hZ hP hH (fun h => v h*star (cubicSymbol q h))).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro h hh
    rw [norm_mul,norm_star,mul_pow]
    apply mul_le_of_le_one_right (sq_nonneg _)
    simpa only [one_pow] using pow_le_pow_left₀ (_root_.norm_nonneg _)
      (norm_cubicSymbol_le_one (hQ q hq) h) 2
  calc
    _ ≤ ∑ _q ∈ Q,
        C*(N*Z)^ε*(N*Z^(1/3:ℝ)+(N*Z)^(2/3:ℝ)+Z^(4/3:ℝ)+Z)*
          ∑ h ∈ H, ‖v h‖^2 := Finset.sum_le_sum hrow
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]; ring

private lemma first_shape_sieve_power {Y θ : ℝ} (hY : 1 ≤ Y) (hθ : 0 < θ)
    (hθ₁ : θ ≤ 1) :
    Y^(θ/16) * (Y^(1+θ/16)*Y)^(θ/16) *
      (Y^(1+θ/16)*Y^(1/3:ℝ)+(Y^(1+θ/16)*Y)^(2/3:ℝ)+Y^(4/3:ℝ)+Y) *
        Y^(1-θ) ≤ 4*Y^(7/3-θ/2) := by
  have hY0 : 0 < Y := by linarith
  have hNY : Y^(1+θ/16)*Y = Y^(2+θ/16) := by
    calc
      _ = Y^(1+θ/16)*Y^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hY0]; congr 1; ring
  have hfirst : Y^(1+θ/16)*Y^(1/3:ℝ) = Y^(4/3+θ/16) := by
    rw [← Real.rpow_add hY0]
    congr 1
    ring
  have hsecond : (Y^(1+θ/16)*Y)^(2/3:ℝ) ≤ Y^(4/3+θ/16) := by
    rw [hNY,← Real.rpow_mul hY0.le]
    exact Real.rpow_le_rpow_of_exponent_le hY (by nlinarith)
  have hthird : Y^(4/3:ℝ) ≤ Y^(4/3+θ/16) :=
    Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  have hlast : Y ≤ Y^(4/3+θ/16) := by
    nth_rw 1 [← Real.rpow_one Y]
    exact Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  have hpoly : Y^(1+θ/16)*Y^(1/3:ℝ)+(Y^(1+θ/16)*Y)^(2/3:ℝ)+Y^(4/3:ℝ)+Y ≤
      4*Y^(4/3+θ/16) := by rw [hfirst]; linarith
  calc
    _ ≤ Y^(θ/16)*(Y^(1+θ/16)*Y)^(θ/16)*(4*Y^(4/3+θ/16))*Y^(1-θ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpoly (by positivity)) (by positivity)
    _ = 4*Y^(7/3-θ+2*(θ/16)+(2+θ/16)*(θ/16)) := by
      rw [hNY,← Real.rpow_mul hY0.le]
      calc
        _ = 4*(Y^(θ/16)*Y^((2+θ/16)*(θ/16))*Y^(4/3+θ/16)*Y^(1-θ)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hY0,← Real.rpow_add hY0,← Real.rpow_add hY0]
          congr 1
          ring_nf
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.rpow_le_rpow_of_exponent_le hY
      nlinarith

/-- Sparse coefficient energy supplies a fixed saving for the first
exceptional conductor shape. All arithmetic support conditions are kept
on the actual coefficient and character sets. -/
theorem first_shape_sparse_mixed_moment {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y E : ℝ), 1 ≤ Y → 0 ≤ E →
      ∀ (P Q H : Finset Eisenstein),
      (∀ p ∈ P, primary p ∧ Squarefree p ∧ norm p ≤ Y^(1+θ/16)) →
      (∀ q ∈ Q, primary q ∧ norm q ≤ Y^(θ/16)) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ Y) →
      ∀ v : Eisenstein → ℂ, (∑ h ∈ H, ‖v h‖^2) ≤ E*Y^(1-θ) →
      (∑ q ∈ Q, ∑ p ∈ P, ‖∑ h ∈ H, v h*mixedCubic p q h‖^2) ≤
        C*E*Y^(7/3-θ/2) := by
  obtain ⟨C,hC,hbound⟩ := unrestricted_mixed_product_sieve
    (show 0 < θ/16 by positivity) (show θ/16 ≤ 1 by linarith)
  refine ⟨72*C,by positivity,?_⟩
  intro Y E hY hE P Q H hP hQ hH v hv
  have hN : 1 ≤ Y^(1+θ/16) := Real.one_le_rpow hY (by positivity)
  have hraw := hbound P Q H (Y^(1+θ/16)) Y hN hY hP (fun q hq => (hQ q hq).1) hH v
  have hQsub : Q ⊆ nonzeroNormBall (Y^(θ/16)) := fun q hq =>
    mem_nonzeroNormBall.mpr ⟨(hQ q hq).2,primary_ne_zero (hQ q hq).1⟩
  have hQcard : (Q.card:ℝ) ≤ 18*Y^(θ/16) :=
    (Nat.cast_le.mpr (Finset.card_le_card hQsub)).trans (nonzeroNormBall_card_le (by positivity))
  have hY0 : 0 < Y := by linarith
  calc
    _ ≤ (18*Y^(θ/16))*C*(Y^(1+θ/16)*Y)^(θ/16)*
        (Y^(1+θ/16)*Y^(1/3:ℝ)+(Y^(1+θ/16)*Y)^(2/3:ℝ)+Y^(4/3:ℝ)+Y)*
          (E*Y^(1-θ)) := by
      apply hraw.trans
      gcongr
    _ = (18*C*E)*(Y^(θ/16)*(Y^(1+θ/16)*Y)^(θ/16)*
        (Y^(1+θ/16)*Y^(1/3:ℝ)+(Y^(1+θ/16)*Y)^(2/3:ℝ)+Y^(4/3:ℝ)+Y)*Y^(1-θ)) := by ring
    _ ≤ (18*C*E)*(4*Y^(7/3-θ/2)) :=
      mul_le_mul_of_nonneg_left (first_shape_sieve_power hY hθ hθ₁) (by positivity)
    _ = _ := by ring

/-- The prime-to-squarefree discrepancy satisfies the first exceptional
second-moment bound, with all fixed angular and norm twists retained. -/
theorem repeatedPrime_first_shape_second_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℝ}
    (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y : ℝ),
      1 ≤ Y → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ Y^c < norm p) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i) →
      ∀ P Q : Finset Eisenstein,
      (∀ p ∈ P, primary p ∧ Squarefree p ∧ norm p ≤ Y^(1+c/32)) →
      (∀ q ∈ Q, primary q ∧ norm q ≤ Y^(c/32)) →
      ∀ (ℓ : ℤ) (u : ℝ) (ν : Eisenstein → ℂ),
      (∀ b ∈ orderedConvolutionSupport S, ‖ν b‖ ≤ 1) →
      (∑ q ∈ Q, ∑ p ∈ P, ‖∑ b ∈ orderedConvolutionSupport S,
        (squarefreeConvolutionError S w b*(theta ℓ b*normTwist u b*ν b))*mixedCubic p q b‖^2) ≤
        C*Y^(7/3-c/4)*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 := by
  obtain ⟨C,hC,hbound⟩ := first_shape_sparse_mixed_moment
    (show 0 < c/2 by positivity) (show c/2 ≤ 1 by linarith)
  obtain ⟨K,hK,henergy⟩ := primeConvolutionError_power_energy (ι := ι)
  have h₁ : c/2/16 = c/32 := by ring
  have h₂ : c/2/2 = c/4 := by ring
  simp only [h₁,h₂] at hbound
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro S w M Y hY hM hS hprod hw P Q hP hQ ℓ u ν hν
  have hY0 : 0 < Y := by linarith
  have hprime : ∀ i, ∀ p ∈ S i, primaryPrime p := fun i p hp => (hS i p hp).1
  let A : ℝ := ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i)
  let v (b : Eisenstein) := squarefreeConvolutionError S w b*(theta ℓ b*normTwist u b*ν b)
  have hH : ∀ b ∈ orderedConvolutionSupport S, b ≠ 0 ∧ norm b ≤ Y := by
    intro b hb
    refine ⟨orderedConvolutionSupport_ne_zero S hprime b hb,?_⟩
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
    exact hprod f hf
  have hE : (∑ b ∈ orderedConvolutionSupport S, ‖v b‖^2) ≤ (K*A^2)*Y^(1-c/2) := by
    have htw := coefficient_twist_energy_le (orderedConvolutionSupport S)
      (squarefreeConvolutionError S w) (fun b => theta ℓ b*normTwist u b*ν b)
      (fun b hb => by
        simpa only [norm_mul,norm_theta (hH b hb).1,norm_normTwist,one_mul,mul_one]
          using hν b hb)
    exact (htw.trans (henergy S w M Y c hY0 hM hS hprod hw)).trans_eq (by dsimp [A]; ring)
  have h := hbound Y (K*A^2) hY (by positivity) P Q (orderedConvolutionSupport S) hP hQ hH v hE
  exact h.trans_eq (by dsimp [A]; ring)

/-- Higher prime powers, including powers of small primes, have a sparse
enough actual support for the same first-shape argument. -/
theorem primePower_first_shape_second_moment {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y A : ℝ), 1 ≤ Y → 0 ≤ A →
      ∀ P Q : Finset Eisenstein,
      (∀ p ∈ P, primary p ∧ Squarefree p ∧ norm p ≤ Y^(1+c/128)) →
      (∀ q ∈ Q, primary q ∧ norm q ≤ Y^(c/128)) →
      ∀ v : Eisenstein → ℂ, (∀ b ∈ largePrimePowerSupport Y c, ‖v b‖ ≤ A) →
      (∑ q ∈ Q, ∑ p ∈ P, ‖∑ b ∈ largePrimePowerSupport Y c,
        v b*mixedCubic p q b‖^2) ≤ C*A^2*Y^(7/3-c/16) := by
  classical
  obtain ⟨C,hC,hbound⟩ := first_shape_sparse_mixed_moment
    (show 0 < c/8 by positivity) (show c/8 ≤ 1 by linarith)
  obtain ⟨K,hK,henergy⟩ := primePowerError_energy_bound
  have h₁ : c/8/16 = c/128 := by ring
  have h₂ : c/8/2 = c/16 := by ring
  simp only [h₁,h₂] at hbound
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro Y A hY hA P Q hP hQ v hv
  have hY0 : 0 < Y := by linarith
  have hH : ∀ b ∈ largePrimePowerSupport Y c, b ≠ 0 ∧ norm b ≤ Y := by
    intro b hb
    exact (mem_nonzeroNormBall.mp (Finset.mem_filter.mp hb).1).symm
  have hE : (∑ b ∈ largePrimePowerSupport Y c, ‖v b‖^2) ≤ (K*A^2)*Y^(1-c/8) :=
    (henergy Y c A hY0 hA v hv).trans_eq (by ring)
  exact (hbound Y (K*A^2) hY (by positivity) P Q (largePrimePowerSupport Y c) hP hQ hH v hE).trans_eq
    (by ring)

end CubicFirstMoment

end

end OAI
