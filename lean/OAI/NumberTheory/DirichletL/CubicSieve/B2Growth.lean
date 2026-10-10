import OAI.NumberTheory.DirichletL.CubicSieve.Growth

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem elementSieveNorm_two_power_log (ξ ε A M N : ℝ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hε : 0 ≤ ε) (hA : 0 ≤ A) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hB1 : ∀ X : ℝ, 1 ≤ X → sieveNorm (2*X) N ≤
      A*(X*N)^ε*(X^ξ + N + (X*N)^(2/3 : ℝ))) :
    elementSieveNorm M N ≤ (384*128^2 : ℝ) * A *
      (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 *
      (M*N)^ε * (M^(1/3 : ℝ)*N + M^ξ) := by
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let R := elementRange M
  have hRne : R.Nonempty := by
    refine ⟨1, ?_⟩
    rw [mem_elementRange]
    refine ⟨one_ne_zero, ?_⟩
    simpa using hM
  have hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M :=
    fun z hz => (mem_elementRange M z).mp hz
  apply FiniteSieveOperator.squared_norm_le_of_energy (elementMatrix M N)
  · positivity
  intro a
  obtain ⟨X,Y,hX,hY,hXY,he⟩ := full_element_dyadic_extraction R hRne M N hR
    (fun j : idealRange N => j.val) Subtype.val_injective
    (fun j => mem_idealRange.mp j.property) a
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hXM : X ≤ M := by nlinarith [sq_nonneg (Y-1)]
  have hYM : Y ≤ M := by nlinarith [sq_nonneg (Y-1)]
  let B := A*(M*N)^ε
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (U : ℝ) (hU : 1 ≤ U) (hUM : U ≤ M) :
      sieveNorm (2*U) N ≤ B*(U^ξ+N+(U*N)^(2/3 : ℝ)) := by
    apply (hB1 U hU).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
      (mul_le_mul_of_nonneg_right hUM hN0.le) hε) hA
  have hmin : min (Y*sieveNorm (2*X) N) (X*sieveNorm (2*Y) N) ≤
      B*min (Y*(X^ξ+N+(X*N)^(2/3 : ℝ))) (X*(Y^ξ+N+(Y*N)^(2/3 : ℝ))) := by
    rw [mul_min_of_nonneg _ _ hB]
    apply min_le_min
    · convert mul_le_mul_of_nonneg_left (hb X hX hXM) hY0.le using 1; ring
    · convert mul_le_mul_of_nonneg_left (hb Y hY hYM) hX0.le using 1; ring
  have hopt := extraction_min_two_power M N X Y ξ hM hN0.le hX hY hXY hξ
  have hH : 0 ≤ (M/(X*Y^2))^(1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hi (z : O) : (∑ j : idealRange N, a j * elementCharacter j.val (mem_idealRange.mp j.property).1.2 z) =
      ∑ j : idealRange N, cubicRow j.val z * a j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  simp_rw [hi] at he
  have hE : 0 ≤ ∑ j : idealRange N, ‖a j‖^2 := by positivity
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmin (show 0 ≤ (192*128^2 : ℝ)*
      (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2*(M/(X*Y^2))^(1/3 : ℝ) by positivity)) hE
  have hbnd := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hopt (show 0 ≤ (192*128^2 : ℝ)*
      (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2*B by positivity)) hE
  have he' := he.trans hh
  rw [← Finset.sum_coe_sort] at he'
  change (∑ z : elementRange M, ‖∑ j : idealRange N, cubicRow j.val z.val * a j‖^2) ≤ _
  apply he'.trans
  convert hbnd using 1 <;> dsimp only [B] <;> ring

theorem HasCubicExponent.full_element_bound {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      elementSieveNorm M N ≤ C*(M*N)^ε*(M^(1/3 : ℝ)*N + M^ξ) := by
  obtain ⟨A,hA,hb⟩ := h.doubled (ε/2) (by positivity)
  let D : ℝ := 2 + 1/((ε/4)*Real.log 2)
  have hD : 0 < D := by
    dsimp [D]
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine ⟨(384*128^2 : ℝ)*A*D^2, by positivity, ?_⟩
  intro M N hM hN
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hlog := CanonicalQuadraticSieve.columnDyadicLength_small_power (ε/4) (by positivity) M hM
  have hLP : (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 ≤ D^2*M^(ε/2) := by
    have hh := pow_le_pow_left₀ (by positivity) hlog 2
    rw [mul_pow, ← Real.rpow_mul_natCast hM0.le] at hh
    have he : (ε/4)*(2:ℕ) = ε/2 := by push_cast; ring
    rw [he] at hh
    exact hh
  have hMP : M^(ε/2) ≤ (M*N)^(ε/2) := Real.rpow_le_rpow hM0.le
    (by nlinarith) (by positivity)
  have hprod : (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 * (M*N)^(ε/2) ≤
      D^2*(M*N)^ε := by
    calc
      _ ≤ (D^2*M^(ε/2))*(M*N)^(ε/2) :=
        mul_le_mul_of_nonneg_right hLP (Real.rpow_nonneg (by positivity) _)
      _ ≤ (D^2*(M*N)^(ε/2))*(M*N)^(ε/2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMP (sq_nonneg _))
          (Real.rpow_nonneg (by positivity) _)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add (mul_pos hM0 hN0)]
        congr 2
        ring
  have he := elementSieveNorm_two_power_log ξ (ε/2) A M N hξ (by positivity) hA.le hM hN
    (fun X hX => hb X N hX hN)
  calc
    _ ≤ (384*128^2 : ℝ)*A*
        (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 *
        (M*N)^(ε/2)*(M^(1/3 : ℝ)*N+M^ξ) := he
    _ = ((384*128^2 : ℝ)*A)*
        ((CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2*(M*N)^(ε/2))*
        (M^(1/3 : ℝ)*N+M^ξ) := by ring
    _ ≤ ((384*128^2 : ℝ)*A)*(D^2*(M*N)^ε)*(M^(1/3 : ℝ)*N+M^ξ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by positivity)) (by positivity)
    _ = _ := by ring

end
end SevenEighths.CubicSieve

end OAI
