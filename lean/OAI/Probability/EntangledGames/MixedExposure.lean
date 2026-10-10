import OAI.Probability.EntangledGames.EffectExposure

namespace OAI

universe u_X u_Y u_I u_m u_n u_J u_K

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {m : Type u_m} {n : Type u_n} {J : Type u_J} {K : Type u_K} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype J] [DecidableEq J] [Nonempty J] [Fintype K] [DecidableEq K] [Nonempty K]

lemma step_left (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (i : I)
    (C : Matrix m n ℂ) (A : J → Matrix m m ℂ) (B : K → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hA1 : ∀ j, A j ≤ 1) (hB : ∀ j, (B j).PosSemidef)
    (F : Profile I X Y → Matrix m m ℂ) (H : Profile I X Y → Matrix n n ℂ)
    (hF : ∀ z, F z ∈ Set.range A) (hF0 : ∀ z, μ.left x₀ i F z ∈ Set.range A)
    (hH : ∀ z, H z ∈ Set.range B) (hFi : IgnoresRight F i) (hHi : IgnoresLeft H i)
    (θ : Profile I X Y → ℝ) (hθ : ∀ z, 0 ≤ θ z)
    (hθL : IgnoresLeft θ i) (hθR : IgnoresRight θ i) :
    (pi (fun _ : I => μ)).avg (fun z => θ z * hsSq
      ((commonMap A (F z) - commonMap A (μ.left x₀ i F z))*C*(commonMap B (H z))ᵀ)) ≤
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (effectEntropy (F z)) (μ.right y₀ i H z)) -
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (effectEntropy (μ.left x₀ i F z)) (H z)) := by
  let ρ := pi (fun _ : I => μ)
  let T := μ.left x₀ i F
  let e : Profile I X Y → ℝ := fun z => θ z * hsSq
    ((commonMap A (F z)-commonMap A (T z))*C*(commonMap B (H z))ᵀ)
  have hTi : IgnoresLeft T i := left_ignoresLeft μ x₀ i F
  have hstep (z : Profile I X Y) : μ.left x₀ i e z ≤
      θ z * (prob C (μ.left x₀ i (fun z => effectEntropy (F z)) z) (H z) -
        prob C (effectEntropy (T z)) (H z)) := by
    have h := commonMap_error_left A hA hA1 (μ.givenSecond x₀ (z i).2)
      (fun x => F (updateLeft z i x)) (fun x => hF _) (hF0 z) C (commonMap B (H z))
    rw [commonMap_gram B hB (hH z)] at h
    have hl : μ.left x₀ i e z = θ z *
        (μ.givenSecond x₀ (z i).2).avg (fun x => hsSq
          ((commonMap A (F (updateLeft z i x))-commonMap A (T z))*C*(commonMap B (H z))ᵀ)) := by
      simp only [left, e, hθL z, hTi z, hHi z, Law.avg, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hl]
    apply mul_le_mul_of_nonneg_left _ (hθ z)
    have heq := (μ.givenSecond x₀ (z i).2).avg_linear
      (fun x => effectEntropy (F (updateLeft z i x))) (probLeft C (H z))
    change prob C (μ.left x₀ i (fun z => effectEntropy (F z)) z) (H z) = _ at heq
    rw [heq]
    exact h
  have havg := ρ.avg_mono hstep
  have hPairL : ρ.avg (fun z => θ z * prob C (μ.left x₀ i (fun z => effectEntropy (F z)) z) (H z)) =
      ρ.avg (fun z => θ z * prob C (effectEntropy (F z)) (H z)) := by
    apply pi_left_pairing μ x₀ i (fun z => effectEntropy (F z))
      (fun z => θ z • probLeft C (H z))
    intro z x
    simp only [hθL z, hHi z]
  have hPairR : ρ.avg (fun z => θ z * prob C (effectEntropy (F z)) (μ.right y₀ i H z)) =
      ρ.avg (fun z => θ z * prob C (effectEntropy (F z)) (H z)) := by
    apply pi_right_pairing μ y₀ i H (fun z => θ z • probRight C (effectEntropy (F z)))
    intro z y
    simp only [hθR z, hFi z]
  have he : ρ.avg (μ.left x₀ i e) = ρ.avg e := pi_avg_left μ x₀ i e
  rw [he] at havg
  have hr : ρ.avg (fun z => θ z * (prob C (μ.left x₀ i (fun z => effectEntropy (F z)) z) (H z) -
        prob C (effectEntropy (T z)) (H z))) =
      ρ.avg (fun z => θ z*prob C (effectEntropy (F z)) (μ.right y₀ i H z)) -
      ρ.avg (fun z => θ z*prob C (effectEntropy (T z)) (H z)) := by
    simp only [mul_sub, Law.avg_sub]
    rw [hPairL, hPairR]
  exact havg.trans_eq hr

lemma step_right (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (i : I)
    (C : Matrix m n ℂ) (A : J → Matrix m m ℂ) (B : K → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hB : ∀ j, (B j).PosSemidef) (hB1 : ∀ j, B j ≤ 1)
    (F : Profile I X Y → Matrix m m ℂ) (H : Profile I X Y → Matrix n n ℂ)
    (hF : ∀ z, F z ∈ Set.range A) (hH : ∀ z, H z ∈ Set.range B)
    (hH1 : ∀ z, μ.right y₀ i H z ∈ Set.range B)
    (hFi : IgnoresRight F i) (hHi : IgnoresLeft H i)
    (θ : Profile I X Y → ℝ) (hθ : ∀ z, 0 ≤ θ z)
    (hθL : IgnoresLeft θ i) (hθR : IgnoresRight θ i) :
    (pi (fun _ : I => μ)).avg (fun z => θ z * hsSq
      (commonMap A (F z)*C*(commonMap B (H z) - commonMap B (μ.right y₀ i H z))ᵀ)) ≤
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (μ.left x₀ i F z) (effectEntropy (H z))) -
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (F z) (effectEntropy (μ.right y₀ i H z))) := by
  let ρ := pi (fun _ : I => μ)
  let T := μ.right y₀ i H
  let e : Profile I X Y → ℝ := fun z => θ z * hsSq
    (commonMap A (F z)*C*(commonMap B (H z)-commonMap B (T z))ᵀ)
  have hTi : IgnoresRight T i := right_ignoresRight μ y₀ i H
  have hstep (z : Profile I X Y) : μ.right y₀ i e z ≤
      θ z * (prob C (F z) (μ.right y₀ i (fun z => effectEntropy (H z)) z) -
        prob C (F z) (effectEntropy (T z))) := by
    have h := commonMap_error_right B hB hB1 (μ.givenFirst y₀ (z i).1)
      (fun y => H (updateRight z i y)) (fun y => hH _) (hH1 z) C (commonMap A (F z))
    rw [commonMap_gram A hA (hF z)] at h
    have hl : μ.right y₀ i e z = θ z *
        (μ.givenFirst y₀ (z i).1).avg (fun y => hsSq
          (commonMap A (F z)*C*(commonMap B (H (updateRight z i y))-commonMap B (T z))ᵀ)) := by
      simp only [right, e, hθR z, hTi z, hFi z, Law.avg, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hl]
    apply mul_le_mul_of_nonneg_left _ (hθ z)
    have heq := (μ.givenFirst y₀ (z i).1).avg_linear
      (fun y => effectEntropy (H (updateRight z i y))) (probRight C (F z))
    change prob C (F z) (μ.right y₀ i (fun z => effectEntropy (H z)) z) = _ at heq
    rw [heq]
    exact h
  have havg := ρ.avg_mono hstep
  have hPairR : ρ.avg (fun z => θ z * prob C (F z) (μ.right y₀ i (fun z => effectEntropy (H z)) z)) =
      ρ.avg (fun z => θ z * prob C (F z) (effectEntropy (H z))) := by
    apply pi_right_pairing μ y₀ i (fun z => effectEntropy (H z))
      (fun z => θ z • probRight C (F z))
    intro z y
    simp only [hθR z, hFi z]
  have hPairL : ρ.avg (fun z => θ z * prob C (μ.left x₀ i F z) (effectEntropy (H z))) =
      ρ.avg (fun z => θ z * prob C (F z) (effectEntropy (H z))) := by
    apply pi_left_pairing μ x₀ i F (fun z => θ z • probLeft C (effectEntropy (H z)))
    intro z x
    simp only [hθL z, hHi z]
  have he : ρ.avg (μ.right y₀ i e) = ρ.avg e := pi_avg_right μ y₀ i e
  rw [he] at havg
  have hr : ρ.avg (fun z => θ z * (prob C (F z) (μ.right y₀ i (fun z => effectEntropy (H z)) z) -
        prob C (F z) (effectEntropy (T z)))) =
      ρ.avg (fun z => θ z*prob C (μ.left x₀ i F z) (effectEntropy (H z))) -
      ρ.avg (fun z => θ z*prob C (F z) (effectEntropy (T z))) := by
    simp only [mul_sub, Law.avg_sub]
    rw [hPairR, hPairL]
  exact havg.trans_eq hr
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype m] [Fintype n]

lemma mixed_pairing (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (l r : List I)
    (hlr : ∀ i ∈ l, i ∉ r) (C : Matrix m n ℂ)
    (F : Profile I X Y → Matrix m m ℂ) (H : Profile I X Y → Matrix n n ℂ)
    (hF : ∀ i ∈ r, IgnoresRight F i) (hH : ∀ i ∈ l, IgnoresLeft H i)
    (θ : Profile I X Y → ℝ) (hθL : ∀ i ∈ l, IgnoresLeft θ i) (hθR : ∀ i ∈ r, IgnoresRight θ i) :
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (μ.lefts x₀ l F z) (μ.rights y₀ r H z)) =
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (F z) (H z)) := by
  calc
    _ = (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (F z) (μ.rights y₀ r H z)) := by
      apply pi_lefts_pairing μ x₀ l F (fun z => θ z • probLeft C (μ.rights y₀ r H z))
      intro i hi z x
      simp only [hθL i hi z, rights_ignoresLeft_notMem μ y₀ r (hlr i hi) (hH i hi) z]
    _ = _ := by
      apply pi_rights_pairing μ y₀ r H (fun z => θ z • probRight C (F z))
      intro i hi z y
      simp only [hθR i hi z, hF i hi z]

lemma fixed_mixed_pairing (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (l r : List I)
    (hlr : ∀ i ∈ l, i ∉ r) (C : Matrix m n ℂ)
    (F : Profile I X Y → Matrix m m ℂ) (H : Profile I X Y → Matrix n n ℂ)
    (hF : ∀ i ∈ r, IgnoresRight F i) (hH : ∀ i ∈ l, IgnoresLeft H i)
    (θ : Profile I X Y → ℝ) (hθL : ∀ i ∈ l, IgnoresLeft θ i) (hθR : ∀ i ∈ r, IgnoresRight θ i)
    (i : I) (hiL : i ∉ l) (hiR : i ∉ r) (q : X×Y) :
    (pi (fun _ : I => μ)).avg (fun z => θ (Function.update z i q) * prob C
      (μ.lefts x₀ l F (Function.update z i q)) (μ.rights y₀ r H (Function.update z i q))) =
    (pi (fun _ : I => μ)).avg (fun z => θ (Function.update z i q) *
      prob C (F (Function.update z i q)) (H (Function.update z i q))) := by
  calc
    _ = (pi (fun _ : I => μ)).avg (fun z => θ (Function.update z i q) *
        prob C (F (Function.update z i q)) (μ.rights y₀ r H (Function.update z i q))) := by
      apply pi_fixed_lefts_pairing μ x₀ l hiL q F (fun z => θ z • probLeft C (μ.rights y₀ r H z))
      intro j hj z x
      simp only [hθL j hj z, rights_ignoresLeft_notMem μ y₀ r (hlr j hj) (hH j hj) z]
    _ = _ := by
      apply pi_fixed_rights_pairing μ y₀ r hiR q H (fun z => θ z • probRight C (F z))
      intro j hj z y
      simp only [hθR j hj z, hF j hj z]
end ThresholdParallelRepetition.MixedExposure

end

end OAI
