import OAI.NumberTheory.DirichletL.Descent.MarkedFourier

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CubicEisenstein LocalReflectionBrackets CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

section Local
variable {F : Type*} [Field F] [Fintype F]

def markedFrequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x h : F) : ℂ :=
  finiteAdditiveFourierCoeff ψ zeroMark h * frequencyMultiplier χ ψ σ ε x h

theorem markedFrequencyRow_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x : F) :
    markedFrequencyRow χ ψ σ ε x 0 = (Fintype.card F : ℂ)⁻¹ := by
  simp [markedFrequencyRow, frequencyMultiplier, finiteAdditiveFourierCoeff, zeroMark]

theorem markedFrequencyRow_units (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x : F) :
    (∑ h : Fˣ, markedFrequencyRow χ ψ σ ε x h) =
      localReflectionActive zeroMark χ ψ σ ε x := by
  unfold markedFrequencyRow finiteAdditiveFourierCoeff frequencyMultiplier localReflectionActive localFourier
  simp only [Units.ne_zero, ite_false,  Units.val_inv_eq_inv_val,
    Finset.mul_sum, neg_mul]
  apply Finset.sum_congr rfl
  intro h hh
  ring

def mixedFrequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (marked : Bool) (j : ℕ) (σ ε : Fˣ) (x h : F) : ℂ :=
  if marked then markedFrequencyRow χ ψ σ ε x h else frequencyRow χ ψ j σ ε x h

end Local

noncomputable local instance markedStratumField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) :=
  Ideal.Quotient.field P
noncomputable local instance markedStratumFintype (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) :=
  Fintype.ofFinite _

theorem actual_mixed_frequency_units (P : Ideal Eis) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P) (hc : ringChar (Eis ⧸ P) ≠ 2)
    (ψ : AddChar (Eis ⧸ P) ℂ) (hψ : ψ.IsPrimitive) (marked : Bool)
    (j : ℕ) (hj : j < 6) (σ ε : (Eis ⧸ P)ˣ) (x : Eis ⧸ P) :
    (∑ h : (Eis ⧸ P)ˣ, mixedFrequencyRow (actualSextic P hg) ψ marked j σ ε x h) =
      if marked then
        (rootCard (Eis ⧸ P) : ℂ)⁻¹ * tau (actualSextic P hg) ψ 2 *
          (((actualSextic P hg) ^ 2)⁻¹) ((σ : Eis ⧸ P) * (ε : Eis ⧸ P) * x)
      else (((actualSextic P hg)⁻¹) ^ 2) σ *
        phase (actualSextic P hg) ψ j ε * bracket (actualSextic P hg) j x := by
  cases marked
  · simp only [mixedFrequencyRow, Bool.false_eq_true, ite_false]
    exact canonical_frequencyRow_units P hg hc ψ hψ j hj σ ε x
  · simp only [mixedFrequencyRow, ite_true]
    rw [markedFrequencyRow_units, actual_marked_active_formula P hg hc ψ hψ σ ε x]

theorem actual_mixed_frequency_zero (P : Ideal Eis) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P) (hc : ringChar (Eis ⧸ P) ≠ 2)
    (ψ : AddChar (Eis ⧸ P) ℂ) (marked : Bool)
    (j : ℕ) (hj : j < 6) (σ ε : (Eis ⧸ P)ˣ) (x : Eis ⧸ P) :
    mixedFrequencyRow (actualSextic P hg) ψ marked j σ ε x 0 =
      if marked then (Fintype.card (Eis ⧸ P) : ℂ)⁻¹
      else if j = 0 then 1 - (Fintype.card (Eis ⧸ P) : ℂ)⁻¹ else 0 := by
  cases marked
  · simp only [mixedFrequencyRow, Bool.false_eq_true, ite_false]
    exact canonical_frequencyRow_zero P hg hc ψ j hj σ ε x
  · simp only [mixedFrequencyRow, ite_true]
    exact markedFrequencyRow_zero _ _ _ _ _

theorem actual_mixed_active_stratum {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hc : ∀ i, ringChar (Eis ⧸ P i) ≠ 2)
    (ψ : ∀ i, AddChar (Eis ⧸ P i) ℂ) (hψ : ∀ i, (ψ i).IsPrimitive)
    (marked : ι → Bool) (j : ι → ℕ) (hj : ∀ i, j i < 6)
    (A : Finset ι) (σ ε : ∀ i, (Eis ⧸ P i)ˣ) (x : ∀ i, Eis ⧸ P i) :
    (∑ h ∈ FixedRayActiveSet.activeStratum (fun i => Eis ⧸ P i) A,
      ∏ i, mixedFrequencyRow (actualSextic (P i) (hg i)) (ψ i) (marked i) (j i)
        (σ i) (ε i) (x i) (h i)) =
      (∏ i ∈ A, if marked i then
        (rootCard (Eis ⧸ P i) : ℂ)⁻¹ * tau (actualSextic (P i) (hg i)) (ψ i) 2 *
          (((actualSextic (P i) (hg i)) ^ 2)⁻¹)
            ((σ i : Eis ⧸ P i) * (ε i : Eis ⧸ P i) * x i)
        else (((actualSextic (P i) (hg i))⁻¹) ^ 2) (σ i) *
          phase (actualSextic (P i) (hg i)) (ψ i) (j i) (ε i) *
            bracket (actualSextic (P i) (hg i)) (j i) (x i)) *
      (∏ i ∈ (Finset.univ : Finset ι) \ A,
        if marked i then (Fintype.card (Eis ⧸ P i) : ℂ)⁻¹
        else if j i = 0 then 1 - (Fintype.card (Eis ⧸ P i) : ℂ)⁻¹ else 0) := by
  rw [FixedRayActiveSet.sum_active_stratum]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    exact actual_mixed_frequency_units (P i) (hg i) (hc i) (ψ i) (hψ i)
      (marked i) (j i) (hj i) (σ i) (ε i) (x i)
  · apply Finset.prod_congr rfl
    intro i hi
    exact actual_mixed_frequency_zero (P i) (hg i) (hc i) (ψ i)
      (marked i) (j i) (hj i) (σ i) (ε i) (x i)

end
end SevenEighths.InverseMoment

end OAI
