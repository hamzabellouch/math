import OAI.NumberTheory.DirichletL.Descent.SecondSourceTuples

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero sourceIdeal_union sourceIdeal_injective sourcePrime source_prime_dvd)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

lemma sourceIdeal_isRadical
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (S : Finset ι) :
    (sourceIdeal p S).IsRadical := by
  change (Ideal.span {∏ i ∈ S,p i}).IsRadical
  rw [FiniteGaussPhase.span_finset_prod]
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact fun _ _ => by simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha,Ideal.mul_eq_inf_of_isCoprime]
    · exact (inferInstance : (Ideal.span {p a}).IsPrime).isRadical.inf ih
    · apply IsCoprime.prod_right
      intro b hb
      exact hcop (fun he => ha (he.symm ▸ hb))

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma cubeRadical_span_dvd_product (B : Finset ι) (v : ι → ℕ)
    (hv : ∀ i ∈ B, 0 < v i) :
    sourceIdeal p B ∣ Ideal.span {primeProduct p B v} := by
  apply span_dvd_of_element_dvd
  change (∏ i ∈ B,p i) ∣ primeProduct p B v
  unfold primeProduct
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  exact dvd_pow_self _ (Nat.ne_of_gt (hv i hi))

theorem cubeSupport_dvd_radical
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    sourceIdeal p B ∣
      (Ideal.span {primeProduct p B v₁}*Ideal.span {primeProduct p B v₂}).radical := by
  apply Ideal.dvd_iff_le.mpr
  apply (sourceIdeal_isRadical p hcop B).radical_le_iff.mpr
  apply Ideal.dvd_iff_le.mp
  rw [Ideal.span_singleton_mul_span_singleton,←primeProduct_add]
  exact cubeRadical_span_dvd_product p B _ hv

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma aLabel_dvd_cubeSupport (B : Finset ι) (ε : ι → Bool) :
    Ideal.span {aLabel p B ε} ∣ sourceIdeal p B := by
  apply span_dvd_of_element_dvd
  unfold aLabel primeProduct
  change (∏ i ∈ B,p i^bit (ε i)) ∣ ∏ i ∈ B,p i
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  cases hh : ε i <;> simp [bit]

theorem firstMask_dvd_cube_radical
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (B C D : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (v₁ v₂ : ι → ℕ) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    sourceIdeal p D ∣ sourceIdeal p C *
      (Ideal.span {primeProduct p B v₁}*Ideal.span {primeProduct p B v₂}).radical := by
  have hd := InverseInitialArithmetic.sourceIdeal_dvd p D (C∪B) hD
  rw [sourceIdeal_union p C B hCB] at hd
  exact hd.trans (mul_dvd_mul_left _ (cubeSupport_dvd_radical p hcop B v₁ v₂ hv))

def cubeSecondSource {Jo Jn : ℕ} (B C D G E V : Finset ι)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (t : Ideal Eis) (k : Eis)
    (oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal) (newAssigned : Fin Jn → ι) :
    SecondOriginalSource ι Jo Jn where
  q0 := Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}
  quotient := t
  J := Ideal.span {jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂}
  C := sourceIdeal p C
  s := Ideal.span {squarefreeLabel p B (fun i => v₁ i+v₂ i)}
  b1 := Ideal.span {primeProduct p B v₁}
  A1 := Ideal.span {aLabel p B ε₁}
  A2 := Ideal.span {aLabel p B ε₂}
  dK := sourceIdeal p D
  J2 := Ideal.span {j2Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}
  b2 := Ideal.span {primeProduct p B v₂}
  common := G
  divisor := E
  overlap := V
  frequency := k
  oldAssigned := oldAssigned
  newAssigned := newAssigned

theorem cubeSecondSource_valid (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    {Jo Jn : ℕ} (B C D G E V : Finset ι) (hCB : Disjoint C B)
    (hD : D ⊆ C∪B) (hE : E ⊆ G)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i)
    (t : Ideal Eis) (k : Eis)
    (oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal) (newAssigned : Fin Jn → ι)
    (hold : ∀ i, (oldAssigned i).val ∣
      Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂} *
      Ideal.span {jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂} * sourceIdeal p C * t)
    (hnew : ∀ i, newAssigned i ∈ G∪V) :
    SecondOriginalValid (cubeSecondSource p B C D G E V v₁ v₂ ε₁ ε₂ t k oldAssigned newAssigned) := by
  constructor
  · change Ideal.span {squarefreeLabel p B (fun i => v₁ i+v₂ i)} *
        Ideal.span {j2Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂} = _
    rw [Ideal.span_singleton_mul_span_singleton,←jLabel_eq_squarefree_mul_j2]
    rfl
  · have hb := congrArg (fun a : Eis => (Ideal.span {a} : Ideal Eis))
      (cube_pair_product_decomposition p B v₁ v₂ ε₁ ε₂ hv)
    simpa only [cubeSecondSource,pow_two,←Ideal.span_singleton_mul_span_singleton] using hb
  · exact (aLabel_dvd_cubeSupport p B ε₁).trans (cubeSupport_dvd_radical p hcop B v₁ v₂ hv)
  · exact (aLabel_dvd_cubeSupport p B ε₂).trans (cubeSupport_dvd_radical p hcop B v₁ v₂ hv)
  · exact firstMask_dvd_cube_radical p hcop B C D hCB hD v₁ v₂ hv
  · change primaryGenerator (sourceIdeal p D) ≠ 0
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  · exact hE
  · exact hold
  · exact hnew

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem oldSlot_dvd_reconstructed_support
    (B C : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) (P t : Ideal Eis)
    (hP : P ∣ sourceIdeal p B*sourceIdeal p C*t) :
    P ∣ Ideal.span {b0Label p B v ε₁ ε₂}*
      Ideal.span {jLabel p B v ε₁ ε₂}*sourceIdeal p C*t := by
  have hb := span_dvd_of_element_dvd (cubeRadical_dvd_jLabel_b0 p B v ε₁ ε₂ hv)
  change sourceIdeal p B ∣ Ideal.span {jLabel p B v ε₁ ε₂*b0Label p B v ε₁ ε₂} at hb
  rw [←Ideal.span_singleton_mul_span_singleton,mul_comm (Ideal.span {jLabel p B v ε₁ ε₂})] at hb
  exact hP.trans (mul_dvd_mul_right (mul_dvd_mul_right hb _) _)

theorem cubeSecondSource_valid_original_slots (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    {Jo Jn : ℕ} (B C D G E V : Finset ι) (hCB : Disjoint C B)
    (hD : D ⊆ C∪B) (hE : E ⊆ G)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i)
    (t : Ideal Eis) (k : Eis)
    (oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal) (newAssigned : Fin Jn → ι)
    (hold : ∀ i, (oldAssigned i).val ∣ sourceIdeal p B*sourceIdeal p C*t)
    (hnew : ∀ i, newAssigned i ∈ G∪V) :
    SecondOriginalValid (cubeSecondSource p B C D G E V v₁ v₂ ε₁ ε₂ t k oldAssigned newAssigned) :=
  cubeSecondSource_valid p hp hpr hcop B C D G E V hCB hD hE v₁ v₂ ε₁ ε₂ hv t k
    oldAssigned newAssigned
    (fun i => oldSlot_dvd_reconstructed_support p B C _ ε₁ ε₂ hv _ t (hold i)) hnew

end
end SevenEighths.InverseMoment

end OAI
