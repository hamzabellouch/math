import OAI.NumberTheory.DirichletL.Reflection.MarkedRestriction

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma mixed_inactive_coefficient (P : PrimeFamily ι)
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (i : ι) :
    finiteAdditiveFourierCoeff (quotientTrace (P.generator i) (P.generator_ne_zero i))
      (mixedPrimeFunction P.generator P.generator_good j S i) 0 =
    if i∈S then (Ideal.absNorm (P.ideal i):ℂ)⁻¹
      else if j i=0 then 1-(Ideal.absNorm (P.ideal i):ℂ)⁻¹ else 0 := by
  change finiteAdditiveFourierCoeff (quotientTrace (P.generator i) (P.generator_ne_zero i))
    (fun x => if i∈S then zeroMark x else (actualSextic (Ideal.span {P.generator i}) (P.generator_good i)^j i) x) 0 = _
  by_cases hi : i∈S
  · simp only [hi,ite_true,zeroMark,finiteAdditiveFourierCoeff_zero_delta]
    have hcard : Fintype.card (Eis⧸Ideal.span {P.generator i})=Ideal.absNorm (P.ideal i) := by
      rw [← P.generator_span i,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
    rw [hcard]
  · simp only [hi,ite_false]
    have ho : ringChar (Eis⧸Ideal.span {P.generator i})≠2 := by
      rw [P.generator_span]
      exact hodd i
    rw [prime_zeroFourier_norm_formula (P.generator i) (P.generator_ne_zero i)
      (P.generator_good i) ho (j i) (hj i),P.generator_span]

lemma mixed_inactive_weight (P : PrimeFamily ι)
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S A : Finset ι) :
    localInactiveWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) A =
    ∏ i∈(Finset.univ:Finset ι)\A,
      if i∈S then (Ideal.absNorm (P.ideal i):ℂ)⁻¹
        else if j i=0 then 1-(Ideal.absNorm (P.ideal i):ℂ)⁻¹ else 0 := by
  unfold localInactiveWeight
  apply Finset.prod_congr rfl
  intro i hi
  exact mixed_inactive_coefficient P hodd j hj S i

lemma mixed_inactive_zero_of_omitted (P : PrimeFamily ι)
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S A : Finset ι) (i : ι) (hi : i∉S) (hji : j i≠0) (hiA : i∉A) :
    localInactiveWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) A=0 := by
  rw [mixed_inactive_weight P hodd j hj]
  apply Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i,hiA⟩)
  simp only [hi,hji,ite_false]

lemma mixed_inactive_nonzero_requires (P : PrimeFamily ι)
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S A : Finset ι)
    (h : localInactiveWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) A≠0) :
    ∀ i, i∉S → j i≠0 → i∈A := by
  intro i hi hji
  by_contra hiA
  exact h (mixed_inactive_zero_of_omitted P hodd j hj S A i hi hji hiA)
end
end SevenEighths.InverseReflectedPhase

end OAI
