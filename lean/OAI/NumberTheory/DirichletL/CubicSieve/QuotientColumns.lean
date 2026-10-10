import OAI.NumberTheory.DirichletL.CubicSieve.CompactDescent

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma finite_sum_restrict {n A : Type*} [Fintype n] [AddCommMonoid A]
    (p : n → Prop) (f : n → A) (hf : ∀ j, ¬p j → f j = 0) :
    (∑ j, f j) = ∑ j : {j // p j}, f j.val := by
  have h := Fintype.sum_subtype_add_sum_subtype p f
  have hz : (∑ j : {j // ¬p j}, f j.val) = 0 :=
    Finset.sum_eq_zero (fun j hj => hf j.val j.property)
  rw [hz, add_zero] at h
  exact h.symm

lemma cubicSmoothedCoprime_restrict {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (p : n → Prop)
    (ha : ∀ j, ¬p j → a j = 0) (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    cubicSmoothedCoprime cols a W M =
      cubicSmoothedCoprime (fun j : {j // p j} => cols j.val) (fun j => a j.val) W M := by
  unfold cubicSmoothedCoprime
  rw [finite_sum_restrict p _ (by
    intro j hj
    simp [ha j hj])]
  apply Finset.sum_congr rfl
  intro j hj
  exact finite_sum_restrict p _ (by
    intro k hk
    simp [ha k hk])

def quotientColumn {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (j : {j // D ∣ cols j}) : Ideal O := idealQuotient D (cols j.val)

def quotientCoefficient {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (d : O) (j : {j // D ∣ cols j}) : ℂ :=
  cubicRow (quotientColumn D cols j) d * a j.val

lemma quotientColumn_injective {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : Function.Injective cols) : Function.Injective (quotientColumn D cols) := by
  intro j k he
  exact Subtype.ext (hc (idealQuotient_injective_on D j.property k.property he))

lemma quotientColumn_admissible {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (j : {j // D ∣ cols j}) :
    Admissible (quotientColumn D cols j) := cubic_admissible_quotient (hc j.val) j.property

lemma cubic_quotient_in_shell {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (N : ℝ)
    (hcols : ∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (j : {j // D ∣ cols j}) :
    (N / (Ideal.absNorm D : ℝ))/2 ≤ (Ideal.absNorm (quotientColumn D cols j) : ℝ) ∧
      (Ideal.absNorm (quotientColumn D cols j) : ℝ) ≤ N / (Ideal.absNorm D : ℝ) := by
  have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero (primaryGenerator_ne_zero_ideal _ (hc j.val).2) j.property
  have hDN : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0)
  have he : (Ideal.absNorm (quotientColumn D cols j) : ℝ) * (Ideal.absNorm D : ℝ) =
      (Ideal.absNorm (cols j.val) : ℝ) := by
    rw [mul_comm, ← Nat.cast_mul, ← map_mul, quotientColumn, idealQuotient_mul j.property]
  refine ⟨?_, idealQuotient_norm_le hD0 j.property N (hcols j.val).2⟩
  have hh : (N/2) / (Ideal.absNorm D : ℝ) ≤ (Ideal.absNorm (quotientColumn D cols j) : ℝ) := by
    apply (div_le_iff₀ hDN).mpr
    rw [he]
    exact (hcols j.val).1
  convert hh using 1; ring

lemma compact_descendant_restrict {n : Type*} [Fintype n]
    (D : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (d : O)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    cubicSmoothedCoprime (fun j => totalQuotient D (cols j))
      (descendedCoefficient D cols a d) W M =
    cubicSmoothedCoprime (quotientColumn D cols) (quotientCoefficient D cols a d) W M := by
  rw [cubicSmoothedCoprime_restrict _ _ (fun j => D ∣ cols j) (by
    intro j hj
    simp only [descendedCoefficient, ite_eq_right hj, mul_zero])]
  have hc : (fun j : {j // D ∣ cols j} => totalQuotient D (cols j.val)) = quotientColumn D cols := by
    funext j
    simp only [totalQuotient, ite_eq_left j.property, quotientColumn]
  have ha : (fun j : {j // D ∣ cols j} => descendedCoefficient D cols a d j.val) =
      quotientCoefficient D cols a d := by
    funext j
    simp only [descendedCoefficient, totalQuotient, ite_eq_left j.property, quotientCoefficient, quotientColumn]
  rw [hc, ha]

lemma quotientCoefficient_energy {n : Type*} [Fintype n]
    (D : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (d : O) :
    (∑ j : {j // D ∣ cols j}, ‖quotientCoefficient D cols a d j‖^2) =
      ∑ j, ‖descendedCoefficient D cols a d j‖^2 := by
  rw [finite_sum_restrict (fun j => D ∣ cols j) _ (by
    intro j hj
    simp only [descendedCoefficient, ite_eq_right hj, mul_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [quotientCoefficient, quotientColumn, descendedCoefficient, totalQuotient, ite_eq_left j.property]

end
end SevenEighths.CubicSieve

end OAI
