import OAI.Combinatorics.SharpThreshold.FourierRestriction
import OAI.Combinatorics.SharpThreshold.FourierReindex
import OAI.Combinatorics.SharpThreshold.BlockSymmetry

namespace OAI

universe u

noncomputable section

open scoped BigOperators

namespace Problem313

variable {ι : Type u} [Fintype ι] (P : ι → Prop) [DecidablePred P]

omit [Fintype ι] in
/-- The coordinate equivalence from a predicate and its complement is ordinary pasting. -/
theorem config_sumCompl_eq_pasteCube
    (x : {i // P i} → Bool) (y : {i // ¬P i} → Bool) :
    Reindex.config (Equiv.sumCompl P) (Sum.elim x y) = pasteCube P x y := by
  funext i
  by_cases hi : P i <;> simp [Reindex.config, pasteCube, hi]

namespace BiasedFourier

/-- The ambient support obtained by adjoining free and exterior supports. -/
def subtypeSupport (A : Finset {i // P i}) (D : Finset {i // ¬P i}) : Finset ι :=
  (A.disjSum D).map (Equiv.sumCompl P).toEmbedding

/-- Conditional Fourier coefficients on arbitrary coordinate subtypes agree with
full coefficients after Fourier transformation in the exterior coordinates. -/
theorem coeff_restricted_coeff_subtype (p : ℝ) (f : (ι → Bool) → ℝ)
    (A : Finset {i // P i}) (D : Finset {i // ¬P i}) :
    coeff p (fun y => coeff p (restrictCube P f y) A) D =
      coeff p f (subtypeSupport P A D) := by
  classical
  let F : ({i // P i} ⊕ {i // ¬P i} → Bool) → ℝ :=
    fun z => f (Reindex.config (Equiv.sumCompl P) z)
  have hsplit : ∀ x y, F (Sum.elim x y) = restrictCube P f y x := by
    intro x y
    simp [F, config_sumCompl_eq_pasteCube, restrictCube]
  calc
    coeff p (fun y => coeff p (restrictCube P f y) A) D =
        coeff p (fun y => coeff p (fun x => F (Sum.elim x y)) A) D := by
      simp only [hsplit]
    _ = coeff p F (A.disjSum D) := coeff_restricted_coeff p F A D
    _ = coeff p f (subtypeSupport P A D) :=
      (coeff_reindex (Equiv.sumCompl P) p F f (fun _ => rfl) (A.disjSum D)).symm

/-- Exact squared-coefficient averaging over arbitrary exterior coordinate subtypes. -/
theorem restricted_coeff_sq_average_subtype [DecidableEq ι] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (A : Finset {i // P i}) :
    (∑ y : {i // ¬P i} → Bool, weight p y *
      (coeff p (restrictCube P f y) A) ^ 2) =
      ∑ D : Finset {i // ¬P i}, (coeff p f (subtypeSupport P A D)) ^ 2 := by
  classical
  symm
  simpa only [coeff_restricted_coeff_subtype] using
    parseval hp hp1 (fun y => coeff p (restrictCube P f y) A)

/-- Free and exterior support sets give each ambient support exactly once. -/
def subtypeSupportEquiv :
    (Finset {i // P i} × Finset {i // ¬P i}) ≃ Finset ι :=
  Finset.sumEquiv.toEquiv.symm.trans (Equiv.sumCompl P).finsetCongr

omit [Fintype ι] in
@[simp]
theorem subtypeSupportEquiv_apply
    (A : Finset {i // P i}) (D : Finset {i // ¬P i}) :
    subtypeSupportEquiv P (A,D) = subtypeSupport P A D := rfl

omit [Fintype ι] in
@[simp]
theorem subtype_subtypeSupport
    (A : Finset {i // P i}) (D : Finset {i // ¬P i}) :
    (subtypeSupport P A D).subtype P = A := by
  ext i
  simp [subtypeSupport]

omit [Fintype ι] in
@[simp]
theorem subtype_not_subtypeSupport
    (A : Finset {i // P i}) (D : Finset {i // ¬P i}) :
    (subtypeSupport P A D).subtype (fun i => ¬P i) = D := by
  ext i
  simp [subtypeSupport]

/-- Sum over each ambient support by its free and exterior pieces. -/
theorem sum_subtypeSupport [DecidableEq ι] (h : Finset ι → ℝ) :
    (∑ A : Finset {i // P i}, ∑ D : Finset {i // ¬P i}, h (subtypeSupport P A D)) =
      ∑ S : Finset ι, h S := by
  classical
  calc
    _ = ∑ AD : Finset {i // P i} × Finset {i // ¬P i},
        h (subtypeSupport P AD.1 AD.2) :=
      (Fintype.sum_prod_type (fun AD : Finset {i // P i} × Finset {i // ¬P i} =>
        h (subtypeSupport P AD.1 AD.2))).symm
    _ = _ := by
      apply Fintype.sum_equiv (subtypeSupportEquiv P)
      rintro ⟨A,D⟩
      rfl

/-- Exact restriction-mass transport for any statistic of the free support.
There is deliberately no restriction on exterior Fourier degree. -/
theorem restriction_mass_subtype [DecidableEq ι] {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : (ι → Bool) → ℝ)
    (L : Finset {i // P i} → ℝ) :
    (∑ y : {i // ¬P i} → Bool, weight p y *
      ∑ A : Finset {i // P i}, L A * coeff p (restrictCube P f y) A ^ 2) =
      ∑ S : Finset ι, L (S.subtype P) * coeff p f S ^ 2 := by
  classical
  calc
    (∑ y : {i // ¬P i} → Bool, weight p y *
        ∑ A : Finset {i // P i}, L A * coeff p (restrictCube P f y) A ^ 2) =
      ∑ A : Finset {i // P i}, L A *
        ∑ y : {i // ¬P i} → Bool, weight p y * coeff p (restrictCube P f y) A ^ 2 := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = ∑ A : Finset {i // P i}, ∑ D : Finset {i // ¬P i},
        L A * coeff p f (subtypeSupport P A D) ^ 2 := by
      simp_rw [restricted_coeff_sq_average_subtype P hp hp1, Finset.mul_sum]
    _ = ∑ S : Finset ι, L (S.subtype P) * coeff p f S ^ 2 := by
      simpa only [subtype_subtypeSupport] using
        sum_subtypeSupport P (fun S => L (S.subtype P) * coeff p f S ^ 2)

/-- Exact restricted Fourier mass at any selection of free-coordinate degrees. -/
theorem restriction_mass_subtype_filter [DecidableEq ι] {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : (ι → Bool) → ℝ)
    (Q : ℕ → Prop) [DecidablePred Q] :
    (∑ y : {i // ¬P i} → Bool, weight p y *
      ∑ A ∈ Finset.univ.filter (fun A : Finset {i // P i} => Q A.card),
        coeff p (restrictCube P f y) A ^ 2) =
      ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Q (S.filter P).card),
        coeff p f S ^ 2 := by
  classical
  simpa only [Finset.sum_filter, Finset.card_subtype, ite_mul, one_mul, zero_mul] using
    restriction_mass_subtype P hp hp1 f (fun A => if Q A.card then 1 else 0)

/-- The low-degree restriction identity in conditional-sum format. -/
theorem restriction_low_degree_mass_subtype [DecidableEq ι] {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : (ι → Bool) → ℝ) (k : ℝ) :
    (∑ S : Finset ι, if (S.filter P).Nonempty ∧ ((S.filter P).card : ℝ) ≤ k
      then coeff p f S ^ 2 else 0) =
      ∑ y : {i // ¬P i} → Bool, weight p y *
        ∑ A : Finset {i // P i}, if A.Nonempty ∧ (A.card : ℝ) ≤ k
          then coeff p (restrictCube P f y) A ^ 2 else 0 := by
  classical
  simpa only [Finset.sum_filter, Finset.card_pos] using
    (restriction_mass_subtype_filter P hp hp1 f (fun d => 0 < d ∧ (d : ℝ) ≤ k)).symm

end BiasedFourier
end Problem313

end

end OAI
