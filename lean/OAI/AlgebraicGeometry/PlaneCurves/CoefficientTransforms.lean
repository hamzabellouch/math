import OAI.AlgebraicGeometry.PlaneCurves.SectionOrder

namespace OAI

/-!
# Coefficient and polynomial transforms for marked normal polynomials
-/

section

namespace Nagata.CoefficientSpaces

/-- The coefficient operation in Pi^-m F(Pi*v), with its exact algebraic
identity valid even at the zeros of Pi. -/
theorem exists_transformed_coefficient {τ L Q : ℂ}
    (hτ : τ ≠ 0) (hL : L ≠ 0) (hQ : Q ≠ 0) (d : ℤ) (m j : ℕ)
    (P : Nagata.W08.automorphicSections τ 9 Q)
    (f : Nagata.W08.automorphicSections τ (3 * (d - 3 * (j : ℤ)))
      (L ^ (d - 3 * (j : ℤ))))
    (hzero : j ≤ m → ∀ z ≠ 0, P.val z = 0 → deriv P.val z ≠ 0 ∧
      ((m - j : ℕ) : ℕ∞) ≤ analyticOrderAt f.val z) :
    ∃ g ∈ coefficientSpace τ L Q d (m : ℤ) (j : ℤ) P.val,
      ∀ z ≠ 0, P.val z ^ m * g z = P.val z ^ j * f.val z := by
  by_cases hj : j ≤ m
  · have hjZ : (j : ℤ) ≤ (m : ℤ) := by exact_mod_cast hj
    have he : ((m : ℤ) - (j : ℤ)).toNat = m - j := by omega
    obtain ⟨g, hg, hf⟩ := exists_low_holomorphic_coefficient hτ hL hQ d (m : ℤ)
      (j : ℤ) hjZ P f (by simpa only [he] using hzero hj)
    refine ⟨g, hg, ?_⟩
    intro z hz
    rw [hf z hz, he, ← mul_assoc, ← pow_add]
    rw [Nat.add_sub_of_le hj]
  · have hjZ : (m : ℤ) < (j : ℤ) := by exact_mod_cast (lt_of_not_ge hj)
    have he : ((j : ℤ) - (m : ℤ)).toNat = j - m := by omega
    refine ⟨multiplyPower P.val (j - m) f.val, ?_, ?_⟩
    · apply (mem_coefficientSpace_second hjZ).mpr
      exact ⟨f.val, f.property, by rw [he]⟩
    · intro z hz
      change P.val z ^ m * (P.val z ^ (j - m) * f.val z) = P.val z ^ j * f.val z
      rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (le_of_lt (lt_of_not_ge hj))]

/-- The weighted coefficient identity cannot turn a genuine nonzero original
section into the zero coefficient. -/
theorem transformed_coefficient_nonzero {τ L Q : ℂ} (d : ℤ) (m j : ℕ)
    (P : Nagata.W08.automorphicSections τ 9 Q)
    (hPfin : ∀ z ≠ 0, analyticOrderAt P.val z ≠ ⊤)
    (f : Nagata.W08.automorphicSections τ (3 * (d - 3 * (j : ℤ)))
      (L ^ (d - 3 * (j : ℤ)))) (g : ℂ → ℂ)
    (hfactor : ∀ z ≠ 0, P.val z ^ m * g z = P.val z ^ j * f.val z)
    (hf : f ≠ 0) : g ≠ 0 := by
  intro hg
  apply hf
  apply multiplySection_injective τ (L ^ (d - 3 * (j : ℤ)))
    (3 * (d - 3 * (j : ℤ))) P.val j
    (Nagata.W08.automorphicSection_analyticOnNhd P) hPfin
  funext z
  change P.val z ^ j * f.val z = P.val z ^ j * 0
  by_cases hz : z = 0
  · subst z
    rw [f.property.1]
  · rw [← hfactor z hz, hg]
    simp

end Nagata.CoefficientSpaces

end

section

namespace Nagata.CoefficientSpaces
open scoped BigOperators

theorem exists_transformed_polynomial {τ L Q : ℂ}
    (hτ : τ ≠ 0) (hL : L ≠ 0) (hQ : Q ≠ 0) (d : ℤ) (m : ℕ)
    (P : Nagata.W08.automorphicSections τ 9 Q)
    (hPsimple : ∀ z ≠ 0, P.val z = 0 → deriv P.val z ≠ 0)
    (F : Polynomial (ℂ → ℂ))
    (hbound : ∀ j : ℕ, (d / 3).toNat < j → F.coeff j = 0)
    (hsource : ∀ j : ℕ, F.coeff j ∈ Nagata.W08.automorphicSections τ
      (3 * (d - 3 * (j : ℤ))) (L ^ (d - 3 * (j : ℤ))))
    (hzero : ∀ j : ℕ, j ≤ (d / 3).toNat → j ≤ m → ∀ z ≠ 0,
      P.val z = 0 → ((m - j : ℕ) : ℕ∞) ≤ analyticOrderAt (F.coeff j) z) :
    ∃ G : polynomialSections τ L Q d (m : ℤ) P.val,
      (∀ j : ℕ, ∀ z ≠ 0, P.val z ^ m * G.val.coeff j z =
        P.val z ^ j * F.coeff j z) ∧ (F ≠ 0 → G ≠ 0) := by
  classical
  let N := (d / 3).toNat
  have hex : ∀ j : Fin (N + 1), ∃ g ∈ coefficientSpace τ L Q d (m : ℤ) (j.val : ℤ) P.val,
      ∀ z ≠ 0, P.val z ^ m * g z = P.val z ^ j.val * F.coeff j.val z := by
    intro j
    exact exists_transformed_coefficient hτ hL hQ d m j.val P
      ⟨F.coeff j.val, hsource j.val⟩ (fun hj z hz hPz =>
        ⟨hPsimple z hz hPz, hzero j.val (Nat.le_of_lt_succ j.isLt) hj z hz hPz⟩)
  choose g hg hfactor using hex
  let c : (j : Fin (N + 1)) → coefficientSpace τ L Q d (m : ℤ) (j.val : ℤ) P.val :=
    fun j => ⟨g j, hg j⟩
  let e := Nagata.Workers.W10.polynomialSectionCoordinates τ L Q d (m : ℤ) P.val
  let G := e.symm c
  have hcoeff (j : Fin (N + 1)) : G.val.coeff j.val = g j := by
    have hh := congrArg (fun v => (v j).val) (e.apply_symm_apply c)
    exact hh
  have hfact : ∀ j : ℕ, ∀ z ≠ 0, P.val z ^ m * G.val.coeff j z =
      P.val z ^ j * F.coeff j z := by
    intro j z hz
    by_cases hj : j ≤ N
    · let ji : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
      rw [hcoeff ji]
      exact hfactor ji z hz
    · have hj' : N < j := lt_of_not_ge hj
      rw [G.property.1 j hj', hbound j hj']
      simp
  refine ⟨G, hfact, ?_⟩
  intro hF hG
  apply hF
  apply Polynomial.ext
  intro j
  by_cases hj : j ≤ N
  · by_contra hfj
    let f : Nagata.W08.automorphicSections τ (3 * (d - 3 * (j : ℤ)))
        (L ^ (d - 3 * (j : ℤ))) := ⟨F.coeff j, hsource j⟩
    have hf : f ≠ 0 := by
      intro hf0
      apply hfj
      exact congrArg Subtype.val hf0
    have hPfin : ∀ z ≠ 0, analyticOrderAt P.val z ≠ ⊤ := by
      intro z hz
      have hp := Nagata.W08.automorphicSection_analyticAt P hz
      by_cases hPz : P.val z = 0
      · rw [hp.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hPz (hPsimple z hz hPz)]
        simp
      · rw [hp.analyticOrderAt_eq_zero.mpr hPz]
        simp
    have hg := transformed_coefficient_nonzero d m j P hPfin f (G.val.coeff j)
      (hfact j) hf
    apply hg
    have hGval := congrArg Subtype.val hG
    rw [hGval]
    rfl
  · exact hbound j (lt_of_not_ge hj)

/-- Scalar evaluation may be taken over the common finite degree range. -/
theorem scalarExpression_eq_range (F : Polynomial (ℂ → ℂ)) (N : ℕ)
    (hbound : ∀ j, N < j → F.coeff j = 0) (z v : ℂ) :
    scalarExpression F z v = ∑ j ∈ Finset.range (N + 1), F.coeff j z * v ^ j := by
  apply Polynomial.sum_eq_of_subset
  · intro j
    simp
  · intro j hj
    apply Finset.mem_range.mpr
    have hne := Polynomial.mem_support_iff.mp hj
    by_contra h
    exact hne (hbound j (by omega))

/-- The coefficient identities are the manuscript's actual local scalar
substitution identity, not merely a matrix or an abstract coefficient model. -/
theorem scalarExpression_transform (F G : Polynomial (ℂ → ℂ)) (N m : ℕ)
    (hF : ∀ j, N < j → F.coeff j = 0) (hG : ∀ j, N < j → G.coeff j = 0)
    (P : ℂ → ℂ) (z v : ℂ)
    (hfactor : ∀ j, P z ^ m * G.coeff j z = P z ^ j * F.coeff j z) :
    P z ^ m * scalarExpression G z v = scalarExpression F z (P z * v) := by
  rw [scalarExpression_eq_range G N hG, scalarExpression_eq_range F N hF,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← mul_assoc, hfactor j, mul_pow]
  ring

end Nagata.CoefficientSpaces

end

section

namespace Nagata.CoefficientSpaces
open scoped BigOperators

/-- The actual nine-theta product as a degree-nine section. -/
noncomputable def nineThetaSection {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0)
    (a : Fin 9 → ℂ) (ha : ∀ i, a i ≠ 0) :
    Nagata.W08.automorphicSections τ 9 (∏ i, -a i) := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    Nagata.W08.markedThetaSection hτ hτ0 a ha

/-- Nine ordinary numerator-order conditions suffice: period automorphy propagates
orders to the complete divisor, and the genuine theta product supplies simplicity. -/
theorem exists_marked_transformed_polynomial {τ L : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hL : L ≠ 0)
    (a : Fin 9 → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j => ∀ k : ℤ, a i ≠ a j * τ ^ k))
    (d : ℤ) (m : ℕ) (F : Polynomial (ℂ → ℂ))
    (hbound : ∀ j : ℕ, (d / 3).toNat < j → F.coeff j = 0)
    (hsource : ∀ j : ℕ, F.coeff j ∈ Nagata.W08.automorphicSections τ
      (3 * (d - 3 * (j : ℤ))) (L ^ (d - 3 * (j : ℤ))))
    (hmarked : ∀ j : ℕ, j ≤ (d / 3).toNat → j ≤ m → ∀ i : Fin 9,
      ((m - j : ℕ) : ℕ∞) ≤ analyticOrderAt (F.coeff j) (a i)) :
    ∃ G : polynomialSections τ L (∏ i, -a i) d (m : ℤ)
        (nineThetaSection hτ hτ0 a ha).val,
      (∀ j : ℕ, ∀ z ≠ 0, (nineThetaSection hτ hτ0 a ha).val z ^ m *
        G.val.coeff j z = (nineThetaSection hτ hτ0 a ha).val z ^ j * F.coeff j z) ∧
      (F ≠ 0 → G ≠ 0) := by
  have hQ : (∏ i, -a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => neg_ne_zero.mpr (ha i))
  refine exists_transformed_polynomial hτ0 hL hQ d m
    (nineThetaSection hτ hτ0 a ha) ?_ F hbound hsource ?_
  · intro z hz hzero
    exact Nagata.W08.markedThetaSection_zero_has_nonzero_deriv hτ hτ0 a ha hdisjoint hz hzero
  · intro j hj hjm z hz hzero
    obtain ⟨i, k, rfl⟩ := (Nagata.W08.markedThetaSection_zero_iff hτ hτ0 a ha hz).mp hzero
    rw [automorphic_order_orbit hτ0 (zpow_ne_zero _ hL)
      (⟨F.coeff j, hsource j⟩ : Nagata.W08.automorphicSections τ
        (3 * (d - 3 * (j : ℤ))) (L ^ (d - 3 * (j : ℤ)))) (ha i) k]
    exact hmarked j hj hjm i

end Nagata.CoefficientSpaces

end

end OAI
