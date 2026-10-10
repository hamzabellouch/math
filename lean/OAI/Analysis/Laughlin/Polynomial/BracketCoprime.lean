import OAI.Analysis.Laughlin.Polynomial.BracketIrreducible

namespace OAI

namespace Laughlin
open MvPolynomial

theorem pair_outside_endpoint {N : ℕ} (i j k l : Fin N) (hij : i < j) (hkl : k < l)
    (hne : (i,j) ≠ (k,l)) : (k ≠ i ∧ k ≠ j) ∨ (l ≠ i ∧ l ≠ j) := by
  by_cases hk : k = i ∨ k = j
  · right
    rcases hk with rfl | rfl
    · constructor
      · exact ne_of_gt hkl
      · intro h
        subst l
        exact hne rfl
    · constructor
      · intro h
        subst l
        exact (lt_asymm hij hkl)
      · exact ne_of_gt hkl
  · exact Or.inl (not_or.mp hk)

theorem bracket_not_dvd_distinct {N : ℕ} (i j k l : Fin N) (hij : i < j) (hkl : k < l)
    (hne : (i,j) ≠ (k,l)) : ¬ bracket i j ∣ bracket k l := by
  intro hd
  rcases pair_outside_endpoint i j k l hij hkl hne with hk | hl
  · let point : SpinorVariables N → ℂ := fun z =>
      if z.2 then (if z.1 = k then 1 else 0) else (if z.1 = k then 0 else 1)
    let ev : MvPolynomial (SpinorVariables N) ℂ →+* ℂ := eval₂Hom (RingHom.id ℂ) point
    have h := map_dvd ev hd
    norm_num [ev,point,bracket,eval₂Hom,hk.1,hk.2,Ne.symm hk.1,Ne.symm hk.2,ne_of_gt hkl] at h
  · let point : SpinorVariables N → ℂ := fun z =>
      if z.2 then (if z.1 = l then 1 else 0) else (if z.1 = l then 0 else 1)
    let ev : MvPolynomial (SpinorVariables N) ℂ →+* ℂ := eval₂Hom (RingHom.id ℂ) point
    have h := map_dvd ev hd
    norm_num [ev,point,bracket,eval₂Hom,hl.1,hl.2,Ne.symm hl.1,Ne.symm hl.2,ne_of_lt hkl] at h

theorem bracket_isRelPrime {N : ℕ} (i j k l : Fin N) (hij : i < j) (hkl : k < l)
    (hne : (i,j) ≠ (k,l)) : IsRelPrime (bracket i j) (bracket k l) :=
  (bracket_irreducible i j (ne_of_lt hij)).isRelPrime_iff_not_dvd.mpr
    (bracket_not_dvd_distinct i j k l hij hkl hne)

theorem bracket_not_associated {N : ℕ} (i j k l : Fin N) (hij : i < j) (hkl : k < l)
    (hne : (i,j) ≠ (k,l)) : ¬ Associated (bracket i j) (bracket k l) := by
  intro h
  exact bracket_not_dvd_distinct i j k l hij hkl hne h.dvd

end Laughlin

end OAI
