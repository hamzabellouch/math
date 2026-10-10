import OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionRegularEuler

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

open scoped BigOperators Classical

variable {A : Type*} [CommRing A] [IsNoetherianRing A]
  [Ring.KrullDimLE 1 A] [IsLocalRing A]

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsLocalRing A] in
private theorem subtype_indicator_sum
    (S : Set (Ideal A)) [Fintype S] (P : Ideal A) (w : Ideal A → ℕ∞) :
    (∑ Q : S, if P = Q.val then w Q.val else 0) =
      if P ∈ S then w P else 0 := by
  classical
  by_cases hp : P ∈ S
  · rw [ite_eq_left hp]
    calc
      (∑ Q : S, if P = Q.val then w Q.val else 0) =
          (if P = P then w P else 0) := by
        apply Finset.sum_eq_single (⟨P, hp⟩ : S)
        · intro Q hQ hne
          have hne' : P ≠ Q.val := by
            intro h
            apply hne
            exact Subtype.ext h.symm
          simp only [hne', ↓reduceIte]
        · simp
      _ = w P := ite_eq_left rfl
  · rw [ite_eq_right hp]
    apply Finset.sum_eq_zero
    intro Q hQ
    have hne : P ≠ Q.val := fun h => hp (h.symm ▸ Q.property)
    simp only [hne, ↓reduceIte]

theorem regular_ring_onecut_length (x : A) (hx : x ∈ nonZeroDivisors A) :
    Module.length A (A ⧸ Ideal.span {x}) =
      minimalPrimeCutSum (⊥ : Ideal A) x := by
  classical
  obtain ⟨n, J, f, hp, he, hcounts⟩ := exists_regular_onecut_sum_and_local_counts x hx
  let ps : ℕ → Ideal A := fun i => (J i).colon {f i}
  let w : Ideal A → ℕ∞ := fun P => Module.length A (A ⧸ (P ⊔ Ideal.span {x}))
  have hsumNat : (Module.length A (A ⧸ Ideal.span {x})).toNat =
      ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then (w (ps i)).toNat else 0 := by
    exact_mod_cast he
  have hsumENat : ((Module.length A (A ⧸ Ideal.span {x})).toNat : ℕ∞) =
      ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then ((w (ps i)).toNat : ℕ∞) else 0 := by
    exact_mod_cast hsumNat
  have hzeroCut : Module.length A (A ⧸ Ideal.span {x}) ≠ ⊤ := by
    exact Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton A hx)
  rw [ENat.natCast_toNat hzeroCut] at hsumENat
  have hsum : Module.length A (A ⧸ Ideal.span {x}) =
      ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then w (ps i) else 0 := by
    refine hsumENat.trans (Finset.sum_congr rfl ?_)
    intro i hi
    split_ifs with hmin
    · exact ENat.natCast_toNat (regular_cut_length_ne_top x hx (ps i))
    · rfl
  let : Fintype ((⊥ : Ideal A).minimalPrimes) :=
    ((⊥ : Ideal A).finite_minimalPrimes_of_isNoetherianRing A).fintype
  have hterm (P : (⊥ : Ideal A).minimalPrimes) :
      (letI : P.val.IsPrime := P.property.1.1
       Module.length (Localization.AtPrime P.val)
          (Localization.AtPrime P.val ⧸ (⊥ : Ideal A).map
            (algebraMap A (Localization.AtPrime P.val))) * w P.val) =
        ∑ i ∈ Finset.range n, if ps i = P.val then w P.val else 0 := by
    let : P.val.IsPrime := P.property.1.1
    rw [hcounts P.val P.property, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : ps i = P.val
    · simp only [ps] at h
      simp only [h, ↓reduceIte, one_mul, ps]
    · simp only [ps] at h
      simp only [h, ↓reduceIte, zero_mul, ps]
  calc
    Module.length A (A ⧸ Ideal.span {x}) =
        ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then w (ps i) else 0 := hsum
    _ = ∑ i ∈ Finset.range n, ∑ P : (⊥ : Ideal A).minimalPrimes,
        if ps i = P.val then w P.val else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (subtype_indicator_sum ((⊥ : Ideal A).minimalPrimes) (ps i) w).symm
    _ = ∑ P : (⊥ : Ideal A).minimalPrimes, ∑ i ∈ Finset.range n,
        if ps i = P.val then w P.val else 0 := Finset.sum_comm
    _ = minimalPrimeCutSum (⊥ : Ideal A) x := by
      unfold minimalPrimeCutSum
      apply Finset.sum_congr rfl
      intro P hP
      exact (hterm P).symm

end PiExponentJets.W28.LocalIntersection

end OAI
