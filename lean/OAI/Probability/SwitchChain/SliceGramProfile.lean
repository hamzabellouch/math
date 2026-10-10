import OAI.Probability.SwitchChain.SliceGramOrbit
import OAI.Probability.SwitchChain.SliceGramAction
import OAI.Probability.SwitchChain.SliceNormalizedFamily

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceGramProfile

variable {V : Type*} [Fintype V] [DecidableEq V]

def profile (q t : ℕ) : ℝ :=
  if h : ∃ p : Finset V × Finset V,
      p.1.card = 2 ∧ p.2.card = 2 ∧ (p.1 ∩ p.2).card = t then
    SliceGramOrbit.gram q h.choose.1 h.choose.2
  else 0

theorem gram_eq_profile (q : ℕ) (P Q : Finset V)
    (hP : P.card = 2) (hQ : Q.card = 2) :
    SliceGramOrbit.gram q P Q = profile (V := V) q (P ∩ Q).card := by
  unfold profile
  split_ifs with h
  · exact SliceGramOrbit.gram_eq_of_intersection q P Q h.choose.1 h.choose.2
      hP hQ h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2.symm
  · exact False.elim (h ⟨(P,Q), hP, hQ, rfl⟩)

theorem twice_column_inner (q : ℕ) (hq : q ≤ Fintype.card V)
    (hp : 0 < SliceMoments.equalMean (Finset.univ : Finset V) q)
    (hp1 : SliceMoments.equalMean (Finset.univ : Finset V) q < 1)
    (i j k l : V) (hij : i ≠ j) (hkl : k ≠ l) :
    2 * ⟪SliceNormalized.column q i j, SliceNormalized.column q k l⟫ =
      SliceGramOrbit.gram q {i,j} {k,l} /
        (SliceMoments.equalMean (Finset.univ : Finset V) q *
          (1 - SliceMoments.equalMean (Finset.univ : Finset V) q)) := by
  rw [SliceNormalized.column_inner q hq hp hp1 i j k l hij hkl]
  simp only [SliceGramOrbit.gram, SliceGramOrbit.centeredPair_pair q i j hij,
    SliceGramOrbit.centeredPair_pair q k l hkl]
  have hp0 := hp.ne'
  have hc : 1 - SliceMoments.equalMean (Finset.univ : Finset V) q ≠ 0 := by linarith
  field_simp

theorem gram_of_intersection_two (q : ℕ) (hq : q ≤ Fintype.card V)
    (i j k l : V) (hij : i ≠ j) (hkl : k ≠ l)
    (hI : (({i,j} : Finset V) ∩ {k,l}).card = 2) :
    SliceGramOrbit.gram q {i,j} {k,l} =
      SliceMoments.equalMean (Finset.univ : Finset V) q *
        (1 - SliceMoments.equalMean (Finset.univ : Finset V) q) := by
  have hg := SliceGramOrbit.gram_eq_of_intersection q {i,j} {k,l} {i,j} {i,j}
    (by simp [hij]) (by simp [hkl]) (by simp [hij]) (by simp [hij])
    (by simpa [hij] using hI)
  rw [hg]
  simp only [SliceGramOrbit.gram, SliceGramOrbit.centeredPair_pair q i j hij,
    ← pow_two]
  exact SliceMoments.average_centeredEqual_sq Finset.univ q (by simpa using hq)
    i j (Finset.mem_univ i) (Finset.mem_univ j) hij

theorem exists_normalized_orbit_entries (q : ℕ) (hq : q ≤ Fintype.card V)
    (hp : 0 < SliceMoments.equalMean (Finset.univ : Finset V) q)
    (hp1 : SliceMoments.equalMean (Finset.univ : Finset V) q < 1) :
    ∃ b d : ℝ, ∀ i j : V, i ≠ j → ∀ k l : V, k ≠ l →
      2 * ⟪SliceNormalized.column q i j, SliceNormalized.column q k l⟫ =
        SliceCoefficients.orbitKernel 1 b d i j k l := by
  let v := SliceMoments.equalMean (Finset.univ : Finset V) q *
    (1 - SliceMoments.equalMean (Finset.univ : Finset V) q)
  have hv : v ≠ 0 := mul_ne_zero hp.ne' (by linarith)
  refine ⟨profile (V := V) q 1 / v, profile (V := V) q 0 / v, ?_⟩
  intro i j hij k l hkl
  rw [twice_column_inner q hq hp hp1 i j k l hij hkl,
    SliceCoefficients.orbitKernel_eq_intersection_card _ _ _ i j k l hij hkl]
  change SliceGramOrbit.gram q {i,j} {k,l} / v = _
  by_cases h2 : (({i,j} : Finset V) ∩ {k,l}).card = 2
  · rw [ite_eq_left h2, gram_of_intersection_two q hq i j k l hij hkl h2]
    exact div_self hv
  · rw [ite_eq_right h2, gram_eq_profile q {i,j} {k,l} (by simp [hij]) (by simp [hkl])]
    by_cases h1 : (({i,j} : Finset V) ∩ {k,l}).card = 1
    · rw [ite_eq_left h1, h1]
    · rw [ite_eq_right h1]
      have hle : (({i,j} : Finset V) ∩ {k,l}).card ≤ 2 := by
        calc
          _ ≤ ({i,j} : Finset V).card := Finset.card_le_card Finset.inter_subset_left
          _ = 2 := by simp [hij]
      have h0 : (({i,j} : Finset V) ∩ {k,l}).card = 0 := by omega
      rw [h0]

end Problem315.SliceGramProfile

end

end OAI
