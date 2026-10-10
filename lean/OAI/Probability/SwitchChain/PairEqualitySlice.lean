import OAI.Probability.SwitchChain.PairEqualityProjection
import OAI.Probability.SwitchChain.SliceMoments

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem observable_eq_equalIndicator (i j k l : Fin n) (G : GraphState n d)
    (ha : active i j k l G) :
    observable i k l G = SliceMoments.equalIndicator k l (leftSet G.val i j) := by
  have hk := (mem_singletonSet G.val i j k).mp ha.1
  have hl := (mem_singletonSet G.val i j l).mp ha.2
  have hkl : (k ∈ leftSet G.val i j) ↔ G.val.Adj i k := by
    rw [mem_leftSet]
    simp only [hk.1, true_and]
    rcases hk.2 with h | h <;> tauto
  have hll : (l ∈ leftSet G.val i j) ↔ G.val.Adj i l := by
    rw [mem_leftSet]
    simp only [hl.1, true_and]
    rcases hl.2 with h | h <;> tauto
  change (if G.val.Adj i k ↔ G.val.Adj i l then (1:ℝ) else 0) = _
  simp only [SliceMoments.equalIndicator, hkl, hll]

theorem assignment_sum (G : GraphState n d) (i j : Fin n)
    (f : Finset (Fin n) → ℝ) :
    (∑ T : Assignment G.val i j, f T.val) =
      ∑ T ∈ (singletonSet G.val i j).powersetCard (leftSet G.val i j).card, f T := by
  let e : Assignment G.val i j ≃
      ↥((singletonSet G.val i j).powersetCard (leftSet G.val i j).card) :=
    { toFun := fun T => ⟨T.val, Finset.mem_powersetCard.mpr T.property⟩
      invFun := fun T => ⟨T.val, Finset.mem_powersetCard.mp T.property⟩
      left_inv := fun T => by apply Subtype.ext; rfl
      right_inv := fun T => by apply Subtype.ext; rfl }
  calc
    _ = ∑ T : ↥((singletonSet G.val i j).powersetCard (leftSet G.val i j).card),
        f T.val := e.sum_comp (fun T => f T.val)
    _ = _ := Finset.sum_coe_sort _ f

theorem reconstructed_sameFiber (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (T : Assignment G.val i j) :
    SameFiber {i,j} G.val ((stateFiberEquiv G i j hij).symm T).val.val := by
  apply (sameFiber_iff_key_eq i j hij _ _).mpr
  exact ((stateFiberEquiv G i j hij).symm T).property.symm

theorem observable_reconstruction (G : GraphState n d) (i j k l : Fin n)
    (hij : i ≠ j) (ha : active i j k l G) (T : Assignment G.val i j) :
    observable i k l ((stateFiberEquiv G i j hij).symm T).val =
      SliceMoments.equalIndicator k l T.val := by
  have hA := (active_sameFiber i j k l hij (reconstructed_sameFiber G i j hij T)).mp ha
  rw [observable_eq_equalIndicator i j k l _ hA]
  rw [stateFiberEquiv_symm_apply, leftSet_trade]

theorem expectation_observable_eq_mean (G : GraphState n d) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) (ha : active i j k l G) :
    expectation n d {i,j} (observable i k l) G =
      SliceMoments.equalMean (singletonSet G.val i j) (leftSet G.val i j).card := by
  rw [expectation_eq_assignment_average G i j hij]
  simp_rw [observable_reconstruction G i j k l hij ha]
  rw [assignment_sum]
  exact SliceMoments.average_equalIndicator _ _
    (Finset.card_le_card (leftSet_subset_singletonSet G.val i j)) k l ha.1 ha.2 hkl

theorem centered_eq_slice (G : GraphState n d) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) (ha : active i j k l G) :
    centered i j k l G = SliceMoments.centeredEqual (singletonSet G.val i j)
      (leftSet G.val i j).card k l (leftSet G.val i j) := by
  unfold centered
  rw [fluctuation_eq_sub]
  change observable i k l G - expectation n d {i,j} (observable i k l) G = _
  rw [observable_eq_equalIndicator i j k l G ha,
    expectation_observable_eq_mean G i j k l hij hkl ha]
  rfl

theorem centered_reconstruction (G : GraphState n d) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) (ha : active i j k l G)
    (T : Assignment G.val i j) :
    centered i j k l ((stateFiberEquiv G i j hij).symm T).val =
      SliceMoments.centeredEqual (singletonSet G.val i j)
        (leftSet G.val i j).card k l T.val := by
  unfold centered
  rw [fluctuation_eq_sub]
  change observable i k l ((stateFiberEquiv G i j hij).symm T).val -
    expectation n d {i,j} (observable i k l) ((stateFiberEquiv G i j hij).symm T).val = _
  rw [observable_reconstruction G i j k l hij ha]
  rw [(expectation_mem {i,j} (observable i k l)) _ G
    (reconstructed_sameFiber G i j hij T).symm]
  rw [expectation_observable_eq_mean G i j k l hij hkl ha]
  rfl

theorem mem_equalitySpace_iff_assignment (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) (f : StateSpace n d) :
    f ∈ equalitySpace i j k l ↔
      ∀ G : GraphState n d, ∃ c : ℝ, ∀ T : Assignment G.val i j,
        f ((stateFiberEquiv G i j hij).symm T).val =
          c * (if active i j k l G then
            SliceMoments.centeredEqual (singletonSet G.val i j)
              (leftSet G.val i j).card k l T.val else 0) := by
  constructor
  · intro hf G
    obtain ⟨c,hc⟩ := hf G
    refine ⟨c, fun T => ?_⟩
    have h := hc _ (reconstructed_sameFiber G i j hij T)
    by_cases ha : active i j k l G
    · simpa only [ite_eq_left ha, centered_reconstruction G i j k l hij hkl ha T] using h
    · simpa only [ite_eq_right ha] using h
  · intro hf G
    obtain ⟨c,hc⟩ := hf G
    refine ⟨c, fun H h => ?_⟩
    let H' : StateFiber G i j :=
      ⟨H, ((sameFiber_iff_key_eq i j hij G.val H.val).mp h).symm⟩
    let T : Assignment G.val i j := stateFiberEquiv G i j hij H'
    have hrecon : ((stateFiberEquiv G i j hij).symm T).val = H :=
      congrArg Subtype.val ((stateFiberEquiv G i j hij).symm_apply_apply H')
    have hT := hc T
    rw [hrecon] at hT
    by_cases ha : active i j k l G
    · have hz := centered_reconstruction G i j k l hij hkl ha T
      rw [hrecon] at hz
      simpa only [ite_eq_left ha, hz] using hT
    · simpa only [ite_eq_right ha] using hT

end Problem315.PairEquality

end

end OAI
