import OAI.Probability.DirectionalWalk.ExperimentContact

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def latePrefixEvent {d ι : ℕ} (e : Step d) (k r N : ℕ)
    (E : Word d → Fin ι → Set (Path d)) (start : Word d → Fin ι → Site d) :
    Set (Path d × Path d) :=
  ⋃ a : {a : Word d | AxisBridgeWord e k a}, ⋃ q : Fin ι,
    ⋃ b : {b | upperContactWord 0 (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b},
      (wordCylinder a ∩ (shiftPath (-wordEnd a) ∘ tailPath a.val.1) ⁻¹' (E a q ∩ wordCylinder b)) ×ˢ
        (shiftPath (start a q) ⁻¹' contactAvoid b)

lemma latePrefixEvent_bound {d ι : ℕ} [NeZero ι]
    (μ : Measure (Row d)) [IsProbabilityMeasure μ] (hell : StrictEllipticity μ)
    (e : Step d) (k r N m : ℕ) (hrN : r ≤ N)
    (E : Word d → Fin ι → Set (Path d)) (hE : ∀ a q, MeasurableSet (E a q))
    (hdis : ∀ a, Pairwise (fun i j => Disjoint (E a i) (E a j)))
    (start : Word d → Fin ι → Site d)
    (hstart : ∀ a, AxisBridgeWord e k a → ∀ q, axisHeight e (start a q) = (N : ℤ)-1)
    (hΔ : axisReachProb μ e r-axisReachProb μ e N ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    ((annealed μ 0).prod (conditioned μ (axisDirection (oppositeStep e))))
      (latePrefixEvent e k r N E start) ≤
      (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  have : IsFiniteMeasure (conditioned μ (axisDirection (oppositeStep e))) := by
    unfold conditioned
    infer_instance
  unfold latePrefixEvent
  calc
    _ ≤ ∑' a : {a : Word d | AxisBridgeWord e k a}, ∑' q : Fin ι,
      ∑' b : {b | upperContactWord 0 (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b},
        ((annealed μ 0).prod (conditioned μ (axisDirection (oppositeStep e))))
          ((wordCylinder a ∩ (shiftPath (-wordEnd a) ∘ tailPath a.val.1) ⁻¹' (E a q ∩ wordCylinder b)) ×ˢ
            (shiftPath (start a q) ⁻¹' contactAvoid b)) := by
        apply (measure_iUnion_le _).trans
        apply ENNReal.tsum_le_tsum
        intro a
        apply (measure_iUnion_le _).trans
        exact ENNReal.tsum_le_tsum (fun q => measure_iUnion_le _)
    _ = (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
      (∑' a : {a : Word d | AxisBridgeWord e k a}, ∑ q,
        ∑' b : {b | upperContactWord 0 (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b},
          annealed μ 0 (wordCylinder a ∩ (shiftPath (-wordEnd a) ∘ tailPath a.val.1) ⁻¹' (E a q ∩ wordCylinder b)) *
          annealed μ (start a q) (avoids (axisUpper e N) ∩ contactAvoid b)) := by
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro a
        rw [tsum_fintype,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro b
        rw [Measure.prod_prod,conditioned_negative_shift μ e _ N (hstart _ a.property _) _ (measurableSet_contactAvoid _)]
        ac_rfl
    _ ≤ _ := mul_le_mul_right (prefix_contact_total_bound μ hell e k r N m hrN E hE hdis start hΔ) _

def prependRelative {d : ℕ} (a : Word d) (R : Path d) : Path d :=
  concatPath a.1 (wordPath a) (shiftPath (wordEnd a) R)

lemma measurable_prependRelative {d : ℕ} (a : Word d) : Measurable (prependRelative a) := by
  apply Measurable.of_eval
  intro j
  by_cases hj : j < a.1
  · simpa only [prependRelative,concatPath,ite_eq_left hj] using
      (measurable_const : Measurable (fun _ : Path d => wordPath a j))
  · have hm : Measurable (fun R : Path d => R (j-a.1)) := measurable_pi_apply _
    simpa only [prependRelative,concatPath,ite_eq_right hj,shiftPath] using hm.add_const (wordEnd a)

lemma prependRelative_recover {d : ℕ} (a : Word d) (X : Path d) (hX : X ∈ wordCylinder a) :
    prependRelative a (shiftPath (-wordEnd a) (tailPath a.1 X)) = X := by
  funext j
  by_cases hj : j < a.1
  · simpa only [prependRelative,concatPath,ite_eq_left hj] using (hX j hj.le).symm
  · simp only [prependRelative,concatPath,ite_eq_right hj,shiftPath,tailPath,
      Nat.add_sub_of_le (Nat.le_of_not_gt hj),neg_add_cancel_right]

lemma latePrefixEvent_of_contact {d ι : ℕ} (e : Step d)
    (k r N : ℕ) (hr : k ≤ r) (hN : k ≤ N)
    (E : Fin ι → Set (Path d)) (z : Fin ι → Site d)
    (X Y : Path d) (q : Fin ι) (hE : X ∈ E q)
    (t τ : ℕ) (htτ : t ≤ τ)
    (hold : AxisBridgeWord e k (prefixWord t X))
    (hband : ∀ j, t ≤ j → j ≤ τ → (k : ℤ) ≤ axisHeight e (X j) ∧ axisHeight e (X j) < (N : ℤ))
    (hreached : ∃ j, t ≤ j ∧ j ≤ τ ∧ (r : ℤ) ≤ axisHeight e (X j))
    (hhit : ∃ j, Y j+z q = X τ)
    (hbefore : ∀ i, t ≤ i → i < τ → ∀ j, Y j+z q ≠ X i) :
    (X,Y) ∈ latePrefixEvent e k (r-k) (N-k)
      (fun a q => prependRelative a ⁻¹' E q) (fun a q => z q-wordEnd a) := by
  let a := prefixWord t X
  let R := shiftPath (-wordEnd a) (tailPath t X)
  let b := prefixWord (τ-t) R
  have ha : X ∈ wordCylinder a := fun j hj => (wordPath_prefixWord t X hj).symm
  have hend : wordEnd a = X t := wordPath_prefixWord t X le_rfl
  have hbpath (j : ℕ) (hj : j ≤ τ-t) : wordPath b j = X (t+j)-X t := by
    rw [wordPath_prefixWord (τ-t) R hj]
    change X (t+j)+(-wordEnd a) = _
    rw [hend,sub_eq_add_neg]
  have hb : upperContactWord 0 (axisUpper e ((r-k : ℕ) : ℤ))
      (axisLower e 0 ∪ axisUpper e ((N-k : ℕ) : ℤ)) b := by
    refine ⟨?_,?_,?_⟩
    · rw [hbpath 0 (Nat.zero_le _),Nat.add_zero,sub_self]
    · obtain ⟨j,htj,hjτ,hjr⟩ := hreached
      refine ⟨j-t,by change j-t ≤ τ-t;omega,?_⟩
      rw [hbpath (j-t) (by omega),Nat.add_sub_of_le htj]
      change ((r-k : ℕ) : ℤ) ≤ axisHeight e (X j-X t)
      rw [sub_eq_add_neg,axisHeight_add,axisHeight_neg,← hend,hold.1,Nat.cast_sub hr]
      omega
    · intro j hj
      rw [hbpath j hj]
      have hjτ : t+j ≤ τ := by change j ≤ τ-t at hj;omega
      obtain ⟨hlo,hhi⟩ := hband (t+j) (by omega) hjτ
      change ¬(axisHeight e (X (t+j)-X t) < (0 : ℤ) ∨
        ((N-k : ℕ) : ℤ) ≤ axisHeight e (X (t+j)-X t))
      rw [sub_eq_add_neg,axisHeight_add,axisHeight_neg,← hend,hold.1,Nat.cast_sub hN]
      omega
  have hca : shiftPath (z q-wordEnd a) Y ∈ contactAvoid b := by
    rw [contactAvoid_iff_firstHit]
    constructor
    · obtain ⟨j,hj⟩ := hhit
      refine ⟨j,?_⟩
      change Y j+(z q-wordEnd a) = wordPath b (τ-t)
      rw [hbpath (τ-t) le_rfl,Nat.add_sub_of_le htτ,hend]
      rw [sub_eq_add_neg,← add_assoc,hj,sub_eq_add_neg]
    · intro i hi
      rintro ⟨j,hj⟩
      apply hbefore (t+i) (by omega) (by change i < τ-t at hi;omega) j
      rw [hbpath i hi.le] at hj
      change Y j+(z q-wordEnd a) = X (t+i)-X t at hj
      rw [hend,sub_eq_add_neg,sub_eq_add_neg,← add_assoc] at hj
      exact add_right_cancel hj
  refine Set.mem_iUnion.mpr ⟨⟨a,hold⟩,Set.mem_iUnion.mpr ⟨q,Set.mem_iUnion.mpr ⟨⟨b,hb⟩,?_⟩⟩⟩
  refine ⟨⟨ha,?_,?_⟩,hca⟩
  · change prependRelative a R ∈ E q
    exact (prependRelative_recover a X ha).symm ▸ hE
  · exact fun j hj => (wordPath_prefixWord (τ-t) R hj).symm

end DirectionalZeroOne

end OAI
