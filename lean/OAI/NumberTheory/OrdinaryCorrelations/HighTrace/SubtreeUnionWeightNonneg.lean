import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ListLocalLeOne
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TreeOccurrences

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma subtreeUnionWeight_nonneg (w : ClosedLine h ℓ) (p : S.Index) (E : Finset (Fin ℓ)) :
    0 ≤ subtreeUnionWeight w p E := by
  have ha : 0 ≤ S.amplitude p := by
    unfold amplitude
    split_ifs
    · exact A_pos.le
    · exact zero_le_one
  exact mul_nonneg (pow_nonneg ha _) (prod_nonneg (fun _ _ => pow_nonneg (beta_nonneg p) _))

@[simp] lemma subtreeUnionWeight_empty (w : ClosedLine h ℓ) (p : S.Index) :
    subtreeUnionWeight w p ∅ = 1 := by simp [subtreeUnionWeight, edgeVertices]

lemma activity_nonneg (p : S.Index) (a : ZMod (p : ℕ)) (v : ℤ) :
    0 ≤ activity (p : ℕ) a v := by unfold activity; split_ifs <;> norm_num

lemma activity_mean (p : S.Index) (v : ℤ) :
    avg (fun a : ZMod (p : ℕ) => activity (p : ℕ) a v) = (p : ℝ)⁻¹ := by
  simp only [avg, activity, add_eq_zero_iff_eq_neg, sum_ite_eq', mem_univ, ite_true,
    ZMod.card, mul_one]

lemma charged_local_le (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (p : S.Index) (a : ZMod (p : ℕ)) :
    |localWithList w 𝔏 p a| * allPrimeCharges w U p a ≤
      |S.primeFactor w p a| * allPrimeCharges w U p a := by
  apply mul_le_mul_of_nonneg_right _ (allPrimeCharges_nonneg w U p a)
  rw [localWithList, abs_mul, abs_of_nonneg (listLocal_nonneg w 𝔏 p a)]
  exact mul_le_of_le_one_right (abs_nonneg _) (listLocal_le_one w 𝔏 p a)

def recordPrime (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) (U : Finset ℤ)
    (p : S.Index) (E : Finset (Fin ℓ)) (a : ZMod (p : ℕ)) : ℝ :=
  if litEdges w p a = E then |localWithList w 𝔏 p a| * allPrimeCharges w U p a else 0

lemma recordPrime_nonneg (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (p : S.Index) (E : Finset (Fin ℓ)) (a : ZMod (p : ℕ)) :
    0 ≤ recordPrime w 𝔏 U p E a := by
  unfold recordPrime
  split_ifs
  · exact mul_nonneg (abs_nonneg _) (allPrimeCharges_nonneg w U p a)
  · exact le_rfl

lemma recordPrime_le_activity (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (hU : U ⊆ goodOrigins w) (p : S.Index) (E : Finset (Fin ℓ))
    (htop : NoComponentTop w U p E) (e : Fin ℓ) (he : e ∈ E) (a : ZMod (p : ℕ)) :
    recordPrime w 𝔏 U p E a ≤
      subtreeUnionWeight w p E * activity (p : ℕ) a (w.offset e.castSucc) := by
  unfold recordPrime
  split_ifs with hE
  · have he' : e ∈ litEdges w p a := hE.symm ▸ he
    have ha := (mem_filter.mp he').2
    rw [activity, ite_eq_left ha, mul_one]
    have hh := charged_prime_le_weight w U hU p a (hE.symm ▸ htop)
    rw [hE] at hh
    exact (charged_local_le w 𝔏 U p a).trans hh
  · exact mul_nonneg (subtreeUnionWeight_nonneg w p E) (activity_nonneg p a _)

theorem fixed_lit_tree_mean (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (hU : U ⊆ goodOrigins w) (p : S.Index) (E : Finset (Fin ℓ))
    (htop : NoComponentTop w U p E) (hE : E.Nonempty) :
    avg (recordPrime w 𝔏 U p E) ≤ subtreeUnionWeight w p E / (p : ℝ) := by
  obtain ⟨e,he⟩ := hE
  calc
    _ ≤ avg (fun a => subtreeUnionWeight w p E * activity (p : ℕ) a (w.offset e.castSucc)) :=
      avg_mono (recordPrime_le_activity w 𝔏 U hU p E htop e he)
    _ = _ := by rw [avg_mul_left, activity_mean, div_eq_mul_inv]

lemma core_primeFactor_zero_of_unlit (w : ClosedLine h ℓ) (p : S.Index)
    (hc : S.IsCore p) (i : Fin ℓ) (hi : (p : ℕ) ∣ w.label i)
    (a : ZMod (p : ℕ)) (ha : a + (w.offset i.castSucc : ZMod (p : ℕ)) ≠ 0) :
    S.primeFactor w p a = 0 := by
  apply prod_eq_zero (mem_univ i)
  simp only [occurrenceFactor, hi, hc, ite_true, activity, ite_eq_right ha, mul_zero, zero_mul]

lemma center_empty_lit_pointwise (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (hU : U ⊆ goodOrigins w) (p : S.Index) (hc : ¬S.IsCore p)
    (hocc : (treeOccurrences w p).Nonempty) (a : ZMod (p : ℕ))
    (hE : litEdges w p a = ∅) :
    |localWithList w 𝔏 p a| * allPrimeCharges w U p a ≤ theta / (p : ℝ) := by
  obtain ⟨e,he⟩ := hocc
  have het := (mem_filter.mp he).1
  have hed := (mem_filter.mp he).2
  have hea : a + (w.offset e.castSucc : ZMod (p : ℕ)) ≠ 0 := by
    intro ha
    have hm : e ∈ litEdges w p a := mem_filter.mpr ⟨he,ha⟩
    simp [hE] at hm
  have ho (i : Fin ℓ) (hi : i ∈ w.treeSteps) : |S.occurrenceFactor w p i a| ≤ 1 := by
    have hh := occurrence_abs_le_lit_amplitude w p a i hi
    simpa only [amplitude, hc, ite_false, ite_self] using hh
  have hop : (∏ i ∈ w.treeSteps, |S.occurrenceFactor w p i a|) ≤ theta / (p : ℝ) := by
    calc
      _ ≤ ∏ i ∈ ({e} : Finset (Fin ℓ)), |S.occurrenceFactor w p i a| :=
        prod_le_prod_of_subset_of_le_one₀ (singleton_subset_iff.mpr het)
          (fun _ _ => abs_nonneg _) (fun i hi _ => ho i hi)
      _ = _ := by
        simp only [prod_singleton, occurrenceFactor, hed, hc, ite_true, ite_false,
          activity, ite_eq_right hea, zero_sub, abs_neg, abs_of_nonneg (theta_div_bounds p).1]
  have htop : NoComponentTop w U p (litEdges w p a) := fun h => (hc h).elim
  have hn := tree_norm_charges_le w U hU p a htop
  rw [hE] at hn
  simp only [edgeVertices, image_empty, union_self, prod_empty] at hn
  calc
    _ ≤ |S.primeFactor w p a| * allPrimeCharges w U p a := charged_local_le w 𝔏 U p a
    _ ≤ _ := charged_prime_le_tree w U p a
    _ ≤ (theta / (p : ℝ)) * 1 := mul_le_mul hop hn
      (mul_nonneg (prod_nonneg (fun _ _ => pow_nonneg (beta_nonneg p) _))
        (prod_nonneg (fun _ _ => primeCharge_nonneg _ _ _ _))) (theta_div_bounds p).1
    _ = _ := mul_one _

theorem fixed_unlit_tree_mean (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (hU : U ⊆ goodOrigins w) (p : S.Index)
    (hocc : (treeOccurrences w p).Nonempty) :
    avg (recordPrime w 𝔏 U p ∅) ≤ (p : ℝ)⁻¹ := by
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos (p : ℕ)
  have hp0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hp.le
  apply (avg_mono (g := fun _ => (p : ℝ)⁻¹) ?_).trans_eq (avg_const _)
  intro a
  unfold recordPrime
  split_ifs with hE
  · by_cases hc : S.IsCore p
    · obtain ⟨e,he⟩ := hocc
      have hed := (mem_filter.mp he).2
      have ha : a + (w.offset e.castSucc : ZMod (p : ℕ)) ≠ 0 := by
        intro ha
        have hm : e ∈ litEdges w p a := mem_filter.mpr ⟨he,ha⟩
        simp [hE] at hm
      rw [localWithList, core_primeFactor_zero_of_unlit w p hc e hed a ha,
        zero_mul, abs_zero, zero_mul]
      exact hp0
    · apply (center_empty_lit_pointwise w 𝔏 U hU p hc hocc a hE).trans
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left hp0 (by norm_num)
  · exact hp0

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
