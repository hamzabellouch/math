import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrimeChargeProduct

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {h ℓ : ℕ}

def treeOccurrences (w : ClosedLine h ℓ) (p : S.Index) : Finset (Fin ℓ) :=
  w.treeSteps.filter (fun i => (p : ℕ) ∣ w.label i)

def litEdges (w : ClosedLine h ℓ) (p : S.Index) (a : ZMod (p : ℕ)) : Finset (Fin ℓ) :=
  (treeOccurrences w p).filter (fun i => a + (w.offset i.castSucc : ZMod (p : ℕ)) = 0)

def edgeVertices (w : ClosedLine h ℓ) (E : Finset (Fin ℓ)) : Finset ℤ :=
  E.image (fun i => w.offset i.castSucc) ∪ E.image (fun i => w.offset i.succ)

lemma edgeVertices_subset (w : ClosedLine h ℓ) (E : Finset (Fin ℓ)) :
    edgeVertices w E ⊆ treeVertices w := by
  intro v hv
  rcases mem_union.mp hv with hv | hv
  · obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    exact departure_mem_vertices w i
  · obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    exact endpoint_mem_vertices w i

lemma lit_vertex_active (w : ClosedLine h ℓ) (p : S.Index) (a : ZMod (p : ℕ))
    {v : ℤ} (hv : v ∈ edgeVertices w (litEdges w p a)) : a + (v : ZMod (p : ℕ)) = 0 := by
  rcases mem_union.mp hv with hv | hv
  · obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    exact (mem_filter.mp hi).2
  · obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    rw [w.label_residue_eq i (mem_filter.mp (mem_filter.mp hi).1).2]
    exact (mem_filter.mp hi).2

def NoComponentTop (w : ClosedLine h ℓ) (U : Finset ℤ) (p : S.Index)
    (E : Finset (Fin ℓ)) : Prop :=
  S.IsCore p → ∀ i ∈ incomingCharges w U,
    w.offset i.succ ∈ edgeVertices w E → (p : ℕ) ∣ w.label i

def isolatedCharge (w : ClosedLine h ℓ) (U : Finset ℤ) (p : S.Index)
    (E : Finset (Fin ℓ)) (a : ZMod (p : ℕ)) (v : ℤ) : ℝ :=
  if S.IsCore p ∧ v ∈ U ∧ a + (v : ZMod (p : ℕ)) = 0 ∧ v ∉ edgeVertices w E
    then Real.exp kappa else 1

lemma isolatedCharge_nonneg (w : ClosedLine h ℓ) (U : Finset ℤ) (p : S.Index)
    (E : Finset (Fin ℓ)) (a : ZMod (p : ℕ)) (v : ℤ) :
    0 ≤ isolatedCharge w U p E a v := by
  unfold isolatedCharge; split_ifs <;> positivity

lemma incoming_charge_le_isolated (w : ClosedLine h ℓ) (U : Finset ℤ) (p : S.Index)
    (E : Finset (Fin ℓ)) (htop : NoComponentTop w U p E)
    (a : ZMod (p : ℕ)) (i : Fin ℓ) (hi : i ∈ incomingCharges w U) :
    S.primeCharge p (w.label i) (w.offset i.succ) a ≤
      isolatedCharge w U p E a (w.offset i.succ) := by
  have hiU := (mem_filter.mp hi).2
  by_cases hc : S.IsCore p
  · by_cases he : w.offset i.succ ∈ edgeVertices w E
    · have hd := htop hc i hi he
      simp [primeCharge, isolatedCharge, hc, hd, he]
    · by_cases ha : a + (w.offset i.succ : ZMod (p : ℕ)) = 0
      · simp only [isolatedCharge, hc, hiU, ha, he, not_false_eq_true, and_self, ite_true]
        unfold primeCharge
        split_ifs
        · exact le_rfl
        · exact Real.one_le_exp (by unfold kappa eta epsilon; positivity)
      · simp [primeCharge, isolatedCharge, ha]
  · simp [primeCharge, isolatedCharge, hc]

lemma incoming_charges_le_vertices (w : ClosedLine h ℓ) (U : Finset ℤ)
    (hU : U ⊆ goodOrigins w) (p : S.Index) (E : Finset (Fin ℓ))
    (htop : NoComponentTop w U p E) (a : ZMod (p : ℕ)) :
    (∏ i ∈ incomingCharges w U, S.primeCharge p (w.label i) (w.offset i.succ) a) ≤
      ∏ v ∈ treeVertices w, isolatedCharge w U p E a v := by
  calc
    _ ≤ ∏ i ∈ incomingCharges w U, isolatedCharge w U p E a (w.offset i.succ) :=
      prod_le_prod₀ (fun _ _ => primeCharge_nonneg _ _ _ _)
        (fun i hi => incoming_charge_le_isolated w U p E htop a i hi)
    _ = ∏ v ∈ U, isolatedCharge w U p E a v := by
      calc
        _ = ∏ v ∈ (incomingCharges w U).image (fun i => w.offset i.succ),
            isolatedCharge w U p E a v := by
          symm
          apply prod_image
          intro i hi j hj hij
          exact tree_destination_injective w (mem_filter.mp hi).1 (mem_filter.mp hj).1 hij
        _ = _ := congrArg (fun V => ∏ v ∈ V, isolatedCharge w U p E a v)
          (incomingCharges_image w U hU)
    _ = ∏ v ∈ treeVertices w, isolatedCharge w U p E a v := by
      apply prod_subset (fun v hv => (good_origin_data w (hU hv)).1)
      intro v hv hn
      simp [isolatedCharge, hn]

def subtreeUnionWeight (w : ClosedLine h ℓ) (p : S.Index) (E : Finset (Fin ℓ)) : ℝ :=
  S.amplitude p ^ E.card * ∏ v ∈ edgeVertices w E, S.beta p ^ w.children v

lemma tree_norm_charges_le (w : ClosedLine h ℓ) (U : Finset ℤ)
    (hU : U ⊆ goodOrigins w) (p : S.Index) (a : ZMod (p : ℕ))
    (htop : NoComponentTop w U p (litEdges w p a)) :
    (∏ i ∈ w.treeSteps, S.beta p ^
      (if a + (w.offset i.castSucc : ZMod (p : ℕ)) = 0 then (1 : ℕ) else 0)) *
    (∏ i ∈ incomingCharges w U, S.primeCharge p (w.label i) (w.offset i.succ) a) ≤
      ∏ v ∈ edgeVertices w (litEdges w p a), S.beta p ^ w.children v := by
  let E := litEdges w p a
  have hn : ∀ v : ℤ, (0 : ℝ) ≤ (if a + (v : ZMod (p : ℕ)) = 0 then
      S.beta p ^ w.children v else 1) := by
    intro v
    have hb := beta_nonneg p
    split_ifs <;> positivity
  rw [tree_normalization]
  calc
    _ ≤ (∏ v ∈ treeVertices w, if a + (v : ZMod (p : ℕ)) = 0 then
          S.beta p ^ w.children v else 1) *
        ∏ v ∈ treeVertices w, isolatedCharge w U p E a v :=
      mul_le_mul_of_nonneg_left (incoming_charges_le_vertices w U hU p E htop a)
        (prod_nonneg (fun v _ => hn v))
    _ = ∏ v ∈ treeVertices w, (if a + (v : ZMod (p : ℕ)) = 0 then
          S.beta p ^ w.children v else 1) * isolatedCharge w U p E a v := by
      rw [prod_mul_distrib]
    _ ≤ ∏ v ∈ treeVertices w, if v ∈ edgeVertices w E then S.beta p ^ w.children v else 1 := by
      apply Finset.prod_le_prod₀
      · intro v hv
        exact mul_nonneg (hn v) (isolatedCharge_nonneg w U p E a v)
      · intro v hv
        by_cases he : v ∈ edgeVertices w E
        · rw [ite_eq_left he, ite_eq_left (lit_vertex_active w p a he)]
          simp [isolatedCharge, he]
        · rw [ite_eq_right he]
          by_cases ha : a + (v : ZMod (p : ℕ)) = 0
          · rw [ite_eq_left ha]
            by_cases hu : S.IsCore p ∧ v ∈ U
            · have hv1 := (good_origin_data w (hU hu.2)).2.2.1
              simp only [isolatedCharge, hu.1, hu.2, ha, he, not_false_eq_true, and_self,
                ite_true, hv1, pow_one, beta_eq_core p hu.1]
              exact betaC_mul_exp_le_one
            · have hc : ¬(S.IsCore p ∧ v ∈ U ∧ a + (v : ZMod (p : ℕ)) = 0 ∧ v ∉ edgeVertices w E) :=
                fun hh => hu ⟨hh.1,hh.2.1⟩
              rw [isolatedCharge, ite_eq_right hc, mul_one]
              exact pow_le_one₀ (beta_nonneg p) (beta_le_one p)
          · simp [isolatedCharge, ha]
    _ = ∏ v ∈ edgeVertices w E, S.beta p ^ w.children v := by
      rw [← prod_filter]
      congr 1
      rw [filter_mem_eq_inter, inter_eq_right.mpr (edgeVertices_subset w E)]

lemma charged_prime_le_tree (w : ClosedLine h ℓ) (U : Finset ℤ)
    (p : S.Index) (a : ZMod (p : ℕ)) :
    |S.primeFactor w p a| * allPrimeCharges w U p a ≤
      (∏ i ∈ w.treeSteps, |S.occurrenceFactor w p i a|) *
      ((∏ i ∈ w.treeSteps, S.beta p ^
        (if a + (w.offset i.castSucc : ZMod (p : ℕ)) = 0 then (1 : ℕ) else 0)) *
       ∏ i ∈ incomingCharges w U, S.primeCharge p (w.label i) (w.offset i.succ) a) := by
  have hret : |∏ i ∈ returnSteps w, S.stepFactor w p i a| *
      (∏ i ∈ returnSteps w, S.primeCharge p (w.label i) (w.offset i.castSucc) a) ≤ 1 := by
    rw [abs_prod, ← prod_mul_distrib]
    exact prod_le_one₀ (fun i _ => mul_nonneg (abs_nonneg _) (primeCharge_nonneg _ _ _ _))
      (fun i _ => charged_return_le_one w p i a)
  have hi0 : 0 ≤ ∏ i ∈ incomingCharges w U,
      S.primeCharge p (w.label i) (w.offset i.succ) a :=
    prod_nonneg (fun i _ => primeCharge_nonneg _ _ _ _)
  rw [primeFactor_split_steps, abs_mul, allPrimeCharges]
  calc
    _ = (|∏ i ∈ w.treeSteps, S.stepFactor w p i a| *
          ∏ i ∈ incomingCharges w U, S.primeCharge p (w.label i) (w.offset i.succ) a) *
        (|∏ i ∈ returnSteps w, S.stepFactor w p i a| *
          ∏ i ∈ returnSteps w, S.primeCharge p (w.label i) (w.offset i.castSucc) a) := by
      unfold returnSteps
      ring
    _ ≤ (|∏ i ∈ w.treeSteps, S.stepFactor w p i a| *
          ∏ i ∈ incomingCharges w U, S.primeCharge p (w.label i) (w.offset i.succ) a) * 1 :=
      mul_le_mul_of_nonneg_left hret (mul_nonneg (abs_nonneg _) hi0)
    _ = _ := by
      simp only [mul_one, abs_prod, stepFactor, abs_mul,
        abs_of_nonneg (pow_nonneg (beta_nonneg p) _), prod_mul_distrib]
      ring

lemma occurrence_abs_le_lit_amplitude (w : ClosedLine h ℓ) (p : S.Index)
    (a : ZMod (p : ℕ)) (i : Fin ℓ) (hi : i ∈ w.treeSteps) :
    |S.occurrenceFactor w p i a| ≤
      if i ∈ litEdges w p a then S.amplitude p else 1 := by
  have ht := theta_div_bounds p
  by_cases hd : (p : ℕ) ∣ w.label i <;>
    by_cases ha : a + (w.offset i.castSucc : ZMod (p : ℕ)) = 0 <;>
    by_cases hc : S.IsCore p
  all_goals simp only [occurrenceFactor, activity, hd, ha, hc, ite_true, ite_false,
    amplitude, litEdges, treeOccurrences, mem_filter, hi, and_true,
    and_false, mul_zero, mul_one, abs_zero, zero_sub, abs_neg]
  · exact le_of_eq (abs_of_pos A_pos)
  · rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]; linarith [ht.1]
  · norm_num
  · exact (abs_of_nonneg ht.1).le.trans ht.2
  all_goals norm_num

lemma occurrence_product_le (w : ClosedLine h ℓ) (p : S.Index) (a : ZMod (p : ℕ)) :
    (∏ i ∈ w.treeSteps, |S.occurrenceFactor w p i a|) ≤
      S.amplitude p ^ (litEdges w p a).card := by
  calc
    _ ≤ ∏ i ∈ w.treeSteps, if i ∈ litEdges w p a then S.amplitude p else 1 :=
      prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i hi => occurrence_abs_le_lit_amplitude w p a i hi)
    _ = _ := by
      rw [prod_ite_mem, inter_eq_right.mpr]
      · simp only [prod_const]
      · exact (filter_subset _ _).trans (filter_subset _ _)

theorem charged_prime_le_weight (w : ClosedLine h ℓ) (U : Finset ℤ)
    (hU : U ⊆ goodOrigins w) (p : S.Index) (a : ZMod (p : ℕ))
    (htop : NoComponentTop w U p (litEdges w p a)) :
    |S.primeFactor w p a| * allPrimeCharges w U p a ≤
      subtreeUnionWeight w p (litEdges w p a) := by
  apply (charged_prime_le_tree w U p a).trans
  unfold subtreeUnionWeight
  apply mul_le_mul (occurrence_product_le w p a) (tree_norm_charges_le w U hU p a htop)
  · exact mul_nonneg (prod_nonneg (fun _ _ => pow_nonneg (beta_nonneg p) _))
      (prod_nonneg (fun _ _ => primeCharge_nonneg _ _ _ _))
  · have hp : 0 ≤ S.amplitude p := by
      unfold amplitude
      split_ifs
      · exact A_pos.le
      · exact zero_le_one
    exact pow_nonneg hp _

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
