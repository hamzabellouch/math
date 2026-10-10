import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TreePrimeSupport
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LabelPrimeSet

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma amplitude_ge_one (p : S.Index) : 1 ≤ S.amplitude p := by
  unfold amplitude
  split_ifs
  · exact Real.one_le_exp (by unfold kappa eta epsilon; positivity)
  · exact le_rfl

lemma occurrence_absolute_crude (w : ClosedLine h ℓ) (p : S.Index) (i : Fin ℓ)
    (r : ZMod (p:ℕ)) :
    |S.occurrenceFactor w p i r| ≤ if (p:ℕ) ∣ w.label i then S.amplitude p else 1 := by
  have ht := theta_div_bounds p
  by_cases hd : (p:ℕ) ∣ w.label i
  · by_cases hc : S.IsCore p
    · simp only [occurrenceFactor,hd,hc,ite_true,amplitude]
      rw [abs_mul,abs_of_pos A_pos]
      apply mul_le_of_le_one_right A_pos.le
      unfold activity; split_ifs <;> norm_num
    · simp only [occurrenceFactor,hd,hc,ite_true,ite_false,amplitude]
      unfold activity
      split_ifs
      · rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]; linarith
      · simpa only [zero_sub,abs_neg,abs_of_nonneg ht.1] using ht.2
  · simp [occurrenceFactor,hd]

lemma primeFactor_absolute_crude (w : ClosedLine h ℓ) (p : S.Index)
    (r : ZMod (p:ℕ)) : |S.primeFactor w p r| ≤ S.amplitude p ^ S.occurrenceCount w p := by
  rw [primeFactor,abs_prod]
  calc
    _ ≤ ∏ i : Fin ℓ, if (p:ℕ) ∣ w.label i then S.amplitude p else 1 := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro i hi
      rw [abs_mul,abs_of_nonneg (pow_nonneg (beta_nonneg p) _)]
      calc
        _ ≤ |S.occurrenceFactor w p i r| * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (beta_nonneg p) (beta_le_one p)) (abs_nonneg _)
        _ ≤ _ := by simpa using occurrence_absolute_crude w p i r
    _ = _ := by simp only [occurrenceCount,← prod_filter,prod_const]

lemma local_absolute_crude (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) (r : ZMod (p:ℕ)) :
    |localWithList w 𝔏 p r| ≤ S.amplitude p ^ S.occurrenceCount w p := by
  rw [localWithList,abs_mul,abs_of_nonneg (listLocal_nonneg w 𝔏 p r)]
  calc
    _ ≤ |S.primeFactor w p r| * 1 :=
      mul_le_mul_of_nonneg_left (listLocal_le_one w 𝔏 p r) (abs_nonneg _)
    _ ≤ _ := by simpa using primeFactor_absolute_crude w p r

lemma list_used_absolute_mean (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) (hp : (p:ℕ) ∈ listSupport w 𝔏) :
    avg (fun r => |localWithList w 𝔏 p r|) ≤
      S.amplitude p ^ S.occurrenceCount w p * (p:ℝ)⁻¹ := by
  obtain ⟨v,hv⟩ := listLocal_has_residue w 𝔏 p hp
  calc
    _ ≤ avg (fun r : ZMod (p:ℕ) => S.amplitude p ^ S.occurrenceCount w p * activity p r v) := by
      apply avg_mono
      intro r
      rw [localWithList,abs_mul,abs_of_nonneg (listLocal_nonneg w 𝔏 p r)]
      exact mul_le_mul (primeFactor_absolute_crude w p r) (hv r)
        (listLocal_nonneg w 𝔏 p r) (pow_nonneg (le_trans zero_le_one (amplitude_ge_one p)) _)
    _ = _ := by rw [avg_mul_left,activity_mean]

lemma core_line_absolute_mean (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) (hc : S.IsCore p) (e : Fin ℓ) (he : (p:ℕ) ∣ w.label e) :
    avg (fun r => |localWithList w 𝔏 p r|) ≤
      S.amplitude p ^ S.occurrenceCount w p * (p:ℝ)⁻¹ := by
  calc
    _ ≤ avg (fun r : ZMod (p:ℕ) => S.amplitude p ^ S.occurrenceCount w p *
        activity p r (w.offset e.castSucc)) := by
      apply avg_mono
      intro r
      by_cases ha : r+(w.offset e.castSucc : ZMod (p:ℕ))=0
      · simpa only [activity,ha,ite_true,mul_one] using local_absolute_crude w 𝔏 p r
      · have hz : S.primeFactor w p r = 0 := by
          apply prod_eq_zero (mem_univ e)
          simp only [occurrenceFactor,he,hc,ite_true,activity,ha,ite_false,mul_zero,zero_mul]
        simp only [localWithList,hz,zero_mul,abs_zero,activity,ha,ite_false,mul_zero,le_refl]
    _ = _ := by rw [avg_mul_left,activity_mean]

lemma center_line_absolute_point (w : ClosedLine h ℓ)
    (p : S.Index) (hc : ¬S.IsCore p) (e : Fin ℓ) (he : (p:ℕ) ∣ w.label e)
    (r : ZMod (p:ℕ)) :
    |S.primeFactor w p r| ≤ activity p r (w.offset e.castSucc) + theta/(p:ℝ) := by
  have ht := theta_div_bounds p
  have hb := beta_nonneg p
  have hb1 := beta_le_one p
  have hocc (i : Fin ℓ) : |S.occurrenceFactor w p i r| ≤ 1 := by
    simpa only [amplitude,hc,ite_false,ite_self] using occurrence_absolute_crude w p i r
  rw [primeFactor,abs_prod]
  calc
    _ ≤ ∏ i : Fin ℓ, if i=e then activity p r (w.offset e.castSucc)+theta/(p:ℝ) else 1 := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro i hi
      rw [abs_mul,abs_of_nonneg (pow_nonneg hb _)]
      calc
        _ ≤ |S.occurrenceFactor w p i r| * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hb hb1) (abs_nonneg _)
        _ ≤ _ := by
          simp only [mul_one]
          by_cases hei : i=e
          · subst i
            simp only [ite_true,occurrenceFactor,he,hc,ite_false]
            exact (abs_sub _ _).trans_eq (by
              rw [abs_of_nonneg (activity_nonneg p r _),abs_of_nonneg ht.1])
          · rw [ite_eq_right hei]
            exact hocc i
    _ = _ := by simp

lemma center_line_absolute_mean (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) (hc : ¬S.IsCore p) (e : Fin ℓ) (he : (p:ℕ) ∣ w.label e) :
    avg (fun r => |localWithList w 𝔏 p r|) ≤ 2*(p:ℝ)⁻¹ := by
  calc
    _ ≤ avg (fun r : ZMod (p:ℕ) => activity p r (w.offset e.castSucc)+theta/(p:ℝ)) := by
      apply avg_mono
      intro r
      rw [localWithList,abs_mul,abs_of_nonneg (listLocal_nonneg w 𝔏 p r)]
      apply (mul_le_mul_of_nonneg_left (listLocal_le_one w 𝔏 p r) (abs_nonneg _)).trans
      simpa only [mul_one] using center_line_absolute_point w p hc e he r
    _ = (p:ℝ)⁻¹+theta/(p:ℝ) := by
      have heq : avg (fun r : ZMod (p:ℕ) => activity p r (w.offset e.castSucc)+theta/(p:ℝ)) =
          avg (fun r : ZMod (p:ℕ) => activity p r (w.offset e.castSucc))+
          avg (fun _r : ZMod (p:ℕ) => theta/(p:ℝ)) := by
        unfold avg
        rw [sum_add_distrib,mul_add]
      rw [heq,activity_mean,avg_const]
    _ ≤ _ := by
      have hp : 0 ≤ (p:ℝ)⁻¹ := by positivity
      norm_num [theta,betaZ,div_eq_mul_inv]
      nlinarith

def fullUsedIndices (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) : Finset S.Index :=
  univ.filter (fun p => (∃ i, (p:ℕ) ∣ w.label i) ∨ (p:ℕ) ∈ listSupport w 𝔏)

lemma crude_prime_mean (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) : avg (fun r => |localWithList w 𝔏 p r|) ≤
      S.amplitude p ^ S.occurrenceCount w p *
        (if p ∈ fullUsedIndices w 𝔏 then 2*(p:ℝ)⁻¹ else 1) := by
  have hn : 0 ≤ S.amplitude p ^ S.occurrenceCount w p * (p:ℝ)⁻¹ := by
    exact mul_nonneg (pow_nonneg (le_trans zero_le_one (amplitude_ge_one p)) _) (by positivity)
  by_cases hp : p ∈ fullUsedIndices w 𝔏
  · rw [ite_eq_left hp]
    change p ∈ univ.filter _ at hp
    rcases (mem_filter.mp hp).2 with ⟨e,he⟩ | hlist
    · by_cases hc : S.IsCore p
      · have hb := core_line_absolute_mean w 𝔏 p hc e he
        nlinarith
      · simpa only [amplitude,hc,ite_false,one_pow,one_mul] using
          center_line_absolute_mean w 𝔏 p hc e he
    · have hb := list_used_absolute_mean w 𝔏 p hlist
      nlinarith
  · rw [ite_eq_right hp,mul_one]
    exact (avg_mono (local_absolute_crude w 𝔏 p)).trans_eq (avg_const _)

lemma chronological_occurrences_le (w : ClosedLine h ℓ)
    (hl : ∀ i, w.label i ∈ D.members) :
    (∑ p : S.Index, S.occurrenceCount w p) ≤ ℓ*⌈C₀*Real.log B⌉₊ := by
  simp only [occurrenceCount,card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  calc
    _ ≤ ∑ _i : Fin ℓ, ⌈C₀*Real.log B⌉₊ := by
      apply sum_le_sum
      intro i hi
      rw [← sum_filter,← card_eq_sum_ones]
      have he : univ.filter (fun p : S.Index => (p:ℕ) ∣ w.label i) =
          labelPrimeSet (w.label i) (hl i) := by
        ext p
        simp only [mem_filter,mem_univ,true_and,mem_labelPrimeSet]
        exact ⟨fun hp => Nat.mem_primeFactors.mpr ⟨S.prime_mem p p.property,hp,
          (w.label_pos i).ne'⟩,fun hp => (Nat.mem_primeFactors.mp hp).2.1⟩
      rw [he,labelPrimeSet_card]
      exact D.omega _ (hl i)
    _ = _ := by simp

lemma crude_amplitude_product (w : ClosedLine h ℓ)
    (hl : ∀ i, w.label i ∈ D.members) :
    (∏ p : S.Index, S.amplitude p ^ S.occurrenceCount w p) ≤ A^(ℓ*⌈C₀*Real.log B⌉₊) := by
  have hA : 1 ≤ A := Real.one_le_exp (by unfold kappa eta epsilon; positivity)
  calc
    _ ≤ ∏ p : S.Index, A^S.occurrenceCount w p := by
      apply Finset.prod_le_prod₀
      · intro p hp; exact pow_nonneg (le_trans zero_le_one (amplitude_ge_one p)) _
      · intro p hp
        have ha : S.amplitude p ≤ A := by unfold amplitude; split_ifs <;> linarith
        exact pow_le_pow_left₀ (le_trans zero_le_one (amplitude_ge_one p)) ha _
    _ = A^(∑ p : S.Index, S.occurrenceCount w p) := prod_pow_eq_pow_sum _ _ _
    _ ≤ _ := pow_le_pow_right₀ hA (chronological_occurrences_le w hl)

lemma fullUsedIndices_card_le (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (hl : ∀ i, w.label i ∈ D.members) :
    (fullUsedIndices w 𝔏).card ≤ ℓ*⌈C₀*Real.log B⌉₊+𝔏.length*(L*⌈C₀*Real.log B⌉₊+1) := by
  have hsub : (fullUsedIndices w 𝔏).image Subtype.val ⊆
      univ.biUnion (fun i : Fin ℓ => (w.label i).primeFactors) ∪ listSupport w 𝔏 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
    rcases (mem_filter.mp hq).2 with ⟨i,hi⟩ | hi
    · exact mem_union_left _ (mem_biUnion.mpr ⟨i,mem_univ _,Nat.mem_primeFactors.mpr
        ⟨S.prime_mem q q.property,hi,(w.label_pos i).ne'⟩⟩)
    · exact mem_union_right _ hi
  calc
    _ = ((fullUsedIndices w 𝔏).image Subtype.val).card :=
      (card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ _ := (card_le_card hsub).trans (card_union_le _ _)
    _ ≤ _ := by
      have hbound := card_biUnion_le_card_mul (univ : Finset (Fin ℓ))
        (fun i => (w.label i).primeFactors) (⌈C₀*Real.log B⌉₊) (fun i hi => D.omega _ (hl i))
      simp only [card_univ,Fintype.card_fin] at hbound
      exact Nat.add_le_add hbound (listSupport_card_le w 𝔏)

lemma cutoffProduct_le_one (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (r : S.CoreResidues) : S.cutoffProduct w cut r ≤ 1 := by
  apply prod_le_one₀
  · intro i hi; exact mul_nonneg (cut.nonneg _ _) (cut.nonneg _ _)
  · intro index hindex
    exact (mul_le_of_le_one_left (cut.nonneg _ _) (cut.le_one _ _)).trans (cut.le_one _ _)

lemma absolute_list_factorization (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (𝔏 : List (AttachedSpec w D L)) (r : S.Residues) :
    |S.kernel w cut r| * listIndicator w 𝔏 r =
      S.cutoffProduct w cut (S.restrictCore r) * ∏ p : S.Index, |localWithList w 𝔏 p (r p)| := by
  simp only [kernel,abs_mul,abs_of_nonneg (cutoffProduct_nonneg S w cut _),abs_prod,
    listIndicator_product,localWithList,abs_of_nonneg (listLocal_nonneg w 𝔏 _ _)]
  rw [prod_mul_distrib]
  ring

theorem crude_unpartitioned_majorant (w : ClosedLine h ℓ)
    (hl : ∀ i, w.label i ∈ D.members) {T : ℝ} (cut : S.Cutoffs T)
    (𝔏 : List (AttachedSpec w D L)) (R : S.Residues → ℝ)
    (hR : ∀ r, 0 ≤ R r ∧ R r ≤ 1) :
    avg (fun r => |S.kernel w cut r| * listIndicator w 𝔏 r * R r) ≤
      A^(ℓ*⌈C₀*Real.log B⌉₊) * 2^(fullUsedIndices w 𝔏).card *
        ∏ p ∈ fullUsedIndices w 𝔏, (p:ℝ)⁻¹ := by
  calc
    _ ≤ avg (fun r : S.Residues => ∏ p, |localWithList w 𝔏 p (r p)|) := by
      apply avg_mono
      intro r
      rw [absolute_list_factorization]
      have hn : 0 ≤ ∏ p, |localWithList w 𝔏 p (r p)| := prod_nonneg (fun _ _ => abs_nonneg _)
      calc
        _ ≤ (1*(∏ p, |localWithList w 𝔏 p (r p)|))*1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right (cutoffProduct_le_one w cut _) hn) (hR r).2 (hR r).1 (by simpa using hn)
        _ = _ := by ring
    _ = ∏ p : S.Index, avg (fun r => |localWithList w 𝔏 p r|) := by
      convert avg_product (Ω := fun p : S.Index => ZMod (p:ℕ)) (fun p r => |localWithList w 𝔏 p r|) using 1
      congr 1
      exact Subsingleton.elim _ _
    _ ≤ ∏ p : S.Index, S.amplitude p ^ S.occurrenceCount w p *
        (if p ∈ fullUsedIndices w 𝔏 then 2*(p:ℝ)⁻¹ else 1) :=
      prod_le_prod₀ (fun p hp => avg_nonneg (fun r => abs_nonneg _)) (fun p hp => crude_prime_mean w 𝔏 p)
    _ = (∏ p : S.Index, S.amplitude p ^ S.occurrenceCount w p) *
        (2^(fullUsedIndices w 𝔏).card * ∏ p ∈ fullUsedIndices w 𝔏, (p:ℝ)⁻¹) := by
      rw [prod_mul_distrib,prod_ite_mem,univ_inter,prod_mul_distrib,prod_const]
    _ ≤ _ := by
      have hn : 0 ≤ 2^(fullUsedIndices w 𝔏).card * ∏ p ∈ fullUsedIndices w 𝔏, (p:ℝ)⁻¹ := by
        positivity
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (crude_amplitude_product w hl) hn

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
