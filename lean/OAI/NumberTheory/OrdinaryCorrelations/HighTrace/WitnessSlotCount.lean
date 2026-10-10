import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.UnselectedCard
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.WitnessTestDescriptor

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SharedSlotPatterns
open Finset Classical

noncomputable def witnessSlotCount (ℓ L J t : ℕ) : ℕ := Fintype.card (WitnessCodeSlot ℓ L J t)
noncomputable def witnessTemplateBudget (ℓ L J t : ℕ) : ℕ :=
  let N := witnessSlotCount ℓ L J t
  (N+1)*Fintype.card (WitnessMetadata ℓ L t)*(N+1)^N *
    ((t+1)*(Fintype.card (WitnessTestDescriptor ℓ L t N)+1)^t)

lemma witnessTemplate_card_uniform (ℓ L J t m : ℕ) (hm : m ≤ witnessSlotCount ℓ L J t) :
    Fintype.card (WitnessTemplateCode ℓ L J t m) ≤
      Fintype.card (WitnessMetadata ℓ L t)*(witnessSlotCount ℓ L J t+1)^(witnessSlotCount ℓ L J t)*
      ((t+1)*(Fintype.card (WitnessTestDescriptor ℓ L t (witnessSlotCount ℓ L J t))+1)^t) := by
  apply (WitnessTemplateCode.card_le ℓ L J t m).trans
  have hc : Fintype.card (WitnessTestDescriptor ℓ L t m) ≤
      Fintype.card (WitnessTestDescriptor ℓ L t (witnessSlotCount ℓ L J t)) := by
    rw [WitnessTemplateCode.descriptor_card,WitnessTemplateCode.descriptor_card]
    gcongr
  change _ ≤ Fintype.card (WitnessMetadata ℓ L t)*
    (witnessSlotCount ℓ L J t+1)^(Fintype.card (WitnessCodeSlot ℓ L J t))*_
  gcongr

abbrev GoodWitnessTemplate (h ℓ L J t m r : ℕ) :=
  {d : WitnessTemplateCode ℓ L J t m // d.WellFormed h ∧ r ≤ d.rank}

noncomputable def witnessTemplateMass (S : PrimeSystem) (P K : ℝ) (h ℓ L J t r : ℕ) : ℝ :=
  ∑ m : Fin (witnessSlotCount ℓ L J t+1),
    ∑ d : GoodWitnessTemplate h ℓ L J t m.val r,
      ∑ v : Fin m.val → S.Index,
        (d.val.system h d.property.1).fiberWeight P K (fun a => (v a:ℕ))

lemma witnessTemplateMass_le (S : PrimeSystem) (P B K : ℝ) (h ℓ L J t r : ℕ)
    (hP : 0 < P) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hS : ∀ p : S.Index, P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp B)
    (hδ : max (K/(P*Real.log 2)) ((2+B)/P) ≤ 1) :
    witnessTemplateMass S P K h ℓ L J t r ≤
      (witnessTemplateBudget ℓ L J t:ℝ) *
        (max 1 (∑ p ∈ S.primes, (p:ℝ)⁻¹))^(witnessSlotCount ℓ L J t) *
        (max (K/(P*Real.log 2)) ((2+B)/P))^r := by
  let N := witnessSlotCount ℓ L J t
  let H : ℝ := max 1 (∑ p ∈ S.primes, (p:ℝ)⁻¹)
  let δ : ℝ := max (K/(P*Real.log 2)) ((2+B)/P)
  let C : ℕ := Fintype.card (WitnessMetadata ℓ L t)*(N+1)^N *
    ((t+1)*(Fintype.card (WitnessTestDescriptor ℓ L t N)+1)^t)
  have h0δ : 0 ≤ δ := le_trans (by positivity : 0 ≤ (2+B)/P) (le_max_right _ _)
  have hH : 1 ≤ H := le_max_left _ _
  have h0H : 0 ≤ H := le_trans zero_le_one hH
  have hrow (m : Fin (N+1)) (d : GoodWitnessTemplate h ℓ L J t m.val r) :
      (∑ v : Fin m.val → S.Index,
        (d.val.system h d.property.1).fiberWeight P K (fun a => (v a:ℕ))) ≤ H^N*δ^r := by
    apply ((d.val.system h d.property.1).fiber_sum_le S.primes P B K hP hB hK
      (fun p hp => ⟨S.prime_mem p hp,(hS ⟨p,hp⟩).1,(hS ⟨p,hp⟩).2⟩)).trans
    apply mul_le_mul
    · apply (pow_le_pow_left₀ (by positivity) (le_max_right (1:ℝ) _) _).trans
      apply pow_le_pow_right₀ hH
      rw [unselected_card,Fintype.card_fin]
      omega
    · exact pow_le_pow_of_le_one h0δ hδ d.property.2
    · positivity
    · positivity
  have hcodes (m : Fin (N+1)) :
      (∑ d : GoodWitnessTemplate h ℓ L J t m.val r,
        ∑ v : Fin m.val → S.Index,
          (d.val.system h d.property.1).fiberWeight P K (fun a => (v a:ℕ))) ≤
      (C:ℝ)*(H^N*δ^r) := by
    calc
      _ ≤ ∑ _ : GoodWitnessTemplate h ℓ L J t m.val r, H^N*δ^r :=
        sum_le_sum (fun d _ => hrow m d)
      _ = (Fintype.card (GoodWitnessTemplate h ℓ L J t m.val r):ℝ)*(H^N*δ^r) := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (pow_nonneg h0H _) (pow_nonneg h0δ _))
        exact_mod_cast (Fintype.card_subtype_le _).trans
          (witnessTemplate_card_uniform ℓ L J t m.val (Nat.lt_succ_iff.mp m.isLt))
  calc
    _ ≤ ∑ _ : Fin (N+1), (C:ℝ)*(H^N*δ^r) := sum_le_sum (fun m _ => hcodes m)
    _ = ((N+1:ℕ):ℝ)*(C:ℝ)*(H^N*δ^r) := by simp [mul_assoc]
    _ = _ := by
      dsimp only [witnessTemplateBudget,C,N,H,δ]
      push_cast
      ring

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
