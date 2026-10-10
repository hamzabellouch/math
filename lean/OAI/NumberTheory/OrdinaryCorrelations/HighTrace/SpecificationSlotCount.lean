import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.UnselectedCard
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SpecificationTemplate

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

noncomputable def specificationSlotCount (L J : ℕ) : ℕ := Fintype.card (SpecCodeSlot L J)
abbrev GoodSpecificationTemplate (h L J m : ℕ) :=
  {d : SpecificationTemplate L J m // d.WellFormed h}
abbrev SpecificationFilling (S : PrimeSystem) (h L J : ℕ) :=
  (m : Fin (specificationSlotCount L J+1)) ×
    (GoodSpecificationTemplate h L J m.val × (Fin m.val → S.Index))
noncomputable instance (S : PrimeSystem) (h L J : ℕ) : Fintype (SpecificationFilling S h L J) := by
  unfold SpecificationFilling
  infer_instance

namespace SpecificationFilling
variable {S : PrimeSystem} {h L J : ℕ}
noncomputable def weight (z : SpecificationFilling S h L J) (P K : ℝ) : ℝ :=
  (z.2.1.val.system h z.2.1.property).fiberWeight P K (fun a => (z.2.2 a:ℕ))
lemma weight_nonneg (z : SpecificationFilling S h L J) (P K : ℝ) : 0 ≤ z.weight P K :=
  TriangularExpressions.fiberWeight_nonneg _ _ _ _
noncomputable def decode (z : SpecificationFilling S h L J) :
    SpecMetadata L × (SpecCodeSlot L J → Option S.Index) :=
  (z.2.1.val.1,fun s => (z.2.1.val.2.1 s).map z.2.2)
end SpecificationFilling

variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L : ℕ}
namespace Specification
variable (s : S.Specification D h L)
noncomputable def primeWeight : ℝ := ∏ p ∈ support (specPrimeCode s), (p:ℝ)⁻¹
noncomputable def filling : SpecificationFilling S h L ⌈C₀*Real.log B⌉₊ :=
  ⟨⟨(support (specPrimeCode s)).card,Nat.lt_succ_of_le (card_support_le _)⟩,
    ⟨s.codeTemplate,s.codeTemplate_formed⟩,values (specPrimeCode s)⟩
lemma decode_filling : s.filling.decode=(specMetadata s,specPrimeCode s) := by
  exact Prod.ext rfl (funext (decode_pattern (specPrimeCode s)))
lemma weight_filling (P : ℝ) (hB : 0 ≤ B) (hS : ∀ p : S.Index, (p:ℝ) ≤ Real.exp B) :
    s.filling.weight P (densitySize B C₀ h L)=s.primeWeight := by
  change (if (s.codeTemplate.system h s.codeTemplate_formed).Admissible P _
    (fun a => (values (specPrimeCode s) a:ℕ)) then
    ∏ a, ((values (specPrimeCode s) a:ℕ):ℝ)⁻¹ else 0)=_
  rw [ite_eq_left (s.codeTemplate_admissible P hB hS)]
  exact (weight_identity (specPrimeCode s) (fun p => (p:ℝ)⁻¹)).symm
end Specification

noncomputable def specificationMajorant (D : S.DivisorFamily B τ C₀) (h L : ℕ) : ℝ :=
  ∑ s : S.Specification D h L, s.primeWeight

lemma specificationMajorant_le_filling (P : ℝ) (hB : 0 ≤ B)
    (hS : ∀ p : S.Index, (p:ℝ) ≤ Real.exp B) :
    specificationMajorant D h L ≤
      ∑ z : SpecificationFilling S h L ⌈C₀*Real.log B⌉₊,
        z.weight P (Specification.densitySize B C₀ h L) := by
  have hf : Function.Injective (Specification.filling (D:=D) (h:=h) (L:=L)) := by
    intro s t he
    have hh := congrArg SpecificationFilling.decode he
    rw [Specification.decode_filling,Specification.decode_filling] at hh
    exact specification_code_injective s t (congrArg Prod.fst hh) (congrArg Prod.snd hh)
  unfold specificationMajorant
  calc
    _ = ∑ z ∈ univ.image Specification.filling, z.weight P (Specification.densitySize B C₀ h L) := by
      rw [sum_image (fun _ _ _ _ he => hf he)]
      exact sum_congr rfl (fun s hs => (s.weight_filling P hB hS).symm)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun z hz hn => z.weight_nonneg _ _)

noncomputable def specificationBudget (L J : ℕ) : ℕ :=
  let N := specificationSlotCount L J
  (N+1)*Fintype.card (SpecMetadata L)*(N+1)^N*N

lemma specificationFilling_sum_le (S : PrimeSystem) (P B K : ℝ) (h L J : ℕ)
    (hP : 0 < P) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hS : ∀ p : S.Index, P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp B) :
    (∑ z : SpecificationFilling S h L J, z.weight P K) ≤
      (specificationBudget L J:ℝ)*(max 1 (∑ p ∈ S.primes,(p:ℝ)⁻¹))^(specificationSlotCount L J)*
        max (K/(P*Real.log 2)) ((2+B)/P) := by
  let N := specificationSlotCount L J
  let H : ℝ := max 1 (∑ p ∈ S.primes,(p:ℝ)⁻¹)
  let δ : ℝ := max (K/(P*Real.log 2)) ((2+B)/P)
  let C : ℕ := Fintype.card (SpecMetadata L)*(N+1)^N*N
  have hH : 1 ≤ H := le_max_left _ _
  have hδ : 0 ≤ δ := (by positivity : 0 ≤ (2+B)/P).trans (le_max_right _ _)
  have hrow (m : Fin (N+1)) (d : GoodSpecificationTemplate h L J m.val) :
      (∑ v : Fin m.val → S.Index, (d.val.system h d.property).fiberWeight P K (fun a => (v a:ℕ))) ≤
      H^N*δ := by
    have hb := (d.val.system h d.property).fiber_sum_le S.primes P B K hP hB hK
      (fun p hp => ⟨S.prime_mem p hp,(hS ⟨p,hp⟩).1,(hS ⟨p,hp⟩).2⟩)
    simp only [pow_one] at hb
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ hδ
    apply (pow_le_pow_left₀ (by positivity) (le_max_right (1:ℝ) _) _).trans
    apply pow_le_pow_right₀ hH
    rw [unselected_card,Fintype.card_fin]
    omega
  have hc (m : Fin (N+1)) : Fintype.card (GoodSpecificationTemplate h L J m.val) ≤ C := by
    apply (Fintype.card_subtype_le _).trans
    change Fintype.card (SpecificationTemplate L J m.val) ≤ C
    simp only [SpecificationTemplate,Fintype.card_prod,Fintype.card_fun,Fintype.card_option,Fintype.card_fin]
    have hmeta : Fintype.card (SpecMetadata L)=(L+1)*(Fintype.card Bool^L*(L+1)) := by
      simp only [SpecMetadata,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
    have hn : N=L*J+1 := by simp [N,specificationSlotCount,SpecCodeSlot]
    rw [←hmeta,←hn]
    dsimp only [C]
    have hm : m.val ≤ N := Nat.lt_succ_iff.mp m.isLt
    calc
      _ ≤ Fintype.card (SpecMetadata L)*((N+1)^N*N) := by gcongr
      _ = _ := by ring
  unfold SpecificationFilling
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ m : Fin (N+1), (C:ℝ)*(H^N*δ) := by
      apply sum_le_sum
      intro m hm
      rw [Fintype.sum_prod_type]
      calc
        _ ≤ ∑ d : GoodSpecificationTemplate h L J m.val, H^N*δ :=
          sum_le_sum (fun d hd => hrow m d)
        _ = (Fintype.card (GoodSpecificationTemplate h L J m.val):ℝ)*(H^N*δ) := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc m) (by positivity)
    _ = _ := by simp [specificationBudget,N,C]; ring

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
