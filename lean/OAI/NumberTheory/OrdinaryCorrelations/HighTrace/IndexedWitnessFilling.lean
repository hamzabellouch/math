import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.WitnessSlotCount
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Realizable

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.ArithmeticSaving
open OrdinaryCorrelations.SharedSlotPatterns
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L t : ℕ}

abbrev IndexedWitnessFilling (S : PrimeSystem) (h ℓ L J t r : ℕ) :=
  (m : Fin (witnessSlotCount ℓ L J t+1)) ×
    (GoodWitnessTemplate h ℓ L J t m.val r × (Fin m.val → S.Index))

noncomputable instance (S : PrimeSystem) (h ℓ L J t r : ℕ) :
    Fintype (IndexedWitnessFilling S h ℓ L J t r) := by
  haveI (m : Fin (witnessSlotCount ℓ L J t+1)) :
      Fintype (GoodWitnessTemplate h ℓ L J t m.val r) := inferInstance
  unfold IndexedWitnessFilling
  infer_instance

namespace IndexedWitnessFilling
variable {J r : ℕ}
noncomputable def weight (z : IndexedWitnessFilling S h ℓ L J t r) (P K : ℝ) : ℝ :=
  (z.2.1.val.system h z.2.1.property.1).fiberWeight P K (fun a => (z.2.2 a:ℕ))
lemma weight_nonneg (z : IndexedWitnessFilling S h ℓ L J t r) (P K : ℝ) :
    0 ≤ z.weight P K := by
  unfold weight TriangularExpressions.fiberWeight
  split_ifs
  · exact prod_nonneg (fun i hi => by positivity)
  · exact le_rfl
noncomputable def decode (z : IndexedWitnessFilling S h ℓ L J t r) :
    WitnessMetadata ℓ L t × (WitnessCodeSlot ℓ L J t → Option S.Index) :=
  (z.2.1.val.1, fun s => (z.2.1.val.2.1 s).map z.2.2)
lemma sum_weight (P K : ℝ) :
    (∑ z : IndexedWitnessFilling S h ℓ L J t r, z.weight P K)=
      witnessTemplateMass S P K h ℓ L J t r := by
  unfold witnessTemplateMass
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro m hm
  exact Fintype.sum_prod_type _
end IndexedWitnessFilling

namespace WitnessConfiguration.Certificate
variable {x : WitnessConfiguration D h ℓ L t} {P K : ℝ} {r : ℕ}
variable (c : x.Certificate P K r)

noncomputable def encode : IndexedWitnessFilling S h ℓ L ⌈C₀*Real.log B⌉₊ t r :=
  ⟨⟨(support x.primeCode).card,Nat.lt_succ_of_le (card_support_le x.primeCode)⟩,
    ⟨c.code,⟨c.formed,c.rank_ge⟩⟩,values x.primeCode⟩

lemma decode_encode : c.encode.decode=x.rawCode := by
  change (c.code.1,fun s => (c.code.2.1 s).map (values x.primeCode))=(x.metadata,x.primeCode)
  rw [c.metadata_eq,c.pattern_eq]
  exact Prod.ext rfl (funext (decode_pattern x.primeCode))

lemma weight_encode : c.encode.weight P K=x.primeWeight := by
  change (if (c.code.system h c.formed).Admissible P K (fun a => (values x.primeCode a:ℕ)) then
    ∏ a, ((values x.primeCode a:ℕ):ℝ)⁻¹ else 0)=x.primeWeight
  rw [ite_eq_left c.admissible]
  exact (weight_identity x.primeCode (fun p => (p:ℝ)⁻¹)).symm
end WitnessConfiguration.Certificate

theorem configurationMass_le_templateMass (P K : ℝ) (r : ℕ)
    (cert : ∀ x : {x : WitnessConfiguration D h ℓ L t // x.Realizable}, x.val.Certificate P K r) :
    (∑ x : {x : WitnessConfiguration D h ℓ L t // x.Realizable}, x.val.primeWeight) ≤
      witnessTemplateMass S P K h ℓ L ⌈C₀*Real.log B⌉₊ t r := by
  let f := fun x : {x : WitnessConfiguration D h ℓ L t // x.Realizable} => (cert x).encode
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply WitnessConfiguration.rawCode_injective
    have hd := congrArg IndexedWitnessFilling.decode he
    simpa only [f,WitnessConfiguration.Certificate.decode_encode] using hd
  rw [←IndexedWitnessFilling.sum_weight]
  calc
    _ = ∑ z ∈ univ.image f, z.weight P K := by
      rw [sum_image (fun x _ y _ he => hf he)]
      exact sum_congr rfl (fun x hx => (cert x).weight_encode.symm)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun z hz hn => z.weight_nonneg P K)

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
