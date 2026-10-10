import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GlobalRecord
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DataInjective
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LinePrimeMemFullUsed

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L t : ℕ}

structure WitnessConfiguration (D : S.DivisorFamily B τ C₀) (h ℓ L t : ℕ) where
  line : ClosedLine h ℓ
  labels : ∀ i, line.label i ∈ D.members
  primitives : List (AttachedSpec line D L)
  length_le : primitives.length ≤ t
  family : PrivateFamily line D L t

abbrev WitnessCodeSlot (ℓ L J t : ℕ) :=
  (Fin ℓ × Fin J) ⊕ (ListCodeSlot L J t ⊕ ((Fin t × SpecCodeSlot L J) ⊕ Fin t))

abbrev WitnessMetadata (ℓ L t : ℕ) :=
  (Fin ℓ → Bool) × ListMetadata ℓ L t × (Fin t → AttachedMetadata ℓ L)

namespace WitnessConfiguration
variable (x : WitnessConfiguration D h ℓ L t)

noncomputable def metadata : WitnessMetadata ℓ L t :=
  (signBit x.line,listMetadata x.line x.primitives t x.length_le,
    fun j => attachedMetadata x.line (x.family.witness j))

noncomputable def primeCode : WitnessCodeSlot ℓ L ⌈C₀*Real.log B⌉₊ t → Option S.Index
  | .inl (i,j) => FiniteSlotEncoding.code (labelPrimeSet (x.line.label i) (x.labels i)) ⌈C₀*Real.log B⌉₊ j
  | .inr (.inl k) => listPrimeCode x.line x.primitives t k
  | .inr (.inr (.inl (j,k))) => specPrimeCode (x.family.witness j).spec k
  | .inr (.inr (.inr j)) => some (x.family.key j)

noncomputable def rawCode := (x.metadata,x.primeCode)

lemma rawCode_injective : Function.Injective
    (rawCode : WitnessConfiguration D h ℓ L t → _) := by
  intro x y he
  have hm := congrArg Prod.fst he
  have hp := congrArg Prod.snd he
  have hline : x.line=y.line := by
    apply GlobalRecord.line_eq_of_labels_signs
    · funext i
      have hsets : labelPrimeSet (x.line.label i) (x.labels i)=
          labelPrimeSet (y.line.label i) (y.labels i) := by
        apply FiniteSlotEncoding.code_injective (m:=⌈C₀*Real.log B⌉₊)
        · rw [labelPrimeSet_card]; exact D.omega _ (x.labels i)
        · rw [labelPrimeSet_card]; exact D.omega _ (y.labels i)
        · funext j
          exact congrFun hp (.inl (i,j))
      rw [←labelPrimeSet_product (x.line.label i) (x.labels i),
        ←labelPrimeSet_product (y.line.label i) (y.labels i),hsets]
    · funext i
      have hs : signBit x.line i=signBit y.line i :=
        congrArg (fun z : WitnessMetadata ℓ L t => z.1 i) hm
      rw [signBit_decode x.line i,signBit_decode y.line i,hs]
  cases x with
  | mk w hw l hl F =>
    cases y with
    | mk v hv m hm' G =>
      dsimp only at hline
      subst v
      have hlist : l=m := list_code_injective w l m t hl hm'
        (congrArg (fun z : WitnessMetadata ℓ L t => z.2.1) hm)
        (funext (fun k => congrFun hp (.inr (.inl k))))
      subst m
      have hfamily : F=G := by
        apply PrivateFamily.data_injective
        apply Prod.ext
        · funext j
          apply attached_code_injective w
          · exact congrArg (fun z : WitnessMetadata ℓ L t => z.2.2 j) hm
          · funext k
            exact congrFun hp (.inr (.inr (.inl (j,k))))
        · funext j
          exact Option.some.inj (congrFun hp (.inr (.inr (.inr j))))
      subst G
      rfl

instance : Finite (WitnessConfiguration D h ℓ L t) :=
  Finite.of_injective _ rawCode_injective

noncomputable instance : Fintype (WitnessConfiguration D h ℓ L t) := Fintype.ofFinite _

lemma primeCode_support (p : S.Index) :
    (∃ k, x.primeCode k=some p) ↔ p ∈ fullUsedIndices x.line (x.primitives++List.ofFn x.family.witness) := by
  constructor
  · rintro ⟨(⟨i,j⟩ | (k | (⟨j,k⟩ | j))),hp⟩
    · have hm := FiniteSlotEncoding.code_mem _ _ j p hp
      exact line_prime_mem_fullUsed x.line _ p ((mem_labelPrimeSet _ _ _).mp hm)
    · have hm := (listPrimeCode_support x.line x.primitives t x.length_le p).mpr ⟨k,hp⟩
      obtain ⟨s,hs,hm⟩ := mem_biUnion.mp hm
      exact list_prime_mem_fullUsed x.line _ s
        (List.mem_append_left _ (List.mem_toFinset.mp hs)) p hm
    · exact list_prime_mem_fullUsed x.line _ (x.family.witness j)
        (List.mem_append_right _ (List.mem_ofFn.mpr ⟨j,rfl⟩)) p
        ((specPrimeCode_support (x.family.witness j).spec p).mpr ⟨k,hp⟩)
    · have he : x.family.key j=p := Option.some.inj hp
      exact he ▸ list_prime_mem_fullUsed x.line _ (x.family.witness j)
        (List.mem_append_right _ (List.mem_ofFn.mpr ⟨j,rfl⟩)) (x.family.key j) (x.family.key_mem j)
  · intro hp
    rcases (mem_filter.mp hp).2 with ⟨i,hi⟩|hp
    · have hc : (labelPrimeSet (x.line.label i) (x.labels i)).card ≤ ⌈C₀*Real.log B⌉₊ := by
        rw [labelPrimeSet_card]; exact D.omega _ (x.labels i)
      have hm : p ∈ labelPrimeSet (x.line.label i) (x.labels i) :=
        (mem_labelPrimeSet _ _ _).mpr
          (Nat.mem_primeFactors.mpr ⟨S.prime_mem p p.property,hi,(x.line.label_pos i).ne'⟩)
      obtain ⟨j,hj⟩ := (FiniteSlotEncoding.mem_iff_code _ _ hc p).mp hm
      exact ⟨.inl (i,j),hj⟩
    · obtain ⟨s,hs,hp⟩ := mem_biUnion.mp hp
      rcases List.mem_append.mp (List.mem_toFinset.mp hs) with hs|hs
      · obtain ⟨k,hk⟩ := (listPrimeCode_support x.line x.primitives t x.length_le p).mp
          (mem_biUnion.mpr ⟨s,List.mem_toFinset.mpr hs,hp⟩)
        exact ⟨.inr (.inl k),hk⟩
      · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hs
        obtain ⟨k,hk⟩ := (specPrimeCode_support (x.family.witness j).spec p).mp hp
        exact ⟨.inr (.inr (.inl (j,k))),hk⟩

lemma codeSlot_card (ℓ L J t : ℕ) :
    Fintype.card (WitnessCodeSlot ℓ L J t)=ℓ*J+2*t*(L*J+1)+t := by
  simp only [WitnessCodeSlot,ListCodeSlot,SpecCodeSlot,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_option,Fintype.card_fin]
  ring

lemma metadata_card (ℓ L t : ℕ) :
    Fintype.card (WitnessMetadata ℓ L t)=
      2^ℓ*((t+1)*(1+(ℓ+1)*((L+1)^2*2^L))^t)*((ℓ+1)*((L+1)^2*2^L))^t := by
  simp only [WitnessMetadata,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,
    ListMetadata,AttachedMetadata,SpecMetadata,Fintype.card_option]
  ring

end WitnessConfiguration
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
