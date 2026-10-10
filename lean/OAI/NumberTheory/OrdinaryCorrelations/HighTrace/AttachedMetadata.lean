import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LabelPrimeSet

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

abbrev AttachedMetadata (ℓ L : ℕ) := Fin (ℓ+1) × SpecMetadata L

noncomputable def attachedMetadata (w : ClosedLine h ℓ) (s : AttachedSpec w D L) :
    AttachedMetadata ℓ L := (s.index,specMetadata s.spec)

lemma attached_code_injective (w : ClosedLine h ℓ) (s t : AttachedSpec w D L)
    (hm : attachedMetadata w s=attachedMetadata w t)
    (hp : specPrimeCode s.spec=specPrimeCode t.spec) : s=t := by
  have hmeta : specMetadata s.spec=specMetadata t.spec := congrArg Prod.snd hm
  have hspec : s.spec=t.spec := specification_code_injective _ _ hmeta hp
  have hv : s.index=t.index := congrArg Prod.fst hm
  cases s
  cases t
  dsimp only at hspec hv
  subst_eqs
  rfl

abbrev ListMetadata (ℓ L n : ℕ) := Fin (n+1) × (Fin n → Option (AttachedMetadata ℓ L))
abbrev ListCodeSlot (L J n : ℕ) := Fin n × SpecCodeSlot L J

noncomputable def listMetadata (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (n : ℕ) (hn : 𝔏.length ≤ n) : ListMetadata ℓ L n :=
  (⟨𝔏.length,Nat.lt_succ_of_le hn⟩,
   fun i => if hi : i.val < 𝔏.length then some (attachedMetadata w (𝔏.get ⟨i.val,hi⟩)) else none)

noncomputable def listPrimeCode (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) (n : ℕ) :
    ListCodeSlot L ⌈C₀*Real.log B⌉₊ n → Option S.Index :=
  fun k => if hi : k.1.val < 𝔏.length then specPrimeCode (𝔏.get ⟨k.1.val,hi⟩).spec k.2 else none

theorem list_code_injective (w : ClosedLine h ℓ) (𝔏 𝔐 : List (AttachedSpec w D L))
    (n : ℕ) (h𝔏 : 𝔏.length ≤ n) (h𝔐 : 𝔐.length ≤ n)
    (hm : listMetadata w 𝔏 n h𝔏=listMetadata w 𝔐 n h𝔐)
    (hp : listPrimeCode w 𝔏 n=listPrimeCode w 𝔐 n) : 𝔏=𝔐 := by
  have hlen : 𝔏.length=𝔐.length := congrArg (fun m : ListMetadata ℓ L n => m.1.val) hm
  apply List.ext_get hlen
  intro i hi hj
  let i' : Fin n := ⟨i,lt_of_lt_of_le hi h𝔏⟩
  apply attached_code_injective w
  · have he := congrArg (fun m : ListMetadata ℓ L n => m.2 i') hm
    simpa only [listMetadata,i',dite_eq_left hi,dite_eq_left hj,Option.some.injEq] using he
  · funext k
    simpa only [listPrimeCode,i',dite_eq_left hi,dite_eq_left hj] using congrFun hp (i',k)

theorem listPrimeCode_support (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (n : ℕ) (hn : 𝔏.length ≤ n) (p : S.Index) :
    p.val ∈ listSupport w 𝔏 ↔ ∃ k, listPrimeCode w 𝔏 n k=some p := by
  constructor
  · intro hp
    obtain ⟨s,hs,hp⟩ := mem_biUnion.mp hp
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hs)
    obtain ⟨k,hk⟩ := (specPrimeCode_support (𝔏.get i).spec p).mp hp
    let i' : Fin n := ⟨i.val,lt_of_lt_of_le i.isLt hn⟩
    exact ⟨(i',k),by simpa only [listPrimeCode,i',dite_eq_left i.isLt] using hk⟩
  · rintro ⟨⟨i,k⟩,hk⟩
    dsimp only [listPrimeCode] at hk
    split_ifs at hk with hi
    · exact mem_biUnion.mpr ⟨𝔏.get ⟨i.val,hi⟩,List.mem_toFinset.mpr (List.get_mem _ _),
        (specPrimeCode_support (𝔏.get ⟨i.val,hi⟩).spec p).mpr ⟨k,hk⟩⟩

lemma specMetadata_card (L : ℕ) : Fintype.card (SpecMetadata L)=(L+1)^2*2^L := by
  simp only [SpecMetadata,Fintype.card_prod,Fintype.card_fin,Fintype.card_fun,Fintype.card_bool]
  ring

lemma listMetadata_card (ℓ L n : ℕ) :
    Fintype.card (ListMetadata ℓ L n)=(n+1)*(1+(ℓ+1)*((L+1)^2*2^L))^n := by
  simp only [ListMetadata,AttachedMetadata,Fintype.card_prod,Fintype.card_option,
    Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
  congr 1
  congr 1
  ring

lemma listCodeSlot_card (L J n : ℕ) : Fintype.card (ListCodeSlot L J n)=n*(L*J+1) := by
  simp only [ListCodeSlot,SpecCodeSlot,Fintype.card_prod,Fintype.card_option,Fintype.card_fin]

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
