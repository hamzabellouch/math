import Mathlib
import OAI.Probability.UnimodularPercolation.Splicing.EndpointMoments

namespace OAI

/-! Covariance for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteTraceCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

@[simp] theorem edgeFieldEquiv_symm_edgeFieldEquiv (b : E ≃ E) (ω : Set E) :
    edgeFieldEquiv b.symm (edgeFieldEquiv b ω) = ω := by
  ext e
  simp only [edgeFieldEquiv_apply,Set.mem_preimage,Equiv.symm_symm,Equiv.symm_apply_apply]

@[simp] theorem spliceStateEquiv_symm_spliceStateEquiv (b : E ≃ E) (s : SpliceState E) :
    spliceStateEquiv b.symm (spliceStateEquiv b s) = s := by
  apply Prod.ext
  · exact edgeFieldEquiv_symm_edgeFieldEquiv b s.1
  · funext i
    exact edgeFieldEquiv_symm_edgeFieldEquiv b (s.2 i)

@[simp] theorem spliceCodeEquiv_symm_spliceCodeEquiv (b : E ≃ E) (c : List (ℕ × E)) :
    spliceCodeEquiv b.symm (spliceCodeEquiv b c) = c := by
  induction c with
  | nil => rfl
  | cons q c ih =>
    rcases q with ⟨i,e⟩
    simpa only [spliceCodeEquiv_apply,List.map_cons,Prod.map_apply,id_eq,Equiv.symm_apply_apply] using
      congrArg (List.cons (i,e)) ih

theorem spliceTrace_aut_map_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ)
    (ω ωf : Set E) (c : List (ℕ × E)) :
    SpliceTrace G (a x) (fun i => edgeFieldEquiv b (η i)) (fun i => a (y i)) k j
      (edgeFieldEquiv b ω) (spliceCodeEquiv b c) (edgeFieldEquiv b ωf) ↔
    SpliceTrace G x η y k j ω c ωf := by
  constructor
  · intro ht
    have hh := ht.aut_map G (isAut_symm G hab) (a x) (fun i => edgeFieldEquiv b (η i))
      (fun i => a (y i)) k j (edgeFieldEquiv b ω) (edgeFieldEquiv b ωf) (spliceCodeEquiv b c)
    simpa only [Equiv.symm_apply_apply,edgeFieldEquiv_symm_edgeFieldEquiv,
      spliceCodeEquiv_symm_spliceCodeEquiv] using hh
  · exact SpliceTrace.aut_map G hab x η y k j ω ωf c

theorem boundedTraceCodes_aut_map_iff (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (k : ℕ) (c : List (ℕ × E)) :
    spliceCodeEquiv b c ∈ boundedTraceCodes Q' k ↔ c ∈ boundedTraceCodes Q k := by
  simp only [mem_boundedTraceCodes,spliceCodeEquiv_apply,List.length_map]
  apply and_congr_right
  intro _
  constructor
  · intro h q hq
    have hh := h (q.1,b q.2) (List.mem_map.mpr ⟨q,hq,rfl⟩)
    exact ⟨hh.1,hh.2.1,(hQ q.2).mpr hh.2.2⟩
  · intro h r hr
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    exact ⟨(h q hq).1,(h q hq).2.1,(hQ q.2).mp (h q hq).2.2⟩

theorem finiteTraceCodes_aut_map_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (Q Q' : Finset E) (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q')
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω : Set E) (c : List (ℕ × E)) :
    spliceCodeEquiv b c ∈ finiteTraceCodes G (a x) (fun i => edgeFieldEquiv b (η i))
      (fun i => a (y i)) k j (edgeFieldEquiv b ω) Q' ↔
      c ∈ finiteTraceCodes G x η y k j ω Q := by
  rw [mem_finiteTraceCodes_iff,mem_finiteTraceCodes_iff,boundedTraceCodes_aut_map_iff b Q Q' hQ,
    replaySplice_aut_map G hab,spliceTrace_aut_map_iff G hab]

 
def finiteTraceCodesEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (Q Q' : Finset E) (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q')
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω : Set E) :
    ↥(finiteTraceCodes G x η y k j ω Q) ≃
      ↥(finiteTraceCodes G (a x) (fun i => edgeFieldEquiv b (η i)) (fun i => a (y i)) k j
        (edgeFieldEquiv b ω) Q') :=
  (spliceCodeEquiv b).subtypeEquiv (fun c => (finiteTraceCodes_aut_map_iff G hab Q Q' hQ x η y k j ω c).symm)

end FiniteTraceCovariance

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteIndexCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

def finiteTraceIndexEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (k : ℕ) (Q Q' : Finset E) (A A' : Finset (SpliceState E))
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (hA : ∀ s, s ∈ A ↔ spliceStateEquiv b s ∈ A')
    (y y' : SpliceState E → ℕ → V) (hy : ∀ s i, y' (spliceStateEquiv b s) i = a (y s i)) :
    FiniteTraceIndex G x k Q A y ≃ FiniteTraceIndex G (a x) k Q' A' y' :=
  Equiv.sigmaCongr ((spliceStateEquiv b).subtypeEquiv hA) (fun s =>
    (spliceCodeEquiv b).subtypeEquiv (fun c => by
      have hy' : y' (spliceStateEquiv b s.val) = fun i => a (y s.val i) := funext (hy s.val)
      change c ∈ finiteTraceCodes G x s.val.2 (y s.val) k 0 s.val.1 Q ↔
        spliceCodeEquiv b c ∈ finiteTraceCodes G (a x) (fun i => edgeFieldEquiv b (s.val.2 i))
          (y' (spliceStateEquiv b s.val)) k 0 (edgeFieldEquiv b s.val.1) Q'
      rw [hy']
      exact (finiteTraceCodes_aut_map_iff G hab Q Q' hQ x s.val.2 (y s.val) k 0 s.val.1 c).symm))

namespace FiniteTraceIndexEquiv
variable (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (k : ℕ) (Q Q' : Finset E) (A A' : Finset (SpliceState E))
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (hA : ∀ s, s ∈ A ↔ spliceStateEquiv b s ∈ A')
    (y y' : SpliceState E → ℕ → V) (hy : ∀ s i, y' (spliceStateEquiv b s) i = a (y s i))

@[simp] theorem input (t : FiniteTraceIndex G x k Q A y) :
    traceIndexInput G (a x) k Q' A' y' (finiteTraceIndexEquiv G hab x k Q Q' A A' hQ hA y y' hy t) =
      spliceStateEquiv b (traceIndexInput G x k Q A y t) := rfl

@[simp] theorem code (t : FiniteTraceIndex G x k Q A y) :
    traceIndexCode G (a x) k Q' A' y' (finiteTraceIndexEquiv G hab x k Q Q' A A' hQ hA y y' hy t) =
      spliceCodeEquiv b (traceIndexCode G x k Q A y t) := rfl

@[simp] theorem output (t : FiniteTraceIndex G x k Q A y) :
    traceIndexOutput G (a x) k Q' A' y' (finiteTraceIndexEquiv G hab x k Q Q' A A' hQ hA y y' hy t) =
      spliceStateEquiv b (traceIndexOutput G x k Q A y t) := by
  have hy' : y' (spliceStateEquiv b t.1.val) = fun i => a (y t.1.val i) := funext (hy t.1.val)
  change runMasks (replayMasks G (a x) (fun i => edgeFieldEquiv b (t.1.val.2 i))
    (y' (spliceStateEquiv b t.1.val)) (spliceCodeEquiv b t.2.val) (edgeFieldEquiv b t.1.val.1))
      (spliceStateEquiv b t.1.val) = _
  rw [hy',replayMasks_aut_map G hab,runMasks_aut_map]
  rfl

@[simp] theorem mass (t : FiniteTraceIndex G x k Q A y) :
    traceIndexMass G (a x) k Q' A' y' (finiteTraceIndexEquiv G hab x k Q Q' A A' hQ hA y y' hy t) =
      traceIndexMass G x k Q A y t := by
  unfold traceIndexMass
  rw [output G hab x k Q Q' A A' hQ hA y y' hy t]
  apply Finset.prod_congr rfl
  intro i _
  have hy' : y' (spliceStateEquiv b t.1.val) = fun i => a (y t.1.val i) := funext (hy t.1.val)
  change (traceContactCount G (fun j => edgeFieldEquiv b (t.1.val.2 j))
    (y' (spliceStateEquiv b t.1.val)) (edgeFieldEquiv b (traceIndexOutput G x k Q A y t).1)
    (a x) (spliceCodeEquiv b t.2.val) (i.val+1):ℝ)⁻¹ = _
  rw [hy',traceContactCount_aut_map G hab]

end FiniteTraceIndexEquiv

 

theorem finiteForwardLoad_aut_map (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (k : ℕ) (Q Q' : Finset E) (A A' : Finset (SpliceState E))
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (hA : ∀ s, s ∈ A ↔ spliceStateEquiv b s ∈ A')
    (y y' : SpliceState E → ℕ → V) (hy : ∀ s i, y' (spliceStateEquiv b s) i = a (y s i))
    (s : SpliceState E) :
    finiteForwardLoad G (a x) k Q' A' y' (spliceStateEquiv b s) = finiteForwardLoad G x k Q A y s := by
  unfold finiteForwardLoad finiteInverseLoad
  rw [← (finiteTraceIndexEquiv G hab x k Q Q' A A' hQ hA y y' hy).sum_comp]
  apply Finset.sum_congr rfl
  intro t _
  rw [FiniteTraceIndexEquiv.output,FiniteTraceIndexEquiv.mass]
  simp only [(spliceStateEquiv b).injective.eq_iff]

end FiniteIndexCovariance

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteFieldCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finset_aut_eq_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') : Q' = Q.map b.toEmbedding := by
  ext e
  simpa only [Finset.mem_map_equiv,b.apply_symm_apply] using (hQ (b.symm e)).symm

noncomputable def finiteFieldAutEquiv (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') : FiniteField Q ≃ FiniteField Q' :=
  (Equiv.finsetCongr b).subtypeEquiv (fun ω => by
    simp only [Finset.mem_powerset]
    change ω ⊆ Q ↔ ω.map b.toEmbedding ⊆ Q'
    rw [finset_aut_eq_map b Q Q' hQ,Finset.map_subset_map])

@[simp] theorem finiteFieldSet_aut_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (ω : FiniteField Q) :
    finiteFieldSet Q' (finiteFieldAutEquiv b Q Q' hQ ω) = edgeFieldEquiv b (finiteFieldSet Q ω) := by
  change (ω.val.map b.toEmbedding : Set E) = b.symm ⁻¹' (ω.val : Set E)
  rw [Finset.coe_map]
  exact b.image_eq_preimage_symm _

@[simp] theorem finiteFieldWeight_aut_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (p : ℝ) (ω : FiniteField Q) :
    finiteFieldWeight Q' p (finiteFieldAutEquiv b Q Q' hQ ω) = finiteFieldWeight Q p ω := by
  change p^(ω.val.map b.toEmbedding).card * (1-p)^(Q'.card-(ω.val.map b.toEmbedding).card) = _
  simp only [Finset.card_map,finset_aut_eq_map b Q Q' hQ]
  rfl

noncomputable def finiteFamilyEquiv (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (J : Finset ℕ) :
    (↥J → FiniteField Q) ≃ (↥J → FiniteField Q') :=
  Equiv.piCongrRight fun _ => finiteFieldAutEquiv b Q Q' hQ

@[simp] theorem finiteFieldFamily_aut_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (J : Finset ℕ) (η : ↥J → FiniteField Q) (i : ℕ) :
    finiteFieldFamily Q' J (finiteFamilyEquiv b Q Q' hQ J η) i =
      edgeFieldEquiv b (finiteFieldFamily Q J η i) := by
  unfold finiteFieldFamily
  split_ifs with hi
  · exact finiteFieldSet_aut_map b Q Q' hQ (η ⟨i,hi⟩)
  · rfl

@[simp] theorem finiteFamilyWeight_aut_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (J : Finset ℕ) (p : ℝ) (η : ↥J → FiniteField Q) :
    finiteFamilyWeight Q' J p (finiteFamilyEquiv b Q Q' hQ J η) = finiteFamilyWeight Q J p η := by
  apply Finset.prod_congr rfl
  intro i _
  exact finiteFieldWeight_aut_map b Q Q' hQ p (η i)

@[simp] theorem restrictFiniteField_aut_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (ω : Set E) :
    restrictFiniteField Q' (edgeFieldEquiv b ω) = finiteFieldAutEquiv b Q Q' hQ (restrictFiniteField Q ω) := by
  apply finiteFieldSet_injective Q'
  rw [finiteFieldSet_aut_map,finiteFieldSet_restrict,finiteFieldSet_restrict]
  ext e
  change (b.symm e ∈ ω ∧ e ∈ Q') ↔ (b.symm e ∈ ω ∧ b.symm e ∈ Q)
  rw [hQ (b.symm e),b.apply_symm_apply]

 

theorem finiteRootLoad_aut_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (J : Finset ℕ) (p : ℝ)
    (f f' : SpliceState E → ℝ) (hf : ∀ s, f' (spliceStateEquiv b s) = f s)
    (ω : FiniteField Q) :
    finiteRootLoad Q' J p f' (finiteFieldAutEquiv b Q Q' hQ ω) = finiteRootLoad Q J p f ω := by
  unfold finiteRootLoad
  rw [← (finiteFamilyEquiv b Q Q' hQ J).sum_comp]
  apply Finset.sum_congr rfl
  intro η _
  rw [finiteFamilyWeight_aut_map,finiteFieldSet_aut_map]
  have he : finiteFieldFamily Q' J (finiteFamilyEquiv b Q Q' hQ J η) =
      fun i => edgeFieldEquiv b (finiteFieldFamily Q J η i) :=
    funext (finiteFieldFamily_aut_map b Q Q' hQ J η)
  rw [he]
  exact congrArg (fun t => finiteFamilyWeight Q J p η * t)
    (hf (finiteFieldSet Q ω,finiteFieldFamily Q J η))

end FiniteFieldCovariance

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section ChoiceIndexCovariance
attribute [local instance] Classical.propDecidable Classical.decEq
variable {P P' : Type*}

def finiteChoiceTraceIndexEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (k : ℕ) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (e : P ≃ P')
    (A : P → Finset (SpliceState E)) (A' : P' → Finset (SpliceState E))
    (hA : ∀ r s, s ∈ A r ↔ spliceStateEquiv b s ∈ A' (e r))
    (y : P → SpliceState E → ℕ → V) (y' : P' → SpliceState E → ℕ → V)
    (hy : ∀ r s i, y' (e r) (spliceStateEquiv b s) i = a (y r s i)) :
    FiniteChoiceTraceIndex G x k Q A y ≃ FiniteChoiceTraceIndex G (a x) k Q' A' y' :=
  Equiv.sigmaCongr e (fun r => finiteTraceIndexEquiv G hab x k Q Q' (A r) (A' (e r)) hQ (hA r)
    (y r) (y' (e r)) (hy r))

namespace FiniteChoiceTraceIndexEquiv
variable (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (k : ℕ) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (e : P ≃ P')
    (A : P → Finset (SpliceState E)) (A' : P' → Finset (SpliceState E))
    (hA : ∀ r s, s ∈ A r ↔ spliceStateEquiv b s ∈ A' (e r))
    (y : P → SpliceState E → ℕ → V) (y' : P' → SpliceState E → ℕ → V)
    (hy : ∀ r s i, y' (e r) (spliceStateEquiv b s) i = a (y r s i))

@[simp] theorem input (t : FiniteChoiceTraceIndex G x k Q A y) :
    choiceTraceInput G (a x) k Q' A' y' (finiteChoiceTraceIndexEquiv G hab x k Q Q' hQ e A A' hA y y' hy t) =
      spliceStateEquiv b (choiceTraceInput G x k Q A y t) := rfl

@[simp] theorem output (t : FiniteChoiceTraceIndex G x k Q A y) :
    choiceTraceOutput G (a x) k Q' A' y' (finiteChoiceTraceIndexEquiv G hab x k Q Q' hQ e A A' hA y y' hy t) =
      spliceStateEquiv b (choiceTraceOutput G x k Q A y t) :=
  FiniteTraceIndexEquiv.output G hab x k Q Q' (A t.1) (A' (e t.1)) hQ (hA t.1)
    (y t.1) (y' (e t.1)) (hy t.1) t.2

@[simp] theorem mass (q : SpliceState E → P → ℝ) (q' : SpliceState E → P' → ℝ)
    (hq : ∀ s r, q' (spliceStateEquiv b s) (e r) = q s r)
    (t : FiniteChoiceTraceIndex G x k Q A y) :
    choiceTraceMass G (a x) k Q' A' y' q'
      (finiteChoiceTraceIndexEquiv G hab x k Q Q' hQ e A A' hA y y' hy t) =
      choiceTraceMass G x k Q A y q t := by
  unfold choiceTraceMass
  rw [input G hab x k Q Q' hQ e A A' hA y y' hy]
  change q' (spliceStateEquiv b (choiceTraceInput G x k Q A y t)) (e t.1) * _ = _
  rw [hq]
  exact congrArg (fun m => q (choiceTraceInput G x k Q A y t) t.1 * m)
    (FiniteTraceIndexEquiv.mass G hab x k Q Q' (A t.1) (A' (e t.1)) hQ (hA t.1)
      (y t.1) (y' (e t.1)) (hy t.1) t.2)

end FiniteChoiceTraceIndexEquiv

theorem finiteChoiceForwardLoad_aut_map [Fintype P] [Fintype P']
    (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (k : ℕ) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (e : P ≃ P')
    (A : P → Finset (SpliceState E)) (A' : P' → Finset (SpliceState E))
    (hA : ∀ r s, s ∈ A r ↔ spliceStateEquiv b s ∈ A' (e r))
    (y : P → SpliceState E → ℕ → V) (y' : P' → SpliceState E → ℕ → V)
    (hy : ∀ r s i, y' (e r) (spliceStateEquiv b s) i = a (y r s i))
    (q : SpliceState E → P → ℝ) (q' : SpliceState E → P' → ℝ)
    (hq : ∀ s r, q' (spliceStateEquiv b s) (e r) = q s r) (s : SpliceState E) :
    finiteChoiceForwardLoad G (a x) k Q' A' y' q' (spliceStateEquiv b s) =
      finiteChoiceForwardLoad G x k Q A y q s := by
  unfold finiteChoiceForwardLoad finiteInverseLoad
  rw [← (finiteChoiceTraceIndexEquiv G hab x k Q Q' hQ e A A' hA y y' hy).sum_comp]
  apply Finset.sum_congr rfl
  intro t _
  rw [FiniteChoiceTraceIndexEquiv.output,FiniteChoiceTraceIndexEquiv.mass G hab x k Q Q' hQ e A A' hA y y' hy q q' hq]
  simp only [(spliceStateEquiv b).injective.eq_iff]

end ChoiceIndexCovariance

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AmplificationCovarianceInput
attribute [local instance] Classical.propDecidable Classical.decEq

theorem edgeField_subset_aut_iff (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (ω : Set E) :
    edgeFieldEquiv b ω ⊆ (Q' : Set E) ↔ ω ⊆ (Q : Set E) := by
  constructor
  · intro h e he
    exact (hQ e).mpr (h (by simpa using he : b e ∈ edgeFieldEquiv b ω))
  · intro h e he
    have hh := (hQ (b.symm e)).mp (h he)
    simpa only [b.apply_symm_apply,Finset.mem_coe] using hh

theorem finiteSpliceDomain_aut_map_iff (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (J : Finset ℕ) (s : SpliceState E) :
    spliceStateEquiv b s ∈ finiteSpliceDomain Q' J ↔ s ∈ finiteSpliceDomain Q J := by
  rw [mem_finiteSpliceDomain_iff,mem_finiteSpliceDomain_iff]
  change (edgeFieldEquiv b s.1 ⊆ (Q':Set E) ∧
    (∀ i,edgeFieldEquiv b (s.2 i) ⊆ (Q':Set E)) ∧ ∀ i ∉ J,edgeFieldEquiv b (s.2 i)=∅) ↔ _
  have hz (η : Set E) : edgeFieldEquiv b η = ∅ ↔ η = ∅ := by
    change edgeFieldEquiv b η = edgeFieldEquiv b ∅ ↔ _
    exact (edgeFieldEquiv b).injective.eq_iff
  simp only [edgeField_subset_aut_iff b Q Q' hQ,hz]

theorem oldRunVertices_map {W W' : Type*} (f : W → W') (k : ℕ) (z : W)
    (r : Fin k → W) (i : ℕ) :
    oldRunVertices k (f z) (fun j => f (r j)) i = f (oldRunVertices k z r i) := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    simp only [oldRunVertices]
    split_ifs with hi
    · exact ih (r 0) (Fin.tail r)
    · rfl

theorem oldRunWeight_map {W W' : Type*} (f : W → W')
    (K : ℕ → W → W → ℝ) (K' : ℕ → W' → W' → ℝ)
    (hK : ∀ i a b, K' i (f a) (f b) = K i a b) (k : ℕ) (z : W) (r : Fin k → W) :
    oldRunWeight K' k (f z) (fun i => f (r i)) = oldRunWeight K k z r := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    simp only [oldRunWeight,hK]
    rw [show Fin.tail (fun i => f (r i)) = (fun i => f (Fin.tail r i)) from rfl,ih]

def finiteVertexEquiv (a : V ≃ V) (B B' : Finset V) (hB : ∀ x, x ∈ B ↔ a x ∈ B') : ↥B ≃ ↥B' :=
  a.subtypeEquiv hB

def finiteRunEquiv (a : V ≃ V) (B B' : Finset V) (hB : ∀ x, x ∈ B ↔ a x ∈ B') (k : ℕ) :
    (Fin k → ↥B) ≃ (Fin k → ↥B') :=
  Equiv.piCongrRight fun _ => finiteVertexEquiv a B B' hB

theorem amplificationVertices_aut_map (a : V ≃ V) (B B' : Finset V)
    (hB : ∀ x, x ∈ B ↔ a x ∈ B') (k : ℕ) (z : ↥B) (r : Fin k → ↥B) (i : ℕ) :
    amplificationVertices B' k (finiteVertexEquiv a B B' hB z) (finiteRunEquiv a B B' hB k r) i =
      a (amplificationVertices B k z r i) :=
  congrArg Subtype.val (oldRunVertices_map (finiteVertexEquiv a B B' hB) k z r i)

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem mass_aut_map (q : LocalEndpointRule G hloc O M L) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x y : V) :
    q.mass (edgeFieldEquiv b ω) (a x) (a y) = q.mass ω x y := by
  simpa only [Equiv.symm_apply_apply,edgeFieldEquiv_apply] using
    q.covariance a.symm b.symm (isAut_symm G hab) ω (a x) (a y)

theorem amplificationWeight_aut_map (q : LocalEndpointRule G hloc O M L) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (B B' : Finset V) (hB : ∀ x, x ∈ B ↔ a x ∈ B')
    (k : ℕ) (z : ↥B) (s : SpliceState E) (r : Fin k → ↥B) :
    q.amplificationWeight B' k (finiteVertexEquiv a B B' hB z) (spliceStateEquiv b s)
      (finiteRunEquiv a B B' hB k r) = q.amplificationWeight B k z s r := by
  apply oldRunWeight_map (finiteVertexEquiv a B B' hB)
  intro i v w
  exact q.mass_aut_map hab (s.2 i) v.val w.val

theorem amplificationInputs_aut_map_iff (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (B B' : Finset V) (hB : ∀ x, x ∈ B ↔ a x ∈ B')
    (x : V) (k n : ℕ) (z : ↥B) (r : Fin k → ↥B) (s : SpliceState E) :
    spliceStateEquiv b s ∈ q.amplificationInputs Q' B' (a x) k n
      (finiteVertexEquiv a B B' hB z) (finiteRunEquiv a B B' hB k r) ↔
      s ∈ q.amplificationInputs Q B x k n z r := by
  rw [q.mem_amplificationInputs,q.mem_amplificationInputs]
  have hn : (cluster G (edgeFieldEquiv b s.1) (a x)).ncard = (cluster G s.1 x).ncard := by
    rw [cluster_edgeFieldEquiv G hab,← a.image_eq_preimage_symm,Set.ncard_image_of_injective _ a.injective]
  change (spliceStateEquiv b s ∈ finiteSpliceDomain Q' (Finset.Icc 1 k) ∧
    a x ∈ vertexOrbit G o ∧ a z.val ∈ vertexOrbit G o ∧
    n ≤ (cluster G (edgeFieldEquiv b s.1) (a x)).ncard ∧
    (cluster G (edgeFieldEquiv b s.1) (a x)).ncard < 2*n ∧
    amplificationVertices B' k (finiteVertexEquiv a B B' hB z) (finiteRunEquiv a B B' hB k r) 0 ∈
      cluster G (edgeFieldEquiv b s.1) (a x) ∧ _) ↔ _
  rw [finiteSpliceDomain_aut_map_iff b Q Q' hQ,mem_vertexOrbit_aut_iff G o hab,
    mem_vertexOrbit_aut_iff G o hab,hn,amplificationVertices_aut_map,
    cluster_edgeFieldEquiv G hab,q.amplificationWeight_aut_map hab B B' hB]
  simp only [Set.mem_preimage,Equiv.symm_apply_apply]

end LocalEndpointRule
end AmplificationCovarianceInput

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AmplificationCovarianceMarginal
attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem amplificationMarginal_aut_map (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (B B' : Finset V) (hB : ∀ x, x ∈ B ↔ a x ∈ B')
    (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) (ω : Set E) :
    q.amplificationMarginal Q' B' (a x) k n (finiteVertexEquiv a B B' hB z) p (edgeFieldEquiv b ω) =
      q.amplificationMarginal Q B x k n z p ω := by
  unfold amplificationMarginal
  rw [restrictFiniteField_aut_map b Q Q' hQ]
  apply finiteRootLoad_aut_map
  intro s
  apply finiteChoiceForwardLoad_aut_map G hab x k Q Q' hQ (finiteRunEquiv a B B' hB k)
  · intro r s
    exact (q.amplificationInputs_aut_map_iff o hab Q Q' hQ B B' hB x k n z r s).symm
  · intro r s i
    exact amplificationVertices_aut_map a B B' hB k z r i
  · intro s r
    exact q.amplificationWeight_aut_map hab B B' hB k z s r

end LocalEndpointRule

theorem mem_incidentSupport_aut_iff (G : BondGraph V E) (hloc : LocallyFinite G)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (B B' : Finset V)
    (hB : ∀ x, x ∈ B ↔ a x ∈ B') (e : E) :
    b e ∈ incidentSupport G hloc B' ↔ e ∈ incidentSupport G hloc B := by
  rw [finset_aut_eq_map a B B' hB,incidentSupport_aut G hloc hab]
  simp only [Finset.mem_map_equiv,Equiv.symm_apply_apply]

theorem finiteBall_aut_iff (G : BondGraph V E) (hloc : LocallyFinite G)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x y : V) (R : ℕ) :
    y ∈ (finite_reachBall hloc x R).toFinset ↔ a y ∈ (finite_reachBall hloc (a x) R).toFinset := by
  simpa only [Set.Finite.mem_toFinset] using (mem_reachBall_aut_iff G hab x y R).symm

theorem localBondBall_aut_iff (G : BondGraph V E) (hloc : LocallyFinite G)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) (R : ℕ) (e : E) :
    e ∈ incidentSupport G hloc (finite_reachBall hloc x R).toFinset ↔
      b e ∈ incidentSupport G hloc (finite_reachBall hloc (a x) R).toFinset :=
  (mem_incidentSupport_aut_iff G hloc hab _ _ (fun y => finiteBall_aut_iff G hloc hab x y R) e).symm

end AmplificationCovarianceMarginal

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section CanonicalAmplificationLoad
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

def amplificationRadius (q : LocalEndpointRule G hloc O M L) (k n : ℕ) : ℕ :=
  2*n+k*M+max q.radius M

noncomputable def amplificationBall (_q : LocalEndpointRule G hloc O M L) (k n : ℕ) (x : V) : Finset V :=
  (finite_reachBall hloc x (2*n+k*M)).toFinset

noncomputable def amplificationBonds (q : LocalEndpointRule G hloc O M L) (k n : ℕ) (x : V) : Finset E :=
  incidentSupport G hloc (finite_reachBall hloc x (q.amplificationRadius k n)).toFinset

 

noncomputable def amplifiedMass (q : LocalEndpointRule G hloc O M L) (k n : ℕ) (p : unitInterval)
    (ω : Set E) (x z : V) : ℝ :=
  if hz : z ∈ q.amplificationBall k n x then
    q.amplificationMarginal (q.amplificationBonds k n x) (q.amplificationBall k n x) x k n ⟨z,hz⟩ p ω / n
  else 0

theorem amplifiedMass_nonneg (q : LocalEndpointRule G hloc O M L) (hL : 1 ≤ L)
    (k n : ℕ) (p : unitInterval) (ω : Set E) (x z : V) : 0 ≤ q.amplifiedMass k n p ω x z := by
  unfold amplifiedMass
  split_ifs
  · exact div_nonneg (q.amplificationMarginal_bounds hL _ _ _ _ _ _ _ _).1 (Nat.cast_nonneg _)
  · exact le_rfl

theorem amplifiedMass_support (q : LocalEndpointRule G hloc O M L)
    (k n : ℕ) (p : unitInterval) (ω : Set E) (x z : V) (h : q.amplifiedMass k n p ω x z ≠ 0) :
    x ∈ O ∧ z ∈ O ∧ Conn G ω x z ∧ (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ 2*n+k*M := by
  unfold amplifiedMass at h
  split_ifs at h with hz
  · apply q.amplificationMarginal_physical_support (q.amplificationBonds k n x) (q.amplificationBall k n x) x k n ⟨z,hz⟩ p ω
    · exact incidentSupport_ball_mono G hloc x (Nat.le_add_right (2*n+k*M) (max q.radius M))
    · intro he
      exact h (by rw [he,zero_div])
  · exact (h rfl).elim

theorem amplifiedMass_local (q : LocalEndpointRule G hloc O M L)
    (k n : ℕ) (p : unitInterval) (ω : Set E) (x z : V) :
    q.amplifiedMass k n p ω x z =
      q.amplifiedMass k n p (ω ∩ (q.amplificationBonds k n x : Set E)) x z := by
  unfold amplifiedMass
  split_ifs
  · exact congrArg (fun t : ℝ => t / n) (q.amplificationMarginal_local _ _ _ _ _ _ _ _)
  · rfl

theorem amplifiedMass_aut_map (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (k n : ℕ) (p : unitInterval)
    (ω : Set E) (x z : V) :
    q.amplifiedMass k n p (edgeFieldEquiv b ω) (a x) (a z) = q.amplifiedMass k n p ω x z := by
  have hB (y : V) : y ∈ q.amplificationBall k n x ↔ a y ∈ q.amplificationBall k n (a x) :=
    finiteBall_aut_iff G hloc hab x y (2*n+k*M)
  have hQ (e : E) : e ∈ q.amplificationBonds k n x ↔ b e ∈ q.amplificationBonds k n (a x) :=
    localBondBall_aut_iff G hloc hab x (q.amplificationRadius k n) e
  unfold amplifiedMass
  by_cases hz : z ∈ q.amplificationBall k n x
  · simp only [dite_eq_left hz,dite_eq_left ((hB z).mp hz)]
    exact congrArg (fun t : ℝ => t / n)
      (q.amplificationMarginal_aut_map o hab _ _ hQ _ _ hB x k n ⟨z,hz⟩ p ω)
  · simp only [dite_eq_right hz,dite_eq_right (mt (hB z).mpr hz)]

 

noncomputable def amplificationLoad (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (hL : 1 ≤ L) (k n : ℕ) (p : unitInterval) :
    CappedLocalLoad G hloc (vertexOrbit G o) (2*n+k*M) where
  mass := q.amplifiedMass k n p
  radius := q.amplificationRadius k n
  nonneg := q.amplifiedMass_nonneg hL k n p
  support := q.amplifiedMass_support k n p
  locality := q.amplifiedMass_local k n p
  covariance := by
    intro a b hab ω x z
    simpa only [Equiv.symm_apply_apply,edgeFieldEquiv_apply,Equiv.symm_symm] using
      q.amplifiedMass_aut_map o (isAut_symm G hab) k n p ω (a x) (a z)

end LocalEndpointRule
end CanonicalAmplificationLoad

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section CanonicalAmplificationRow
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem amplificationBonds_query {O : Set V} (q : LocalEndpointRule G hloc O M L)
    (k n : ℕ) (x a : V) (ha : a ∈ q.amplificationBall k n x) :
    incidentSupport G hloc (finite_reachBall hloc a (max q.radius M)).toFinset ⊆
      q.amplificationBonds k n x := by
  apply incidentSupport_mono
  intro y hy
  simp only [Set.Finite.mem_toFinset] at hy ⊢
  exact reachBall_triangle G x a (2*n+k*M) (max q.radius M)
    (by simpa only [amplificationBall,Set.Finite.mem_toFinset] using ha) hy

theorem amplificationBonds_root {O : Set V} (q : LocalEndpointRule G hloc O M L)
    (k n : ℕ) (x : V) :
    incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset ⊆
      q.amplificationBonds k n x := by
  apply incidentSupport_ball_mono
  unfold amplificationRadius
  omega

theorem amplificationLoad_row (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (hL : 1 ≤ L) (k n : ℕ) (p : unitInterval) (ω : Set E) (x : V) :
    (q.amplificationLoad o hL k n p).row ω x =
      q.amplificationRow (q.amplificationBonds k n x) (q.amplificationBall k n x) x k n p ω / n := by
  change (∑' z, q.amplifiedMass k n p ω x z) = _
  rw [tsum_eq_sum (s := q.amplificationBall k n x) (fun z hz => by
    simp only [amplifiedMass,dite_eq_right hz])]
  rw [← Finset.sum_coe_sort]
  simp only [amplifiedMass,dite_eq_left (Subtype.prop _)]
  exact (Finset.sum_div _ _ _).symm

theorem amplificationRow_local {O : Set V} (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : Set E) :
    q.amplificationRow Q B x k n p ω = q.amplificationRow Q B x k n p (ω ∩ (Q : Set E)) := by
  unfold amplificationRow
  apply Finset.sum_congr rfl
  intro z _
  exact q.amplificationMarginal_local Q B x k n z p ω

theorem amplificationLoad_mean_finite (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (hL : 1 ≤ L) (k n : ℕ) (p : unitInterval) (x : V) :
    (∫ ω, (q.amplificationLoad o hL k n p).row ω x ∂law p) =
      finiteFieldIntegral (q.amplificationBonds k n x) p
        (q.amplificationRow (q.amplificationBonds k n x) (q.amplificationBall k n x) x k n p) / n := by
  simp_rw [q.amplificationLoad_row o hL k n p]
  rw [integral_div]
  congr 1
  exact integral_finite_local _ p _ (q.amplificationRow_local _ _ x k n p)

theorem amplificationLoad_second_moment_finite (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (hL : 1 ≤ L) (k n : ℕ) (p : unitInterval) (x : V) :
    (∫ ω, (q.amplificationLoad o hL k n p).row ω x ^ 2 ∂law p) =
      finiteFieldIntegral (q.amplificationBonds k n x) p (fun ω =>
        q.amplificationRow (q.amplificationBonds k n x) (q.amplificationBall k n x) x k n p ω ^ 2) / (n:ℝ)^2 := by
  simp_rw [q.amplificationLoad_row o hL k n p,div_pow]
  rw [integral_div]
  congr 1
  exact integral_finite_local _ p _ (fun ω => congrArg (·^2) (q.amplificationRow_local _ _ x k n p ω))

end LocalEndpointRule
end CanonicalAmplificationRow

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section NormalizedAmplificationMoment
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem amplificationLoad_second_moment_le [Nonempty E] (hconn : Connected G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (p : unitInterval) (x : V) (k n d : ℕ) (hn : 0 < n)
    (hdeg : ∀ a, degree G a ≤ d) :
    (∫ ω, (q.amplificationLoad (root i₀) hL k n p).row ω x ^ 2 ∂law p) ≤
      (4 * q.successProbability p (root i₀)^k +
        (((k*M)+(k*M)^2+d*(k*M)^3:ℕ):ℝ) * inverseCodeMass M L^k / n) *
          (∫ ω, (q.amplificationLoad (root i₀) hL k n p).row ω x ∂law p) +
      (2 * (c*((k*M:ℕ)*q.successProbability p (root i₀)^k)))^2 *
        finiteClusterWindowMass G (q.amplificationBonds k n x) p x (n-k*M) (2*n) := by
  rw [q.amplificationLoad_second_moment_finite,q.amplificationLoad_mean_finite]
  have h := q.amplificationRow_second_moment_le hconn root weight Γ hΓ htr hcov hw hw1 c hc hmin
    i₀ hw₀ hL (q.amplificationBonds k n x) (q.amplificationBall k n x) p x k n d hdeg
    (fun a ha => q.amplificationBonds_query k n x a ha)
  have hn' : (n:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  apply (div_le_div_of_nonneg_right h (sq_nonneg (n:ℝ))).trans_eq
  push_cast
  field_simp

end LocalEndpointRule
end NormalizedAmplificationMoment

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FinitePathExhaustion
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finitePathTest (B : Finset V) (K : V → V → ℝ) (F : V → ℝ) (k : ℕ) (z : ↥B) : ℝ :=
  ∑ r : Fin k → ↥B, oldRunWeight (fun _ a b => K a.val b.val) k z r * F (oldRunVertices k z r 0).val

@[simp] theorem finitePathTest_zero (B : Finset V) (K : V → V → ℝ) (F : V → ℝ) (z : ↥B) :
    finitePathTest B K F 0 z = F z.val := by
  simp [finitePathTest,oldRunWeight,oldRunVertices]

theorem finitePathTest_succ (B : Finset V) (K : V → V → ℝ) (F : V → ℝ) (k : ℕ) (z : ↥B) :
    finitePathTest B K F (k+1) z = ∑ a : ↥B, K z.val a.val * finitePathTest B K F k a :=
  oldRun_test_succ (fun _ (a b : ↥B) => K a.val b.val) (fun (a : ↥B) => F a.val) k z

 

theorem finitePathTest_support (G : BondGraph V E) (B : Finset V) (K : V → V → ℝ) (F : V → ℝ)
    (O : Set V) (x : V) (R M : ℕ)
    (hK : ∀ a b, K a b ≠ 0 → a ∈ O ∧ a ∈ reachBall G b M)
    (hF : ∀ a, F a ≠ 0 → a ∈ O ∧ a ∈ reachBall G x R)
    (k : ℕ) (z : ↥B) (hz : finitePathTest B K F k z ≠ 0) :
    z.val ∈ O ∧ z.val ∈ reachBall G x (R+k*M) := by
  induction k generalizing z with
  | zero => simpa using hF z.val (by simpa using hz)
  | succ k ih =>
    rw [finitePathTest_succ] at hz
    obtain ⟨a,_,ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
    have hh := mul_ne_zero_iff.mp ha
    obtain ⟨haO,haB⟩ := ih a hh.2
    obtain ⟨hzO,hzB⟩ := hK z.val a.val hh.1
    refine ⟨hzO,?_⟩
    have hg := reachBall_triangle G x a.val (R+k*M) M haB hzB
    simpa only [Nat.add_mul,one_mul,Nat.add_assoc] using hg

 

theorem finitePathTest_total (G : BondGraph V E) (B : Finset V) (K : V → V → ℝ) (F : V → ℝ)
    (O : Set V) (x : V) (R M N : ℕ) (u : ℝ)
    (hK : ∀ a b, K a b ≠ 0 → a ∈ O ∧ a ∈ reachBall G b M)
    (hF : ∀ a, F a ≠ 0 → a ∈ O ∧ a ∈ reachBall G x R)
    (hcolumn : ∀ j < N, ∀ a : ↥B, a.val ∈ O → a.val ∈ reachBall G x (R+j*M) →
      ∑ z : ↥B, K z.val a.val = u) :
    ∀ j ≤ N, (∑ z : ↥B, finitePathTest B K F j z) = u^j * ∑ z : ↥B, F z.val := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    simp_rw [finitePathTest_succ]
    rw [Finset.sum_comm]
    have he : (∑ a : ↥B, ∑ z : ↥B, K z.val a.val * finitePathTest B K F j a) =
        u * ∑ a : ↥B, finitePathTest B K F j a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_mul]
      by_cases ha : finitePathTest B K F j a = 0
      · simp only [ha,mul_zero]
      · obtain ⟨haO,haB⟩ := finitePathTest_support G B K F O x R M hK hF j a ha
        rw [hcolumn j (by omega) a haO haB]
    rw [he,ih (by omega)]
    ring

end FinitePathExhaustion

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section AmplificationBoundaryExhaustion
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem kernel_range_support {O : Set V} (q : LocalEndpointRule G hloc O M L)
    (p : unitInterval) (a b : V) (h : q.kernel p a b ≠ 0) : a ∈ O ∧ a ∈ reachBall G b M := by
  constructor
  · by_contra ha
    exact h (q.kernel_zero_of_start_not_mem p a b ha)
  · by_contra ha
    exact h (q.kernel_outside_reverse_ball_zero p a b ha)

theorem orbitBinConnection_range_support (o : V) (p : unitInterval) (n : ℕ) (x a : V)
    (h : orbitBinConnection G p o n x a ≠ 0) :
    a ∈ vertexOrbit G o ∧ a ∈ reachBall G x (2*n) := by
  have ha : a ∈ vertexOrbit G o := by
    by_contra ha
    exact h (by simp only [orbitBinConnection,ha,and_false,ite_false])
  refine ⟨ha,?_⟩
  by_contra hb
  exact h (by simp only [orbitBinConnection,binConnection_outside G p n x a hb,ite_self])

theorem amplificationBall_column {O : Set V} (q : LocalEndpointRule G hloc O M L)
    (p : unitInterval) (k n j : ℕ) (hj : j < k) (x a : V)
    (ha : a ∈ reachBall G x (2*n+j*M)) :
    (∑ z : ↥(q.amplificationBall k n x), q.kernel p z.val a) = ∑' z, q.kernel p z a := by
  rw [Finset.sum_coe_sort (q.amplificationBall k n x) (fun z => q.kernel p z a)]
  symm
  apply tsum_eq_sum
  intro z hz
  apply q.kernel_outside_reverse_ball_zero
  intro hza
  have hh := reachBall_triangle G x a (2*n+j*M) M ha hza
  have hle : (2*n+j*M)+M ≤ 2*n+k*M := by
    calc
      _ = 2*n+(j+1)*M := by ring
      _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right M (by omega)) _
  exact hz (by
    simpa only [amplificationBall,Set.Finite.mem_toFinset] using (reachBall_mono G x hle hh))

theorem amplificationPath_total {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L)
    (p : unitInterval) (k n : ℕ) (x : V) (hx : x ∈ vertexOrbit G (root i₀)) :
    (∑ z : ↥(q.amplificationBall k n x),
      finitePathTest (q.amplificationBall k n x) (q.kernel p) (orbitBinConnection G p (root i₀) n x) k z) =
      q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n := by
  have ht := finitePathTest_total G (q.amplificationBall k n x) (q.kernel p)
    (orbitBinConnection G p (root i₀) n x) (vertexOrbit G (root i₀)) x (2*n) M k
    (q.successProbability p (root i₀)) (q.kernel_range_support p)
    (orbitBinConnection_range_support (root i₀) p n x) (by
      intro j hj a haO haB
      rw [q.amplificationBall_column p k n j hj x a.val haB]
      exact q.kernel_column_eq_success root weight Γ htr hΓ hw i₀ hw₀ p a.val haO) k le_rfl
  rw [ht]
  congr 1
  rw [Finset.sum_coe_sort (q.amplificationBall k n x) (orbitBinConnection G p (root i₀) n x),← orbitBinConnection_row G hloc p (root i₀) n x hx]
  symm
  apply tsum_eq_sum
  intro z hz
  by_contra h
  have hb := (orbitBinConnection_range_support (root i₀) p n x z h).2
  exact hz (by
    simpa only [amplificationBall,Set.Finite.mem_toFinset] using
      reachBall_mono G x (Nat.le_add_right (2*n) (k*M)) hb)

end LocalEndpointRule
end AmplificationBoundaryExhaustion

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section AmplificationExactMean
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem amplificationMarginal_mean_pathTest [Nonempty E] (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval)
    (hx : x ∈ vertexOrbit G o)
    (hroot : incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset ⊆ Q)
    (hquery : ∀ a ∈ B, incidentSupport G hloc (finite_reachBall hloc a q.radius).toFinset ⊆ Q) :
    (∫ ω, q.amplificationMarginal Q B x k n z p ω ∂law p) =
      finitePathTest B (q.kernel p) (orbitBinConnection G p o n x) k z := by
  by_cases hz : z.val ∈ vertexOrbit G o
  · rw [q.amplificationMarginal_mean_kernel Q B x k n z p hx hz hquery]
    unfold finitePathTest
    apply Finset.sum_congr rfl
    intro r _
    rw [finiteBinConnection_eq_binConnection G hloc Q p x n _ hroot]
    by_cases hr : oldRunWeight (fun _ (a b : ↥B) => q.kernel p a.val b.val) k z r = 0
    · simp only [hr,mul_zero,zero_mul]
    · have hy : (oldRunVertices k z r 0).val ∈ vertexOrbit G o :=
        oldRun_endpoint_mem (fun a : ↥B => a.val ∈ vertexOrbit G o)
          (fun _ (a b : ↥B) => q.kernel p a.val b.val)
          (fun _ a b hab => by
            by_contra hb
            exact hab (q.kernel_zero_of_end_not_mem p a.val b.val hb)) k z hz r hr
      rw [orbitBinConnection,ite_eq_left ⟨hx,hy⟩]
      exact mul_comm _ _
  · have hm (ω : Set E) : q.amplificationMarginal Q B x k n z p ω = 0 := by
      by_contra h
      exact hz (q.amplificationMarginal_support Q B x k n z p ω h).2.1
    simp_rw [hm,integral_zero]
    symm
    by_contra h
    exact hz (finitePathTest_support G B (q.kernel p) (orbitBinConnection G p o n x)
      (vertexOrbit G o) x (2*n) M (q.kernel_range_support p)
      (orbitBinConnection_range_support o p n x) k z h).1

 

theorem amplificationLoad_mean [Nonempty E] {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (p : unitInterval) (k n : ℕ) (x : V) (hx : x ∈ vertexOrbit G (root i₀)) :
    (∫ ω, (q.amplificationLoad (root i₀) hL k n p).row ω x ∂law p) =
      q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n / n := by
  simp_rw [q.amplificationLoad_row]
  rw [integral_div]
  congr 1
  unfold amplificationRow
  rw [integral_finsetSum _ (fun z _ => integrable_finite_local _ p _
    (q.amplificationMarginal_local _ _ x k n z p))]
  simp_rw [q.amplificationMarginal_mean_pathTest (root i₀) _ _ x k n _ p hx
    (q.amplificationBonds_root k n x) (fun a ha =>
      (incidentSupport_ball_mono G hloc a (le_max_left _ _)).trans (q.amplificationBonds_query k n x a ha))]
  exact q.amplificationPath_total root weight Γ htr hΓ hw i₀ hw₀ p k n x hx

end LocalEndpointRule
end AmplificationExactMean

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section AmplificationLoadOperator
attribute [local instance] Classical.propDecidable Classical.decEq
namespace CappedLocalLoad
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ}

noncomputable def kernel (q : CappedLocalLoad G hloc O M) (p : unitInterval) (x y : V) : ℝ :=
  ∫ ω, q.mass ω x y ∂law p

theorem kernel_nonneg (q : CappedLocalLoad G hloc O M) (p : unitInterval) (x y : V) :
    0 ≤ q.kernel p x y := integral_nonneg (q.nonneg · x y)

end CappedLocalLoad

 
theorem exists_operator_of_scaled_matrix (F : V → V → ℝ) (c C : ℝ) (hc : 0 < c)
    (A : Hilbert V →L[ℂ] Hilbert V) (hAnorm : ‖A‖ ≤ C)
    (hA : ∀ x y, matrixCoeff A x y = (c * F x y : ℂ)) :
    ∃ T : Hilbert V →L[ℂ] Hilbert V, ‖T‖ ≤ C/c ∧
      ∀ x y, matrixCoeff T x y = (F x y : ℂ) := by
  refine ⟨((c⁻¹:ℝ):ℂ) • A,?_,?_⟩
  · rw [norm_smul,Complex.norm_of_nonneg (inv_nonneg.mpr hc.le)]
    simpa only [div_eq_mul_inv,mul_comm] using
      mul_le_mul_of_nonneg_left hAnorm (inv_nonneg.mpr hc.le)
  · intro x y
    change ((c⁻¹:ℝ):ℂ)*matrixCoeff A x y = _
    rw [hA]
    have hc' : (c:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    simp only [Complex.ofReal_inv]
    field_simp

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem amplificationLoad_scaled_kernel [Nonempty E] (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (hL : 1 ≤ L)
    (k n : ℕ) (hn : 0 < n) (p : unitInterval) (x z : V)
    (hz : z ∈ q.amplificationBall k n x) :
    (n:ℝ) * (q.amplificationLoad o hL k n p).kernel p x z =
      ∫ ω, q.amplificationMarginal (q.amplificationBonds k n x) (q.amplificationBall k n x)
        x k n ⟨z,hz⟩ p ω ∂law p := by
  change (n:ℝ) * (∫ ω, q.amplifiedMass k n p ω x z ∂law p) = _
  simp only [amplifiedMass,dite_eq_left hz,integral_div]
  have hn' : (n:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  field_simp

 

theorem amplificationLoad_exists_operator [Nonempty E] (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (hL : 1 ≤ L)
    (k n : ℕ) (hn : 0 < n) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ a b, matrixCoeff A a b = (q.kernel p a b : ℂ)) :
    ∃ T : Hilbert V →L[ℂ] Hilbert V, ‖T‖ ≤ binOrbitRow G p o n * ‖A‖^k / n ∧
      ∀ x z, matrixCoeff T x z = ((q.amplificationLoad o hL k n p).kernel p x z : ℂ) := by
  let F := (q.amplificationLoad o hL k n p).kernel p
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hposA : PositiveRealMatrix A := fun x z => by
    rw [hA]
    exact ⟨rfl,q.kernel_nonneg p x z⟩
  obtain ⟨S,hSnorm,hS⟩ := exists_operator_of_amplification_domination G hloc p o n k A hposA
    (fun x z => (n:ℝ)*F x z) (fun x z => mul_nonneg hn'.le ((q.amplificationLoad o hL k n p).kernel_nonneg p x z))
    (by
      intro H hH x z
      have hposH : PositiveRealMatrix H := fun a b => by
        rw [hH]
        exact ⟨rfl,orbitBinConnection_nonneg G p o n a b⟩
      have hpos := (((hposA.pow k).mul hposH) z x).2
      by_cases hz : z ∈ q.amplificationBall k n x
      · rw [q.amplificationLoad_scaled_kernel o hL k n hn p x z hz]
        by_cases ho : x ∈ vertexOrbit G o ∧ z ∈ vertexOrbit G o
        · exact q.amplificationMarginal_operator_le o _ _ x k n ⟨z,hz⟩ p ho.1 ho.2
            (q.amplificationBonds_root k n x) (fun a ha =>
              (incidentSupport_ball_mono G hloc a (le_max_left _ _)).trans (q.amplificationBonds_query k n x a ha)) A H hA hH
        · have hm (ω : Set E) : q.amplificationMarginal (q.amplificationBonds k n x)
              (q.amplificationBall k n x) x k n ⟨z,hz⟩ p ω = 0 := by
            by_contra h
            have hs := q.amplificationMarginal_support _ _ x k n ⟨z,hz⟩ p ω h
            exact ho ⟨hs.1,hs.2.1⟩
          simpa only [hm,integral_zero] using hpos
      · have he : F x z = 0 := by
          change (∫ ω, q.amplifiedMass k n p ω x z ∂law p) = 0
          simp only [amplifiedMass,dite_eq_right hz,integral_zero]
        simpa only [he,mul_zero] using hpos)
  exact exists_operator_of_scaled_matrix F n _ hn' S hSnorm (by
    intro x z
    simpa only [Complex.ofReal_mul] using hS x z)

end LocalEndpointRule
end AmplificationLoadOperator

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section TruncationOperator
attribute [local instance] Classical.propDecidable Classical.decEq
namespace CappedLocalLoad
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ}

theorem truncate_kernel_le (q : CappedLocalLoad G hloc O M) (p : unitInterval)
    (b : ℝ) (hb : 0 < b) (L : ℝ) (x y : V) :
    (q.truncate b hb L).kernel p x y ≤ b⁻¹ * q.kernel p x y := by
  rw [kernel,← integral_const_mul]
  exact integral_mono ((q.truncate b hb L).integrable_mass p x y)
    ((q.integrable_mass p x y).const_mul b⁻¹) (q.truncate_mass_le b hb L · x y)

 

theorem truncate_exists_operator (q : CappedLocalLoad G hloc O M) (p : unitInterval)
    (b : ℝ) (hb : 0 < b) (L : ℝ)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.kernel p x y : ℂ)) :
    ∃ T : Hilbert V →L[ℂ] Hilbert V, ‖T‖ ≤ ‖A‖/b ∧
      ∀ x y, matrixCoeff T x y = ((q.truncate b hb L).kernel p x y : ℂ) := by
  have hscale (x y : V) : matrixCoeff (((b⁻¹:ℝ):ℂ) • A) x y = (b⁻¹ * q.kernel p x y : ℝ) := by
    change ((b⁻¹:ℝ):ℂ)*matrixCoeff A x y = _
    rw [hA,Complex.ofReal_mul]
  obtain ⟨T,hT,hK⟩ := exists_operator_of_matrix_domination
    (fun x y => b⁻¹ * q.kernel p x y) ((q.truncate b hb L).kernel p)
    (fun x y => mul_nonneg (inv_nonneg.mpr hb.le) (q.kernel_nonneg p x y))
    (fun x y => by
      rw [abs_of_nonneg ((q.truncate b hb L).kernel_nonneg p x y)]
      exact q.truncate_kernel_le p b hb L x y)
    (((b⁻¹:ℝ):ℂ) • A) hscale
  refine ⟨T,hT.trans_eq ?_,hK⟩
  rw [norm_smul,Complex.norm_of_nonneg (inv_nonneg.mpr hb.le)]
  ring

end CappedLocalLoad
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

 
theorem normalize_mass_operator (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (hu : 0 < q.successProbability p o)
    (A : Hilbert V →L[ℂ] Hilbert V) (C : ℝ) (hAnorm : ‖A‖ ≤ C)
    (hA : ∀ x y, matrixCoeff A x y = (q.kernel p x y : ℂ)) :
    ∃ T : Hilbert V →L[ℂ] Hilbert V, ‖T‖ ≤ C/q.successProbability p o ∧
      ∀ x y, matrixCoeff T x y = (q.normalizedKernel o p x y : ℂ) := by
  apply exists_operator_of_scaled_matrix (q.normalizedKernel o p) (q.successProbability p o) C hu A hAnorm
  intro x y
  rw [hA]
  simp only [normalizedKernel,← Complex.ofReal_mul]
  congr 1
  rw [← mul_assoc,mul_inv_cancel₀ hu.ne',one_mul]

 

theorem mass_operator_of_normalized (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (hu : 0 < q.successProbability p o)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ)) :
    ∃ T : Hilbert V →L[ℂ] Hilbert V, ‖T‖ = q.successProbability p o * ‖A‖ ∧
      ∀ x y, matrixCoeff T x y = (q.kernel p x y : ℂ) := by
  refine ⟨(q.successProbability p o : ℂ) • A,?_,?_⟩
  · rw [norm_smul,Complex.norm_of_nonneg hu.le]
  · intro x y
    change (q.successProbability p o : ℂ)*matrixCoeff A x y = _
    rw [hA]
    simp only [normalizedKernel,← Complex.ofReal_mul]
    congr 1
    rw [← mul_assoc,mul_inv_cancel₀ hu.ne',one_mul]

end LocalEndpointRule
end TruncationOperator

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section AmplificationTruncationStep
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem normalized_operator_norm_pos (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (hu : 0 < q.successProbability p o)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ)) : 0 < ‖A‖ := by
  apply norm_pos_iff.mpr
  intro ha
  have hz (y : V) : q.kernel p o y = 0 := by
    have he := hA o y
    rw [ha] at he
    have he' : (q.successProbability p o)⁻¹ * q.kernel p o y = 0 :=
      Complex.ofReal_eq_zero.mp he.symm
    exact (mul_eq_zero.mp he').resolve_left (inv_ne_zero hu.ne')
  have he : q.successProbability p o = 0 := by
    simp only [successProbability,hz,tsum_zero]
  exact hu.ne' he

 

theorem amplification_truncation_step [Nonempty E] {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (p : unitInterval) (k n : ℕ) (hn : 0 < n)
    (hu : 0 < q.successProbability p (root i₀))
    (hbin : 0 < binOrbitRow G p (root i₀) n)
    (b L' : ℝ) (hb : 0 < b)
    (hmoment : (∫ ω, (q.amplificationLoad (root i₀) hL k n p).row ω (root i₀)^2 ∂law p) / b ≤
      (q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n / n)/4)
    (hbad : b * (law p).real {ω | CappedBadGoodness G ω (root i₀) (2*n+k*M) L'} ≤
      (q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n / n)/4)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel (root i₀) p x y : ℂ)) :
    ∃ q' : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) (2*n+k*M) L',
      (q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n / n)/(2*b) ≤
        q'.successProbability p (root i₀) ∧
      ∃ A' : Hilbert V →L[ℂ] Hilbert V, 0 < ‖A'‖ ∧ ‖A'‖ ≤ 2*‖A‖^k ∧
        ∀ x y, matrixCoeff A' x y = (q'.normalizedKernel (root i₀) p x y : ℂ) := by
  let load := q.amplificationLoad (root i₀) hL k n p
  let q' := load.truncate b hb L'
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hb₀ : 0 < q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n / n :=
    div_pos (mul_pos (pow_pos hu _) hbin) hn'
  have hself : root i₀ ∈ vertexOrbit G (root i₀) := by
    refine ⟨Equiv.refl V,Equiv.refl E,?_,rfl⟩
    intro e
    simp
  have hmean := q.amplificationLoad_mean root weight Γ htr hΓ hw i₀ hw₀ hL p k n (root i₀) hself
  have hnew := load.truncate_success_lower p b hb L' (root i₀) _ hmean.ge hmoment hbad
  have hu' : 0 < q'.successProbability p (root i₀) :=
    (div_pos hb₀ (mul_pos (by norm_num) hb)).trans_le hnew
  obtain ⟨B,hBnorm,hB⟩ := q.mass_operator_of_normalized (root i₀) p hu A hA
  obtain ⟨C,hCnorm,hC⟩ := q.amplificationLoad_exists_operator (root i₀) hL k n hn p B hB
  obtain ⟨D,hDnorm,hD⟩ := load.truncate_exists_operator p b hb L' C hC
  have hD' : ‖D‖ ≤ (binOrbitRow G p (root i₀) n * (q.successProbability p (root i₀)*‖A‖)^k/n)/b := by
    rw [hBnorm] at hCnorm
    exact hDnorm.trans (div_le_div_of_nonneg_right hCnorm hb.le)
  obtain ⟨A',hA'norm,hA'⟩ := q'.normalize_mass_operator (root i₀) p hu' D _ hD' hD
  refine ⟨q',hnew,A',q'.normalized_operator_norm_pos (root i₀) p hu' A' hA',hA'norm.trans ?_,hA'⟩
  apply (div_le_iff₀ hu').mpr
  apply (div_le_iff₀ hb).mpr
  apply (div_le_iff₀ hn').mpr
  have hret := (div_le_iff₀ (mul_pos (show (0:ℝ)<2 by norm_num) hb)).mp hnew
  have hret' := (div_le_iff₀ hn').mp hret
  rw [mul_pow]
  calc
    _ = (q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n) * ‖A‖^k := by ring
    _ ≤ (q'.successProbability p (root i₀)*(2*b)*n)*‖A‖^k :=
      mul_le_mul_of_nonneg_right hret' (pow_nonneg (norm_nonneg _) _)
    _ = _ := by ring

end LocalEndpointRule
end AmplificationTruncationStep

end Percolation

end OAI
