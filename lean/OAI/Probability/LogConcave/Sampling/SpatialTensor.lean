import Mathlib
import OAI.Probability.LogConcave.JetEstimates.TensorExpression

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

universe u

def spatialTensor {d : ℕ} {S K : Type u} (F : (S → Fin d) → Point d → ℝ)
    (l : List K) (y : Point d) (c : K ⊕ S → Fin d) : ℝ :=
  JetCalculus.jet (fun k => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl k))) l
    (F (fun s => c (Sum.inr s))) y

lemma fullList_perm {K : Type u} [Fintype K] {l m : List K}
    (hl : l.Nodup) (hm : m.Nodup) (hal : ∀k,k∈l) (ham : ∀k,k∈m) : l.Perm m := by
  apply (List.perm_ext_iff_of_nodup hl hm).mpr
  intro k
  simp only [hal k,ham k]

lemma spatialTensor_relabel {d : ℕ} {S T K J : Type u}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤ : ℕ∞) (F c))
    (e : S ≃ T) (f : K ≃ J) (l : List K) (m : List J)
    (hlm : (l.map f).Perm m) (y : Point d) (c : J ⊕ T → Fin d) :
    spatialTensor F l y (c ∘ (f.sumCongr e))=
      spatialTensor (fun a => F (a ∘ e)) m y c := by
  unfold spatialTensor
  simp only [Function.comp_def,Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr]
  have hh := congrFun (JetCalculus.jet_perm (hF (fun s => c (Sum.inr (e s))))
    (fun j => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl j))) hlm) y
  rw [JetCalculus.jet_map] at hh
  exact hh

lemma spatialTensor_polySmooth {d : ℕ} {S K : Type u}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (l : List K) (c : K ⊕ S → Fin d) : PolySmooth (fun y => spatialTensor F l y c) :=
  (hF _).jet _ l

lemma spatialTensor_allSplit_relabel {d : ℕ} {S T K J : Type u}
    [Fintype S] [Fintype T] [Fintype K] [Fintype J]
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤ : ℕ∞) (F c))
    (e : S ≃ T) (f : K ≃ J) (l : List K) (m : List J)
    (hlm : (l.map f).Perm m) (y : Point d) (B : ℝ)
    (hB : TensorEnergy.AllSplitBound (spatialTensor F l y) B) :
    TensorEnergy.AllSplitBound (spatialTensor (fun a => F (a ∘ e)) m y) B := by
  have hh := hB.reindex (f.sumCongr e)
  simpa only [spatialTensor_relabel F hF e f l m hlm y] using hh

def spatialEnvelope {d : ℕ} {S : Type} [Fintype S]
    (F : (S → Fin d) → Point d → ℝ) (j : ℕ) (y : Point d) : ℝ :=
  TensorEnergy.splitEnvelope (spatialTensor F (List.finRange j) y)

lemma spatialEnvelope_nonneg {d : ℕ} {S : Type} [Fintype S]
    (F : (S → Fin d) → Point d → ℝ) (j : ℕ) (y : Point d) : 0≤ spatialEnvelope F j y :=
  TensorEnergy.splitEnvelope_nonneg _

lemma spatialEnvelope_measurable {d : ℕ} {S : Type} [Fintype S]
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c)) (j : ℕ) :
    Measurable (spatialEnvelope F j) :=
  TensorEnergy.measurable_splitEnvelope _ (fun c =>
    (spatialTensor_polySmooth F hF (List.finRange j) c).smooth.continuous.measurable)

lemma spatialTensor_allSplit_envelope {d : ℕ} {S K : Type} [Fintype S] [Fintype K]
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤ : ℕ∞) (F c))
    (l : List K) (hl : l.Nodup) (hall : ∀k,k∈l) (y : Point d) :
    TensorEnergy.AllSplitBound (spatialTensor F l y) (spatialEnvelope F (Fintype.card K) y) := by
  let e := (Fintype.equivFin K).symm
  have hp : ((List.finRange (Fintype.card K)).map e).Perm l :=
    fullList_perm ((List.nodup_finRange _).map e.injective) hl
      (fun k => by simp only [List.mem_map]; exact ⟨e.symm k,by simp,e.apply_symm_apply k⟩) hall
  have hh := spatialTensor_allSplit_relabel F hF (Equiv.refl S) e
    (List.finRange (Fintype.card K)) l hp y _ (TensorEnergy.allSplitBound_envelope _)
  simpa only [Function.comp_def,Equiv.refl_apply,spatialEnvelope] using hh

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical

universe u

def selectList {K : Type u} (p : K → Prop) [DecidablePred p] : List K → List {k // p k}
  | [] => []
  | k::l => if h : p k then ⟨k,h⟩::selectList p l else selectList p l

lemma map_selectList {K : Type u} (p : K → Prop) [DecidablePred p] (l : List K) :
    (selectList p l).map Subtype.val=l.filter (fun k => decide (p k)) := by
  induction l with
  | nil => rfl
  | cons k l ih => by_cases h:p k <;> simp [selectList,h,ih]

lemma selectList_nodup {K : Type u} (p : K → Prop) [DecidablePred p]
    {l : List K} (hl : l.Nodup) : (selectList p l).Nodup := by
  apply List.Nodup.of_map (f:=Subtype.val)
  rw [map_selectList]
  exact hl.filter _

lemma selectList_full {K : Type u} (p : K → Prop) [DecidablePred p]
    {l : List K} (hall : ∀k,k∈l) : ∀ k : {k // p k}, k∈selectList p l := by
  intro k
  have hh : k.val∈(selectList p l).map Subtype.val := by
    rw [map_selectList]
    simp [hall,k.property]
  obtain ⟨z,hz,hzk⟩ := List.mem_map.mp hh
  have he : z=k := Subtype.ext hzk
  rwa [he] at hz

lemma jet_selectList {d : ℕ} {K : Type u} (p : K → Prop) [DecidablePred p]
    (v : K → Point d) (l : List K) (f : Point d → ℝ) :
    JetCalculus.jet (fun k : {k // p k} => v k.val) (selectList p l) f=
      JetCalculus.jet v (l.filter (fun k => decide (p k))) f := by
  rw [←map_selectList p l,JetCalculus.jet_map]
  rfl

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

lemma conditionalU_map {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ)
    (y u : Point d) (L : ℝ) {S T : Type*} (v : T → Point d) (e : S → T) (l : List S) :
    conditionalU F x r ρ y u L v (l.map e)=conditionalU F x r ρ y u L (v ∘ e) l := by
  unfold conditionalU
  simp only [List.length_map,JetCalculus.jet_map,Function.comp_def]

lemma jointU_map {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    {S T : Type*} (v : T → Point d) (e : S → T) (l : List S) (i : Fin d) :
    jointU F x r L v (l.map e) i=jointU F x r L (v ∘ e) l i := by
  funext p
  exact conditionalU_map F x r p.1 p.2 _ L v e l

namespace TensorAtom
variable {S : Type}

def jetList (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (hne : l≠[]) : TensorAtom (S ⊕ Unit) :=
  match l,hN,hall,hne with
  | [],_,_,he => (he rfl).elim
  | a::l,hN,hall,_ => ⟨l.length+2,.jet l.length,
      lastEquiv (List.Nodup.getEquivOfForallMemList (a::l) hN hall)⟩

lemma jetList_weight (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (hne : l≠[]) :
    (jetList l hN hall hne).expression.weight=l.length-1 := by
  cases l with
  | nil => exact (hne rfl).elim
  | cons a l => rfl

lemma jetList_eval {d : ℕ} (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (hne : l≠[])
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : S ⊕ Unit → Fin d) :
    (jetList l hN hall hne).eval F x r L c=
      fun p => L⁻¹*jointU F x r L (fun s => JetCalculus.spaceBasis d (c (Sum.inl s)))
        l (c (Sum.inr ())) p := by
  cases l with
  | nil => exact (hne rfl).elim
  | cons a l =>
    let e := List.Nodup.getEquivOfForallMemList (a::l) hN hall
    change (fun p => L⁻¹*jointU F x r L
      (fun j : Fin (l.length+1) => JetCalculus.spaceBasis d (c (lastEquiv e j.castSucc)))
      (List.finRange (l.length+1)) (c (lastEquiv e (Fin.last (l.length+1)))) p)=_
    simp only [lastEquiv_castSucc]
    rw [show lastEquiv e (Fin.last (l.length+1))=Sum.inr () from lastEquiv_last e]
    have he : (List.finRange (a::l).length).map e=(a::l) := by
      change (List.finRange (a::l).length).map (a::l).get=(a::l)
      exact List.map_get_finRange (a::l)
    have hh := jointU_map F x r L (fun s => JetCalculus.spaceBasis d (c (Sum.inl s))) e
      (List.finRange (a::l).length) (c (Sum.inr ()))
    rw [he] at hh
    rw [hh]
    rfl

def swapLast : (S ⊕ Unit) ⊕ Unit ≃ (S ⊕ Unit) ⊕ Unit :=
  (Equiv.sumAssoc S Unit Unit).trans ((Equiv.sumCongr (Equiv.refl S) (Equiv.sumComm Unit Unit)).trans
    (Equiv.sumAssoc S Unit Unit).symm)

@[simp] lemma swapLast_left (s : S) : swapLast (Sum.inl (Sum.inl s))=Sum.inl (Sum.inl s) := rfl
@[simp] lemma swapLast_inner : (swapLast (S:=S)) (Sum.inl (Sum.inr ()))=Sum.inr () := rfl
@[simp] lemma swapLast_outer : (swapLast (S:=S)) (Sum.inr ())=Sum.inl (Sum.inr ()) := rfl

def extendedU (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) : TensorAtom ((S ⊕ Unit) ⊕ Unit) :=
  (jetList (Sum.inr ()::l.map Sum.inl) (extra_list_nodup hN)
    (by intro s; cases s <;> simp [hall]) (by simp)).relabel swapLast

lemma extendedU_weight (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) :
    (extendedU l hN hall).expression.weight=l.length := by
  simp only [extendedU,relabel,jetList_weight,List.length_cons,List.length_map,Nat.add_sub_cancel]

lemma extendedU_eval {d : ℕ} (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l)
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : (S ⊕ Unit) ⊕ Unit → Fin d) :
    (extendedU l hN hall).eval F x r L c=fun p => L⁻¹*
      jointU F x r L (Sum.elim (fun s => JetCalculus.spaceBasis d (c (Sum.inl (Sum.inl s))))
        (fun _ : Unit => JetCalculus.spaceBasis d (c (Sum.inr ()))))
        (Sum.inr ()::l.map Sum.inl) (c (Sum.inl (Sum.inr ()))) p := by
  rw [extendedU,relabel_eval,jetList_eval]
  funext p
  congr 2
  funext s
  cases s <;> rfl

end TensorAtom
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

lemma jointU_selectList {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    {S : Type} (v : S → Point d) (l : List S) (P : S → Prop) [DecidablePred P] (i : Fin d) :
    jointU F x r L (fun s : {s // P s} => v s.val) (selectList P l) i=
      jointU F x r L v (l.filter (fun s => decide (P s))) i := by
  rw [←map_selectList P l,jointU_map]
  rfl

lemma selectList_lengths {S : Type} (P : S → Prop) [DecidablePred P] (l : List S) :
    (selectList P l).length+(selectList (fun s => ¬P s) l).length=l.length := by
  induction l with
  | nil => rfl
  | cons s l ih => by_cases hs:P s <;> simp [selectList,hs] <;> omega

namespace TensorAtom
variable {S : Type}

def splitLabels (a : Finset S) : {s // s∈a} ⊕ ({s // s∉a} ⊕ Unit) ≃ S ⊕ Unit :=
  (Equiv.sumAssoc _ _ _).symm.trans (Equiv.sumCongr (Equiv.sumCompl (fun s => s∈a)) (Equiv.refl Unit))

@[simp] lemma splitLabels_left (a : Finset S) (s : {s // s∈a}) :
    splitLabels a (Sum.inl s)=Sum.inl s.val := rfl
@[simp] lemma splitLabels_right (a : Finset S) (s : {s // s∉a}) :
    splitLabels a (Sum.inr (Sum.inl s))=Sum.inl s.val := rfl
@[simp] lemma splitLabels_field (a : Finset S) :
    splitLabels a (Sum.inr (Sum.inr ()))=Sum.inr () := rfl

variable [Fintype S]

def splitProduct (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l)
    (a : Finset S) (ha : a.Nonempty) : TensorAtom (S ⊕ Unit) := by
  letI : Nonempty {s // s∈a} := ⟨⟨ha.choose,ha.choose_spec⟩⟩
  exact ((jetList (selectList (fun s => s∈a) l) (selectList_nodup _ hN)
    (selectList_full _ hall) (by
      intro he
      have hh := selectList_full (fun s => s∈a) hall ⟨ha.choose,ha.choose_spec⟩
      simp [he] at hh)).contract
    (extendedU (selectList (fun s => s∉a) l) (selectList_nodup _ hN)
      (selectList_full _ hall))).relabel (splitLabels a)

lemma splitProduct_weight (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l)
    (a : Finset S) (ha : a.Nonempty) :
    (splitProduct l hN hall a ha).expression.weight=l.length-1 := by
  let : Nonempty {s // s∈a} := ⟨⟨ha.choose,ha.choose_spec⟩⟩
  dsimp only [splitProduct,relabel]
  rw [contract_weight,jetList_weight,extendedU_weight]
  have hp : 0<(selectList (fun s => s∈a) l).length := by
    apply List.length_pos_iff.mpr
    intro he
    have hh := selectList_full (fun s => s∈a) hall ⟨ha.choose,ha.choose_spec⟩
    simp [he] at hh
  have hs := selectList_lengths (fun s => s∈a) l
  omega

lemma splitProduct_eval {d : ℕ} (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l)
    (a : Finset S) (ha : a.Nonempty) (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (c : S ⊕ Unit → Fin d) (p : ℝ × Point d) :
    (splitProduct l hN hall a ha).eval F x r L c p=
      ∑ k : Fin d,(L⁻¹*jointU F x r L (fun s => JetCalculus.spaceBasis d (c (Sum.inl s)))
        (l.filter (fun s => s∈a)) k p)*
      (L⁻¹*jointU F x r L
        (Sum.elim (fun s => JetCalculus.spaceBasis d (c (Sum.inl s)))
          (fun _ : Unit => JetCalculus.spaceBasis d k))
        (Sum.inr ()::(l.filter (fun s => s∉a)).map Sum.inl) (c (Sum.inr ())) p) := by
  let : Nonempty {s // s∈a} := ⟨⟨ha.choose,ha.choose_spec⟩⟩
  dsimp only [splitProduct]
  rw [relabel_eval,contract_eval]
  apply Finset.sum_congr rfl
  intro k _
  rw [jetList_eval,extendedU_eval]
  simp only [Function.comp_apply,Sum.elim_inl,Sum.elim_inr,splitLabels_left,splitLabels_right,splitLabels_field]
  congr 1
  · rw [jointU_selectList F x r L (fun s => JetCalculus.spaceBasis d (c (Sum.inl s))) l (fun s => s∈a) k]
  · have he : (Sum.inr ()::(selectList (fun s => s∉a) l).map Sum.inl).map
        (Sum.map Subtype.val id)=Sum.inr ()::(l.filter (fun s => s∉a)).map Sum.inl := by
      simp only [List.map_cons,Sum.map_inr,id_eq,List.map_map]
      rw [←map_selectList (fun s => s∉a) l,List.map_map]
      rfl
    have hh := jointU_map F x r L
      (Sum.elim (fun s => JetCalculus.spaceBasis d (c (Sum.inl s)))
        (fun _ : Unit => JetCalculus.spaceBasis d k)) (Sum.map Subtype.val id)
      (Sum.inr ()::(selectList (fun s => s∉a) l).map Sum.inl) (c (Sum.inr ()))
    rw [he] at hh
    rw [hh]
    congr 2
    funext s
    cases s <;> rfl

end TensorAtom
end LogConcaveSampling

end

end

end

end OAI
