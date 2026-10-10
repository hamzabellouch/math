import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.HistoryLaw
import OAI.Combinatorics.SharpRamsey.Reciprocal.SourceReciprocalExposure

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section

variable {β C ι : Type} [Fintype β] [Fintype C] [Fintype ι] [DecidableEq ι]

def Law.equiprobable (A : Type) [Fintype A] [Nonempty A] : Law A where
  mass _ := 1/(Fintype.card A:ℝ)
  nonneg _ := by positivity
  total := by simp [ne_of_gt (show (0:ℝ)<Fintype.card A by exact_mod_cast Fintype.card_pos)]

lemma Law.equiprobable_sum (A : Type) [Fintype A] [Nonempty A] (f : A→ℝ) :
    (∑ a,(Law.equiprobable A).mass a*f a)=(∑ a,f a)/Fintype.card A := by
  simp only [Law.equiprobable,one_div,←mul_sum]
  ring

def pasteTuple (S : Finset ι) (z : S→β) (x : (Sᶜ:Finset ι)→β) : ι→β :=
  fun i=>if h : i∈S then z ⟨i,h⟩ else x ⟨i,mem_compl.mpr h⟩

omit [Fintype β] in
lemma pasteTuple_compl (S : Finset ι) (z : S→β) (x : (Sᶜ:Finset ι)→β) (i : (Sᶜ:Finset ι)) :
    pasteTuple S z x i=x i := by simp [pasteTuple,mem_compl.mp i.property]

lemma Law.restore_restrict (p : Law (ι→β)) (S : Finset ι) (f : (ι→β)→ℝ) :
    (∑ z,(p.restrict S).mass z*∑ x,((p.cond (fun y (i:S)=>y i) z).restrict Sᶜ).mass x*
      f (pasteTuple S z x))=∑ y,p.mass y*f y := by
  have h := p.history_sum (fun y (i:S)=>y i) f
  apply Eq.trans _ h
  apply sum_congr rfl
  intro z _
  by_cases hz : (p.restrict S).mass z=0
  · change (p.restrict S).mass z * _=(p.restrict S).mass z * _
    rw [hz,zero_mul,zero_mul]
  · congr 1
    rw [Law.restrict,Law.sum_map]
    apply sum_congr rfl
    intro y _
    by_cases hy : (p.cond (fun y (i:S)=>y i) z).mass y=0
    · simp only [hy,zero_mul]
    · have he := (p.cond_support (fun y (i:S)=>y i) z hz y hy).2
      congr 2
      funext i
      by_cases hi : i∈S
      · simp only [pasteTuple,dite_eq_left hi]
        exact (congrFun he ⟨i,hi⟩).symm
      · simp only [pasteTuple,dite_eq_right hi]

structure ExposureModel (ι β C : Type) [Fintype β] where
  History : Type
  [finiteHistory : Fintype History]
  historyLaw : @Law History finiteHistory
  Index : History→Type
  [finiteIndex : ∀ z,Fintype (Index z)]
  [decIndex : ∀ z,DecidableEq (Index z)]
  tupleLaw : ∀ z,Law (Index z→β)
  remaining : History→ℕ
  embedding : ∀ z,C×Fin (remaining z) ↪ Index z
  owner : ∀ z,Index z→Option C
  origin : ∀ z,Index z↪ι
  restore : ∀ z,(Index z→β)→ι→β
  restore_origin : ∀ z x i,restore z x (origin z i)=x i

attribute [instance] ExposureModel.finiteHistory ExposureModel.finiteIndex ExposureModel.decIndex

namespace ExposureModel
variable (M : ExposureModel ι β C)

def expectation (f : (ι→β)→ℝ) : ℝ :=
  ∑ z,M.historyLaw.mass z*∑ x,(M.tupleLaw z).mass x*f (M.restore z x)

def initial (p : Law (ι→β)) {m : ℕ} (e : C×Fin m↪ι) (own : ι→Option C) :
    ExposureModel ι β C where
  History := Unit
  finiteHistory := inferInstance
  historyLaw := Law.equiprobable Unit
  Index _ := ι
  finiteIndex _ := inferInstance
  decIndex _ := inferInstance
  tupleLaw _ := p
  remaining _ := m
  embedding _ := e
  owner _ := own
  origin _ := Function.Embedding.refl ι
  restore _ := id
  restore_origin _ _ _ := rfl

omit [Fintype C] in
lemma initial_expectation (p : Law (ι→β)) {m : ℕ} (e : C×Fin m↪ι) (own : ι→Option C)
    (f : (ι→β)→ℝ) : (initial p e own).expectation f=∑ y,p.mass y*f y := by
  change (∑ _z : Unit,(1/(Fintype.card Unit:ℝ))*(∑ x,p.mass x*f x))=_
  simp

def join {m : ℕ} (p : Law (ι→β)) (e : C×Fin (m+1)↪ι)
    (child : ∀ f : C→Fin (m+1), (freshRepresentatives e f→β)→
      ExposureModel ↥((freshRepresentatives e f)ᶜ) β C) : ExposureModel ι β C where
  History := Σ f : C→Fin (m+1), Σ z : freshRepresentatives e f→β, (child f z).History
  finiteHistory := inferInstance
  historyLaw := (Law.equiprobable (C→Fin (m+1))).sigma (fun f=>
    (p.restrict (freshRepresentatives e f)).sigma (fun z=>(child f z).historyLaw))
  Index h := (child h.1 h.2.1).Index h.2.2
  finiteIndex _ := inferInstance
  decIndex _ := inferInstance
  tupleLaw h := (child h.1 h.2.1).tupleLaw h.2.2
  remaining h := (child h.1 h.2.1).remaining h.2.2
  embedding h := (child h.1 h.2.1).embedding h.2.2
  owner h := (child h.1 h.2.1).owner h.2.2
  origin h := ((child h.1 h.2.1).origin h.2.2).trans (Function.Embedding.subtype _)
  restore h x := pasteTuple (freshRepresentatives e h.1) h.2.1
    ((child h.1 h.2.1).restore h.2.2 x)
  restore_origin h x i := by
    change pasteTuple (freshRepresentatives e h.1) h.2.1
      ((child h.1 h.2.1).restore h.2.2 x) ((child h.1 h.2.1).origin h.2.2 i).val=x i
    rw [pasteTuple_compl]
    exact (child h.1 h.2.1).restore_origin h.2.2 x i

lemma join_expectation {m : ℕ} (p : Law (ι→β)) (e : C×Fin (m+1)↪ι)
    (child : ∀ f : C→Fin (m+1), (freshRepresentatives e f→β)→
      ExposureModel ↥((freshRepresentatives e f)ᶜ) β C)
    (φ : (ι→β)→ℝ) :
    (join p e child).expectation φ=
      (∑ f : C→Fin (m+1),∑ z,(p.restrict (freshRepresentatives e f)).mass z*
        (child f z).expectation (fun x=>φ (pasteTuple (freshRepresentatives e f) z x)))/
          Fintype.card (C→Fin (m+1)) := by
  unfold expectation
  change (∑ h,((Law.equiprobable (C→Fin (m+1))).sigma (fun f=>
    (p.restrict (freshRepresentatives e f)).sigma (fun z=>(child f z).historyLaw))).mass h*
      ∑ x,((child h.1 h.2.1).tupleLaw h.2.2).mass x*
        φ (pasteTuple (freshRepresentatives e h.1) h.2.1 ((child h.1 h.2.1).restore h.2.2 x)))=_
  rw [Law.sigma_sum]
  simp_rw [Law.sigma_sum]
  exact Law.equiprobable_sum _ _

lemma join_preserves {m : ℕ} (p : Law (ι→β)) (e : C×Fin (m+1)↪ι)
    (child : ∀ f : C→Fin (m+1), (freshRepresentatives e f→β)→
      ExposureModel ↥((freshRepresentatives e f)ᶜ) β C)
    (hchild : ∀ f z φ,(child f z).expectation φ=
      ∑ x,((p.cond (fun y (i:freshRepresentatives e f)=>y i) z).restrict
        (freshRepresentatives e f)ᶜ).mass x*φ x)
    (φ : (ι→β)→ℝ) : (join p e child).expectation φ=∑ y,p.mass y*φ y := by
  rw [join_expectation]
  simp_rw [hchild,p.restore_restrict]
  rw [sum_const,card_univ,nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (ne_of_gt (show (0:ℝ)<Fintype.card (C→Fin (m+1)) by exact_mod_cast Fintype.card_pos))

end ExposureModel
end
end SharpLogRamsey.Selection

end

end OAI
