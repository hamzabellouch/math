import OAI.Computability.TypeSystem.Interface

namespace OAI

namespace PureTypeSystem.OneChildInterpretation

section
universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))

abbrev Bits := Nat → Bool

def extendBit (θ : Bits) (b : Bool) : Bits
  | 0 => b
  | n+1 => θ n

def head : Expr S → Option Nat
  | .var n => some n
  | .app f _ => head f
  | _ => none

/-- Both choices are tested at each binder. Specialization will select the
extreme choice given by the unique internal support path. -/
noncomputable def eval (Γ : List (Expr S)) (A : Expr S) (σ : Nat → Expr S) (θ : Bits) : Set (Expr S) :=
  if Profile P Γ A ∈ C ∧ Ω.profile (A.subst σ) ∈ C then
    match A with
    | .pi D E => RawProduct Ω D E σ (eval Γ D σ θ)
        (fun n b => eval (D :: Γ) E (Expr.extend σ n) (extendBit θ b))
    | A => match head A with
      | none => Top Ω (A.subst σ).normalForm
      | some i => if θ i then Top Ω (A.subst σ).normalForm else Bottom Ω (A.subst σ).normalForm
  else Top Ω (A.subst σ).normalForm

@[simp] theorem head_rename (A : Expr S) (ρ : Nat → Nat) :
    head (A.rename ρ) = (head A).map ρ := by
  induction A with
  | app f n ihf ihn => exact ihf
  | var i => rfl
  | sort s => rfl
  | lam D m ihD ihm => rfl
  | pi D E ihD ihE => rfl

theorem head_subst {A : Expr S} {i : Nat} (hi : head A = some i) (σ : Nat → Expr S) :
    head (A.subst σ) = head (σ i) := by
  induction A with
  | var j => cases hi; rfl
  | app f n ihf ihn => exact ihf hi
  | sort s => cases hi
  | pi D E ihD ihE => cases hi
  | lam D m ihD ihm => cases hi

theorem head_beta {A B : Expr S} {i : Nat} (hi : head A = some i) (hr : Beta A B) :
    head B = some i := by
  induction hr with
  | head D m n => cases hi
  | app_left hr ih => exact ih hi
  | app_right hr ih => exact hi
  | lam_domain hr ih => cases hi
  | lam_body hr ih => cases hi
  | pi_domain hr ih => cases hi
  | pi_body hr ih => cases hi

theorem head_reduces {A B : Expr S} {i : Nat} (hi : head A = some i) (hr : Reduces A B) :
    head B = some i := by
  induction hr with
  | refl => exact hi
  | tail hr hs ih => exact head_beta ih hs

theorem head_normalForm {A : Expr S} {i : Nat} (hi : head A = some i) (hw : WeaklyNormalizing A) :
    head A.normalForm = some i := head_reduces hi (Expr.normalForm_spec hw).1

theorem eval_pi (Γ : List (Expr S)) (D E : Expr S) (σ : Nat → Expr S) (θ : Bits) :
    eval Ω C Γ (.pi D E) σ θ =
      if Profile P Γ (.pi D E) ∈ C ∧ Ω.profile ((Expr.pi D E).subst σ) ∈ C then
        RawProduct Ω D E σ (eval Ω C Γ D σ θ)
          (fun n b => eval Ω C (D :: Γ) E (Expr.extend σ n) (extendBit θ b))
      else Top Ω ((Expr.pi D E).subst σ).normalForm := rfl

theorem eval_head {Γ : List (Expr S)} {A : Expr S} {σ : Nat → Expr S} {θ : Bits} {i : Nat}
    (hg : Profile P Γ A ∈ C) (ha : Ω.profile (A.subst σ) ∈ C) (hi : head A = some i) :
    eval Ω C Γ A σ θ = if θ i then Top Ω (A.subst σ).normalForm else Bottom Ω (A.subst σ).normalForm := by
  cases A <;> simp only [eval,ite_eq_left (And.intro hg ha)]
  all_goals first | (cases hi <;> rfl) | (rw [hi])

theorem eval_sort (Γ : List (Expr S)) (s : S) (σ : Nat → Expr S) (θ : Bits) :
    eval Ω C Γ (.sort s) σ θ = Top Ω (.sort s) := by
  simp only [eval,head,ite_self,Expr.subst,Expr.normalForm_of_normal (Normal.sort s)]

variable (hw : SystemWeaklyNormalizing P)
include hw

theorem eval_candidate {Γ : List (Expr S)} {A : Expr S} {s : S}
    {σ : Nat → Expr S} (hA : HasType P Γ A (.sort s)) (hσ : Ω.TypedSubstitution Γ σ) (θ : Bits) :
    IsCandidate Ω (A.subst σ).normalForm (eval Ω C Γ A σ θ) := by
  induction A generalizing Γ s σ θ with
  | pi D E ihD ihE =>
    rw [eval]
    split
    · obtain ⟨a,b,c,hD,hE,_,_⟩ := hA.generation_pi
      have hX := ihD hD hσ θ
      apply rawProduct_candidate hw hA hσ hX
      intro n hn bit
      have hrawD := ContextTower.HasType.subst hD hσ
      have ht := (hX.upper hn).1.conversion hrawD
        (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
      exact ihE hE (hσ.cons ht) (extendBit θ bit)
    · exact top_candidate
  | var i =>
    simp only [eval,head]
    split
    · split <;> first | exact top_candidate | exact bottom_candidate
    · exact top_candidate
  | sort s => simp only [eval,head,ite_self]; exact top_candidate
  | lam D m ihD ihm => simp only [eval,head,ite_self]; exact top_candidate
  | app f n ihf ihn =>
    simp only [eval]
    split
    · cases hh : head (.app f n) with
      | none => exact top_candidate
      | some i =>
        change IsCandidate Ω (Expr.subst σ (.app f n)).normalForm
          (if θ i then Top Ω (Expr.subst σ (.app f n)).normalForm else Bottom Ω (Expr.subst σ (.app f n)).normalForm)
        split <;> first | exact top_candidate | exact bottom_candidate
    · exact top_candidate

omit hw in
theorem eval_outside {Γ : List (Expr S)} {A : Expr S} {σ : Nat → Expr S} {θ : Bits}
    (ho : Profile P Γ A ∉ C ∨ Ω.profile (A.subst σ) ∉ C) :
    eval Ω C Γ A σ θ = Top Ω (A.subst σ).normalForm := by
  have hn : ¬ (Profile P Γ A ∈ C ∧ Ω.profile (A.subst σ) ∈ C) :=
    fun h => ho.elim (fun hn => hn h.1) (fun hn => hn h.2)
  cases A <;> simp only [eval,ite_eq_right hn]

def dropSupport : Option (Nat × Bool) → Option (Nat × Bool)
  | some (0,_) => none
  | some (n+1,p) => some (n,p)
  | none => none

def flipSupport : Option (Nat × Bool) → Option (Nat × Bool) :=
  Option.map (fun (n,p) => (n,!p))

noncomputable def support (Γ : List (Expr S)) (A : Expr S) : Option (Nat × Bool) :=
  if Profile P Γ A ∈ C then
    match A with
    | .pi D E => if Profile P Γ D ∈ C then flipSupport (support Γ D)
        else dropSupport (support (D :: Γ) E)
    | A => (head A).map (fun i => (i,false))
  else none

structure Environment (Γ : List (Expr S)) where
  images : Nat → Expr S
  typed : Ω.TypedSubstitution Γ images
  bits : Bits

noncomputable def R {Γ : List (Expr S)} (A : Expr S) (e : Environment Ω Γ) : Set (Expr S) :=
  eval Ω C Γ A.normalForm e.images e.bits

theorem normal_subst_eq {Γ : List (Expr S)} {A : Expr S}
    (hA : Expected P Γ A) (e : Environment Ω Γ) :
    (A.normalForm.subst e.images).normalForm = (A.subst e.images).normalForm := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · rw [Expr.normalForm_of_normal (Normal.sort s)]
  · exact Expr.normalForm_converts
      ((ContextTower.HasType.subst (hA.normalForm hw) e.typed).weaklyNormalizing hw)
      ((ContextTower.HasType.subst hA e.typed).weaklyNormalizing hw)
      (.symm _ _ ((Expr.normalForm_spec (hA.weaklyNormalizing hw)).1.converts.subst e.images))

theorem R_candidate {Γ : List (Expr S)} {A : Expr S} (hA : Expected P Γ A) (e : Environment Ω Γ) :
    IsCandidate Ω (A.subst e.images).normalForm (R Ω C A e) := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · simp only [R,Expr.normalForm_of_normal (Normal.sort s),eval,head,ite_self]
    exact top_candidate
  · rw [← normal_subst_eq Ω hw (.sorted hA) e]
    exact eval_candidate Ω C hw (hA.normalForm hw) e.typed e.bits

theorem R_conversion {Γ : List (Expr S)} {A B : Expr S}
    (hA : Expected P Γ A) (hB : Expected P Γ B) (hc : Converts A B) (e : Environment Ω Γ) :
    R Ω C A e = R Ω C B e := by
  simp only [R,Expr.normalForm_converts (hA.wn hw) (hB.wn hw) hc]

end

section
universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))
variable (hw : SystemWeaklyNormalizing P)

theorem eval_recontext {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (hc : ContextEquivalent P Γ Δ)
    (σ : Nat → Expr S) (θ : Bits) : eval Ω C Γ A σ θ = eval Ω C Δ A σ θ := by
  induction A generalizing Γ Δ s σ θ with
  | pi D E ihD ihE =>
    obtain ⟨a,b,c,hD,hE,_,_⟩ := hA.generation_pi
    have hp : Profile P Γ (.pi D E) = Profile P Δ (.pi D E) := Set.ext (fun s => hc.typing _ _)
    rw [eval_pi,eval_pi,hp]
    congr 1
    apply congrArg₂ (RawProduct Ω D E σ) (ihD hD hc σ θ)
    funext n bit
    exact ihE hE (hc.cons hD) _ _
  | var i =>
    have hp : Profile P Γ (.var i) = Profile P Δ (.var i) := Set.ext (fun s => hc.typing _ _)
    simp only [eval,hp]
  | sort s => rw [eval_sort,eval_sort]
  | app f n ihf ihn =>
    have hp : Profile P Γ (.app f n) = Profile P Δ (.app f n) := Set.ext (fun s => hc.typing _ _)
    simp only [eval,hp]
  | lam D m ihD ihm => exact False.elim hA.lambda_cannot_have_sort_type

include hw in
theorem eval_rename {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (hΔ : ValidContext P Δ)
    (ρ : Nat → Nat) (hρ : TypingTree.DeclRenaming Γ Δ ρ)
    (σ τ : Nat → Expr S) (θ ψ : Bits) (hσ : τ ∘ ρ = σ) (hθ : ψ ∘ ρ = θ) :
    eval Ω C Γ A σ θ = eval Ω C Δ (A.rename ρ) τ ψ := by
  induction A generalizing Γ Δ s ρ σ τ θ ψ with
  | pi D E ihD ihE =>
    obtain ⟨a,b,c,hD,hE,_,_⟩ := hA.generation_pi
    have hp := Profile.rename hw hA hΔ ρ (hρ.typed hΔ)
    have he (M : Expr S) : (M.rename ρ).subst τ = M.subst σ := by rw [Expr.subst_rename,hσ]
    rw [eval_pi]
    change _ = eval Ω C Δ (.pi (D.rename ρ) (E.rename (Expr.liftRen ρ))) τ ψ
    rw [eval_pi]
    have hraw : (Expr.pi (D.rename ρ) (E.rename (Expr.liftRen ρ))).subst τ = (Expr.pi D E).subst σ := he (.pi D E)
    have hX := ihD hD hΔ ρ hρ σ τ θ ψ hσ hθ
    have hY : (fun n bit => eval Ω C (D :: Γ) E (Expr.extend σ n) (extendBit θ bit)) =
        (fun n bit => eval Ω C (D.rename ρ :: Δ) (E.rename (Expr.liftRen ρ))
          (Expr.extend τ n) (extendBit ψ bit)) := by
      funext n bit
      apply ihE hE (.cons hΔ (hD.rename hΔ ρ (hρ.typed hΔ))) _ (hρ.lift D)
      · funext i; cases i with
        | zero => rfl
        | succ i => exact congrFun hσ i
      · funext i; cases i with
        | zero => rfl
        | succ i => exact congrFun hθ i
    change Profile P Δ (Expr.pi (D.rename ρ) (E.rename (Expr.liftRen ρ))) = _ at hp
    rw [hp,hraw]
    congr 1
    unfold RawProduct
    rw [hraw,hX,hY]
  | sort s => rw [eval_sort,Expr.rename,eval_sort]
  | var i =>
    have hp := Profile.rename hw hA hΔ ρ (hρ.typed hΔ)
    have he : (.var (ρ i) : Expr S).subst τ = Expr.subst σ (.var i) := congrFun hσ i
    change Profile P Δ (.var (ρ i)) = _ at hp
    simp only [eval,Expr.rename,hp,he,head]
    rw [show ψ (ρ i) = θ i from congrFun hθ i]
  | lam D m ihD ihm => exact False.elim hA.lambda_cannot_have_sort_type
  | app f n ihf ihn =>
    have hp := Profile.rename hw hA hΔ ρ (hρ.typed hΔ)
    have he : ((Expr.app f n).rename ρ).subst τ = (Expr.app f n).subst σ := by rw [Expr.subst_rename,hσ]
    simp only [Expr.rename] at hp he ⊢
    simp only [eval,hp,he,head,head_rename]
    cases hh : head f with
    | none => rfl
    | some i => simp only [Option.map_some]; rw [show ψ (ρ i) = θ i from congrFun hθ i]

namespace Environment
variable {Ω}
def Ext {Γ : List (Expr S)} {D : Expr S} (e : Environment Ω Γ) (f : Environment Ω (D :: Γ)) (n : Expr S) : Prop :=
  f.images = Expr.extend e.images n ∧ ∀ i, f.bits (i+1) = e.bits i
end Environment

theorem R_sort {Γ : List (Expr S)} (s : S) (e : Environment Ω Γ) :
    R Ω C (.sort s) e = Top Ω (.sort s) := by
  rw [R,Expr.normalForm_of_normal (Normal.sort s),eval_sort]

include hw in
theorem R_weakening {Γ : List (Expr S)} {D A n : Expr S} {s : S}
    {e : Environment Ω Γ} {f : Environment Ω (D :: Γ)}
    (hD : HasType P Γ D (.sort s)) (hA : Expected P Γ A) (he : e.Ext f n) :
    R Ω C (A.rename Nat.succ) f = R Ω C A e := by
  rcases hA with ⟨a,rfl⟩ | ⟨a,hA⟩
  · exact (R_sort Ω C a f).trans (R_sort Ω C a e).symm
  · rw [R,R,Expr.normalForm_rename (hA.weaklyNormalizing hw)]
    symm
    apply eval_rename Ω C hw (hA.normalForm hw) (.cons hD.valid hD) Nat.succ (TypingTree.DeclRenaming.weaken D)
    · rw [he.1]; rfl
    · exact funext (fun i => he.2 i)

end

section
universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))
variable (hw : SystemWeaklyNormalizing P)
include hw

theorem normal_product {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s)) (σ : Nat → Expr S)
    (hσ : Ω.TypedSubstitution Γ σ) (θ : Bits) :
    eval Ω C Γ (Expr.pi D E).normalForm σ θ =
      if Profile P Γ (.pi D E) ∈ C ∧ Ω.profile ((Expr.pi D E).subst σ) ∈ C then
        RawProduct Ω D E σ (eval Ω C Γ D.normalForm σ θ)
          (fun n b => eval Ω C (D :: Γ) E.normalForm (Expr.extend σ n) (extendBit θ b))
      else Top Ω ((Expr.pi D E).subst σ).normalForm := by
  obtain ⟨a,b,c,hD,hE,hr,_⟩ := hp.generation_pi
  have hDN := hD.normalForm hw
  have hEN := hE.normalForm hw
  have cD := (Expr.normalForm_spec (hD.weaklyNormalizing hw)).1.converts
  have cE := (Expr.normalForm_spec (hE.weaklyNormalizing hw)).1.converts
  let ctx := ContextEquivalent.head_conversion hD hDN cD
  have hEN' := (ctx.typing _ _).mp hEN
  have hpn : HasType P Γ (.pi D.normalForm E.normalForm) (.sort c) := .product hDN hEN' hr
  have nc := Converts.pi cD cE
  have he : Profile P Γ (.pi D E) = Profile P Γ (.pi D.normalForm E.normalForm) :=
    Profile.converts (hp.weaklyNormalizing hw) (hpn.weaklyNormalizing hw) nc
  have hrw := (ContextTower.HasType.subst hp hσ).weaklyNormalizing hw
  have hnw := (ContextTower.HasType.subst hpn hσ).weaklyNormalizing hw
  have hnf := Expr.normalForm_converts hrw hnw (nc.subst σ)
  have hae : Ω.profile ((Expr.pi D E).subst σ) = Ω.profile ((Expr.pi D.normalForm E.normalForm).subst σ) := by
    rw [←Ω.profile_normalForm ((Expr.pi D E).subst σ),←Ω.profile_normalForm ((Expr.pi D.normalForm E.normalForm).subst σ),hnf]
  rw [Expr.normalForm_pi (hD.weaklyNormalizing hw) (hE.weaklyNormalizing hw),eval_pi,←he,←hae]
  split
  · unfold RawProduct
    rw [←hnf]
    simp_rw [←eval_recontext Ω C hEN ctx]
  · exact congrArg (Top Ω) hnf.symm

theorem R_outside {Γ : List (Expr S)} {A : Expr S} (hA : Expected P Γ A)
    (e : Environment Ω Γ) (ho : Profile P Γ A ∉ C ∨ Ω.profile (A.subst e.images) ∉ C) :
    R Ω C A e = Top Ω (A.subst e.images).normalForm := by
  have hnf := normal_subst_eq Ω hw hA e
  rw [R,eval_outside Ω C,hnf]
  rcases ho with ho | ho
  · exact .inl (by rwa [Profile.normalForm])
  · exact .inr (by
      rw [←Ω.profile_normalForm (A.normalForm.subst e.images),hnf,Ω.profile_normalForm]
      exact ho)

theorem product_iff {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s)) (hg : Profile P Γ (.pi D E) ∈ C)
    (e : Environment Ω Γ) (ha : Ω.profile ((Expr.pi D E).subst e.images) ∈ C) (h : Expr S) :
    h ∈ R Ω C (.pi D E) e ↔
      h ∈ Top Ω ((Expr.pi D E).subst e.images).normalForm ∧
      ∀ n, n ∈ R Ω C D e → ∀ f : Environment Ω (D :: Γ), e.Ext f n → Expr.app h n ∈ R Ω C E f := by
  rw [R,normal_product Ω C hw hp e.images e.typed e.bits,ite_eq_left ⟨hg,ha⟩]
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  constructor
  · rintro ⟨ht,hbody⟩
    refine ⟨ht,?_⟩
    intro n hn f he
    have hb : f.bits = extendBit e.bits (f.bits 0) := by
      funext i; cases i with
      | zero => rfl
      | succ i => exact he.2 i
    change Expr.app h n ∈ eval Ω C (D :: Γ) E.normalForm f.images f.bits
    rw [he.1,hb]
    exact hbody n hn (f.bits 0)
  · rintro ⟨ht,hbody⟩
    refine ⟨ht,?_⟩
    intro n hn bit
    have hrawD := ContextTower.HasType.subst hD e.typed
    have hnt := ((R_candidate Ω C hw (.sorted hD) e).upper hn).1.conversion hrawD
      (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
    let f : Environment Ω (D :: Γ) := ⟨Expr.extend e.images n,e.typed.cons hnt,extendBit e.bits bit⟩
    exact hbody n hn f ⟨rfl,fun _ => rfl⟩

end

section
universe u
open Classical
variable {S : Type u} {P : Specification S} (C : Set (Set S))

/-- Replaced supported heads are assigned the extremum appropriate to the
comparison direction and path parity. Unreplaced heads retain their bit. -/
def CompatibleBits (r : Option (Nat × Bool)) (dir : Bool) (σ : Nat → Expr S) (θ ψ : Bits) : Prop :=
  ∀ i p, r = some (i,p) → (∃ j, σ i = .var j ∧ θ i = ψ j) ∨ θ i = Bool.xor dir p

def Below {α : Type*} (dir : Bool) (X Y : Set α) : Prop := if dir then Y ⊆ X else X ⊆ Y

theorem support_outside {Γ : List (Expr S)} {A : Expr S} (h : Profile P Γ A ∉ C) :
    support (P := P) C Γ A = none := by cases A <;> simp only [support,ite_eq_right h]

theorem support_head {Γ : List (Expr S)} {A : Expr S} {i : Nat}
    (hg : Profile P Γ A ∈ C) (hi : head A = some i) : support (P := P) C Γ A = some (i,false) := by
  cases A <;> simp only [support,ite_eq_left hg]
  all_goals first | (cases hi <;> rfl) | (rw [hi]; rfl)

theorem bits_domain {Γ : List (Expr S)} {D E : Expr S} {dir : Bool}
    {σ : Nat → Expr S} {θ ψ : Bits} (hg : Profile P Γ (.pi D E) ∈ C)
    (hb : CompatibleBits (support (P := P) C Γ (.pi D E)) dir σ θ ψ) :
    CompatibleBits (support (P := P) C Γ D) (!dir) σ θ ψ := by
  intro i p hi
  by_cases hd : Profile P Γ D ∈ C
  · have hp : support (P := P) C Γ (.pi D E) = some (i,!p) := by
      rw [support,ite_eq_left hg,ite_eq_left hd,flipSupport,hi]; rfl
    rcases hb i (!p) hp with h | h
    · exact .inl h
    · right
      have he : Bool.xor dir (!p) = Bool.xor (!dir) p := by cases dir <;> cases p <;> rfl
      exact h.trans he
  · rw [support_outside C hd] at hi
    cases hi

theorem bits_body (hw : SystemWeaklyNormalizing P)
    (hno : ∀ {I J K}, ProfileTriple P I J K → I ∈ C → J ∈ C → K ∈ C → False)
    {Γ : List (Expr S)} {D E : Expr S} {s : S} {dir : Bool}
    {σ : Nat → Expr S} {θ ψ : Bits} (hp : HasType P Γ (.pi D E) (.sort s))
    (hg : Profile P Γ (.pi D E) ∈ C)
    (hb : CompatibleBits (support (P := P) C Γ (.pi D E)) dir σ θ ψ) (bit : Bool) :
    CompatibleBits (support (P := P) C (D :: Γ) E) dir (Expr.liftSub σ) (extendBit θ bit) (extendBit ψ bit) := by
  intro i p hi
  by_cases hd : Profile P Γ D ∈ C
  · have he : Profile P (D :: Γ) E ∉ C := fun he => hno (Profile.triple hw hp) hd he hg
    rw [support_outside C he] at hi
    cases hi
  · cases i with
    | zero => exact .inl ⟨0,rfl,rfl⟩
    | succ i =>
      have hh : support (P := P) C Γ (.pi D E) = some (i,p) := by
        rw [support,ite_eq_left hg,ite_eq_right hd,hi]; rfl
      rcases hb i p hh with ⟨j,hj,he⟩ | he
      · left
        exact ⟨j+1,by rw [Expr.liftSub_succ,hj]; rfl,he⟩
      · exact .inr he

noncomputable def chosenBit (Γ : List (Expr S)) (A : Expr S) : Bool :=
  match support (P := P) C Γ A with
  | some (0,p) => p
  | _ => true

theorem bits_single (Γ : List (Expr S)) (A N : Expr S) (θ : Bits) :
    CompatibleBits (support (P := P) C Γ A) false (Expr.single N) (extendBit θ (chosenBit (P := P) C Γ A)) θ := by
  intro i p hi
  cases i with
  | zero =>
    right
    simp only [extendBit,chosenBit,hi,Bool.false_xor]
  | succ i => exact .inl ⟨i,rfl,rfl⟩

end

section
universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))
variable (hw : SystemWeaklyNormalizing P)
include hw

theorem subst_profile_path {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (hΔ : ValidContext P Δ) (δ : Nat → Expr S)
    (hδ : TypedSubstitution P Γ Δ δ) :
    PositivePath (PrimaryEdge P) (Profile P Δ (A.subst δ)) (Profile P Γ A) :=
  Profile.inclusion_path
    (Profile.feasible ((hA.subst hΔ δ hδ).weaklyNormalizing hw) (Profile.nonempty_of_sorted hw (hA.subst hΔ δ hδ)))
    (Profile.feasible (hA.weaklyNormalizing hw) (Profile.nonempty_of_sorted hw hA))
    (Profile.growth hw (hA.weaklyNormalizing hw) hΔ δ hδ)

theorem neutral_compare {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (hΔ : ValidContext P Δ) (δ : Nat → Expr S)
    (hδ : TypedSubstitution P Γ Δ δ) (e : Environment Ω Δ) (θ : Bits) (dir : Bool) {i : Nat}
    (hi : head A = some i) (hg : Profile P Γ A ∈ C)
    (hp : Profile P Δ (A.subst δ) ∈ C)
    (ha : Ω.profile (A.subst (fun i => (δ i).subst e.images)) ∈ C)
    (hb : CompatibleBits (support (P := P) C Γ A) dir δ θ e.bits) :
    Below dir (eval Ω C Γ A (fun i => (δ i).subst e.images) θ) (R Ω C (A.subst δ) e) := by
  have ht := hA.subst hΔ δ hδ
  have hcomp : ((A.subst δ).subst e.images) = A.subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
  have hc := R_candidate Ω C hw (.sorted ht) e
  rw [hcomp] at hc
  rw [eval_head Ω C hg ha hi]
  rcases hb i false (support_head C hg hi) with ⟨j,hj,hbit⟩ | hbit
  · have hhead : head (A.subst δ).normalForm = some j :=
      head_normalForm (by rw [head_subst hi,hj]; rfl) (ht.weaklyNormalizing hw)
    have hnf := normal_subst_eq Ω hw (.sorted ht) e
    have ha' : Ω.profile (((A.subst δ).normalForm).subst e.images) ∈ C := by
      rw [←Ω.profile_normalForm (((A.subst δ).normalForm).subst e.images),hnf,Ω.profile_normalForm,hcomp]
      exact ha
    have he : R Ω C (A.subst δ) e =
        if e.bits j then Top Ω (A.subst (fun i => (δ i).subst e.images)).normalForm
        else Bottom Ω (A.subst (fun i => (δ i).subst e.images)).normalForm := by
      rw [R,eval_head Ω C (by rwa [Profile.normalForm]) ha' hhead,hnf,hcomp]
    rw [he,hbit]
    cases dir <;> exact Set.Subset.rfl
  · simp only [Bool.xor_false] at hbit
    rw [hbit]
    cases dir with
    | false => exact bottom_le hc
    | true => exact hc.upper

omit hw in
@[simp] theorem head_apps (M : Expr S) (ns : List (Expr S)) : head (M.apps ns) = head M := by
  induction ns generalizing M with
  | nil => rfl
  | cons n ns ih => exact ih _

omit hw in
theorem normal_app_head {Γ : List (Expr S)} {f n : Expr S} {s : S}
    (ht : HasType P Γ (.app f n) (.sort s)) (hn : Normal (.app f n)) :
    ∃ i, head (.app f n) = some i := by
  have hneutral {M : Expr S} (h : Neutral M) : ∃ i, head M = some i := by
    induction h with
    | var i => exact ⟨i,rfl⟩
    | app h ih => exact ih
  obtain ⟨s,he⟩ | h | ⟨D,E,he⟩ := ht.sorted_normal_shape hn
  · cases he
  · exact hneutral h
  · cases he

variable (hC : IsComponent (PrimaryEdge P) C)
variable (hno : ∀ {I J K}, ProfileTriple P I J K → I ∈ C → J ∈ C → K ∈ C → False)
include hC hno hw

/-- The one-child polarity comparison at a generic normal type. The post-type
may have arbitrary newly exposed normal constructors. -/
theorem compare_subst {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (hN : Normal A)
    (hrel : ∃ K ∈ C, Reach (PrimaryEdge P) (Profile P Γ A) K)
    (hΔ : ValidContext P Δ) (δ : Nat → Expr S) (hδ : TypedSubstitution P Γ Δ δ)
    (e : Environment Ω Δ) (θ : Bits) (dir : Bool)
    (hb : CompatibleBits (support (P := P) C Γ A) dir δ θ e.bits) :
    Below dir (eval Ω C Γ A (fun i => (δ i).subst e.images) θ) (R Ω C (A.subst δ) e) := by
  induction A generalizing Γ Δ s δ θ dir with
  | var i =>
    have ht := hA.subst hΔ δ hδ
    have he : (((Expr.var i).subst δ).subst e.images) = (Expr.var i).subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
    have hpa := Ω.profile_subst_path hw ht e.typed
    have hpg := subst_profile_path hw hA hΔ δ hδ
    by_cases ha : Ω.profile ((Expr.var i).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg : Profile P Γ (Expr.var i) ∈ C := by
      obtain ⟨K,hK,hpath⟩ := hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp : Profile P Δ ((Expr.var i).subst δ) ∈ C := by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach
    exact neutral_compare Ω C hw hA hΔ δ hδ e θ dir rfl hg hp ha hb
  | app f n ihf ihn =>
    have ht := hA.subst hΔ δ hδ
    have he : (((Expr.app f n).subst δ).subst e.images) = (Expr.app f n).subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
    have hpa := Ω.profile_subst_path hw ht e.typed
    have hpg := subst_profile_path hw hA hΔ δ hδ
    by_cases ha : Ω.profile ((Expr.app f n).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg : Profile P Γ (Expr.app f n) ∈ C := by
      obtain ⟨K,hK,hpath⟩ := hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp : Profile P Δ ((Expr.app f n).subst δ) ∈ C := by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach

    obtain ⟨i,hi⟩ := normal_app_head hA hN
    exact neutral_compare Ω C hw hA hΔ δ hδ e θ dir hi hg hp ha hb
  | sort a =>
    have ht := hA.subst hΔ δ hδ
    have he : (((Expr.sort a).subst δ).subst e.images) = (Expr.sort a).subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
    have hpa := Ω.profile_subst_path hw ht e.typed
    have hpg := subst_profile_path hw hA hΔ δ hδ
    by_cases ha : Ω.profile ((Expr.sort a).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg : Profile P Γ (Expr.sort a) ∈ C := by
      obtain ⟨K,hK,hpath⟩ := hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp : Profile P Δ ((Expr.sort a).subst δ) ∈ C := by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach

    rw [eval_sort,Expr.subst,R_sort]
    cases dir <;> exact Set.Subset.rfl
  | lam D m ihD ihm =>
    have ht := hA.subst hΔ δ hδ
    have he : (((Expr.lam D m).subst δ).subst e.images) = (Expr.lam D m).subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
    have hpa := Ω.profile_subst_path hw ht e.typed
    have hpg := subst_profile_path hw hA hΔ δ hδ
    by_cases ha : Ω.profile ((Expr.lam D m).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg : Profile P Γ (Expr.lam D m) ∈ C := by
      obtain ⟨K,hK,hpath⟩ := hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp : Profile P Δ ((Expr.lam D m).subst δ) ∈ C := by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach
    exact False.elim hA.lambda_cannot_have_sort_type
  | pi D E ihD ihE =>
    have ht := hA.subst hΔ δ hδ
    have he : (((Expr.pi D E).subst δ).subst e.images) = (Expr.pi D E).subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
    have hpa := Ω.profile_subst_path hw ht e.typed
    have hpg := subst_profile_path hw hA hΔ δ hδ
    by_cases ha : Ω.profile ((Expr.pi D E).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg : Profile P Γ (Expr.pi D E) ∈ C := by
      obtain ⟨K,hK,hpath⟩ := hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp : Profile P Δ ((Expr.pi D E).subst δ) ∈ C := by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach

    obtain ⟨a,b,c,hD,hE,hr,_⟩ := hA.generation_pi
    have hDn := hN.pi_domain
    have hEn := hN.pi_body
    have tr := Profile.triple hw hA
    have relD : ∃ K ∈ C, Reach (PrimaryEdge P) (Profile P Γ D) K := ⟨_,hg,.single (.domain tr)⟩
    have relE : ∃ K ∈ C, Reach (PrimaryEdge P) (Profile P (D :: Γ) E) K := ⟨_,hg,.single (.codomain tr)⟩
    have hδD := hD.subst hΔ δ hδ
    have dom := ihD hD hDn relD hΔ δ hδ e θ (!dir) (bits_domain C hg hb)
    have body (n : Expr S) (hn : n ∈ R Ω C (D.subst δ) e) (bit : Bool) :
        Below dir (eval Ω C (D :: Γ) E (Expr.extend (fun i => (δ i).subst e.images) n) (extendBit θ bit))
          (eval Ω C (D.subst δ :: Δ) (E.subst (Expr.liftSub δ)).normalForm
            (Expr.extend e.images n) (extendBit e.bits bit)) := by
      have hrawD := ContextTower.HasType.subst hδD e.typed
      have hnt := ((R_candidate Ω C hw (.sorted hδD) e).upper hn).1.conversion hrawD
        (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
      let f : Environment Ω (D.subst δ :: Δ) := ⟨Expr.extend e.images n,e.typed.cons hnt,extendBit e.bits bit⟩
      have hbody := ihE hE hEn relE (.cons hΔ hδD) (Expr.liftSub δ) (hδ.lift hδD)
        f (extendBit θ bit) dir (bits_body C hw hno hA hg hb bit)
      have hei : (fun i => (Expr.liftSub δ i).subst f.images) = Expr.extend (fun i => (δ i).subst e.images) n := by
        funext i
        cases i with
        | zero => rfl
        | succ i => exact Expr.subst_raise_extend (δ i) n e.images
      rw [hei] at hbody
      exact hbody
    rw [eval_pi,ite_eq_left ⟨hg,ha⟩,R,Expr.subst,normal_product Ω C hw ht _ e.typed e.bits,ite_eq_left ⟨hp,by change Ω.profile (((Expr.pi D E).subst δ).subst e.images) ∈ C; rwa [he]⟩]
    change Below dir (RawProduct Ω D E _ _ _) (RawProduct Ω (D.subst δ) (E.subst (Expr.liftSub δ)) e.images _ _)
    have hraw : ((Expr.pi (D.subst δ) (E.subst (Expr.liftSub δ))).subst e.images).normalForm =
        ((Expr.pi D E).subst (fun i => (δ i).subst e.images)).normalForm := congrArg Expr.normalForm he
    cases dir with
    | false =>
      intro h hh
      refine ⟨hraw.symm ▸ hh.1,?_⟩
      intro n hn bit
      exact body n hn bit (hh.2 n (dom hn) bit)
    | true =>
      intro h hh
      refine ⟨hraw ▸ hh.1,?_⟩
      intro n hn bit
      exact body n (dom hn) bit (hh.2 n (dom hn) bit)

end

universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))
variable (hw : SystemWeaklyNormalizing P) (hC : IsComponent (PrimaryEdge P) C)
variable (hno : ∀ {I J K}, ProfileTriple P I J K → I ∈ C → J ∈ C → K ∈ C → False)
include hw hC hno

theorem specialization {Γ : List (Expr S)} {D E N : Expr S} {s : S}
    (e : Environment Ω Γ) (hp : HasType P Γ (.pi D E) (.sort s))
    (hN : HasType P Γ N D) (hg : Profile P Γ (.pi D E) ∈ C)
    (ha : Ω.profile ((Expr.pi D E).subst e.images) ∈ C) (h : Expr S)
    (hh : h ∈ R Ω C (.pi D E) e) (hn : N.subst e.images ∈ R Ω C D e) :
    Expr.app h (N.subst e.images) ∈ R Ω C (E.instantiate N) e := by
  obtain ⟨a,b,c,hD,hE,hr,_⟩ := hp.generation_pi
  let bit := chosenBit (P := P) C (D :: Γ) E.normalForm
  let f : Environment Ω (D :: Γ) := ⟨Expr.extend e.images (N.subst e.images),
    e.typed.cons (ContextTower.HasType.subst hN e.typed),extendBit e.bits bit⟩
  have hm := ((product_iff Ω C hw hp hg e ha h).mp hh).2 (N.subst e.images) hn f ⟨rfl,fun _ => rfl⟩
  have hrel : ∃ K ∈ C, Reach (PrimaryEdge P) (Profile P (D :: Γ) E.normalForm) K := by
    rw [Profile.normalForm]
    exact ⟨_,hg,.single (.codomain (Profile.triple hw hp))⟩
  have hc := compare_subst Ω C hw hC hno (hE.normalForm hw)
    (Expr.normalForm_spec (hE.weaklyNormalizing hw)).2 hrel hD.valid (Expr.single N)
    (TypedSubstitution.single hN) e f.bits false (bits_single C (D :: Γ) E.normalForm N e.bits)
  have he : (fun i => (Expr.single N i).subst e.images) = f.images := by
    funext i; cases i <;> rfl
  rw [he] at hc
  have hout := hc hm
  have ht := hE.instantiate hN
  have ht' := (hE.normalForm hw).instantiate hN
  have cE := (Expr.normalForm_spec (hE.weaklyNormalizing hw)).1.converts.subst (Expr.single N)
  exact (R_conversion Ω C hw (.sorted ht) (.sorted ht') cE e).symm ▸ hout

/-- One-child components need no relational exclusion: both fresh extremes
are tested, and polarity selects one of those tests at specialization. -/
noncomputable def componentInterface : ComponentInterface Ω hw C where
  Env := Environment Ω
  images := Environment.images
  typed := Environment.typed
  inhabit σ hσ := ⟨⟨σ,hσ,fun _ => false⟩,rfl⟩
  Ext := Environment.Ext
  ext_images he := he.1
  extend e _ n hn := ⟨⟨Expr.extend e.images n,e.typed.cons hn,extendBit e.bits false⟩,rfl,fun _ => rfl⟩
  R := R Ω C
  candidate e hA := R_candidate Ω C hw hA e
  conversion e ha hb hc := R_conversion Ω C hw ha hb hc e
  outside e ht ho := R_outside Ω C hw ht e ho
  weakening hd he hx := R_weakening Ω C hw hd he hx
  product_intro e hp hg ha h ht hb := (product_iff Ω C hw hp hg e ha h).mpr ⟨ht,hb⟩
  specialization e hp hN hg ha h hh hn := specialization Ω C hw hC hno e hp hN hg ha h hh hn

end PureTypeSystem.OneChildInterpretation

end OAI
