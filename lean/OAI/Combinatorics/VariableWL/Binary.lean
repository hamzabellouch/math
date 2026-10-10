import OAI.Combinatorics.VariableWL.CellularCircuit

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.Binary
attribute [local instance] Classical.propDecidable
abbrev Digits (d : ℕ) := Fin d → Bool

def number : {d : ℕ} → Digits d → ℕ
  | 0,_ => 0
  | d+1,x => (x 0).toNat+2*number (fun i : Fin d => x i.succ)

theorem number_lt {d : ℕ} (x : Digits d) : number x<2^d := by
  induction d with
  | zero => simp [number]
  | succ d ih =>
    have ht := ih (fun i : Fin d => x i.succ)
    have hb : (x 0).toNat ≤ 1 := by cases x 0 <;> decide
    simp only [number,pow_succ]
    omega

theorem number_injective {d : ℕ} : Function.Injective (@number d) := by
  induction d with
  | zero => intro x y _; exact Subsingleton.elim _ _
  | succ d ih =>
    intro x y he
    have hb : x 0=y 0 := by
      dsimp only [number] at he
      cases hx : x 0 <;> cases hy : y 0 <;> simp_all only [Bool.toNat_false,Bool.toNat_true] <;> omega
    have ht : (fun i : Fin d => x i.succ)=(fun i : Fin d => y i.succ) := by
      apply ih
      dsimp only [number] at he
      rw [hb] at he
      omega
    funext i
    exact Fin.cases hb (fun j => congrFun ht j) i

@[simp] theorem number_false (d : ℕ) : number (fun _ : Fin d => false)=0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp [number,ih]

@[simp] theorem number_true (d : ℕ) : number (fun _ : Fin d => true)+1=2^d := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [number,Bool.toNat_true,pow_succ]; omega

noncomputable def equivalence (d : ℕ) : Digits d ≃ Fin (2^d) :=
  Equiv.ofBijective (fun x => ⟨number x,number_lt x⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨fun x y h => number_injective (congrArg Fin.val h), by simp⟩)

@[simp] theorem equivalence_val {d : ℕ} (x : Digits d) : (equivalence d x).val=number x := rfl

def domain {d : ℕ} (bit : Bool) (h i : Fin d) : Finset Bool :=
  if i<h then {bit} else if i=h then {!bit} else Finset.univ

def table {d : ℕ} (h i : Fin d) (x : Bool) : Bool := if i≤h then !x else x

def Allowed {d : ℕ} (bit : Bool) (h : Fin d) (x : Digits d) : Prop := ∀ i, x i ∈ domain bit h i

def flip {d : ℕ} (h : Fin d) (x : Digits d) : Digits d := fun i => table h i (x i)

theorem domain_nonempty {d : ℕ} (bit : Bool) (h i : Fin d) : (domain bit h i).Nonempty := by
  unfold domain
  split_ifs <;> simp

theorem table_injective {d : ℕ} (h i : Fin d) : Function.Injective (table h i) := by
  intro x y he
  unfold table at he
  split_ifs at he with h
  · exact Bool.not_injective he
  · exact he

theorem allowed_iff {d : ℕ} (bit : Bool) (h : Fin d) (x : Digits d) :
    Allowed bit h x ↔ x h = !bit ∧ ∀ i, i<h → x i=bit := by
  constructor
  · intro hx
    exact ⟨by simpa [domain] using hx h,fun i hi => by simpa [domain,hi] using hx i⟩
  · rintro ⟨hh,hlt⟩ i
    by_cases hi : i<h
    · simp [domain,hi,hlt i hi]
    · by_cases he : i=h
      · subst i
        simp [domain,hh]
      · simp [domain,hi,he]

theorem allowed_unique {d : ℕ} (bit : Bool) (h k : Fin d) (x : Digits d)
    (hh : Allowed bit h x) (hk : Allowed bit k x) : h=k := by
  obtain ⟨hh,hh'⟩ := (allowed_iff bit h x).mp hh
  obtain ⟨hk,hk'⟩ := (allowed_iff bit k x).mp hk
  rcases lt_trichotomy h k with hl | he | hl
  · have hf := hk' h hl
    rw [hh] at hf
    cases bit <;> cases hf
  · exact he
  · have hf := hh' k hl
    rw [hk] at hf
    cases bit <;> cases hf

theorem exists_allowed {d : ℕ} (bit : Bool) (x : Digits d)
    (hx : x ≠ fun _ => bit) : ∃ h, Allowed bit h x := by
  classical
  let U := Finset.univ.filter (fun i => x i ≠ bit)
  have hu : U.Nonempty := by
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hx
    exact ⟨i,by simp [U,hi]⟩
  let h := U.min' hu
  have hh : x h ≠ bit := (Finset.mem_filter.mp (Finset.min'_mem U hu)).2
  refine ⟨h,(allowed_iff bit h x).mpr ⟨?_,?_⟩⟩
  · cases he : x h <;> cases bit <;> simp_all
  · intro i hi
    by_contra he
    have him : i ∈ U := by simp [U,he]
    have hle : h ≤ i := Finset.min'_le U i him
    exact not_le_of_gt hi hle

theorem number_flip {d : ℕ} (h : Fin d) (x : Digits d) (hx : Allowed true h x) :
    number (flip h x)=number x+1 := by
  induction d with
  | zero => exact Fin.elim0 h
  | succ d ih =>
    cases h using Fin.cases with
    | zero =>
      have hh : x 0=false := (allowed_iff true 0 x).mp hx |>.1
      have ht : (fun i : Fin d => flip 0 x i.succ)=(fun i : Fin d => x i.succ) := by
        funext i
        simp [flip,table]
      simp only [number]
      rw [ht]
      simp [flip,table,hh,Nat.add_comm]
    | succ h =>
      obtain ⟨hh,hlt⟩ := (allowed_iff true h.succ x).mp hx
      have hz : x 0=true := hlt 0 (Fin.succ_pos h)
      have htail : Allowed true h (fun i : Fin d => x i.succ) :=
        (allowed_iff true h _).mpr ⟨hh,fun i hi => hlt i.succ (Fin.succ_lt_succ_iff.mpr hi)⟩
      have ht : (fun i : Fin d => flip h.succ x i.succ)=flip h (fun i : Fin d => x i.succ) := by
        funext i
        simp [flip,table]
      have he := ih h (fun i : Fin d => x i.succ) htail
      simp only [number]
      rw [ht]
      simp only [flip,table,Fin.zero_le,ite_eq_left,hz,Bool.not_true,Bool.toNat_false,Bool.toNat_true,zero_add]
      omega

theorem number_borrow {d : ℕ} (h : Fin d) (x : Digits d) (hx : Allowed false h x) :
    number (flip h x)+1=number x := by
  induction d with
  | zero => exact Fin.elim0 h
  | succ d ih =>
    cases h using Fin.cases with
    | zero =>
      have hh : x 0=true := (allowed_iff false 0 x).mp hx |>.1
      have ht : (fun i : Fin d => flip 0 x i.succ)=(fun i : Fin d => x i.succ) := by
        funext i
        simp [flip,table]
      simp only [number]
      rw [ht]
      simp [flip,table,hh,Nat.add_comm]
    | succ h =>
      obtain ⟨hh,hlt⟩ := (allowed_iff false h.succ x).mp hx
      have hz : x 0=false := hlt 0 (Fin.succ_pos h)
      have htail : Allowed false h (fun i : Fin d => x i.succ) :=
        (allowed_iff false h _).mpr ⟨hh,fun i hi => hlt i.succ (Fin.succ_lt_succ_iff.mpr hi)⟩
      have ht : (fun i : Fin d => flip h.succ x i.succ)=flip h (fun i : Fin d => x i.succ) := by
        funext i
        simp [flip,table]
      have he := ih h (fun i : Fin d => x i.succ) htail
      simp only [number]
      rw [ht]
      simp only [flip,table,Fin.zero_le,ite_eq_left,hz,Bool.not_false,Bool.toNat_false,Bool.toNat_true,zero_add]
      omega

def cyclicDomain {d : ℕ} (bit : Bool) (h : Option (Fin d)) (i : Fin d) : Finset Bool :=
  match h with | none => {bit} | some h => domain bit h i

def cyclicTable {d : ℕ} (h : Option (Fin d)) (i : Fin d) (x : Bool) : Bool :=
  match h with | none => !x | some h => table h i x

def CyclicAllowed {d : ℕ} (bit : Bool) (h : Option (Fin d)) (x : Digits d) : Prop :=
  ∀ i, x i ∈ cyclicDomain bit h i

def cyclicFlip {d : ℕ} (h : Option (Fin d)) (x : Digits d) : Digits d := fun i => cyclicTable h i (x i)

theorem cyclicDomain_nonempty {d : ℕ} (bit : Bool) (h : Option (Fin d)) (i : Fin d) :
    (cyclicDomain bit h i).Nonempty := by
  cases h with
  | none => exact Finset.singleton_nonempty _
  | some h => exact domain_nonempty bit h i

theorem cyclicTable_injective {d : ℕ} (h : Option (Fin d)) (i : Fin d) :
    Function.Injective (cyclicTable h i) := by
  cases h with
  | none => exact Bool.not_injective
  | some h => exact table_injective h i

theorem cyclicAllowed_none {d : ℕ} (bit : Bool) (x : Digits d) :
    CyclicAllowed bit none x ↔ x=fun _ => bit := by
  simp only [CyclicAllowed,cyclicDomain,Finset.mem_singleton]
  exact ⟨fun h => funext h,fun h i => congrFun h i⟩

theorem exists_cyclicAllowed {d : ℕ} (bit : Bool) (x : Digits d) : ∃ h, CyclicAllowed bit h x := by
  by_cases hx : x=fun _ => bit
  · exact ⟨none,(cyclicAllowed_none bit x).mpr hx⟩
  · obtain ⟨h,hh⟩ := exists_allowed bit x hx
    exact ⟨some h,hh⟩

theorem cyclicAllowed_unique {d : ℕ} (bit : Bool) (h k : Option (Fin d)) (x : Digits d)
    (hh : CyclicAllowed bit h x) (hk : CyclicAllowed bit k x) : h=k := by
  cases h with
  | none =>
    cases k with
    | none => rfl
    | some k =>
      have hx := (cyclicAllowed_none bit x).mp hh
      have hn := (allowed_iff bit k x).mp hk |>.1
      rw [hx] at hn
      cases bit <;> cases hn
  | some h =>
    cases k with
    | none =>
      have hx := (cyclicAllowed_none bit x).mp hk
      have hn := (allowed_iff bit h x).mp hh |>.1
      rw [hx] at hn
      cases bit <;> cases hn
    | some k => exact congrArg some (allowed_unique bit h k x hh hk)

theorem cyclic_increment {d : ℕ} (h : Option (Fin d)) (x : Digits d) (hx : CyclicAllowed true h x) :
    number (cyclicFlip h x)=(number x+1) % 2^d := by
  cases h with
  | none =>
    have he := (cyclicAllowed_none true x).mp hx
    subst x
    change number (fun _ : Fin d => false)=(number (fun _ : Fin d => true)+1) % 2^d
    rw [number_false,number_true,Nat.mod_self]
  | some h =>
    have he := number_flip h x hx
    have ht := number_lt (flip h x)
    change number (flip h x)=(number x+1) % 2^d
    rw [← he,Nat.mod_eq_of_lt ht]

theorem cyclic_decrement {d : ℕ} (h : Option (Fin d)) (x : Digits d) (hx : CyclicAllowed false h x) :
    number (cyclicFlip h x)=(number x+2^d-1) % 2^d := by
  cases h with
  | none =>
    have he := (cyclicAllowed_none false x).mp hx
    subst x
    have hn := number_true d
    have ht := number_lt (fun _ : Fin d => true)
    have hn' : number (fun _ : Fin d => true)=2^d-1 := by omega
    change number (fun _ : Fin d => true)=(number (fun _ : Fin d => false)+2^d-1) % 2^d
    rw [number_false,Nat.zero_add,← hn',Nat.mod_eq_of_lt ht]
  | some h =>
    have he := number_borrow h x hx
    have ht := number_lt (flip h x)
    change number (flip h x)=(number x+2^d-1) % 2^d
    have hh : number x+2^d-1=number (flip h x)+2^d := by omega
    rw [hh,Nat.add_mod_right,Nat.mod_eq_of_lt ht]

end VariableWL.Binary

namespace VariableWL.Binary
attribute [local instance] Classical.propDecidable

def GreaterAt {d : ℕ} (μ x : Digits d) (h : Fin d) : Prop :=
  μ h=false ∧ x h=true ∧ ∀ i, h < i → x i=μ i

theorem number_lt_iff {d : ℕ} (μ x : Digits d) : number μ<number x ↔ ∃ h, GreaterAt μ x h := by
  induction d with
  | zero => simp [number]
  | succ d ih =>
    let μ' : Digits d := fun i => μ i.succ
    let x' : Digits d := fun i => x i.succ
    have hμ : (μ 0).toNat ≤ 1 := by cases μ 0 <;> decide
    have hx : (x 0).toNat ≤ 1 := by cases x 0 <;> decide
    constructor
    · intro hlt
      change (μ 0).toNat+2*number μ'<(x 0).toNat+2*number x' at hlt
      by_cases ht : number μ'<number x'
      · obtain ⟨h,hm,hh,hhi⟩ := (ih μ' x').mp ht
        refine ⟨h.succ,hm,hh,?_⟩
        intro i hi
        cases i using Fin.cases with
        | zero => exact False.elim (by simp at hi)
        | succ i => exact hhi i (Fin.succ_lt_succ_iff.mp hi)
      · have he : number μ'=number x' := by omega
        have het : μ'=x' := number_injective he
        have hμ0 : μ 0=false := by
          cases heμ : μ 0
          · rfl
          · simp only [heμ,Bool.toNat_true] at hlt
            omega
        have hx0 : x 0=true := by
          cases hex : x 0
          · simp only [hex,Bool.toNat_false] at hlt
            omega
          · rfl
        refine ⟨0,hμ0,hx0,?_⟩
        intro i hi
        cases i using Fin.cases with
        | zero => exact False.elim (lt_irrefl _ hi)
        | succ i => exact (congrFun het i).symm
    · rintro ⟨h,hμh,hxh,hhi⟩
      cases h using Fin.cases with
      | zero =>
        have he : x'=μ' := funext (fun i => hhi i.succ (Fin.succ_pos i))
        change (μ 0).toNat+2*number μ'<(x 0).toNat+2*number x'
        rw [he,hμh,hxh]
        simp
      | succ h =>
        have ht : number μ'<number x' := (ih μ' x').mpr
          ⟨h,hμh,hxh,fun i hi => hhi i.succ (Fin.succ_lt_succ_iff.mpr hi)⟩
        change (μ 0).toNat+2*number μ'<(x 0).toNat+2*number x'
        omega

def thresholdDomain {d : ℕ} (μ : Digits d) (h : Option {h : Fin d // μ h=false}) (i : Fin d) : Finset Bool :=
  match h with
  | none => {μ i}
  | some h => if h.val < i then {μ i} else if i=h.val then {true} else Finset.univ

def ThresholdAllowed {d : ℕ} (μ : Digits d) (h : Option {h : Fin d // μ h=false}) (x : Digits d) : Prop :=
  ∀ i, x i ∈ thresholdDomain μ h i

theorem thresholdDomain_nonempty {d : ℕ} (μ : Digits d) (h : Option {h : Fin d // μ h=false}) (i : Fin d) :
    (thresholdDomain μ h i).Nonempty := by
  cases h with
  | none => exact Finset.singleton_nonempty _
  | some h => simp only [thresholdDomain]; split_ifs <;> simp

theorem threshold_none {d : ℕ} (μ x : Digits d) : ThresholdAllowed μ none x ↔ x=μ := by
  simp only [ThresholdAllowed,thresholdDomain,Finset.mem_singleton]
  exact ⟨fun h => funext h,fun h i => congrFun h i⟩

theorem threshold_some {d : ℕ} (μ x : Digits d) (h : {h : Fin d // μ h=false}) :
    ThresholdAllowed μ (some h) x ↔ GreaterAt μ x h.val := by
  constructor
  · intro hh
    exact ⟨h.property,by simpa [thresholdDomain] using hh h.val,
      fun i hi => by simpa [thresholdDomain,hi] using hh i⟩
  · rintro ⟨_,hh,hhi⟩ i
    by_cases hi : h.val < i
    · simp [thresholdDomain,hi,hhi i hi]
    · by_cases he : i=h.val
      · subst i
        simp [thresholdDomain,hh]
      · simp [thresholdDomain,hi,he]

theorem threshold_exact {d : ℕ} (μ x : Digits d) :
    (∃ h, ThresholdAllowed μ h x) ↔ number μ ≤ number x := by
  constructor
  · rintro ⟨h,hh⟩
    cases h with
    | none => rw [(threshold_none μ x).mp hh]
    | some h => exact Nat.le_of_lt ((number_lt_iff μ x).mpr ⟨h.val,(threshold_some μ x h).mp hh⟩)
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · obtain ⟨i,hi⟩ := (number_lt_iff μ x).mp h
      exact ⟨some ⟨i,hi.1⟩,(threshold_some μ x ⟨i,hi.1⟩).mpr hi⟩
    · exact ⟨none,(threshold_none μ x).mpr (number_injective h).symm⟩

theorem threshold_count {d : ℕ} (μ : Digits d) :
    Fintype.card (Option {h : Fin d // μ h=false}) ≤ d+1 := by
  classical
  simp only [Fintype.card_option]
  simpa using Nat.add_le_add_right (Fintype.card_subtype_le (fun h : Fin d => μ h=false)) 1

end VariableWL.Binary

namespace VariableWL.Circuit
variable {S : Type uVariable1} {A : Type uVariable2} {E : Type uVariable3} {S' : Type uVariable4} {A' : Type uVariable5} {E' : Type uVariable6}

def mapGate (s : S → S') (a : A → A') : Gate S A → Gate S' A' := Sum.map s a

def mapPort (s : S → S') (a : A → A') : Port S A → Port S' A' := Sum.map s (Prod.map a id)

namespace System
variable {C : System S A E} {D : System S' A' E'}

theorem TrueGate.map (s : S → S') (a : A → A')
    (hseed : ∀ x ∈ C.seeds, s x ∈ D.seeds)
    (hedge : ∀ e, ∃ f, D.source f=mapGate s a (C.source e) ∧
      D.destination f=mapPort s a (C.destination e))
    {g : Gate S A} (hg : C.TrueGate g) : D.TrueGate (mapGate s a g) := by
  induction hg with
  | seed x hx => exact .seed _ (hseed x hx)
  | scalar e x he hs ih =>
    obtain ⟨f,hf,hp⟩ := hedge e
    change D.TrueGate (.inl (s x))
    apply TrueGate.scalar f (s x)
    · rw [hp,he]
      rfl
    · rw [hf]
      exact ih
  | and x e f he hf hs ht ihe ihf =>
    obtain ⟨e',he',hp⟩ := hedge e
    obtain ⟨f',hf',hq⟩ := hedge f
    change D.TrueGate (.inr (a x))
    apply TrueGate.and (a x) e' f'
    · rw [hp,he]
      rfl
    · rw [hq,hf]
      rfl
    · rw [he']
      exact ihe
    · rw [hf']
      exact ihf
end System
end VariableWL.Circuit

end OAI
