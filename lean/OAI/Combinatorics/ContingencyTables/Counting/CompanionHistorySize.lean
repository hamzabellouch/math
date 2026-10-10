import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseSize
import OAI.Combinatorics.ContingencyTables.Counting.CompanionOuterHistoryProgram

namespace OAI

/-! # Polynomial stored size throughout the adaptive history fold -/
namespace ContingencyTables.CompanionOuterHistoryProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial CompanionStoredSize

private lemma getD_property {X : Type} (P : X→Prop) (xs : List X) (i : ℕ) (d : X)
    (hx : ∀ x∈xs,P x) (hd : P d) : P (xs.getD i d) := by
  rw [List.getD_eq_getElem?_getD]
  cases he : xs[i]? with
  | none => exact hd
  | some x => exact hx x (List.mem_of_getElem? he)

lemma old_property (P : Stored→Prop) (state : State) (bits : List Bool)
    (hi : P state.1.2) (hs : ∀ s∈state.2,P s) (hd : P default) :
    P (CompanionOuterPhaseProgram.old (state,bits)) := by
  unfold CompanionOuterPhaseProgram.old
  split_ifs
  · exact hi
  · exact getD_property P state.2 _ default hs hd

lemma default_height (M : ℕ) : StoredHeight M (default : Stored) := by
  constructor
  · intro row hr
    exact False.elim (List.not_mem_nil hr)
  · change max (0:ℕ).size (0:ℕ).size ≤ M
    simp only [Nat.size_zero,max_self,Nat.zero_le]

lemma default_shape (R : ℕ) : StoredShape R (default : Stored) := by
  exact ⟨Nat.zero_le _,fun row hr => False.elim (List.not_mem_nil hr)⟩

lemma fold_length (words : List (List Bool)) (state : State) :
    (words.foldl (fun s bits => advance (bits,s)) state).2.length=state.2.length+words.length := by
  induction words generalizing state with
  | nil => simp
  | cons word words ih =>
    simp only [List.foldl_cons]
    rw [ih]
    change (state.2++[next (word,state)]).length+words.length=state.2.length+(word::words).length
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega

lemma fold_fixed (words : List (List Bool)) (state : State) :
    (words.foldl (fun s bits => advance (bits,s)) state).1=state.1 := by
  induction words generalizing state with
  | nil => rfl
  | cons word words ih => exact ih _

lemma fold_bounds (p : Polynomial ℕ)
    (hp : ∀ (z : CompanionOuterPhaseProgram.Input) (S M R : ℕ),
      weight z.1.1.1 ≤ S → weight z.2 ≤ S → z.1.2.length ≤ S → 1 ≤ M →
      StoredHeight M (CompanionOuterPhaseProgram.old z) →
      StoredShape R (CompanionOuterPhaseProgram.old z) → p.eval S ≤ R →
      StoredHeight (M+p.eval S) (CompanionOuterPhaseProgram.output z) ∧
        StoredShape R (CompanionOuterPhaseProgram.output z))
    (words : List (List Bool)) (state : State) (S M R : ℕ)
    (hprep : weight state.1.1 ≤ S) (hwords : ∀ bits∈words,weight bits ≤ S)
    (hlen : state.2.length+words.length ≤ S) (hM : 1 ≤ M)
    (hi : StoredHeight M state.1.2) (hs : ∀ s∈state.2,StoredHeight M s)
    (hri : StoredShape R state.1.2) (hrs : ∀ s∈state.2,StoredShape R s)
    (hR : p.eval S ≤ R) :
    let out := words.foldl (fun s bits => advance (bits,s)) state
    StoredHeight (M+words.length*p.eval S) out.1.2 ∧
      (∀ s∈out.2,StoredHeight (M+words.length*p.eval S) s) ∧
      StoredShape R out.1.2 ∧ (∀ s∈out.2,StoredShape R s) := by
  induction words generalizing state M with
  | nil => simpa only [List.foldl_nil,List.length_nil,Nat.zero_mul,Nat.add_zero] using ⟨hi,hs,hri,hrs⟩
  | cons word words ih =>
    have hmold := old_property (StoredHeight M) state word hi hs (default_height M)
    have hrold := old_property (StoredShape R) state word hri hrs (default_shape R)
    have hn := hp (state,word) S M R hprep (hwords word (by simp)) (by
      change state.2.length ≤ S
      simp only [List.length_cons] at hlen
      omega) hM hmold hrold hR
    have hnew : ∀ s∈(advance (word,state)).2,StoredHeight (M+p.eval S) s := by
      intro s hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact height_mono (Nat.le_add_right _ _) (hs s hmem)
      · have he := List.mem_singleton.mp hmem
        subst s
        exact hn.1
    have hrnew : ∀ s∈(advance (word,state)).2,StoredShape R s := by
      intro s hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact hrs s hmem
      · have he := List.mem_singleton.mp hmem
        subst s
        exact hn.2
    have hh := ih (advance (word,state)) (M+p.eval S) hprep
      (fun bits hb => hwords bits (by simp [hb]))
      (by simpa only [advance,List.length_append,List.length_singleton,List.length_cons,List.length_nil,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hlen)
      (by omega) (height_mono (Nat.le_add_right _ _) hi) hnew hri hrnew
    simpa only [List.foldl_cons,List.length_cons,Nat.add_mul,Nat.one_mul,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh


/-- The loop's live representation has a fixed polynomial bound even on
malformed inputs; the only changing numeric values are additive-height fractions. -/
theorem polynomial_historyFold : PolynomialTime (fold advanceRealizer) := by
  obtain ⟨p,hp⟩ := CompanionPhaseSize.phase_bounds
  let s : Polynomial ℕ := 2*X+1
  let r : Polynomial ℕ := s+p.comp s
  let h : Polynomial ℕ := s+s*(p.comp s)
  let w : Polynomial ℕ := r*(r*(8*h+4)+2)+8*h+5
  let out : Polynomial ℕ := 2+s+s*(w+1)
  apply polynomial_fold polynomial_advance out
  intro words state pre post he
  let B := weight (words,state)
  let S := 2*B+1
  let R := S+p.eval S
  let M := S+S*p.eval S
  have hstate : weight state ≤ B := weight_snd (words,state)
  have hwords : weight words ≤ B := weight_fst (words,state)
  have hpre : pre.length ≤ B :=
    (list_length_le_weight pre).trans ((weight_prefix he).trans hwords)
  have histlen : state.2.length ≤ B :=
    (list_length_le_weight _).trans ((weight_snd state).trans hstate)
  have hprep : weight state.1.1 ≤ S :=
    ((weight_fst state.1).trans ((weight_fst state).trans hstate)).trans (by dsimp [S]; omega)
  have hmem : ∀ bits∈pre,weight bits ≤ S := by
    intro bits hb
    have hb' : bits∈words := by rw [he]; exact List.mem_append_left post hb
    exact ((weight_mem hb').trans hwords).trans (by dsimp [S]; omega)
  have hn : state.2.length+pre.length ≤ S := by dsimp [S]; omega
  have hinit : StoredHeight S state.1.2 :=
    height_mono (by have := (weight_snd state.1).trans ((weight_fst state).trans hstate); dsimp [S]; omega)
      (height_of_weight _)
  have hinits : ∀ x∈state.2,StoredHeight S x := by
    intro x hx
    have hxw := (weight_mem hx).trans ((weight_snd state).trans hstate)
    exact height_mono (by dsimp [S]; omega) (height_of_weight x)
  have hrinit : StoredShape R state.1.2 :=
    shape_mono (by have := (weight_snd state.1).trans ((weight_fst state).trans hstate); dsimp [R,S]; omega)
      (shape_of_weight _)
  have hrinits : ∀ x∈state.2,StoredShape R x := by
    intro x hx
    have hxw := (weight_mem hx).trans ((weight_snd state).trans hstate)
    exact shape_mono (by dsimp [R,S]; omega) (shape_of_weight x)
  have hp' : ∀ (z : CompanionOuterPhaseProgram.Input) (S M R : ℕ),
      weight z.1.1.1 ≤ S → weight z.2 ≤ S → z.1.2.length ≤ S → 1 ≤ M →
      StoredHeight M (CompanionOuterPhaseProgram.old z) →
      StoredShape R (CompanionOuterPhaseProgram.old z) → p.eval S ≤ R →
      StoredHeight (M+p.eval S) (CompanionOuterPhaseProgram.output z) ∧
        StoredShape R (CompanionOuterPhaseProgram.output z) := hp
  have hb := fold_bounds p hp' pre state S S R hprep hmem hn (by dsimp [S]; omega)
    hinit hinits hrinit hrinits (by dsimp [R]; omega)
  let result := pre.foldl (fun s bits => advance (bits,s)) state
  have hm : S+pre.length*p.eval S ≤ M := by
    have hle : pre.length ≤ S := by dsimp [S]; omega
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hle) S
  have hstored : ∀ x∈result.2,weight x ≤ R*(R*(8*M+4)+2)+8*M+5 := by
    intro x hx
    exact weight_of_bounds x R M (hb.2.2.2 x hx) (height_mono hm (hb.2.1 x hx))
  have hw := weight_map_bound (f := id) (as := result.2) hstored
  simp only [List.map_id] at hw
  have hlen : result.2.length ≤ S := (fold_length pre state).trans_le hn
  have hw' : weight result.2 ≤ S*(R*(R*(8*M+4)+2)+8*M+5+1)+1 :=
    hw.trans (by gcongr)
  have hf : weight result.1 ≤ S := by
    change weight ((pre.foldl (fun s bits => advance (bits,s)) state).1) ≤ S
    rw [fold_fixed]
    exact ((weight_fst state).trans hstate).trans (by dsimp [S]; omega)
  change weight result ≤ out.eval B
  conv_lhs => rw [show result=(result.1,result.2) from rfl,weight_prod]
  have hout : out.eval B=2+S+S*(R*(R*(8*M+4)+2)+8*M+5+1) := by
    simp only [out,w,r,h,s,R,M,S,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,eval_comp]
  rw [hout]
  omega

lemma polynomial_run : PolynomialTime runRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_pair polynomial_first (polynomial_constant []))) polynomial_historyFold

lemma polynomial_storedHistory : PolynomialTime storedHistoryRealizer :=
  polynomial_composition polynomial_run polynomial_second

lemma polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair polynomial_first polynomial_storedHistory)
    (polynomial_constant [])) CompanionOuterPhaseProgram.polynomial_old

end ContingencyTables.CompanionOuterHistoryProgram

end OAI
