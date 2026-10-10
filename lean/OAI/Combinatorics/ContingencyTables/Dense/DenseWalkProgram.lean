import OAI.Combinatorics.ContingencyTables.Dense.DenseStepGrowth

namespace OAI

/-! # A polynomial loop of binary dense transition words -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

def advance (z : List Bool×FlatExponentData) : FlatExponentData :=
  replaceFlat (z.2,flatWordStep (z.2,z.1))

def advanceRealizer : Realizer advance := by
  let swap : Realizer (fun z : List Bool×FlatExponentData => (z.2,z.1)) := pair second first
  let next := composition swap flatWordStepRealizer
  exact composition (pair second next) replaceFlatRealizer

theorem polynomial_advance : PolynomialTime advanceRealizer := by
  unfold advanceRealizer
  exact polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_flatWordStep))
    polynomial_replaceFlat

lemma advance_parameters (data : FlatExponentData) (bits : List Bool) :
    (advance (bits,data)).1.1=data.1.1 ∧ (advance (bits,data)).2=data.2 := ⟨rfl,rfl⟩

lemma advance_growth (data : FlatExponentData) (bits : List Bool) (S : ℕ)
    (h : ∀ a∈data.1.2,a.size≤S) :
    (advance (bits,data)).1.2.length=data.1.2.length ∧
      ∀ a∈(advance (bits,data)).1.2,a.size≤S+2 := flatWordStep_growth _ S h

def walkWords (z : FlatExponentData×List (List Bool)) : FlatExponentData :=
  z.2.foldl (fun data bits => advance (bits,data)) z.1

def walkWordsRealizer : Realizer walkWords :=
  composition (pair second first) (fold advanceRealizer)

lemma fold_advance_parameters (bits : List (List Bool)) (data : FlatExponentData) :
    let out := bits.foldl (fun data bits => advance (bits,data)) data
    out.1.1=data.1.1 ∧ out.2=data.2 ∧ out.1.2.length=data.1.2.length := by
  induction bits generalizing data with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons b bs ih =>
    have h := ih (advance (b,data))
    have hl : (advance (b,data)).1.2.length=data.1.2.length := by
      have hx := advance_growth data b (data.1.2.map Nat.size).sum
        (fun a ha => List.single_le_sum (fun _ _ => Nat.zero_le _) a.size
          (List.mem_map.mpr ⟨a,ha,rfl⟩))
      exact hx.1
    exact ⟨h.1,h.2.1,h.2.2.trans hl⟩

lemma fold_advance_sizes (bits : List (List Bool)) (data : FlatExponentData) (S : ℕ)
    (h : ∀ a∈data.1.2,a.size≤S) :
    ∀ a∈(bits.foldl (fun data bits => advance (bits,data)) data).1.2,
      a.size≤S+2*bits.length := by
  induction bits generalizing data S with
  | nil => simpa using h
  | cons b bs ih =>
    have hg := advance_growth data b S h
    have ht := ih (advance (b,data)) (S+2) hg.2
    intro a ha
    have h := ht a ha
    simpa only [List.length_cons,List.foldl_cons] using
      h.trans_eq (by omega : S+2+2*bs.length=S+2*(bs.length+1))

theorem polynomial_walkWords : PolynomialTime walkWordsRealizer := by
  apply polynomial_composition (polynomial_pair polynomial_second polynomial_first)
  apply polynomial_fold polynomial_advance (20*(X+1)^2)
  intro bits data pre post he
  let S := weight (bits,data)
  let out := pre.foldl (fun data bits => advance (bits,data)) data
  have hd : weight data≤S := weight_snd (bits,data)
  have hp : pre.length≤S := (list_length_le_weight pre).trans
    ((weight_prefix he).trans (weight_fst (bits,data)))
  have hxs : weight data.1.2≤S := (weight_snd data.1).trans ((weight_fst data).trans hd)
  have hn : data.1.2.length≤S := (list_length_le_weight _).trans hxs
  have hi : ∀ a∈data.1.2,a.size≤S := fun a ha =>
    (size_le_weight a).trans ((weight_mem ha).trans hxs)
  have hs := fold_advance_sizes pre data S hi
  have ht := fold_advance_parameters pre data
  have hw : weight out.1.2≤out.1.2.length*(4*(S+2*pre.length)+2)+1 := by
    have h := weight_map_bound (f := id) (as := out.1.2) (N := 4*(S+2*pre.length)+1)
      (fun a ha => (weight_nat_le a).trans (by have h := hs a ha; omega))
    simpa only [List.map_id_fun,id_eq,Nat.add_assoc] using h
  have hm : weight out.1.1≤S := by
    rw [ht.1]
    exact (weight_fst data.1).trans ((weight_fst data).trans hd)
  have hd' : weight out.2≤S := by
    rw [ht.2.1]
    exact (weight_snd data).trans hd
  have hl : out.1.2.length≤S := ht.2.2.trans_le hn
  have hmul : out.1.2.length*(4*(S+2*pre.length)+2)≤S*(12*S+2) :=
    Nat.mul_le_mul hl (by omega)
  simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  change weight out≤20*(S+1)^2
  have heq : weight out=1+(1+weight out.1.1+weight out.1.2)+weight out.2 := by
    rw [weight_prod,weight_prod]
  nlinarith

end ContingencyTables.DensePrograms

end OAI
