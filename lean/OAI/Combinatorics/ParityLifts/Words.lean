import OAI.Combinatorics.ParityLifts.Arithmetic

namespace OAI

namespace ParityWL.Complexity

def wordsStep (xs : List (List Bool)) : List (List Bool) :=
  xs.map (false::·) ++ xs.map (true::·)

def words : ℕ → List (List Bool)
  | 0 => [[]]
  | n+1 => wordsStep (words n)

@[simp] lemma mem_words (n : ℕ) (bs : List Bool) : bs∈words n ↔ bs.length=n := by
  induction n generalizing bs with
  | zero => simp [words]
  | succ n ih =>
    cases bs with
    | nil => simp [words,wordsStep]
    | cons b bs => cases b <;> simp [words,wordsStep,ih]

@[simp] lemma length_words (n : ℕ) : (words n).length=2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [words,wordsStep,ih,pow_succ]; omega

lemma bool_list_size (bs : List Bool) : (treeEncode bs).size≤4*bs.length+1 := by
  induction bs with
  | nil => simp [DataTree.size]
  | cons b bs ih => cases b <;> simp_all [DataTree.size] <;> omega

lemma words_size (n : ℕ) : (treeEncode (words n)).size≤1+2^n*(4*n+2) := by
  rw [treeEncode_list_size]
  apply Nat.add_le_add_left
  have h := list_sum_map_le (words n) (fun a => (treeEncode a).size+1) (4*n+2) (by
    intro a ha
    have he := (mem_words n a).mp ha
    have hb := bool_list_size a
    omega)
  simpa using h

def PolyProgram.wordsStep : PolyProgram (List (List Bool)) (List (List Bool)) wordsStep := by
  let F := ((PolyProgram.const false).pair (PolyProgram.id (List Bool))).comp (PolyProgram.cons Bool)
  let T := ((PolyProgram.const true).pair (PolyProgram.id (List Bool))).comp (PolyProgram.cons Bool)
  exact (F.map.pair T.map).comp (PolyProgram.append (List Bool))

lemma fold_wordsStep (xs : List Bool) (n : ℕ) :
    xs.foldl (fun s _ => wordsStep s) (words n)=words (n+xs.length) := by
  induction xs generalizing n with
  | nil => simp
  | cons b xs ih =>
    change xs.foldl (fun s _ => wordsStep s) (words (n+1)) = _
    rw [ih]
    congr 1
    simp only [List.length_cons]
    omega

@[simp] lemma TreeProgram.congr_time {α β : Type} [TreeCodec α] [TreeCodec β]
    {f g : α → β} (P : TreeProgram α β f) (h : ∀ x, f x=g x) :
    (P.congr h).time=P.time := by
  cases funext h
  rfl

def TreeProgram.words : TreeProgram ℕ (List (List Bool)) Complexity.words := by
  let P := (TreeProgram.snd Bool (List (List Bool))).comp PolyProgram.wordsStep.program
  let I := PolyProgram.ticks.program.pair (TreeProgram.const ([[]]:List (List Bool)))
  refine (I.comp P.foldl).congr ?_
  intro n
  change (List.replicate n false).foldl (fun s _ => Complexity.wordsStep s) (Complexity.words 0)=_
  simp only [fold_wordsStep,List.length_replicate,Nat.zero_add]

lemma word_stage_size {xs ys zs : List Bool} (n : ℕ) (he : ys++zs=xs) (hn : xs.length=n) :
    (treeEncode (zs,words ys.length)).size ≤ 10*(n+1)*2^n := by
  have hy : ys.length≤n := by have := congrArg List.length he; simp at this; omega
  have hz : zs.length≤n := by have := congrArg List.length he; simp at this; omega
  have hpow : 2^ys.length≤2^n := Nat.pow_le_pow_right (by omega) hy
  have h1 : 1≤2^n := Nat.one_le_two_pow
  have hs := words_size ys.length
  have hb := bool_list_size zs
  simp only [treeEncode_pair,DataTree.size]
  have hm : 2^ys.length*(4*ys.length+2)≤2^n*(4*n+2) := by gcongr
  nlinarith

lemma TreeProgram.words_bound : ∃ (C E : ℕ), ∀ n : ℕ,
    TreeProgram.words.time n ≤ C * (n+1)^E * 2^(E*n) := by
  let P := (TreeProgram.snd Bool (List (List Bool))).comp PolyProgram.wordsStep.program
  let Q := (PolyProgram.snd Bool (List (List Bool))).comp PolyProgram.wordsStep
  have hP : Q.program=P := rfl
  let E := Q.degree+3
  let C := 1000+100*Q.coefficient*11^Q.degree
  refine ⟨C,E,?_⟩
  intro n
  let X := (n+1)*2^n
  have hx : 1≤X := by dsimp [X]; exact Nat.mul_pos (by omega) (by positivity)
  have hw : P.foldWork (List.replicate n false) (Complexity.words 0) ≤
      (n+1)*(10*(10*X+1)+Q.coefficient*(11*X)^Q.degree+1) := by
    refine (TreeProgram.foldWork_prefix P _ _ (10*X) (Q.coefficient*(11*X)^Q.degree) ?_ ?_).trans ?_
    · intro ys zs he
      change (treeEncode (zs,ys.foldl (fun s _ => wordsStep s) (Complexity.words 0))).size ≤ _
      rw [fold_wordsStep,Nat.zero_add]
      simpa only [X,Nat.mul_assoc] using word_stage_size n he (List.length_replicate ..)
    · intro ys a zs he
      rw [← hP]
      apply (Q.bound _).trans
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      have h := word_stage_size n he (List.length_replicate ..)
      change (treeEncode (a,ys.foldl (fun s _ => wordsStep s) (Complexity.words 0))).size+1 ≤ _
      rw [fold_wordsStep,Nat.zero_add]
      have hta := (treeEncode a).size_pos
      simp only [treeEncode_pair,treeEncode_cons,DataTree.size] at h ⊢
      change _ ≤ 11*X
      have hX : 10*(n+1)*2^n=10*X := by dsimp [X]; ring
      rw [hX] at h
      omega
    · simp
  have ho := words_size n
  have hinit : (PolyProgram.ticks.program.pair (TreeProgram.const ([[]]:List (List Bool)))).time n ≤
      20*(n+1) := by
    simp [PolyProgram.ticks, PolyProgram.expr, PolyProgram.of_linear,
      TreeProgram.pair, TreeProgram.const, TExpr.cost, DataTree.size]
    omega
  have ht : TreeProgram.words.time n ≤
      20*(n+1)+(n+1)*(10*(10*X+1)+Q.coefficient*(11*X)^Q.degree+1)+1+2^n*(4*n+2)+4 := by
    simp only [TreeProgram.words, TreeProgram.congr_time]
    change (PolyProgram.ticks.program.pair (TreeProgram.const ([[]]:List (List Bool)))).time n +
      (P.foldWork (List.replicate n false) (Complexity.words 0) +
        (treeEncode (([]:List Bool), (List.replicate n false).foldl
          (fun s _ => wordsStep s) (Complexity.words 0))).size + 1) + 1 ≤ _
    rw [fold_wordsStep,List.length_replicate,Nat.zero_add]
    simp only [treeEncode_pair,treeEncode_nil,DataTree.size]
    omega
  have hnX : n+1≤X := by dsimp [X]; exact Nat.le_mul_of_pos_right _ (by positivity)
  have hpow : X^Q.degree ≤ X^(Q.degree+2) := Nat.pow_le_pow_right hx (by omega)
  have hpow1 : X≤X^(Q.degree+2) := by
    simpa using Nat.pow_le_pow_right hx (show 1≤Q.degree+2 by omega)
  have hxE : X^(Q.degree+2)*X = X^E := by dsimp [E]; rw [pow_succ]; congr 1
  have hbig : TreeProgram.words.time n ≤ C*X^E := by
    let Y := X^(Q.degree+2)
    let A := Q.coefficient*11^Q.degree
    have hY : 1≤Y := Nat.one_le_pow _ _ hx
    have hq : Q.coefficient*(11*X)^Q.degree ≤ A*Y := by
      rw [mul_pow]; dsimp only [A,Y]
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (Q.coefficient*11^Q.degree) hpow
    have hn : 2^n*(4*n+2)≤6*X := by
      dsimp [X]
      calc
        _ ≤ 2^n*(6*(n+1)) := Nat.mul_le_mul_left _ (by omega)
        _ = _ := by ring
    have hinner : 10*(10*X+1)+Q.coefficient*(11*X)^Q.degree+1 ≤ (111+A)*Y := by
      have h100 : 100*X≤100*Y := Nat.mul_le_mul_left 100 hpow1
      nlinarith only [h100,hY,hq]
    have houter : (n+1)*(10*(10*X+1)+Q.coefficient*(11*X)^Q.degree+1) ≤ X*((111+A)*Y) :=
      Nat.mul_le_mul hnX hinner
    have hmore : 20*(n+1)+1+2^n*(4*n+2)+4 ≤ 40*X*Y := by
      have hh : X≤X*Y := Nat.le_mul_of_pos_right X hY
      nlinarith only [hnX,hn,hx,hh]
    calc
      _ ≤ (40*X*Y)+X*((111+A)*Y) := by omega
      _ ≤ (1000+100*A)*(Y*X) := by nlinarith [Nat.zero_le (A*X*Y)]
      _ = C*X^E := by dsimp only [C,A,Y]; rw [← hxE]; ring
  apply hbig.trans
  dsimp only [X]
  rw [mul_pow, ← pow_mul]
  rw [show n*E=E*n by exact Nat.mul_comm _ _]
  exact le_of_eq (by ring)

end ParityWL.Complexity

end OAI
