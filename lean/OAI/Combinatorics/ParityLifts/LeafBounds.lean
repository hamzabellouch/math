import OAI.Combinatorics.ParityLifts.DegreeBits

namespace OAI

namespace ParityWL.Complexity

lemma PolyProgram.wordsOutput_degree_form (t : ℕ) [NeZero t] :
    (PolyProgram.wordsOutput t).degree=
      ((PolyProgram.choiceWithWords t).comp (PolyProgram.graphOutput t)).degree := by
  unfold PolyProgram.wordsOutput
  exact PolyProgram.congr_degree _ _
lemma PolyProgram.wordsOutput_degree (t : ℕ) [NeZero t] :
    (PolyProgram.wordsOutput t).degree=(PolyProgram.wordsOutput 1).degree := by
  rw [PolyProgram.wordsOutput_degree_form,PolyProgram.wordsOutput_degree_form]
  simp only [PolyProgram.comp_degree,PolyProgram.choiceWithWords_degree,PolyProgram.graphOutput_degree]

lemma TreeProgram.leafOutput_time (t : ℕ) [NeZero t] (ht : 0<t) (F : BitFormula) :
    (TreeProgram.leafOutput t ht).time F =
      (PolyProgram.leafPrepare t ht).program.time F +
      (TreeProgram.insertWords t).time (bitGroup t F,leafWords t F) + 1 +
      (PolyProgram.wordsOutput t).program.time (bitGroup t F,leafWords t F,Complexity.words (leafWords t F)) + 1 := by
  rfl

lemma TreeProgram.insertWords_time (t : ℕ) (x : (Fin t → BitFormula) × ℕ) :
    (TreeProgram.insertWords t).time x=TreeProgram.words.time x.2+3*(treeEncode x).size+3 := by
  simp only [TreeProgram.insertWords,TreeProgram.pair,TreeProgram.comp,TreeProgram.fst,TreeProgram.snd]
  omega

lemma tableInput_size (t : ℕ) (Q : Fin t → BitFormula) (q : ℕ) :
    (treeEncode (Q,q,words q)).size+1 ≤ 10*((treeEncode (Q,q)).size+1)*2^q := by
  have hw := words_size q
  have hpow : 1≤2^q := Nat.one_le_two_pow
  simp only [treeEncode_pair,treeEncode_nat,numTree_size,DataTree.size] at *
  nlinarith [DataTree.size_pos (treeEncode Q)]

lemma leaf_numeric_bound (A a B D W e X q p i o Z T : ℕ) (hx : 1≤X)
    (hp : p≤A*X^a) (hz : Z≤p+1) (hq : q+1≤Z)
    (hi : i≤W*(q+1)^e*2^(e*q)+4*Z+8) (ht : T≤10*Z*2^q) (ho : o≤B*T^D) :
    p+i+1+o+1 ≤ (A+4*(A+1)+(W+8)*(A+1)^e+B*(10*(A+1))^D+3)*
      X^(a*(e+D+1))*2^((e+D+1)*q) := by
  let E := e+D+1
  have he : e≤E := by dsimp [E]; omega
  have hd : D≤E := by dsimp [E]; omega
  have hZ : Z≤(A+1)*X^a := by nlinarith [Nat.one_le_pow a X hx]
  have hX (d : ℕ) (h : d≤E) : X^(a*d)≤X^(a*E) :=
    Nat.pow_le_pow_right hx (Nat.mul_le_mul_left a h)
  have htwo (d : ℕ) (h : d≤E) : 2^(d*q)≤2^(E*q) :=
    Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right q h)
  have hone : 1≤X^(a*E)*2^(E*q) := by
    have := Nat.one_le_pow (a*E) X hx
    have := Nat.one_le_two_pow (n:=E*q)
    nlinarith
  have hbase : X^a≤X^(a*E)*2^(E*q) := by
    calc
      X^a = X^(a*1) := by rw [Nat.mul_one]
      _ ≤ X^(a*E) := hX _ (by dsimp [E]; omega)
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by positivity)
  have hinter : i≤((W+8)*(A+1)^e+4*(A+1)) * (X^(a*E)*2^(E*q)) := by
    have hzpow := Nat.pow_le_pow_left (hq.trans hZ) e
    rw [mul_pow,←pow_mul] at hzpow
    have hh : (q+1)^e*2^(e*q)≤(A+1)^e*(X^(a*E)*2^(E*q)) := by
      calc
        _ ≤ ((A+1)^e*X^(a*e))*2^(e*q) := Nat.mul_le_mul_right _ hzpow
        _ ≤ ((A+1)^e*X^(a*E))*2^(E*q) := Nat.mul_le_mul
          (Nat.mul_le_mul_left _ (hX _ he)) (htwo _ he)
        _ = _ := by ring
    have hconst : 1≤(A+1)^e*(X^(a*E)*2^(E*q)) := by
      have := Nat.one_le_pow e (A+1) (by omega)
      nlinarith
    nlinarith [Nat.mul_le_mul_left W hh, Nat.mul_le_mul_left (A+1) hbase]
  have hout : o≤B*(10*(A+1))^D * (X^(a*E)*2^(E*q)) := by
    apply ho.trans
    have hztable : T≤(10*(A+1))*(X^a*2^q) := by
      calc
        _ ≤ 10*Z*2^q := ht
        _ ≤ 10*((A+1)*X^a)*2^q := by gcongr
        _ = _ := by ring
    calc
      B*T^D ≤ B*((10*(A+1))*(X^a*2^q))^D := by gcongr
      _ = B*(10*(A+1))^D*(X^(a*D)*2^(D*q)) := by
        simp only [mul_pow,←pow_mul]; rw [Nat.mul_comm q D]; ring
      _ ≤ _ := by
        apply Nat.mul_le_mul_left
        exact Nat.mul_le_mul (hX _ hd) (htwo _ hd)
  have hprep := Nat.mul_le_mul_left A hbase
  change p+i+1+o+1≤(A+4*(A+1)+(W+8)*(A+1)^e+B*(10*(A+1))^D+3)*X^(a*E)*2^(E*q)
  nlinarith

/-- All exponential work in a leaf has an absolute exponent. -/
theorem leafOutput_bound : ∃ E : ℕ, 0<E ∧ ∀ (t : ℕ) [NeZero t] (ht : 0<t), ∃ C d : ℕ,
    0<C ∧ ∀ F : BitFormula, (TreeProgram.leafOutput t ht).time F ≤
      C*((treeEncode F).size+1)^d * 2^(E*leafWords t F) := by
  obtain ⟨W,e,hw⟩ := TreeProgram.words_bound
  let D := (PolyProgram.wordsOutput 1).degree
  refine ⟨e+D+1,by omega,?_⟩
  intro t _ ht
  let P := PolyProgram.leafPrepare t ht
  let Q := PolyProgram.wordsOutput t
  have hD : Q.degree=D := PolyProgram.wordsOutput_degree t
  refine ⟨P.coefficient+4*(P.coefficient+1)+(W+8)*(P.coefficient+1)^e+Q.coefficient*(10*(P.coefficient+1))^D+3,
    P.degree*(e+D+1),by omega,?_⟩
  intro F
  rw [TreeProgram.leafOutput_time]
  apply leaf_numeric_bound
  · omega
  · exact P.bound F
  · have hz := (P.program.run F).bounds.2.1
    change (treeEncode (bitGroup t F,leafWords t F)).size≤P.program.time F at hz
    exact Nat.add_le_add_right hz 1
  · simp only [treeEncode_pair,treeEncode_nat,numTree_size,DataTree.size]
    omega
  · rw [TreeProgram.insertWords_time]
    have hh := hw (leafWords t F)
    change TreeProgram.words.time (leafWords t F)+3*(treeEncode (bitGroup t F,leafWords t F)).size+3≤_
    omega
  · exact tableInput_size t _ _
  · have hb := Q.bound (bitGroup t F,leafWords t F,words (leafWords t F))
    rw [hD] at hb
    change Q.program.time _≤Q.coefficient*_
    exact hb
end ParityWL.Complexity

end OAI
