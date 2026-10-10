import OAI.Combinatorics.ParityLifts.SparsePost

namespace OAI

namespace ParityWL.Complexity

noncomputable def normalizeProgram : PolyProgram (List Bool) BitFormula
    (fun bs => minimizeList (parseFormula bs)) :=
  PolyProgram.parseFormula.comp (PolyProgram.minimizeList BitLiteral)

noncomputable def satCode (p : FCode) : FCode := .seq normalizeProgram.program.code p

lemma normalize_run {N : ℕ} (F : Formula N) :
    BEval normalizeProgram.program.code (treeEncode (encodeFormula F))
      (normalizeProgram.program.time (encodeFormula F)) (treeEncode (minimizeList F.bitList)) := by
  rw [Formula.bitList_parse]
  exact normalizeProgram.program.run (encodeFormula F)

lemma poly_bit_input_bound {α : Type} [TreeCodec α] {f : List Bool → α}
    (P : PolyProgram (List Bool) α f) :
    ∃ A : ℝ, 0<A ∧ ∀ bs, (P.program.time bs : ℝ) ≤ A*(bs.length+1 : ℝ)^P.degree := by
  refine ⟨(P.coefficient*6^P.degree+1 : ℕ),by positivity,?_⟩
  intro bs
  have hsz : (treeEncode bs).size+1 ≤ 6*(bs.length+1) := by
    have := treeEncode_bits_size bs
    omega
  have hb := (P.bound bs).trans (Nat.mul_le_mul_left P.coefficient (Nat.pow_le_pow_left hsz _))
  rw [mul_pow] at hb
  have h : P.program.time bs ≤ (P.coefficient*6^P.degree+1)*(bs.length+1)^P.degree := by
    nlinarith [Nat.one_le_pow P.degree (bs.length+1) (by omega)]
  exact_mod_cast h

lemma decision_numeric_bound (D A B a : ℝ) (d L N : ℕ) (T R s : ℝ)
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hT0 : 0 ≤ T) (hR0 : 0 ≤ R)
    (hT : T ≤ A*(L+1 : ℝ)^d) (hR : R ≤ B*2^(a*N))
    (hs : s ≤ D*(T+R+2)^2+44*L+20) :
    s ≤ (D*(A+B+2)^2+64)*(L+1 : ℝ)^(2*d+2)*2^((2*a)*N) := by
  let X : ℝ := (L+1 : ℝ)^(d+1)*2^(a*N)
  have hL : (1 : ℝ) ≤ L+1 := by have := Nat.cast_nonneg (α:=ℝ) L; linarith
  have hpow : (1 : ℝ) ≤ 2^(a*N) := Real.one_le_rpow (by norm_num) (by positivity)
  have hXp : (1 : ℝ) ≤ (L+1 : ℝ)^(d+1) := one_le_pow₀ hL
  have hX : 1 ≤ X := by dsimp only [X]; nlinarith
  have hLp : (L+1 : ℝ)^d ≤ X := by
    apply (pow_le_pow_right₀ hL (by omega : d ≤ d+1)).trans
    exact le_mul_of_one_le_right (by positivity) hpow
  have hExp : 2^(a*N) ≤ X := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hL)
  have hLX : (L : ℝ) ≤ X := by
    calc
      _ ≤ (L+1 : ℝ)^1 := by simp
      _ ≤ (L+1 : ℝ)^(d+1) := pow_le_pow_right₀ hL (by omega)
      _ ≤ X := le_mul_of_one_le_right (by positivity) hpow
  have hb : T+R+2 ≤ (A+B+2)*X := by
    nlinarith [mul_le_mul_of_nonneg_left hLp hA,mul_le_mul_of_nonneg_left hExp hB]
  have hb2 := pow_le_pow_left₀ (by positivity : 0 ≤ T+R+2) hb 2
  have he2 : ((2 : ℝ)^(a*N))^2=2^((2*a)*N) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    ring
  have he : X^2=(L+1 : ℝ)^(2*d+2)*2^((2*a)*N) := by
    dsimp only [X]
    rw [mul_pow,←pow_mul,he2]
    congr 2
    omega
  rw [mul_pow] at hb2
  calc
    s ≤ (D*(A+B+2)^2+64)*X^2 := by
      nlinarith [mul_le_mul_of_nonneg_left hb2 hD]
    _ = _ := by rw [he]; ring

/-- The input polynomial degree is fixed once for the parser/compiler, independently
of the sparsification threshold, target dimension, and the supplied WL machine. -/
lemma sat_code_rate (p : FCode) (R : ℕ → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hR : ExpBound R r)
    (hp : ∀ {N : ℕ} (F : Formula N), ∃ b,
      RBEval p (treeEncode (minimizeList F.bitList)) (R N) (treeEncode b) ∧
      (b=true↔F.Satisfiable)) :
    ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧
      SATTimeBound (satCode p).decision (fun N L =>
        C*(L+1 : ℝ)^(2*normalizeProgram.degree+2)*2^((2*r+ε)*N)) := by
  intro ε hε
  obtain ⟨A,hA,hpre⟩ := poly_bit_input_bound normalizeProgram
  obtain ⟨B,hB,hpost⟩ := hR.absorb (ε/2) (by positivity)
  let D : ℝ := 500*((satCode p).factor+2 : ℝ)*((satCode p).depth+2 : ℝ)
  let C := D*(A+B+2)^2+64
  refine ⟨C,by dsimp [C,D]; positivity,?_⟩
  intro N F
  obtain ⟨b,hb,he⟩ := hp F
  have hrun := (normalize_run F).real.seq hb
  obtain ⟨s,hs,hcost⟩ := hrun.decision
  refine ⟨s,b,hs,he,?_⟩
  have hcost' : (s : ℝ) ≤ D*((normalizeProgram.program.time (encodeFormula F) : ℝ)+R N+2)^2+
      44*(encodeFormula F).length+20 := by
    convert hcost using 1
    dsimp only [D,satCode]
    ring
  have hh := decision_numeric_bound D A B (r+ε/2) normalizeProgram.degree
    (encodeFormula F).length N (normalizeProgram.program.time (encodeFormula F)) (R N) s
    (by dsimp [D]; positivity) hA.le hB.le (by positivity) (Nat.cast_nonneg _) (hR.1 N)
    (hpre (encodeFormula F)) (hpost N) hcost'
  rw [show 2*(r+ε/2)=2*r+ε by ring] at hh
  exact hh

end ParityWL.Complexity

end OAI
