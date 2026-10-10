import OAI.Computability.MatchingCount.RawInput

namespace OAI

section

namespace BinaryMatching.Raw.InputData
open StackCode Algorithm Optimize

def powerBits (k : ℕ) : List Bool := List.replicate k false++[true]
lemma powerBits_eq (k : ℕ) : powerBits k=(2^k).bits := by
  induction k with
  | zero => simp [powerBits]
  | succ k ih =>
    rw [pow_succ,Nat.mul_comm,Nat.bit0_bits (2^k) (by positivity)]
    simpa only [powerBits,List.replicate_succ,List.cons_append] using congrArg (List.cons false) ih
@[fun_prop] theorem powerBits_poly : Poly powerBits := by unfold powerBits; fun_prop

def smallSolve (z : Data) : List Bool :=
  if z.1=0 then [true] else
  if z.1%2=1 then [] else
  if z.1=2 then multiplicityBits z.2 0 1 else
  let r := result (parameters z)
  if r < -10*(z.1:ℤ) then [] else powerBits (r-5*(z.1:ℤ)).toNat

def smallEstimate (G : Input) : ℕ :=
  if G.n=0 then 1 else
  if G.n%2=1 then 0 else
  if G.n=2 then rawMultiplicity G 0 1 else integralEstimate G
lemma smallSolve_repr (G : Input) : smallSolve (G.n,G.records.map repr)=(smallEstimate G).bits := by
  unfold smallSolve smallEstimate
  dsimp only
  by_cases hn0 : G.n=0
  · simp only [hn0,ite_true]; rfl
  simp only [hn0,ite_false]
  by_cases ho : G.n%2=1
  · simp only [ho,ite_true]; rfl
  simp only [ho,ite_false]
  by_cases hn2 : G.n=2
  · simpa only [hn2,ite_true] using multiplicityBits_repr G 0 1
  simp only [hn2,ite_false]
  have he : Even G.n := Nat.even_iff.mpr (by omega)
  have hn : 2≤G.n := by omega
  rw [parameters_repr,result_rep G hn he]
  dsimp only [integralEstimate]
  split_ifs
  · rfl
  · exact powerBits_eq _
@[fun_prop] theorem smallSolve_poly : Poly smallSolve := by
  have h : Poly (fun z : Data => if decide (z.1=0) then [true] else
      if decide (z.1%2=1) then [] else if decide (z.1=2) then multiplicityBits z.2 0 1 else
      if decide (result (parameters z) < -10*(z.1:ℤ)) then [] else
        powerBits (result (parameters z)-5*(z.1:ℤ)).toNat) := by fun_prop
  exact h.congr (fun z => by simp only [smallSolve,decide_eq_true_eq])

def solve (z : Data) : List Bool := if 2*z.2.length<z.1 then [] else smallSolve z

def sparseEstimate (G : Input) : ℕ := if 2*G.records.length<G.n then 0 else smallEstimate G
lemma sparseEstimate_correct (G : Input) :
    sparseEstimate G≤count G ∧ count G≤2^(9*G.n)*sparseEstimate G ∧ (sparseEstimate G=0 ↔ count G=0) := by
  unfold sparseEstimate
  split_ifs with hguard
  · have hz := count_zero_of_uncovered G (lt_of_le_of_lt (covered_card_le_records G) hguard)
    simp [hz]
  · unfold smallEstimate
    split_ifs with hn0 hodd hn2
    · rw [count_zero_vertices G hn0,hn0]
      norm_num
    · rw [count_odd_vertices G (Nat.odd_iff.mpr hodd)]
      simp
    · rw [count_two_vertices G hn2]
      refine ⟨le_rfl,?_,Iff.rfl⟩
      exact Nat.le_mul_of_pos_left _ (by positivity)
    · have hn : 4≤G.n := by omega
      have he : Even G.n := Nat.even_iff.mpr (by omega)
      rw [integralEstimate_eq G (by omega)]
      exact estimate_correct G hn he

lemma sparseEstimate_eq_approximate (G : Input) : sparseEstimate G=approximate G := by
  unfold sparseEstimate
  split_ifs with hg
  · symm
    exact (approximate_correct G).2.2.mpr
      (count_zero_of_uncovered G (lt_of_le_of_lt (covered_card_le_records G) hg))
  · unfold smallEstimate approximate
    simp only [Nat.odd_iff]
    split_ifs with hn0 ho hn2 hc
    · rfl
    · rfl
    · rfl
    · rw [integralEstimate_eq G (by omega)]
      exact (estimate_correct G (by omega) (Nat.even_iff.mpr (by omega))).2.2.mpr
        (count_zero_of_uncovered G hc)
    · exact integralEstimate_eq G (by omega)

lemma solve_decoded (G : Input) :
    solve (decode (G.n.bits,G.records.map Parse.recordRepr))=(sparseEstimate G).bits := by
  unfold solve sparseEstimate
  rw [decode_length,List.length_map,decode_n_encoded]
  by_cases hg : 2*G.records.length<G.n
  · rw [ite_eq_left hg,ite_eq_left (by omega)]
    rfl
  · rw [ite_eq_right hg,ite_eq_right (by omega),decode_encoded G (by omega),smallSolve_repr]
@[fun_prop] theorem solve_poly : Poly solve := by
  have hh : Poly (fun z : Data => if decide (2*z.2.length<z.1) then [] else smallSolve z) := by fun_prop
  exact hh.congr (fun z => by simp only [solve,decide_eq_true_eq])

def runInput (l : List Bool) : List Bool := solve (decode (Parse.input l))
lemma runInput_encoded (G : Input) : runInput (encodeInput G)=(sparseEstimate G).bits := by
  rw [runInput,Parse.input_encoded,solve_decoded]
@[fun_prop] theorem runInput_poly : Poly runInput := by unfold runInput; fun_prop

def bitAlgorithm (b : Bits) : Bits := ⟨runInput b.data⟩
theorem bitAlgorithm_poly : Poly bitAlgorithm := by
  change Poly (fun b : Bits => Bits.mk (runInput b.data))
  exact Poly.comp Bits.mk (fun b : Bits => runInput b.data) Poly.bitsEncode
    (Poly.comp runInput Bits.data runInput_poly Poly.bitsDecode)

noncomputable def binaryRoutine : Routine Bits.data Bits.data bitAlgorithm := bitAlgorithm_poly.routine
lemma bitAlgorithm_encoded (G : Input) :
    (bitAlgorithm ⟨encodeInput G⟩).data=(sparseEstimate G).bits := by
  change runInput (encodeInput G)=(sparseEstimate G).bits
  exact runInput_encoded G

noncomputable def countingRoutine : Routine encodeInput Nat.bits sparseEstimate :=
  binaryRoutine.reindex encodeInput Nat.bits sparseEstimate (fun G => Bits.mk (encodeInput G))
    (fun _ => rfl) bitAlgorithm_encoded

theorem deterministic_approximate_counting :
    ∃ A : Input → ℕ,
      ∃ machine : Turing.TM2ComputableInPolyTime encodeInput Nat.bits A,
        (∀ k, Finite (machine.tm.Γ k)) ∧
        (∃ P : Polynomial ℕ, ∀ G,(A G).bits.length≤P.eval (encodeInput G).length) ∧
        ∀ G,A G≤count G ∧ count G≤2^(9*G.n)*A G ∧ (A G=0 ↔ count G=0) := by
  refine ⟨sparseEstimate,countingRoutine.machine,countingRoutine.machine_alphabets_finite,?_,sparseEstimate_correct⟩
  refine ⟨Polynomial.X+countingRoutine.time,?_⟩
  intro G
  simpa only [Polynomial.eval_add,Polynomial.eval_X] using countingRoutine.length_bound G
end BinaryMatching.Raw.InputData

namespace BinaryMatching

theorem deterministic_approximate_counting :
    ∃ A : Input → ℕ,
      ∃ machine : Turing.TM2ComputableInPolyTime encodeInput Nat.bits A,
        (∀ k, Finite (machine.tm.Γ k)) ∧
        (∃ P : Polynomial ℕ, ∀ G,(A G).bits.length≤P.eval (encodeInput G).length) ∧
        ∀ G,A G≤count G ∧ count G≤2^(9*G.n)*A G ∧ (A G=0 ↔ count G=0) :=
  Raw.InputData.deterministic_approximate_counting
end BinaryMatching
end

end OAI
