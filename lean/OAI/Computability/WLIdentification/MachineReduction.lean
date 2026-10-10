import OAI.Computability.WLIdentification.MachineCells

namespace OAI

namespace WLIdentification

namespace Machine
open BinaryAddress

def actionConfig (M : Machine) (c : Configuration M) : Configuration M :=
  let a := M.action c.state (c.tape c.head)
  { state := a.1
    head := c.head + a.2.2.displacement
    tape := Function.update c.tape c.head a.2.1 }

theorem step_action (M : Machine) (c : Configuration M) : step M c = M.actionConfig c := by
  by_cases h : c.state = 1 ∨ c.state = 2
  · simp only [step, h, ite_true, actionConfig, action_halt M _ _ h,
      Move.displacement, add_zero, Function.update_eq_self]
  · simp only [step, h, ite_false, actionConfig, action]

theorem displacement_bound (m : Move) : -1 ≤ m.displacement ∧ m.displacement ≤ 1 := by
  cases m <;> simp [Move.displacement]

@[simp] theorem run_succ (M : Machine) (w : Word) (t : ℕ) :
    run M w (t + 1) = step M (run M w t) := Function.iterate_succ_apply' _ _ _

theorem head_bound (M : Machine) (w : Word) (t : ℕ) :
    -(t : ℤ) ≤ (run M w t).head ∧ (run M w t).head ≤ t := by
  induction t with
  | zero => simp [run, initial]
  | succ t ih =>
    rw [run_succ, step_action]
    have hm := displacement_bound (M.action (run M w t).state ((run M w t).tape (run M w t).head)).2.2
    dsimp only [actionConfig]
    push_cast
    omega

structure RingAgrees (M : Machine) (d T : ℕ) (c : Configuration M) (q : M.TapeConfig (Bits d)) : Prop where
  state : c.state = q.state
  head : residue d c.head = q.head
  tape : ∀ z : ℤ, -(T : ℤ) ≤ z ∧ z ≤ T → c.tape z = q.tape (residue d z)

theorem initial_ringAgrees (M : Machine) {d T : ℕ} (w : Word)
    (hsize : 2 * T < 2 ^ d) (hm : w.length ≤ T) :
    RingAgrees M d T (initial M w) (M.ringInitial w) := by
  refine ⟨rfl, residue_zero d, ?_⟩
  intro z hz
  by_cases h0 : 0 ≤ z
  · have hlt : z < (2 ^ d : ℕ) := by omega
    simp only [initial, h0, ite_true, ringInitial, value_residue_of_nonneg h0 hlt]
  · have hneg : z < 0 := by omega
    have hgt : -(2 ^ d : ℕ) < z := by omega
    have hv := value_residue_negative hgt hneg
    have hn : w.length ≤ value (residue d z) := by omega
    simp only [initial, h0, ite_false, ringInitial, List.getElem?_eq_none hn]
    rfl

variable {M : Machine} {d T : ℕ}

theorem RingAgrees.step {c : Configuration M} {q : M.TapeConfig (Bits d)}
    (h : RingAgrees M d T c q) (hsize : 2 * T < 2 ^ d)
    (hc : -(T : ℤ) ≤ c.head ∧ c.head ≤ T) :
    RingAgrees M d T (step M c) (q.advance (rotation d)) := by
  have ha : M.action c.state (c.tape c.head) = M.action q.state (q.tape q.head) := by
    rw [h.state, h.tape _ hc, h.head]
  rw [step_action]
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg Prod.fst ha
  · change residue d (c.head + (M.action c.state (c.tape c.head)).2.2.displacement) = _
    rw [ha]
    cases hm : (M.action q.state (q.tape q.head)).2.2 with
    | left => simp only [TapeConfig.advance, hm, Move.displacement,
        ← sub_eq_add_neg, residue_sub_one, h.head]
    | stay => simp only [TapeConfig.advance, hm, Move.displacement, add_zero, h.head]
    | right => simp only [TapeConfig.advance, hm, Move.displacement, residue_add_one, h.head]
  · intro z hz
    change Function.update c.tape c.head (M.action c.state (c.tape c.head)).2.1 z =
      Function.update q.tape q.head (M.action q.state (q.tape q.head)).2.1 (residue d z)
    rw [ha]
    by_cases he : z = c.head
    · subst z
      rw [h.head, Function.update_self, Function.update_self]
    · have hr : residue d z ≠ q.head := by
        intro hr
        apply he
        exact residue_injective_window hsize hz hc (hr.trans h.head.symm)
      rw [Function.update_of_ne he, Function.update_of_ne hr]
      exact h.tape z hz

theorem run_ringAgrees (M : Machine) {d T : ℕ} (w : Word)
    (hsize : 2 * T < 2 ^ d) (hm : w.length ≤ T) (t : ℕ) (ht : t ≤ T) :
    RingAgrees M d T (run M w t) (M.ringRun w t) := by
  induction t with
  | zero => exact initial_ringAgrees M w hsize hm
  | succ t ih =>
    have hhead := head_bound M w t
    rw [run_succ, ringRun_succ]
    exact (ih (by omega)).step hsize (by constructor <;> omega)

theorem ringRun_halted (M : Machine) {d : ℕ} (w : Word) (t u : ℕ)
    (h : (@ringRun M d w t).state = 1 ∨ (@ringRun M d w t).state = 2) :
    @ringRun M d w (t + u) = M.ringRun w t := by
  induction u with
  | zero => simp only [add_zero]
  | succ u ih =>
    rw [← Nat.add_assoc, ringRun_succ, ih]
    exact TapeConfig.advance_halted _ _ h

theorem compiledCircuit_run (M : Machine) {d T : ℕ} (w : Word)
    (hsize : 2 * T < 2 ^ d) (hT : 0 < T) (hm : w.length ≤ T)
    {t : ℕ} (ht : t ≤ T) (hhalt : Halted (run M w t)) :
    (M.compiledCircuit d w).Accepted ↔ (run M w t).state = 1 := by
  have hd : 2 < 2 ^ d := by omega
  have hi : inputSpan w < 2 ^ d := by dsimp only [inputSpan]; omega
  rw [compiledCircuit_ringRun M hd w hi]
  have hag := run_ringAgrees M w hsize hm t ht
  have hr : (@ringRun M d w t).state = 1 ∨ (@ringRun M d w t).state = 2 := by
    rw [← hag.state]
    exact hhalt
  have ht' : t + (2 ^ d - 1 - t) = 2 ^ d - 1 := by omega
  rw [← ht', ringRun_halted M w t _ hr]
  rw [hag.state]

end Machine

namespace AffineBlocks
variable {C B : Type} [Fintype C] [DecidableEq C] [Fintype B]
theorem graph_nonempty (D : AffineBlocks C B) (c : C) (beta : B → Bit) :
    0 < (D.graph beta).order := by
  classical
  change 0 < Fintype.card (LeafVertex (tagSize D.colorNat))
  exact Fintype.card_pos_iff.mpr ⟨.inl (.inl (c, 0))⟩
end AffineBlocks

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} [Fintype P] [Fintype E] [Fintype Z] [Fintype T]
    (C : ProductCircuit r P E Z T)

/-- The fixed-width output construction, with private-wire length absorbed. -/
noncomputable def outputGraph (hr : 32 ≤ r) : Graph :=
  (((C.schemas.layout (4 * (r + 1) - 1)).affine (by omega)).graph 0)

theorem outputGraph_correct (hr : 32 ≤ r) : WLdim (C.outputGraph hr) ≤ r ↔ C.Accepted :=
  C.dimension_iff_accepted hr (4 * (r + 1) - 1) (by omega)

theorem outputGraph_nonempty (hr : 32 ≤ r) : 0 < (C.outputGraph hr).order := by
  classical
  let i : Fin r := ⟨0, by omega⟩
  let R := C.schemas.layout (4 * (r + 1) - 1)
  let h : R.HName := ⟨.inl (.primary none), i, ⟨false, by simp [R, ComparisonSchemas.layout,
    ComparisonSchemas.layoutLabels]⟩, ⟨false, by simp [R, ComparisonSchemas.layout,
    ComparisonSchemas.layoutLabels]⟩⟩
  let c : R.Coordinate := .inl ⟨h, ⟨0, by exact Nat.zero_lt_one⟩⟩
  exact (R.affine (by omega)).graph_nonempty c 0

end ProductCircuit

namespace Machine

def paddedExponent (C e m : ℕ) : ℕ := C * (m + 1) ^ e + m + 32

def addressWidth (C e m : ℕ) : ℕ := paddedExponent C e m + 2

def reductionDimension (C e m : ℕ) : ℕ := addressWidth C e m + addressWidth C e m

theorem reductionDimension_ge (C e m : ℕ) : 68 ≤ reductionDimension C e m := by
  simp only [reductionDimension, addressWidth, paddedExponent]
  omega

theorem compiledCircuit_decides {L : BinaryLanguage} {M : Machine} {C e : ℕ}
    (h : DecidesWithin M L (fun m => 2 ^ (C * (m + 1) ^ e))) (w : Word) :
    (M.compiledCircuit (addressWidth C e w.length) w).Accepted ↔ w ∈ L := by
  obtain ⟨t, ht, hhalt, hacc⟩ := h w
  let p := paddedExponent C e w.length
  have hp : C * (w.length + 1) ^ e ≤ p := by dsimp [p, paddedExponent]; omega
  have hm : w.length ≤ 2 ^ p := by
    have hpow : 2 ^ w.length ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) (by dsimp [p, paddedExponent]; omega)
    exact (le_of_lt (Nat.lt_two_pow_self (n := w.length))).trans hpow
  have ht' : t ≤ 2 ^ p := ht.trans (Nat.pow_le_pow_right (by decide) hp)
  have hsize : 2 * 2 ^ p < 2 ^ addressWidth C e w.length := by
    change 2 * 2 ^ p < 2 ^ (p + 2)
    rw [pow_add]
    have : 0 < 2 ^ p := by positivity
    norm_num
    omega
  exact (M.compiledCircuit_run w hsize (by positivity) hm ht' hhalt).trans hacc

noncomputable def reductionGraph (M : Machine) (C e : ℕ) (w : Word) : Graph := by
  classical
  exact (M.compiledCircuit (addressWidth C e w.length) w).outputGraph
    (by change 32 ≤ reductionDimension C e w.length; have := reductionDimension_ge C e w.length; omega)

theorem reductionGraph_correct {L : BinaryLanguage} {M : Machine} {C e : ℕ}
    (h : DecidesWithin M L (fun m => 2 ^ (C * (m + 1) ^ e))) (w : Word) :
    WLdim (M.reductionGraph C e w) ≤ reductionDimension C e w.length ↔ w ∈ L := by
  classical
  exact (ProductCircuit.outputGraph_correct _ _).trans (compiledCircuit_decides h w)

theorem reductionGraph_nonempty (M : Machine) (C e : ℕ) (w : Word) :
    0 < (M.reductionGraph C e w).order := by
  classical
  exact ProductCircuit.outputGraph_nonempty _ _

end Machine

/-- Canonical most-significant-first binary representation. -/
def binaryWord (n : ℕ) : Word := n.bits.reverse

theorem binaryValue_append_bit (l : Word) (b : Bool) :
    binaryValue (l ++ [b]) = 2 * binaryValue l + if b then 1 else 0 := by
  simp [binaryValue, List.foldl_append]

@[simp] theorem binaryValue_binaryWord (n : ℕ) : binaryValue (binaryWord n) = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [binaryWord, Nat.bits_append_bit n b hn, List.reverse_cons, binaryValue_append_bit]
    change 2 * binaryValue (binaryWord n) + (if b then 1 else 0) = Nat.bit b n
    rw [ih, Nat.bit_val]
    cases b <;> rfl

theorem binaryWord_leading {n : ℕ} (hn : 0 < n) : ∃ t, binaryWord n = true :: t := by
  induction n using Nat.binaryRec' with
  | zero => omega
  | bit b n hb ih =>
    by_cases hz : n = 0
    · subst n
      obtain rfl := hb rfl
      exact ⟨[], rfl⟩
    · obtain ⟨t, ht⟩ := ih (by omega)
      refine ⟨t ++ [b], ?_⟩
      rw [binaryWord, Nat.bits_append_bit n b hb, List.reverse_cons]
      change binaryWord n ++ [b] = _
      rw [ht]
      rfl

/-- The order header is genuinely uniquely parsable, including order zero. -/
theorem unary_frame_injective {n m : ℕ} {s t : Word}
    (h : List.replicate n true ++ false :: s = List.replicate m true ++ false :: t) :
    n = m ∧ s = t := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simpa [List.replicate_succ] using h
    | succ m => simp [List.replicate_succ] at h
  | succ n ih =>
    cases m with
    | zero => simp [List.replicate_succ] at h
    | succ m =>
      have h' : List.replicate n true ++ false :: s = List.replicate m true ++ false :: t := by
        simpa [List.replicate_succ] using h
      obtain ⟨hn, ht⟩ := ih h'
      exact ⟨congrArg Nat.succ hn, ht⟩

private theorem split_matrix_length (n m : ℕ) (f : Fin n → Fin m → Bool) :
    ((List.ofFn fun i => List.ofFn (f i)).flatten).length = n * m := by
  simp [List.length_flatten, List.map_ofFn, Function.comp_def]

@[simp] theorem matrixWord_length (G : Graph) : (matrixWord G).length = G.order * G.order :=
  split_matrix_length _ _ _

private theorem split_matrix_injective (n m : ℕ) (f g : Fin n → Fin m → Bool)
    (h : (List.ofFn fun i => List.ofFn (f i)).flatten =
      (List.ofFn fun i => List.ofFn (g i)).flatten) : f = g := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    simp only [List.ofFn_succ, List.flatten_cons] at h
    obtain ⟨hh, ht⟩ := List.append_inj h (by simp)
    have hh' : f 0 = g 0 := List.ofFn_inj.mp hh
    have ht' := ih (fun i => f i.succ) (fun i => g i.succ) ht
    funext i
    refine Fin.cases hh' (fun i => congrFun ht' i) i

@[ext (iff := false)] theorem Graph.ext (G H : Graph) (hn : G.order = H.order)
    (he : ∀ i j, G.edge i j = H.edge (i.cast hn) (j.cast hn)) : G = H := by
  cases G with | mk n e hs hl =>
    cases H with | mk m f ht hm =>
      simp only at hn
      subst m
      have : e = f := by funext i j; exact he i j
      subst f
      rfl

theorem inputWord_injective {G H : Graph} {u v : Word}
    (h : inputWord G u = inputWord H v) : G = H ∧ u = v := by
  have hh : List.replicate G.order true ++ false :: (matrixWord G ++ u) =
      List.replicate H.order true ++ false :: (matrixWord H ++ v) := by
    simpa only [inputWord, List.append_assoc, List.cons_append, List.nil_append] using h
  obtain ⟨hn, hs⟩ := unary_frame_injective hh
  obtain ⟨hm, hv⟩ := List.append_inj hs (by simp only [matrixWord_length, hn])
  refine ⟨?_, hv⟩
  apply Graph.ext _ _ hn
  cases G with | mk n e hsym hl =>
    cases H with | mk m f hsym' hl' =>
      simp only at hn
      subst m
      have he := split_matrix_injective n n e f hm
      subst f
      intro i j
      rfl

/-- Correctness of serialization includes exclusion of every malformed alternative parse. -/
theorem inputWord_mem_iff (G : Graph) (hn : 0 < G.order) (k : ℕ) (hk : 0 < k) :
    inputWord G (binaryWord k) ∈ dimensionLanguage ↔ WLdim G ≤ k := by
  constructor
  · rintro ⟨H, bits, _, _, _, he, hw⟩
    obtain ⟨rfl, rfl⟩ := inputWord_injective he
    simpa [List.replicate_succ] using hw
  · intro h
    exact ⟨G, binaryWord k, hn, binaryWord_leading hk, by simpa, rfl, by simpa⟩

namespace Machine

/-- The literal binary output of the compressed-computation graph reduction.
The separate cost obligation is a genuine `ComputesWithin` statement. -/
noncomputable def reductionWord (M : Machine) (C e : ℕ) (w : Word) : Word :=
  inputWord (M.reductionGraph C e w) (binaryWord (reductionDimension C e w.length))

theorem reductionWord_correct {L : BinaryLanguage} {M : Machine} {C e : ℕ}
    (h : DecidesWithin M L (fun m => 2 ^ (C * (m + 1) ^ e))) (w : Word) :
    w ∈ L ↔ M.reductionWord C e w ∈ dimensionLanguage := by
  rw [reductionWord, inputWord_mem_iff _ (M.reductionGraph_nonempty C e w) _
    (by have := reductionDimension_ge C e w.length; omega), reductionGraph_correct h w]

end Machine

end WLIdentification

end OAI
