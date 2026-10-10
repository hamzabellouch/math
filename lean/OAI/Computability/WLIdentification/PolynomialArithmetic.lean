import OAI.Computability.WLIdentification.WordArithmetic

namespace OAI

namespace WLIdentification

namespace WordExpressions
namespace Poly
variable {n : ℕ}

theorem replicate {c : (Fin n → Word) → ℕ} (hc : NatPoly c) (b : Bool) :
    Poly (fun S => List.replicate (c S) b) := by
  apply (tabulate hc (BoolPoly.const b)).congr
  intro S
  simp

theorem mapBits {w : (Fin n → Word) → Word} {p : (Fin (n+1) → Word) → Bool}
    (hw : Poly w) (hp : BoolPoly p) :
    Poly (fun S => (List.range (w S).length).map (fun i => p (Fin.snoc S (unary i)))) :=
  tabulate (NatPoly.length hw) hp

theorem append {u v : (Fin n → Word) → Word} (hu : Poly u) (hv : Poly v) :
    Poly (fun S => u S ++ v S) := by
  let p : (Fin (n+1) → Word) → Bool := fun T =>
    if (T (Fin.last n)).length < (u (T ∘ Fin.castSucc)).length then
      (u (T ∘ Fin.castSucc))[(T (Fin.last n)).length]?.getD false
    else (v (T ∘ Fin.castSucc))[(T (Fin.last n)).length-(u (T ∘ Fin.castSucc)).length]?.getD false
  have hp : BoolPoly p := by
    apply (branches
      (NatPoly.lt (NatPoly.var (Fin.last n)) (NatPoly.length (rename hu Fin.castSucc)))
      (nth (rename hu Fin.castSucc) (NatPoly.var (Fin.last n)))
      (nth (rename hv Fin.castSucc) (NatPoly.sub (NatPoly.var (Fin.last n))
        (NatPoly.length (rename hu Fin.castSucc))))).congr
    intro T
    dsimp only [p]
    by_cases hh : (T (Fin.last n)).length < (u (T ∘ Fin.castSucc)).length <;> simp [hh]
  have h := tabulate (NatPoly.add (NatPoly.length hu) (NatPoly.length hv)) hp
  apply h.congr
  intro S
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_map, List.getElem_range, p, Fin.snoc_last, unary,
    List.length_replicate, snoc_prefix, List.getElem_append]
  split
  · rename_i hh
    rw [List.getElem?_eq_getElem hh]
    rfl
  · rename_i hh
    have hv' : i-(u S).length < (v S).length := by simp only [List.length_append] at hj; omega
    rw [List.getElem?_eq_getElem hv']
    rfl

theorem reverse {w : (Fin n → Word) → Word} (hw : Poly w) : Poly (fun S => (w S).reverse) := by
  have hp := nth (rename hw Fin.castSucc)
    (NatPoly.sub (NatPoly.length (rename hw Fin.castSucc)) (NatPoly.succ (NatPoly.var (Fin.last n))))
  apply (tabulate (NatPoly.length hw) hp).congr
  intro S
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_map, List.getElem_range, Fin.snoc_last, unary, List.length_replicate,
    snoc_prefix]
  have hi' : i < (w S).length := by simpa using hj
  rw [List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some, List.getElem_reverse, Nat.sub_sub, Nat.add_comm]

theorem take {w : (Fin n → Word) → Word} {c : (Fin n → Word) → ℕ}
    (hw : Poly w) (hc : NatPoly c) : Poly (fun S => (w S).take (c S)) := by
  apply (cutOf hw (NatPoly.sub (NatPoly.length hw) hc)).congr
  intro S
  simp only [unary, List.length_replicate]
  by_cases h : c S ≤ (w S).length
  · rw [Nat.sub_sub_self h]
  · rw [show (w S).length-c S = 0 by omega, Nat.sub_zero, List.take_length,
      List.take_of_length_le (by omega)]

theorem dropPrefix {w : (Fin n → Word) → Word} {c : (Fin n → Word) → ℕ}
    (hw : Poly w) (hc : NatPoly c) : Poly (fun S => (w S).drop (c S)) := by
  have hp := nth (rename hw Fin.castSucc)
    (NatPoly.add (NatPoly.rename hc Fin.castSucc) (NatPoly.var (Fin.last n)))
  apply (tabulate (NatPoly.sub (NatPoly.length hw) hc) hp).congr
  intro S
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_map, List.getElem_range, Fin.snoc_last, unary, List.length_replicate,
    snoc_prefix, List.getElem_drop]
  rw [List.getElem?_eq_getElem (by simpa only [List.length_drop] using (show c S+i < (w S).length from by
    simp only [List.length_drop] at hj; omega))]
  rfl

end Poly
end WordExpressions

namespace WordExpressions.NatPoly
variable {n : ℕ}

theorem sum {c : (Fin n → Word) → ℕ} {f : (Fin (n+1) → Word) → ℕ}
    (hc : NatPoly c) (hf : NatPoly f) :
    NatPoly (fun S => ((List.range (c S)).map (fun i => f (Fin.snoc S (unary i)))).sum) := by
  let step : (Fin (n+2) → Word) → ℕ := fun T => (T (accum n)).length+f (T ∘ Fin.castSucc)
  have hstep : NatPoly step := add (var _) (rename hf _)
  have hs (S : Fin n → Word) (k : ℕ) : stages step S 0 k =
      ((List.range k).map (fun i => f (Fin.snoc S (unary i)))).sum := by
    induction k with
    | zero => rfl
    | succ k ih => simp [stages, step, ih, List.sum_range_succ]
  obtain ⟨C,hC,hcb⟩ := bound hc
  obtain ⟨F,hF,hfb⟩ := bound hf
  let H := fun N => C N*F (N+C N)
  have hH : ComputationBounds.Polynomial H :=
    ComputationBounds.mul hC (ComputationBounds.compose hF (ComputationBounds.add ComputationBounds.identity hC))
  have hstage (S : Fin n → Word) (N : ℕ) (hS : ∀ j, (S j).length ≤ N) :
      ∀ k ≤ c S, stages step S 0 k ≤ H N := by
    have heval (k : ℕ) (hk : k ≤ c S) : f (Fin.snoc S (unary k)) ≤ F (N+C N) := by
      apply hfb
      intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.snoc_last, unary, List.length_replicate]
        exact (hk.trans (hcb S N hS)).trans (Nat.le_add_left _ _)
      · simpa only [Fin.snoc_castSucc] using (hS i).trans (Nat.le_add_right _ _)
    have haux (k : ℕ) (hk : k ≤ c S) : stages step S 0 k ≤ k*F (N+C N) := by
      induction k with
      | zero => simp [stages]
      | succ k ih =>
        simp only [stages, step, extend_accum, unary, List.length_replicate, extend_prefix]
        have hi := ih (by omega)
        have he := heval k (by omega)
        change stages step S 0 k+f (Fin.snoc S (unary k)) ≤ _
        simpa only [Nat.succ_mul] using Nat.add_le_add hi he
    intro k hk
    exact (haux k hk).trans (Nat.mul_le_mul_right _ (hk.trans (hcb S N hS)))
  apply (loop hc (const 0) hstep H hH hstage).congr
  intro S
  dsimp only
  rw [hs]

end WordExpressions.NatPoly

namespace WordExpressions.NatPoly
variable {n : ℕ}

theorem pair {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) :
    NatPoly (fun S => Nat.pair (f S) (g S)) := by
  apply (ite (lt hf hg) (add (mul hg hg) hf) (add (add (mul hf hf) hf) hg)).congr
  intro S
  simp only [Nat.pair]
  by_cases h : f S < g S <;> simp [h]

theorem sqrt {f : (Fin n → Word) → ℕ} (hf : NatPoly f) : NatPoly (fun S => (f S).sqrt) := by
  have hp : BoolPoly (fun T : Fin (n+1) → Word =>
      decide ((T (Fin.last n)).length*(T (Fin.last n)).length ≤ f (T ∘ Fin.castSucc))) :=
    le (mul (var _) (var _)) (rename hf _)
  apply (findGreatest hf hp).congr
  intro S
  dsimp only
  apply congrArg unary
  simp only [Fin.snoc_last, unary, List.length_replicate, snoc_prefix, decide_eq_true_eq]
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨Nat.sqrt_le_self _, fun _ => Nat.sqrt_le _, ?_⟩
  intro i hi _ hsq
  have := Nat.le_sqrt.mpr hsq
  omega

theorem unpair_fst {f : (Fin n → Word) → ℕ} (hf : NatPoly f) :
    NatPoly (fun S => (Nat.unpair (f S)).1) := by
  have hs := sqrt hf
  have hr := sub hf (mul hs hs)
  apply (ite (lt hr hs) hr hs).congr
  intro S
  by_cases h : f S-(f S).sqrt*(f S).sqrt < (f S).sqrt <;> simp [Nat.unpair, h]

theorem unpair_snd {f : (Fin n → Word) → ℕ} (hf : NatPoly f) :
    NatPoly (fun S => (Nat.unpair (f S)).2) := by
  have hs := sqrt hf
  have hr := sub hf (mul hs hs)
  apply (ite (lt hr hs) hs (sub hr hs)).congr
  intro S
  by_cases h : f S-(f S).sqrt*(f S).sqrt < (f S).sqrt <;> simp [Nat.unpair, h]

end WordExpressions.NatPoly

namespace WordExpressions.NatPoly
variable {n : ℕ}

theorem cap_mul (b x c : ℕ) : Min.min (Min.min x c*b) c = Min.min (x*b) c := by
  by_cases hb : b = 0
  · simp [hb]
  have hb : 1 ≤ b := by omega
  by_cases hx : x ≤ c
  · rw [min_eq_left hx]
  · have hxc : c ≤ x := by omega
    rw [min_eq_right hxc, min_eq_right (by nlinarith), min_eq_right (by nlinarith)]

theorem cappedPow {b e c : (Fin n → Word) → ℕ} (hb : NatPoly b) (he : NatPoly e) (hc : NatPoly c) :
    NatPoly (fun S => Min.min ((b S)^(e S)) (c S)) := by
  let f : (Fin (n+2) → Word) → ℕ := fun T => Min.min ((T (accum n)).length*b (T ∘ old)) (c (T ∘ old))
  have hf : NatPoly f := min (mul (var _) (rename hb _)) (rename hc _)
  have hs (S : Fin n → Word) (k : ℕ) : stages f S (Min.min 1 (c S)) k = Min.min ((b S)^k) (c S) := by
    induction k with
    | zero => simp [stages]
    | succ k ih => simp only [stages, f, extend_accum, unary, List.length_replicate, extend_base, ih,
        cap_mul, pow_succ]
  obtain ⟨C,hC,hcb⟩ := bound hc
  apply (loop he (min (const 1) hc) hf C hC (by
    intro S N hS k _
    rw [hs]
    exact (min_le_right _ _).trans (hcb S N hS))).congr
  intro S
  dsimp only
  rw [hs]

end WordExpressions.NatPoly

namespace WordExpressions.NatPoly
variable {n : ℕ}

theorem bitsSize {f : (Fin n → Word) → ℕ} (hf : NatPoly f) : NatPoly (fun S => (f S).size) := by
  have hp : BoolPoly (fun T : Fin (n+1) → Word =>
      decide (Min.min (2^(T (Fin.last n)).length) (f (T ∘ Fin.castSucc)+1) ≤ f (T ∘ Fin.castSucc))) :=
    le (cappedPow (const 2) (var _) (succ (rename hf _))) (rename hf _)
  have hmax := findGreatest hf hp
  apply (ite (eqtest hf (const 0)) (const 0) (succ hmax)).congr
  intro S
  simp only [Fin.snoc_last, unary, List.length_replicate, snoc_prefix, decide_eq_true_eq]
  by_cases hz : f S = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte]
    have hpos : 0 < (f S).size := by
      by_contra hh
      have := Nat.size_le.mp (show (f S).size ≤ 0 from by omega)
      simp only [pow_zero] at this
      omega
    have hsize : (f S).size ≤ f S := Nat.size_le.mpr Nat.lt_two_pow_self
    have hmaxeq : Nat.findGreatest (fun i => Min.min (2^i) (f S+1) ≤ f S) (f S) = (f S).size-1 := by
      apply Nat.findGreatest_eq_iff.mpr
      refine ⟨by omega, ?_, ?_⟩
      · intro _
        apply (min_le_left _ _).trans
        have hn : ¬ f S < 2^((f S).size-1) := by
          intro hn
          have := Nat.size_le.mpr hn
          omega
        omega
      · intro i hi _ hle
        have hpow : f S < 2^i := Nat.size_le.mp (by omega)
        omega
    rw [hmaxeq]
    congr 1
    omega

theorem div_cap (x y : ℕ) : x / Min.min y (x+1) = x/y := by
  by_cases hy : y ≤ x+1
  · rw [min_eq_left hy]
  · rw [min_eq_right (by omega), Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]

theorem testBit {f i : (Fin n → Word) → ℕ} (hf : NatPoly f) (hi : NatPoly i) :
    BoolPoly (fun S => (f S).testBit (i S)) := by
  apply (eqtest (mod (div hf (cappedPow (const 2) hi (succ hf))) (const 2)) (const 1)).congr
  intro S
  simp only [div_cap, Nat.testBit_eq_decide_div_mod_eq]

end WordExpressions.NatPoly
namespace WordExpressions.Poly
variable {n : ℕ}

theorem bits {f : (Fin n → Word) → ℕ} (hf : NatPoly f) : Poly (fun S => (f S).bits) := by
  apply (tabulate (NatPoly.bitsSize hf)
    (NatPoly.testBit (NatPoly.rename hf Fin.castSucc) (NatPoly.var (Fin.last n)))).congr
  intro S
  apply List.ext_getElem (by simp [Nat.size_eq_bits_len])
  intro i hi hj
  simp only [List.getElem_map, List.getElem_range, Fin.snoc_last, unary,
    List.length_replicate, snoc_prefix, Nat.testBit_eq_inth, List.getI_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem hj]
  rfl

theorem binary {f : (Fin n → Word) → ℕ} (hf : NatPoly f) : Poly (fun S => (f S).bits.reverse) :=
  reverse (bits hf)

end WordExpressions.Poly

namespace WordExpressions
namespace NatPoly
variable {n : ℕ}

/-- Saturated, genuine left-to-right binary decoding. It stays unary-bounded by c. -/
def decodeCap (w : Word) (c : ℕ) : ℕ := w.foldl (fun x b => Min.min (2*x+if b then 1 else 0) c) 0

theorem decodeCap_aux (w : Word) (c x : ℕ) :
    w.foldl (fun x b => Min.min (2*x+if b then 1 else 0) c) (Min.min x c) =
      Min.min (w.foldl (fun x b => 2*x+if b then 1 else 0) x) c := by
  induction w generalizing x with
  | nil => rfl
  | cons b w ih =>
    simp only [List.foldl_cons]
    have hm : Min.min (2*Min.min x c+if b then 1 else 0) c =
        Min.min (2*x+if b then 1 else 0) c := by
      cases b
      · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero, Nat.mul_comm] using cap_mul 2 x c
      · simp only [↓reduceIte]
        by_cases hx : x ≤ c
        · rw [min_eq_left hx]
        · rw [min_eq_right (by omega : c ≤ x), min_eq_right (by omega : c ≤ 2*c+1),
            min_eq_right (by omega : c ≤ 2*x+1)]
    rw [hm, ih]

theorem decodeCap_correct (w : Word) (c : ℕ) : decodeCap w c = Min.min (binaryValue w) c := by
  simpa only [decodeCap, binaryValue, zero_min] using decodeCap_aux w c 0

theorem decode {w : (Fin n → Word) → Word} {c : (Fin n → Word) → ℕ}
    (hw : Poly w) (hc : NatPoly c) : NatPoly (fun S => Min.min (binaryValue (w S)) (c S)) := by
  let f : (Fin (n+2) → Word) → ℕ := fun T =>
    Min.min (2*(T (accum n)).length+if (w (T ∘ old))[(T (index n)).length]?.getD false then 1 else 0) (c (T ∘ old))
  have hf : NatPoly f := min
    (add (mul (const 2) (var _)) (ite (Poly.nth (Poly.rename hw old) (var _)) (const 1) (const 0)))
    (rename hc old)
  have hs (S : Fin n → Word) (k : ℕ) (hk : k ≤ (w S).length) :
      stages f S 0 k = decodeCap ((w S).take k) (c S) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk' : k < (w S).length := by omega
      simp only [stages, f, extend_accum, unary, List.length_replicate, extend_base, extend_index,
        List.getElem?_eq_getElem hk', Option.getD_some, ih (by omega)]
      rw [List.take_succ_eq_append_getElem hk']
      simp only [decodeCap, List.foldl_append, List.foldl_cons, List.foldl_nil]
  obtain ⟨C,hC,hcb⟩ := bound hc
  apply (loop (length hw) (const 0) hf C hC (by
    intro S N hS k hk
    rw [hs S k hk, decodeCap_correct]
    exact (min_le_right _ _).trans (hcb S N hS))).congr
  intro S
  dsimp only
  rw [hs S _ (le_refl _), List.take_length, decodeCap_correct]

end NatPoly
end WordExpressions

end WLIdentification

end OAI
