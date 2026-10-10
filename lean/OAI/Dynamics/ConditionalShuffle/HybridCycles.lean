import OAI.Dynamics.ConditionalShuffle.CycleIterate

namespace OAI

noncomputable section
open scoped Classical
namespace Thorp.Conditional.Hybrid
open OverlayEnergy Revealed.Instrument

lemma raw_append (d n m : ℕ) (v : RawState (d+1))
    (s : Fin n → Bool) (r : Fin m → Bool) (a : History (d+1) n) (b : History (d+1) m) :
    raw d v (n+m) (Fin.append s r) (Fin.append a b) = raw d (raw d v n s a) m r b := by
  induction m with
  | zero =>
      have hr : Fin.append s r = s := by funext i; exact Fin.append_left s r i
      have hb : Fin.append a b = a := by funext i; exact Fin.append_left a b i
      rw [hr, hb]; rfl
  | succ m ih =>
      obtain ⟨⟨q,r⟩,rfl⟩ := (Fin.snocEquiv (fun _ : Fin (m+1) => Bool)).surjective r
      obtain ⟨⟨c,b⟩,rfl⟩ := (Fin.snocEquiv (fun _ : Fin (m+1) => Coins (d+1))).surjective b
      erw [Fin.append_snoc, Fin.append_snoc, raw_snoc, raw_snoc, ih]

lemma raw_public (d : ℕ) (v : RawState (d+1)) (t : ℕ) (ω : History (d+1) t) :
    raw d v t (fun _ => false) ω = rawPermute v (run (d+1) t ω) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change rawPermute (raw d v t (fun _ => false) (Fin.init ω)) (step (d+1) (ω (Fin.last t))) = _
      rw [ih, run_succ]
      rfl

lemma raw_private (d : ℕ) (v : RawState (d+1)) (t : ℕ) (ω : History (d+1) t) :
    raw d v t (fun _ => true) ω = rawIterate d v t ω := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change rawNext d (raw d v t (fun _ => true) (Fin.init ω)) (ω (Fin.last t)) = _
      rw [ih]; rfl

def periodLength (g : ℕ) := (9*(g+3)+200*(g+3))+(g+3)

lemma periodLength_eq (g : ℕ) : periodLength g = 210*(g+3) := by unfold periodLength; omega

def cycleSchedule (g : ℕ) : Fin (periodLength g) → Bool :=
  Fin.append (Fin.append (fun _ : Fin (9*(g+3)) => false)
    (fun _ : Fin (200*(g+3)) => false)) (fun _ : Fin (g+3) => true)

def tripleHistory (Ω : Type) (a b c : ℕ) :
    (((Fin a → Ω) × (Fin b → Ω)) × (Fin c → Ω)) ≃ (Fin ((a+b)+c) → Ω) :=
  (Equiv.prodCongr (Fin.appendEquiv a b) (Equiv.refl _)).trans (Fin.appendEquiv (a+b) c)

lemma tripleHistory_apply (Ω : Type) (a b c : ℕ) (ω) :
    tripleHistory Ω a b c ω = Fin.append (Fin.append ω.1.1 ω.1.2) ω.2 := rfl

def cycleHistory (g : ℕ) : CycleCoins g ≃ (Fin (periodLength g) → Bits g) :=
  tripleHistory (Bits g) (9*(g+3)) (200*(g+3)) (g+3)

lemma cycleHistory_apply (g : ℕ) (ω : CycleCoins g) :
    cycleHistory g ω = Fin.append (Fin.append ω.1.1 ω.1.2) ω.2 :=
  tripleHistory_apply (Bits g) _ _ _ ω

lemma raw_cycle (g : ℕ) (v : RawState (g+3)) (ω : CycleCoins g) :
    raw (g+2) v (periodLength g) (cycleSchedule g) (cycleHistory g ω) = cycle g v ω := by
  rw [cycleHistory_apply]
  unfold cycleSchedule
  erw [raw_append, raw_append, raw_public, raw_public, raw_private]
  rfl

def repeatedSchedule (g n : ℕ) : Fin (periodLength g*n) → Bool :=
  chunks Bool (periodLength g) n (fun _ => cycleSchedule g)

def repeatedHistory (g n : ℕ) : (Fin n → CycleCoins g) ≃ (Fin (periodLength g*n) → Bits g) :=
  (Equiv.piCongrRight (fun _ : Fin n => cycleHistory g)).trans (chunks (Bits g) (periodLength g) n)

lemma repeatedHistory_apply (g n : ℕ) (ω : Fin n → CycleCoins g) :
    repeatedHistory g n ω = chunks (Bits g) (periodLength g) n (fun i => cycleHistory g (ω i)) := by
  rfl

lemma raw_cycles (g : ℕ) (v : RawState (g+3)) (n : ℕ) (ω : Fin n → CycleCoins g) :
    raw (g+2) v (periodLength g*n) (repeatedSchedule g n) (repeatedHistory g n ω) = cycles g v n ω := by
  induction n with
  | zero => rfl
  | succ n ih =>
      obtain ⟨⟨c,ω⟩,rfl⟩ := (Fin.snocEquiv (fun _ : Fin (n+1) => CycleCoins g)).surjective ω
      have hs : (fun _ : Fin (n+1) => cycleSchedule g) =
          Fin.snoc (fun _ : Fin n => cycleSchedule g) (cycleSchedule g) := by
        funext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      have hh : (fun i : Fin (n+1) => cycleHistory g ((Fin.snoc ω c : Fin (n+1) → CycleCoins g) i)) =
          Fin.snoc (fun i : Fin n => cycleHistory g (ω i)) (cycleHistory g c) := by
        funext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [repeatedHistory_apply, repeatedSchedule]
      rw [hs]
      change raw (g+2) v _ _ (chunks (Bits g) _ _
        (fun i => cycleHistory g ((Fin.snoc ω c : Fin (n+1) → CycleCoins g) i))) = _
      rw [hh, chunks_snoc, chunks_snoc]
      erw [raw_append]
      change raw (g+2) (raw (g+2) v _ (repeatedSchedule g n) (repeatedHistory g n ω))
        _ (cycleSchedule g) (cycleHistory g c) = _
      rw [ih, raw_cycle]
      simp only [cycles, Fin.snocEquiv, Equiv.coe_fn_mk, Fin.init_snoc, Fin.snoc_last]

lemma repeated_energy (g : ℕ) (v : RawState (g+3))
    (hw : ∀ x, v.free x = false → v.weight x = 0) (hz : ∑ x, v.weight x = 0)
    (hf : Fintype.card (Position (g+3)) ≤ 64 * freeCount v.free)
    (hk : freeCount v.free ≤ 2^g)
    (hs : 256*(g+4) ≤ Fintype.card (Position (g+3))) (n : ℕ) :
    energy (g+2) v (periodLength g*n) (repeatedSchedule g n) ≤ rawEnergy v * OverlayEnergy.coefficient g^n := by
  have hh := mean_equiv (repeatedHistory g n)
    (fun ω : History (g+3) (periodLength g*n) =>
      rawEnergy (raw (g+2) v (periodLength g*n) (repeatedSchedule g n) ω))
  change mean (fun ω : Fin n → CycleCoins g =>
      rawEnergy (raw (g+2) v _ (repeatedSchedule g n) (repeatedHistory g n ω))) = _ at hh
  simp only [raw_cycles] at hh
  change mean (fun ω : History (g+3) (periodLength g*n) => _) ≤ _
  have hi := cycles_expected_energy g v hw hz hf hk hs n
  exact (mean_fintype_irrel _ _ _).le.trans (hh.symm.le.trans hi)

lemma repeated_point_energy (g : ℕ) (B : Position (g+3) → Bool) (tag) (ht : B tag = true)
    (hf : Fintype.card (Position (g+3)) ≤ 64*freeCount B) (hk : freeCount B ≤ 2^g)
    (hs : 256*(g+4) ≤ Fintype.card (Position (g+3))) (n : ℕ) :
    energy (g+2) (initialState (g+3) B tag ht).raw (periodLength g*n) (repeatedSchedule g n) ≤
      OverlayEnergy.coefficient g^n := by
  have hh := repeated_energy g (initialState (g+3) B tag ht).raw
    (initialState (g+3) B tag ht).supported (initialState (g+3) B tag ht).mass_zero hf hk hs n
  exact hh.trans (mul_le_of_le_one_left (pow_nonneg (coefficient_nonneg g) n)
    (initialState (g+3) B tag ht).energy_le_one)

end Thorp.Conditional.Hybrid

end

end OAI
