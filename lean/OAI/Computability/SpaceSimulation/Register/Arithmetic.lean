import OAI.Computability.SpaceSimulation.Register.Fold

namespace OAI

/-! Arithmetic operators in the bit-space closure. Many are
intentionally very slow. -/
namespace Fifths
namespace Comp
variable {X I : Type} {x : I → List X} {S a u v b c : I → ℕ}
open Bin

theorem add (h : Comp x S a b) (g : Comp x S a c) :
    Comp x S a (fun i => b i + c i) := by
  refine fold (fun i j => b i+j) g h ?_ ?_
  · let f : Through c → I := fun i => i.1.1
    exact (h.target.pull f).add ((g.target.pull f).mono fun i => i.2)
  · intro e _ _ l
    exact l.plus1
theorem sub (h : Comp x S a b) (g : Comp x S a c) :
    Comp x S a (fun i => b i - c i) := by
  refine fold (fun i j => b i-j) g h ?_ ?_
  · let f : Through c → I := fun i => i.1.1
    exact (h.target.pull f).mono (fun i => Nat.sub_le _ _)
  · intro e _ _ l
    exact l.minus1.congr (fun i => by
      show b i.1.1 - i.1.2 - 1 = _
      omega)

theorem mul (h : Comp x S a b) (g : Comp x S a c) :
    Comp x S a (fun i => b i * c i) := by
  refine fold (fun i j => b i*j) g ((Comp.constant h.source 0).congr (fun i => by simp)) ?_ ?_
  · let f : Through c → I := fun i => i.1.1
    exact (h.target.pull f).mul ((g.target.pull f).mono fun i => i.2)
  · intro e p _ l
    let f : Before c → I := fun i => i.1.1
    exact (l.add (p.trans (h.pull f))).congr (fun i => by simp [mul_add,f])

theorem pow (h : Comp x S a b) (g : Comp x S a c)
    (p : Fits S (fun i => b i ^ c i)) : Comp x S a (fun i => b i ^ c i) := by
  refine fold (fun i j => b i^j) g ((Comp.constant h.source 1).congr (fun i => by simp)) ?_ ?_
  · let f : Through c → I := fun i => i.1.1
    refine ((p.pull f).add (Fits.const _ 1)).mono (fun i => ?_)
    by_cases e : b (f i) = 0
    · change b (f i) ^ i.1.2 ≤ b (f i) ^ c (f i) + 1
      rw [e]
      by_cases a : i.1.2 = 0
      · simp [a]
      · simp [a]
    · apply le_trans (Nat.pow_le_pow_right (Nat.pos_of_ne_zero e) i.2)
      exact Nat.le_succ _
  · intro e r _ l
    let f : Before c → I := fun i => i.1.1
    exact (l.mul (r.trans (h.pull f))).congr (fun i => by simp [pow_succ,f])

-- Boolean tests and selections
variable {B C : I → Bool}

theorem flip (h : Comp x S a (fun i => (B i).toNat)) :
    Comp x S a (fun i => (!B i).toNat) :=
  ((Comp.constant h.source 1).sub h).congr fun i => by cases B i <;> rfl

theorem both (h : Comp x S a (fun i => (B i).toNat))
    (g : Comp x S a (fun i => (C i).toNat)) :
    Comp x S a (fun i => (B i && C i).toNat) :=
  (h.mul g).congr fun i => by cases B i <;> cases C i <;> rfl

theorem either (h : Comp x S a (fun i => (B i).toNat))
    (g : Comp x S a (fun i => (C i).toNat)) :
    Comp x S a (fun i => (B i || C i).toNat) :=
  (flip (h.flip.both g.flip)).congr fun i => by cases B i <;> cases C i <;> rfl

theorem lt (h : Comp x S a b) (g : Comp x S a c) :
    Comp x S a (fun i => (decide (b i < c i)).toNat) := by
  refine (g.sub h).testnz.congr (fun i => ?_)
  by_cases l : b i < c i
  · simp [notZero,Nat.ne_of_gt (Nat.sub_pos_of_lt l),l]
  · simp [notZero,Nat.sub_eq_zero_of_le (le_of_not_gt l),l]

theorem le (h : Comp x S a b) (g : Comp x S a c) :
    Comp x S a (fun i => (decide (b i ≤ c i)).toNat) := by
  refine flip (B := fun i => decide (c i < b i)) (g.lt h) |>.congr (fun i => ?_)
  by_cases l : b i ≤ c i <;> simp [l]
  omega

theorem eq (h : Comp x S a b) (g : Comp x S a c) :
    Comp x S a (fun i => (decide (b i = c i)).toNat) := by
  refine ((h.le g).both (g.le h)).congr (fun i => ?_)
  rcases lt_trichotomy (b i) (c i) with l|l|l
  · simp [l.le,l.ne,not_le_of_gt l]
  · simp [l]
  · simp [l.le,l.ne.symm,not_le_of_gt l]

theorem min (h : Comp x S a b) (g : Comp x S a c) :
    Comp x S a (fun i => min (b i) (c i)) :=
  ((h.le g).iteB h g).congr fun i => by
    by_cases l : b i ≤ c i
    · simp [l]
    · simp [l, min_eq_right (le_of_not_ge l)]
theorem max (h : Comp x S a b) (g : Comp x S a c) :
    Comp x S a (fun i => max (b i) (c i)) :=
  ((h.le g).iteB g h).congr fun i => by
    by_cases l : b i ≤ c i
    · simp [l]
    · simp [l,max_eq_left (le_of_not_ge l)]

private theorem div_step (j n : ℕ) :
    (if notZero n && decide ((j/n+1)*n ≤ j+1) then
      j/n+1 else j/n) = (j+1)/n := by
  by_cases h : n = 0
  · subst n; simp [notZero]
  have p := Nat.pos_of_ne_zero h
  have hb : j < (j/n+1)*n := (Nat.div_lt_iff_lt_mul p).mp (Nat.lt_succ_self _)
  by_cases l : (j/n+1)*n ≤ j+1
  · have e : (j/n+1)*n = j+1 := by omega
    have v : n ∣ j+1 := ⟨j/n+1, by simpa [mul_comm] using e.symm⟩
    simp [notZero,h,l,Nat.succ_div,v]
  · have a : (j+1)/n < j/n+1 := (Nat.div_lt_iff_lt_mul p).mpr (lt_of_not_ge l)
    have g : j/n ≤ (j+1)/n := Nat.div_le_div_right (Nat.le_succ _)
    simpa only [decide_eq_false l,Bool.and_false, Bool.false_eq_true, ite_false] using
      Nat.le_antisymm g (by omega)

theorem div (h : Comp x S a b) (g : Comp x S a c) :
    Comp x S a (fun i => b i / c i) := by
  refine fold (fun i j => j / c i) h ((Comp.constant h.source 0).congr
    (fun i => by simp)) ?_ ?_
  · let f : Through b → I := fun i => i.1.1
    exact (h.target.pull f).mono (fun i => le_trans (Nat.div_le_self _ _) i.2)
  · intro e r k l
    let f : Before b → I := fun i => i.1.1
    have q := r.trans (g.pull f)
    have v := q.testnz.both ((l.plus1.mul q).le k.plus1)
    exact (v.iteB l.plus1 l).congr (fun i => div_step _ _)

theorem mod (h : Comp x S a b) (g : Comp x S a c) :
    Comp x S a (fun i => b i % c i) := by
  apply (h.sub ((h.div g).mul g)).congr
  intro i
  have l := Nat.mod_add_div (b i) (c i)
  rw [mul_comm]
  omega

theorem size (h : Comp x S a b) :
    Comp x S a (fun i => (b i).size) := by
  let n := fun i => (b i).size
  let w := fun i (j : ℕ) => Bin.pair j (b i / 2^j)
  have e : Comp x S a (fun i => w i 0) :=
    ((Comp.constant h.source 0).pair h).congr (fun i => by simp [w])
  have p : Fits (fun i : Through n => S i.1.1)
      (fun i => w i.1.1 i.1.2) := by
    let f : Through n → I := fun i => i.1.1
    refine ((h.target.pull f).mono ?_).pair ((h.target.pull f).mono ?_)
    · exact fun i => le_trans i.2 (Bin.size_le_self _)
    · exact fun _ => Nat.div_le_self _ _
  have g : Comp x S (fun i => w i 0) (fun i => w i (n i)) := by
    refine loop n w ?_ ?_
    · let f : Before n → Through n := fun i => ⟨i.1,i.2.le⟩
      have r : Comp (fun i : Before n => x i.1.1) (fun i => S i.1.1)
          (fun i => w i.1.1 i.1.2) (fun i => w i.1.1 i.1.2) :=
        Comp.refl (p.pull f)
      exact (r.left.plus1.pair (r.right.div (Comp.constant r.source 2))).congr
        (fun i => by simp [w,pow_succ,Nat.div_div_eq_div_mul])
    · have r : Comp (fun i : Through n => x i.1.1) (fun i => S i.1.1)
          (fun i => w i.1.1 i.1.2) (fun i => w i.1.1 i.1.2) :=
        Comp.refl p
      apply r.right.testnz.congr
      intro i
      by_cases l : i.1.2 < n i.1.1
      · have a : 2^i.1.2 ≤ b i.1.1 := Nat.lt_size.mp l
        simp [notZero,l,Nat.ne_of_gt (Nat.div_pos a (by positivity))]
      · have a := Nat.size_le.mp (le_of_not_gt l)
        simp [notZero,l,Nat.div_eq_of_lt a]
  exact (e.trans g).left

end Comp
end Fifths

end OAI
