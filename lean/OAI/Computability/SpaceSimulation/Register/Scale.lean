import OAI.Computability.SpaceSimulation.Binary

namespace OAI

/-! Uniform bounds pulled along index sets. Add 1 to the reference
function so that constant-size data and empty histories never require
a separate positivity premise. Used also with restrictions of runs to
sets of promise instances. -/

namespace Fifths

/-- `Scaled S f` = f is at most a constant multiple of S+1 at
every argument. -/
def Scaled {I : Type} (S f : I → ℕ) : Prop :=
  ∃ c : ℕ, ∀ i, f i ≤ c * (S i + 1)

/-- Bit length bound (all instances, same constant); not by itself a
computability assertion. -/
def Fits {I : Type} (S f : I → ℕ) : Prop :=
  Scaled S (fun i => (f i).size)

namespace Scaled
variable {I : Type} {S A f g : I → ℕ}

theorem pull (h : Scaled S f) {L : Type} (e : L → I) :
    Scaled (fun i => S (e i)) (fun i => f (e i)) := by
  obtain ⟨c,h⟩ := h
  exact ⟨c,fun i => h (e i)⟩

theorem of_le (h : Scaled S f) (l : ∀ i, g i ≤ f i) : Scaled S g := by
  obtain ⟨c,h⟩ := h
  exact ⟨c, fun i => le_trans (l i) (h i)⟩

theorem congr (h : Scaled S f) (l : ∀ i, f i = g i) : Scaled S g :=
  h.of_le (fun i => (l i).symm.le)

theorem const (S : I → ℕ) (n : ℕ) : Scaled S (fun _ => n) :=
  ⟨n,fun _ => Nat.le_mul_of_pos_right _ (by omega)⟩

theorem refl (S : I → ℕ) : Scaled S S :=
  ⟨1,fun _ => by simp⟩

theorem add (h : Scaled S f) (l : Scaled S g) :
    Scaled S (fun i => f i + g i) := by
  obtain ⟨c,h⟩ := h
  obtain ⟨d,l⟩ := l
  exact ⟨c+d,fun i => by rw [add_mul]; exact add_le_add (h i) (l i)⟩

theorem mulConst (h : Scaled S f) (d : ℕ) :
    Scaled S (fun i => f i * d) := by
  obtain ⟨c,h⟩ := h
  exact ⟨c*d,fun i => by simpa [mul_comm,mul_left_comm,mul_assoc] using
    (Nat.mul_le_mul_right d (h i))⟩

theorem mulFamily {T : I → ℕ} (h : Scaled S f) (l : Scaled T g) :
    Scaled (fun i => (S i + 1)*(T i + 1)) (fun i => f i * g i) := by
  obtain ⟨c,h⟩ := h
  obtain ⟨d,l⟩ := l
  refine ⟨c*d,fun i => ?_⟩
  calc
    _ ≤ (c*(S i + 1)) * (d*(T i+1)) := Nat.mul_le_mul (h i) (l i)
    _ = (c*d) * ((S i+1)*(T i+1)) := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_left (c*d) (Nat.le_succ _)

theorem trans (h : Scaled S f) (l : Scaled A S) : Scaled A f := by
  obtain ⟨d,l⟩ := l.add (Scaled.const A 1)
  obtain ⟨c,h⟩ := h
  exact ⟨c*d, fun i => by rw [mul_assoc]; exact le_trans (h i) (Nat.mul_le_mul_left c (l i))⟩
end Scaled

namespace Fits
variable {I : Type} {S A f g : I → ℕ}

theorem pull (h : Fits S f) {L : Type} (e : L → I) :
    Fits (fun i => S (e i)) (fun i => f (e i)) :=
  Scaled.pull h e

theorem mono (h : Fits S f) (l : ∀ i, g i ≤ f i) : Fits S g :=
  Scaled.of_le h (fun i => Nat.size_le_size (l i))

theorem congr (h : Fits S f) (l : ∀ i, f i = g i) : Fits S g :=
  h.mono (fun i => (l i).symm.le)
theorem const (S : I → ℕ) (n : ℕ) : Fits S (fun _ => n) :=
  Scaled.const S n.size

theorem of_scaled (h : Scaled S f) : Fits S f :=
  h.of_le (fun _i => Bin.size_le_self _)

theorem up (h : Fits S f) (l : Scaled A S) : Fits A f :=
  Scaled.trans h l

theorem add (h : Fits S f) (l : Fits S g) : Fits S (fun i => f i + g i) := by
  refine Scaled.of_le ((Scaled.add h l).add (Scaled.const S 1)) ?_
  intro i
  exact le_trans (Bin.add_size _ _) (Nat.add_le_add_right (max_le (by omega) (by omega)) 1)

theorem mul (h : Fits S f) (l : Fits S g) : Fits S (fun i => f i * g i) :=
  Scaled.of_le (Scaled.add h l) (fun _i => Bin.mul_size _ _)

theorem pow (f g : I → ℕ) (h : Scaled S (fun i => g i * (f i).size)) :
    Fits S (fun i => f i ^ g i) :=
  Scaled.of_le ((Scaled.const S 1).add h) (fun _i => Bin.pow_size _ _)

theorem pair (h : Fits S f) (l : Fits S g) : Fits S (fun i => Bin.pair (f i) (g i)) :=
  Scaled.of_le (((Scaled.add h h).add (Scaled.const S 1)).add l) (fun i => by
    show (Bin.pair _ _).size ≤ ((f i).size+(f i).size+1)+(g i).size
    rw [Bin.pair_size]; omega)

theorem pair_left (h : Fits S (fun i => Bin.pair (f i) (g i))) : Fits S f :=
  Scaled.of_le h (fun i => by
    show (f i).size ≤ (Bin.pair _ _).size
    rw [Bin.pair_size]
    omega)

theorem pair_right (h : Fits S (fun i => Bin.pair (f i) (g i))) : Fits S g :=
  Scaled.of_le h (fun i => by
    show (g i).size ≤ (Bin.pair _ _).size
    rw [Bin.pair_size]; omega)
end Fits

end Fifths

end OAI
