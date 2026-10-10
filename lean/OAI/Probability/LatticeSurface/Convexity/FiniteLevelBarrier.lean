import Mathlib

namespace OAI

noncomputable section

namespace ClusterDisplacement

open Set

variable {I : Type*} [Fintype I]

lemma finite_level_barrier (l : I → ℝ) (f : ℕ → ℝ) (N : ℕ) (r : ℝ) (hr : 0≤r)
    (hnear : ∀n≤N,∃i,|f n-l i|≤r)
    (hjump : ∀n<N,|f (n+1)-f n|≤r) :
    |f N-f 0|≤5*(Fintype.card I:ℝ)*r := by
  classical
  have hnon : Nonempty I := by obtain ⟨i,_⟩:=hnear 0 (Nat.zero_le _);exact ⟨i⟩
  let := hnon
  let a : ℕ → I := fun n => if hn : n≤N then Classical.choose (hnear n hn) else Classical.choice hnon
  have ha (n : ℕ) (hn : n≤N) : |f n-l (a n)|≤r := by
    simp only [a,dite_eq_left hn]
    exact Classical.choose_spec (hnear n hn)
  let G : SimpleGraph I := {
    Adj := fun i j => i≠j ∧ |l i-l j|≤3*r
    symm := ⟨by intro i j h;exact ⟨h.1.symm,by simpa only [abs_sub_comm] using h.2⟩⟩
    loopless := ⟨by intro i h;exact h.1 rfl⟩}
  have hedge (n : ℕ) (hn : n<N) : G.Reachable (a n) (a (n+1)) := by
    by_cases heq : a n=a (n+1)
    · rw [heq]
    · apply SimpleGraph.Adj.reachable
      refine ⟨heq,?_⟩
      have e₀ := ha n hn.le
      have e₁ := ha (n+1) hn
      have ej := hjump n hn
      have ht := abs_sub_le (l (a n)) (f n) (f (n+1))
      have hu := abs_sub_le (l (a n)) (f (n+1)) (l (a (n+1)))
      rw [abs_sub_comm (l (a n)) (f n)] at ht
      rw [abs_sub_comm (f n) (f (n+1))] at ht
      linarith
  have hreach (n : ℕ) (hn : n≤N) : G.Reachable (a 0) (a n) := by
    induction n with
    | zero => exact .refl _
    | succ n ih => exact (ih (Nat.le_trans (Nat.le_succ n) hn)).trans (hedge n hn)
  obtain ⟨p⟩ := hreach N le_rfl
  let q := p.toPath
  have hlen := q.property.length_lt
  have hwalk {i j : I} (w : G.Walk i j) : |l i-l j|≤(w.length:ℝ)*(3*r) := by
    induction w with
    | nil => simp
    | @cons i j k hij w ih =>
      have ht := abs_sub_le (l i) (l j) (l k)
      have he : |l i-l j|≤3*r := hij.2
      simp only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith
  have hd := hwalk q.val
  have hcard : (1:ℝ)≤Fintype.card I := Nat.one_le_cast.mpr (Fintype.card_pos_iff.mpr hnon)
  have hl : (q.val.length:ℝ)≤Fintype.card I := Nat.cast_le.mpr hlen.le
  have hbound : |l (a 0)-l (a N)|≤3*(Fintype.card I:ℝ)*r := by nlinarith
  have e₀ := ha 0 (Nat.zero_le _)
  have eN := ha N le_rfl
  have ht := abs_sub_le (f N) (l (a N)) (l (a 0))
  have hu := abs_sub_le (f N) (l (a 0)) (f 0)
  rw [abs_sub_comm (l (a N)) (l (a 0))] at ht
  rw [abs_sub_comm (l (a 0)) (f 0)] at hu
  nlinarith

end ClusterDisplacement

end

end OAI
