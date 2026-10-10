import OAI.Analysis.LipschitzEquivalence.SelectionStep

namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem damping_congr (n : ℕ) {z z' : ℕ → Smooth H}
    (h : ∀ i < n, z i = z' i) (x : H) :
    damping (Finset.range n) z x = damping (Finset.range n) z' x := by
  apply Finset.prod_congr rfl
  intro i hi
  rw [h i (Finset.mem_range.mp hi)]

structure ConstructionPrefix (K Q : Set H) (C ρ α : ℝ) (μ : ℕ → Space H)
    (ε η : ℕ → ℝ) (n : ℕ) where
  z : ℕ → Smooth H
  w : ℕ → Smooth H
  a : ℕ → RowItem K C ρ μ
  lip : ∀ i < n, LipschitzWith 1 (z i).val
  zero : ∀ i < n, (z i).val 0 = 0 ∧ (w i).val 0 = 0
  high : ∀ i < n, α ≤ smoothPair (a i).a (z i)
  mass : ∀ i j, j < i → i < n → gradMass (a i).a (z j) ≤ η j
  error : ∀ i < n, ∀ x ∈ Q,
    ‖Smooth.grad x (w i)-damping (Finset.range i) z x • Smooth.grad x (z i)‖ ≤ ε i
  rich : ((triangularRows K C ρ α μ).restrict
    (fun b => ∀ i < n, gradMass b.a (z i) ≤ η i)).Rich

namespace ConstructionPrefix
variable {K Q : Set H} {C ρ α : ℝ} {μ : ℕ → Space H} {ε η : ℕ → ℝ}

theorem extend (hQ : IsCompact Q) (hC : 0 ≤ C) (hα : 0 < α)
    (hε : ∀ i, 0 < ε i) (hη : ∀ i, 0 < η i) {n : ℕ}
    (p : ConstructionPrefix K Q C ρ α μ ε η n) :
    ∃ q : ConstructionPrefix K Q C ρ α μ ε η (n+1),
      ∀ i < n, q.z i = p.z i ∧ q.w i = p.w i ∧ q.a i = p.a i := by
  classical
  obtain ⟨f,w,a,hf,hf0,hw0,hPa,hhigh,herr,hrich⟩ :=
    selection_step hQ hC hα _ p.rich (fun i : Fin n => p.z i)
      (fun i => p.lip i i.isLt) (hε n) (hη n)
  let z' := Function.update p.z n f
  let w' := Function.update p.w n w
  let a' := Function.update p.a n a
  have hz (i : ℕ) (hi : i < n) : z' i = p.z i := Function.update_of_ne (by omega) _ _
  have hw (i : ℕ) (hi : i < n) : w' i = p.w i := Function.update_of_ne (by omega) _ _
  have ha (i : ℕ) (hi : i < n) : a' i = p.a i := Function.update_of_ne (by omega) _ _
  have hzn : z' n = f := by simp [z']
  have hwn : w' n = w := by simp [w']
  have han : a' n = a := by simp [a']
  refine ⟨{
    z := z'
    w := w'
    a := a'
    lip := ?_
    zero := ?_
    high := ?_
    mass := ?_
    error := ?_
    rich := ?_ },fun i hi => ⟨hz i hi,hw i hi,ha i hi⟩⟩
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi|rfl
    · rw [hz i hi]; exact p.lip i hi
    · rw [hzn]; exact hf
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi|rfl
    · rw [hz i hi,hw i hi]; exact p.zero i hi
    · rw [hzn,hwn]; exact ⟨hf0,hw0⟩
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi|rfl
    · rw [hz i hi,ha i hi]; exact p.high i hi
    · rw [hzn,han]; exact hhigh
  · intro i j hji hi
    have hj : j < n := by omega
    rw [hz j hj]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi|rfl
    · rw [ha i hi]; exact p.mass i j hji hi
    · rw [han]; exact hPa j hj
  · intro i hi x hx
    have hd : damping (Finset.range i) z' x = damping (Finset.range i) p.z x :=
      damping_congr i (fun j hj => hz j (by omega)) x
    rw [hd]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi|rfl
    · rw [hz i hi,hw i hi]; exact p.error i hi x hx
    · rw [hzn,hwn]
      have he := herr x hx
      have hprod := Fin.prod_univ_eq_prod_range (fun j => 1-‖Smooth.grad x (p.z j)‖) i
      change ‖Smooth.grad x w-(∏ j : Fin i, (1-‖Smooth.grad x (p.z j)‖)) • Smooth.grad x f‖ ≤ ε i at he
      rw [hprod] at he
      exact he
  · intro N
    obtain ⟨v,hv,hP⟩ := hrich N
    refine ⟨v,hv,fun i j hj => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj|rfl
    · rw [hz j hj]; exact (hP i).1 j hj
    · rw [hzn]; exact (hP i).2

end ConstructionPrefix

theorem exists_detecting_sequence {K Q : Set H} (hQ : IsCompact Q)
    {C ρ α : ℝ} {μ : ℕ → Space H} (hC : 0 ≤ C) (hα : 0 < α)
    (hRich : (triangularRows K C ρ α μ).Rich) (ε η : ℕ → ℝ)
    (hε : ∀ i, 0 < ε i) (hη : ∀ i, 0 < η i) :
    ∃ (z w : ℕ → Smooth H) (a : ℕ → RowItem K C ρ μ),
      (∀ i, LipschitzWith 1 (z i).val) ∧
      (∀ i, (z i).val 0 = 0 ∧ (w i).val 0 = 0) ∧
      (∀ i, α ≤ smoothPair (a i).a (z i)) ∧
      (∀ i j, j < i → gradMass (a i).a (z j) ≤ η j) ∧
      ∀ i x, x ∈ Q →
        ‖Smooth.grad x (w i)-damping (Finset.range i) z x • Smooth.grad x (z i)‖ ≤ ε i := by
  classical
  obtain ⟨v,hv⟩ := hRich 1
  let p0 : ConstructionPrefix K Q C ρ α μ ε η 0 := {
    z := fun _ => 0
    w := fun _ => 0
    a := fun _ => v 0
    lip := fun i hi => (Nat.not_lt_zero i hi).elim
    zero := fun i hi => (Nat.not_lt_zero i hi).elim
    high := fun i hi => (Nat.not_lt_zero i hi).elim
    mass := fun i _ _ hi => (Nat.not_lt_zero i hi).elim
    error := fun i hi => (Nat.not_lt_zero i hi).elim
    rich := fun N => by
      obtain ⟨v,hv⟩ := hRich N
      exact ⟨v,hv,fun _ i hi => (Nat.not_lt_zero i hi).elim⟩ }
  have hex (n : ℕ) (p : ConstructionPrefix K Q C ρ α μ ε η n) :=
    p.extend hQ hC hα hε hη
  let next (n : ℕ) (p : ConstructionPrefix K Q C ρ α μ ε η n) := (hex n p).choose
  have hn (n : ℕ) (p : ConstructionPrefix K Q C ρ α μ ε η n) (i : ℕ) (hi : i < n) :
      (next n p).z i = p.z i ∧ (next n p).w i = p.w i ∧ (next n p).a i = p.a i :=
    (hex n p).choose_spec i hi
  let p : (n : ℕ) → ConstructionPrefix K Q C ρ α μ ε η n := Nat.rec p0 next
  have hp (n : ℕ) : p (n+1) = next n (p n) := rfl
  have hstable (i m : ℕ) (him : i < m) :
      (p m).z i = (p (i+1)).z i ∧ (p m).w i = (p (i+1)).w i ∧
      (p m).a i = (p (i+1)).a i := by
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases hi : i < m
      · rw [hp]
        exact ⟨(hn m (p m) i hi).1.trans (ih hi).1,
          (hn m (p m) i hi).2.1.trans (ih hi).2.1,
          (hn m (p m) i hi).2.2.trans (ih hi).2.2⟩
      · have : m = i := by omega
        subst m
        exact ⟨rfl,rfl,rfl⟩
  let z := fun i => (p (i+1)).z i
  let w := fun i => (p (i+1)).w i
  let a := fun i => (p (i+1)).a i
  refine ⟨z,w,a,fun i => (p (i+1)).lip i (by omega),
    fun i => (p (i+1)).zero i (by omega),fun i => (p (i+1)).high i (by omega),?_,?_⟩
  · intro i j hji
    have hm := (p (i+1)).mass i j hji (by omega)
    rw [(hstable j (i+1) (by omega)).1] at hm
    exact hm
  · intro i x hx
    have he := (p (i+1)).error i (by omega) x hx
    have hd : damping (Finset.range i) (p (i+1)).z x = damping (Finset.range i) z x :=
      damping_congr i (fun j hj => (hstable j (i+1) (by omega)).1) x
    rw [hd] at he
    exact he

end LipschitzCounterexample.CompactWSC
end

end OAI
