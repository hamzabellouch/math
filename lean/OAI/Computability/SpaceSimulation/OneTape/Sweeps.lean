import OAI.Computability.SpaceSimulation.OneTape.Wander

namespace OAI

namespace Fifths.Single
open Finset Square
variable {X : Type} (M : Single X)

def across (x : List X) (W : Site) (n : ℕ) := M.place x W n != M.place x W (n+1)
def crossings (x : List X) (W : Site) (n : ℕ) :=
  ∑ j ∈ Finset.range n, (M.across x W j).toNat
theorem crossings_mono (x : List X) (W : Site) : Monotone (M.crossings x W) :=
  monotone_nat_of_le_succ (fun t => by simp [crossings, sum_range_succ])

section
variable (x : List X) (W : Site)

theorem tick_value {n : ℕ} (h : n ≤ W.T) :
    (M.parseCtrl W.T (M.view x W n).ctrl).tick.val = n := by
  simp only [view, M.roundtrip]
  exact Square.cut_ok _ _ h
theorem waited (n i : ℕ) (l : n ≤ W.T)
    (p : ¬(n<W.T ∧ M.place x W n = i)) :
    M.localStep x W i ((M.view x W n).ctrl,(M.view x W n).cells i) =
      ((M.view x W n).ctrl,(M.view x W n).cells i) := by
  dsimp only [localStep]
  rw [M.tick_value x W l]
  have e := M.so_select x W n
  unfold chooseBlock at e
  rw [e,ite_eq_right p]

/-- Sweep from time t with the currently selected block. If neither
cap nor crossing reached, advanced just one tick per local iteration.
At a crossing bank its credit. Unselected buffers unchanged throughout.
-/
theorem sweep_time (t : ℕ) (l : t ≤ W.T) (n : ℕ) :
    let i := M.place x W t
    ∃ j, t ≤ j ∧ j ≤ W.T ∧
      M.sweep x W (M.view x W t).ctrl ((M.view x W t).cells i) n =
        ((M.view x W j).ctrl,(M.view x W j).cells i) ∧
      (∀ u, u ≠ i → (M.view x W t).cells u = (M.view x W j).cells u) ∧
      (j = W.T ∨
       M.place x W j = i ∧ j = t+n ∨
       M.place x W j ≠ i ∧ M.crossings x W t < M.crossings x W j) := by
  induction n with
  | zero =>
    exact ⟨t,le_rfl,l,rfl,fun _ _ => rfl,.inr (.inl ⟨rfl,rfl⟩)⟩
  | succ n ih =>
    dsimp only at ih ⊢
    obtain ⟨j,p,h,s,v,g⟩ := ih
    rw [sweep,s,M.so_select]
    rcases g with a|⟨a,b⟩|⟨a,b⟩
    · have d : ¬ (j<W.T ∧ M.place x W j = M.place x W t) := by omega
      exact ⟨j,p,h,M.waited x W j _ h d,v,.inl a⟩
    · by_cases q : j = W.T
      · exact ⟨j,p,h,M.waited x W j _ h (by omega),v,.inl q⟩
      have e : j < W.T := by omega
      obtain ⟨w,y⟩ := M.realize x W j (M.place x W t) e a
      refine ⟨j+1,by omega,e,w,fun u r => (v u r).trans (y u r),?_⟩
      by_cases z : M.place x W (j+1) = M.place x W t
      · exact .inr (.inl ⟨z,by omega⟩)
      · have r : M.crossings x W j < M.crossings x W (j+1) := by
          have g : M.across x W j = true := by simp [across, a,Ne.symm z]
          simp [crossings,sum_range_succ,g]
        exact .inr (.inr ⟨z,lt_of_le_of_lt (M.crossings_mono x W p) r⟩)
    · exact ⟨j,p,h,M.waited x W j _ h (fun h => a h.2),v,.inr (.inr ⟨a,b⟩)⟩

theorem visited (t : ℕ) (l : t≤W.T) :
    ∃ j, t ≤ j ∧ j ≤ W.T ∧
      (M.tour x W).step (M.view x W t) = M.view x W j ∧
      (j = W.T ∨ M.crossings x W t < M.crossings x W j) := by
  obtain ⟨j,p,h,e,u,q⟩ := M.sweep_time x W t l W.T
  refine ⟨j,p,h,?_,?_⟩
  · dsimp only [Tour.step,tour]
    rw [M.so_select,e]
    have a : Function.update (M.view x W t).cells (M.place x W t) ((M.view x W j).cells (M.place x W t)) =
        (M.view x W j).cells := by
      funext k
      by_cases e : k=M.place x W t
      · subst k; simp
      · rw [Function.update_of_ne e]; exact u k e
    dsimp only
    rw [a]
  · rcases q with q|⟨q,f⟩|⟨q,f⟩
    · exact .inl q
    · left; omega
    · exact .inr f
theorem story_ok (n : ℕ) :
    ∃ t, t ≤ W.T ∧ (M.tour x W).story n = M.view x W t ∧
      (t = W.T ∨ n ≤ M.crossings x W t) := by
  induction n with
  | zero => exact ⟨0,Nat.zero_le _,rfl,.inr (Nat.zero_le _)⟩
  | succ n ih =>
    obtain ⟨t,h,p,g⟩ := ih
    rw [Tour.story,p]
    obtain ⟨j,v,l,e,k⟩ := M.visited x W t h
    exact ⟨j,l,e, by omega⟩

noncomputable def doneAt (z : ℕ) : Bool :=
  decide ((M.parseCtrl W.T z).tick.val = W.T)
noncomputable def predict (z : ℕ) : M.Outcome :=
  M.finish (M.parseCtrl W.T z).state

theorem reported {n}
    (p : M.doneAt W ((M.tour x W).story n).ctrl = true) :
    M.predict W ((M.tour x W).story n).ctrl = M.outcome x W.T := by
  obtain ⟨j,l,e,q⟩ := M.story_ok x W n
  unfold doneAt at p
  rw [e, M.tick_value x W l] at p
  rw [e, of_decide_eq_true p]
  simp [predict,view,M.roundtrip,outcome,capture]
theorem closes {n} (l : M.crossings x W W.T < n) :
    M.doneAt W ((M.tour x W).story n).ctrl = true := by
  obtain ⟨j,h,e,k⟩ := M.story_ok x W n
  have q := M.crossings_mono x W h
  unfold doneAt; rw [e,M.tick_value x W h,decide_eq_true_eq]
  omega
end

-- At most one crossing per unit move when summing across offsets.
private theorem divides_shift {b u m : ℕ}
    (h : (u+m)/b ≠ (u+(m+1))/b) : b ∣ u+m+1 := by
  by_contra l
  rw [← add_assoc,Nat.succ_div] at h
  simp [l] at h
private theorem unique_cross {b u v m n : ℕ} (_p : 0 < b) (l : u<b) (h : v<b)
    (x : m ≤ n+1) (y : n ≤ m+1)
    (a : (u+m)/b ≠ (u+n)/b) (c : (v+m)/b ≠ (v+n)/b) : u=v := by
  have f : ∀ u v s : ℕ, u < v → v < b →
      ¬ (b ∣ u+s+1 ∧ b ∣ v+s+1) := by
    rintro u v s q h ⟨a,c⟩
    have r : b ∣ v-u := by
      rw [show v-u=(v+s+1)-(u+s+1) by omega]
      exact Nat.dvd_sub c a
    have := Nat.le_of_dvd (show 0<v-u by omega) r
    omega
  suffices g : ∃ s, b ∣ u+s+1 ∧ b ∣ v+s+1 by
    obtain ⟨s,r,t⟩ := g
    rcases lt_trichotomy u v with a|a|a
    · exact (f u v s a h ⟨r,t⟩).elim
    · exact a
    · exact (f v u s a l ⟨t,r⟩).elim
  rcases le_total m n with e|e
  · have g : n=m+1 := by
      by_contra h; have g : m=n := by omega
      exact a (by rw [g])
    rw [g] at a c
    exact ⟨m,divides_shift a,divides_shift c⟩
  · have g : m=n+1 := by
      by_contra h; have g : m=n := by omega
      exact a (by rw [g])
    rw [g] at a c
    exact ⟨n,divides_shift a.symm,divides_shift c.symm⟩

section
variable (x : List X) (T k : ℕ) (kp : 0<k)
private theorem atMostOne (j : ℕ) (e : j < T) :
    (∑ a : Fin (k*k), (M.across x (Site.mk T k kp a) j).toNat) ≤ 1 := by
  let u := M.seenPos x T j
  let v := M.seenPos x T (j+1)
  have y : disp u = (M.atTime x j).tape.pos := M.seenBack x e.le
  have z : disp v = (M.atTime x (j+1)).tape.pos := M.seenBack x e
  have g : ∃ d : Dir, disp v = disp u + d.delta := by
    rw [y,z]; exact ⟨_,rfl⟩
  obtain ⟨d,p⟩ := g
  have r := d.bounds
  unfold disp at p
  let f := fun a : Fin (k*k) => M.across x (Site.mk T k kp a) j
  have m (a : Fin (k*k)) (e : f a = true) :
      (a.val+u.val)/(k*k) ≠ (a.val+v.val)/(k*k) := by
    simpa [f,across,place,Site.home,Site.b,u,v] using e
  change (∑ a, (f a).toNat) ≤ 1
  by_cases l : ∃ a, f a = true
  · obtain ⟨w,h⟩ := l
    rw [sum_eq_single_of_mem w (mem_univ w)]
    · simp [h]
    · intro a _ b
      cases e : f a
      · rfl
      exact (b (Fin.ext (unique_cross (Nat.mul_pos kp kp) a.isLt w.isLt
        (by omega) (by omega) (m a e) (m w h)))).elim
  · push Not at l
    have h (a) := Bool.eq_false_iff.mpr (l a)
    simp [h]

theorem offsets :
    (∑ a : Fin (k*k), M.crossings x (Site.mk T k kp a) T) ≤ T := by
  unfold crossings; rw [sum_comm]
  calc
    _ ≤ ∑ _ ∈ Finset.range T, 1 := sum_le_sum (fun i v =>
      M.atMostOne x T k kp i (mem_range.mp v))
    _ = T := by simp

theorem sufficient (h : T ≤ k^5) :
    ∃ a : Fin (k*k), M.doneAt (Site.mk T k kp a)
      (((M.tour x (Site.mk T k kp a)).story ((k+1)*(k*k))).ctrl) = true := by
  suffices h : ∃ a : Fin (k*k), M.crossings x (Site.mk T k kp a) T <
        (k+1)*(k*k) from
    let ⟨a,q⟩ := h; ⟨a,M.closes x _ q⟩
  by_contra! b
  have f : k*k*((k+1)*(k*k)) ≤ T := by
    have p : (∑ _a : Fin (k*k), (k+1)*(k*k)) ≤ _ :=
      sum_le_sum (fun i _ => b i)
    simpa using p.trans (M.offsets x T k kp)
  have v : 0 < k^4 := pow_pos kp _
  rw [show k*k*((k+1)*(k*k)) = k^5 + k^4 by ring] at f
  omega

end
end Fifths.Single

end OAI
