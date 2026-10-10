import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListRoutePathOrder

namespace OAI

/-! Preservation of the exact finite coordinate/route representation by one
round, and hence by the fixed number of rounds of the literal compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode
open scoped Classical

variable {Γ : SimpleGraph Pair}

private theorem range_map_congr {a b : ℕ} {f g : ℕ → Pair}
    (h : a=b) (hf : ∀ k, f k=g k) :
    (List.range (2*a+2)).map f=(List.range (2*b+2)).map g :=
  congrArg₂ List.map (funext hf) (congrArg (fun k => List.range (2*k+2)) h)

theorem tagPath_next (x : Input) (hx : Valid x.2.1)
    (P : QMAPathEmbedding (schedule x.2.1 hx) Γ) (hP : Represents x.2 hx P)
    (t : Tags (x.1,x.2.1)) :
    tagPath x t = (List.range (2*(schedule (QuantumListSchedule.value (x.1,x.2.1))
      (value_valid (x.1,x.2.1) hx)).work ((tagEquiv (x.1,x.2.1)).symm t)+2)).map
        ((nextEmbedding (x.1,x.2.1) hx P).point ((tagEquiv (x.1,x.2.1)).symm t)) := by
  rcases t with i | ⟨i,k⟩
  · change (decoratedEntry x (indexEquiv false x.2.1.2.2 i).val).2 = _
    rw [decoratedEntry_represents x hx P hP]
    change (List.range (2*(schedule x.2.1 hx).work (retainedEquiv x.2.1 hx i).val+2)).map
      (P.point (retainedEquiv x.2.1 hx i).val) = _
    exact (range_map_congr
      ((schedule x.2.1 hx).retained_work_zero (retainedEquiv x.2.1 hx i))
      (fun _ => rfl)).trans
      (range_map_congr (next_work_retained x.1 x.2.1 hx i)
        (next_point_retained x.1 x.2.1 hx P i)).symm
  · change pathPiece (decoratedEntry x (indexEquiv true x.2.1.2.2 i).val) k = _
    rw [decoratedEntry_represents x hx P hP,← selected_index x.2.1 hx i]
    let e := qmaSelectedIndex (schedule x.2.1 hx).active (activePermutation x.2.1 hx i)
    let w := (schedule x.2.1 hx).work e
    let f := P.point e
    have hw : 0<w := (schedule x.2.1 hx).selected_work_pos (activePermutation x.2.1 hx i)
    have h0 : 0<2*w+2 := by omega
    have h1 : 1<2*w+2 := by omega
    have h2 : 2<2*w+2 := by omega
    have hn : 2*(w-1)+2=2*w := by omega
    fin_cases k
    · change [lookup ((List.range (2*w+2)).map f) 1,
        lookup ((List.range (2*w+2)).map f) 2] = _
      have hl : [lookup ((List.range (2*w+2)).map f) 1,
        lookup ((List.range (2*w+2)).map f) 2] =
        (List.range 2).map (fun k => f (k+1)) := by
        rw [lookup_range f _ _ h1,lookup_range f _ _ h2]
        rfl
      exact hl.trans (range_map_congr (next_work_central x.1 x.2.1 hx i)
        (next_point_central x.1 x.2.1 hx P i)).symm
    · change [lookup ((List.range (2*w+2)).map f) 0,
        lookup ((List.range (2*w+2)).map f) 1] = _
      have hl : [lookup ((List.range (2*w+2)).map f) 0,
        lookup ((List.range (2*w+2)).map f) 1] = (List.range 2).map f := by
        rw [lookup_range f _ _ h0,lookup_range f _ _ h1]
        rfl
      exact hl.trans (range_map_congr (next_work_left x.1 x.2.1 hx i)
        (next_point_left x.1 x.2.1 hx P i)).symm
    · change (((List.range (2*w+2)).map f).drop 2).reverse = _
      have hl : (((List.range (2*w+2)).map f).drop 2).reverse =
        (List.range (2*(w-1)+2)).map (fun k => f (2*w+1-k)) := by
        rw [tail_reverse,hn]
      exact hl.trans (range_map_congr (next_work_right x.1 x.2.1 hx i)
        (next_point_right x.1 x.2.1 hx P i)).symm

theorem paths_next (x : Input) (hx : Valid x.2.1)
    (P : QMAPathEmbedding (schedule x.2.1 hx) Γ) (hP : Represents x.2 hx P) :
    paths x=List.ofFn (fun e => (List.range (2*(schedule
      (QuantumListSchedule.value (x.1,x.2.1)) (value_valid (x.1,x.2.1) hx)).work e+2)).map
        ((nextEmbedding (x.1,x.2.1) hx P).point e)) := by
  rw [paths_tagged]
  apply congrArg List.ofFn
  funext e
  have h := tagPath_next x hx P hP (tagEquiv (x.1,x.2.1) e)
  simpa only [Equiv.symm_apply_apply] using h

theorem value_represents (x : Input) (hx : Valid x.2.1)
    (P : QMAPathEmbedding (schedule x.2.1 hx) Γ) (hP : Represents x.2 hx P) :
    Represents (value x) (value_valid (x.1,x.2.1) hx) (nextEmbedding (x.1,x.2.1) hx P) :=
  ⟨positions_next x hx P hP,paths_next x hx P hP⟩

theorem iterate_state (N : ℚ) (s : State) (k : ℕ) :
    (iterate N k s).1=QuantumListSchedule.iterate N k s.1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change QuantumListSchedule.value (N,(iterate N k s).1)=_
    rw [ih]
    rfl

theorem iterate_represents (N : ℚ) (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs) Γ) (hP : Represents s hs P)
    {X Y : ℕ} (hbox : P.Bounded X Y) (k : ℕ) :
    ∃ (hs' : Valid (iterate N k s).1)
      (P' : QMAPathEmbedding (schedule (iterate N k s).1 hs') Γ),
      Represents (iterate N k s) hs' P' ∧ P'.Bounded X Y := by
  induction k with
  | zero => exact ⟨hs,P,hP,hbox⟩
  | succ k ih =>
    obtain ⟨hk,Q,hQ,hQbox⟩ := ih
    exact ⟨value_valid (N,(iterate N k s).1) hk,
      nextEmbedding (N,(iterate N k s).1) hk Q,
      value_represents (N,iterate N k s) hk Q hQ,
      nextEmbedding_bounded (N,(iterate N k s).1) hk Q hQbox⟩

theorem compile_realization {N : ℚ} (hN : 0<N) (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs) Γ) (hP : Represents s hs P)
    {D X Y : ℕ} (hD : ∀ e ∈ s.1.2.2, e.1≤D) (hbox : P.Bounded X Y) :
    ∃ (hs' : Valid (iterate N D s).1)
      (P' : QMAPathEmbedding (schedule (iterate N D s).1 hs') Γ),
      Represents (iterate N D s) hs' P' ∧ P'.Bounded X Y ∧
      (∀ e, Γ.Adj (P'.position ((schedule (iterate N D s).1 hs').graph.left e))
        (P'.position ((schedule (iterate N D s).1 hs').graph.right e))) ∧
      (iterate N D s).1.1+(iterate N D s).1.2.2.length≤5^D*(s.1.1+s.1.2.2.length) ∧
      |QuantumListSchedule.energy (iterate N D s).1-QuantumListSchedule.energy s.1|≤(D:ℝ)/(N:ℝ) := by
  obtain ⟨hs',Q,hQ,hQbox⟩ := iterate_represents N s hs P hP hbox D
  refine ⟨hs',Q,hQ,hQbox,?_,?_,?_⟩
  · have hc : ∀ e ∈ (iterate N D s).1.2.2, e.1=0 := by
      rw [iterate_state]
      exact QuantumListSchedule.iterate_complete N s.1 hD
    exact Q.adjacent_of_complete (fun e => hc _ (List.get_mem _ e))
  · rw [iterate_state]
    exact QuantumListSchedule.iterate_size N s.1 D
  · rw [iterate_state]
    exact QuantumListSchedule.iterate_energy_error hN s.1 hs D

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
