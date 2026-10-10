import OAI.Dynamics.ConditionalShuffle.ResetPartial

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter Topology
namespace Thorp.Conditional

def reversePosition (d : ℕ) : State d where
  toFun x := fun i => x i.rev
  invFun x := fun i => x i.rev
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

@[simp] lemma reversePosition_apply (d : ℕ) (x : Position d) (i : Fin d) :
    reversePosition d x i = x i.rev := rfl

@[simp] lemma reversePosition_involutive (d : ℕ) (x : Position d) :
    reversePosition d (reversePosition d x) = x := by ext i; simp

lemma reversePosition_cons (d : ℕ) (b : Bool) (x : Position d) :
    reversePosition (d+1) (Fin.cons b x) = Fin.snoc (reversePosition d x) b := by
  ext i; refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp [Fin.rev_castSucc]

lemma reversePosition_snoc (d : ℕ) (b : Bool) (x : Position d) :
    reversePosition (d+1) (Fin.snoc x b) = Fin.cons b (reversePosition d x) := by
  have := congrArg (reversePosition (d+1)) (reversePosition_cons d b (reversePosition d x))
  simpa only [reversePosition_involutive] using this.symm

def reverseCoins (d : ℕ) : Coins (d+1) ≃ Coins (d+1) where
  toFun c := c ∘ reversePosition d
  invFun c := c ∘ reversePosition d
  left_inv c := by funext x; change c (reversePosition d (reversePosition d x)) = c x; rw [reversePosition_involutive]
  right_inv c := by funext x; change c (reversePosition d (reversePosition d x)) = c x; rw [reversePosition_involutive]

lemma reverse_step_cancel (d : ℕ) (c : Coins (d+1)) (x : Position (d+1)) :
    step (d+1) (reverseCoins d c) (reversePosition (d+1) (step (d+1) c x)) =
      reversePosition (d+1) x := by
  obtain ⟨⟨b,x⟩,rfl⟩ := (Fin.consEquiv (fun _ : Fin (d+1) => Bool)).surjective x
  change step (d+1) (reverseCoins d c) (reversePosition (d+1) (step (d+1) c (Fin.cons b x))) = reversePosition (d+1) (Fin.cons b x)
  rw [step_cons d c b x, scatterPosition_eq_snoc, reversePosition_snoc, step_cons d (reverseCoins d c),
    scatterPosition_eq_snoc, reversePosition_cons]
  have he : reverseCoins d c (reversePosition d x) = c x := by change c (reversePosition d (reversePosition d x)) = c x; rw [reversePosition_involutive]
  rw [he, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

lemma reverse_step (d : ℕ) (c : Coins (d+1)) :
    step (d+1) (reverseCoins d c) =
      reversePosition (d+1) * (step (d+1) c)⁻¹ * reversePosition (d+1) := by
  apply Equiv.ext; intro x
  have hh := reverse_step_cancel d c ((step (d+1) c).symm (reversePosition (d+1) x))
  change step (d+1) (reverseCoins d c) x =
    reversePosition (d+1) ((step (d+1) c).symm (reversePosition (d+1) x))
  simpa only [Equiv.apply_symm_apply, reversePosition_involutive] using hh

def reverseHistory (d t : ℕ) : History (d+1) t ≃ History (d+1) t where
  toFun ω := fun i => reverseCoins d (ω i.rev)
  invFun ω := fun i => reverseCoins d (ω i.rev)
  left_inv ω := by
    funext i x
    change ω i.rev.rev (reversePosition d (reversePosition d x)) = ω i x
    rw [Fin.rev_rev, reversePosition_involutive]
  right_inv ω := by
    funext i x
    change ω i.rev.rev (reversePosition d (reversePosition d x)) = ω i x
    rw [Fin.rev_rev, reversePosition_involutive]

lemma run_cons (d t : ℕ) (c : Coins d) (ω : History d t) :
    run d (t+1) (Fin.cons c ω) = run d t ω * step d c := by
  simp [run, List.ofFn_succ]

lemma reverseHistory_cons (d t : ℕ) (c : Coins (d+1)) (ω : History (d+1) t) :
    reverseHistory d (t+1) (Fin.cons c ω) = Fin.snoc (reverseHistory d t ω) (reverseCoins d c) := by
  ext i; refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [reverseHistory]
  · simp [reverseHistory, Fin.rev_castSucc]

lemma reverse_run (d t : ℕ) (ω : History (d+1) t) :
    run (d+1) t (reverseHistory d t ω) =
      reversePosition (d+1) * (run (d+1) t ω)⁻¹ * reversePosition (d+1) := by
  have hr : reversePosition (d+1) * reversePosition (d+1) = 1 := by
    apply Equiv.ext; intro x; exact reversePosition_involutive (d+1) x
  induction t with
  | zero => simp [run_zero, hr]
  | succ t ih =>
      obtain ⟨⟨c,ω⟩,rfl⟩ := (Fin.consEquiv (fun _ : Fin (t+1) => Coins (d+1))).surjective ω
      change run (d+1) (t+1) (reverseHistory d (t+1) (Fin.cons c ω)) =
        reversePosition (d+1) * (run (d+1) (t+1) (Fin.cons c ω))⁻¹ * reversePosition (d+1)
      rw [reverseHistory_cons, run_succ]
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
      rw [ih, reverse_step, run_cons, mul_inv_rev]
      calc
        _ = reversePosition (d+1) * (step (d+1) c)⁻¹ *
            (reversePosition (d+1) * reversePosition (d+1)) *
            (run (d+1) t ω)⁻¹ * reversePosition (d+1) := by group
        _ = _ := by rw [hr]; group

end Thorp.Conditional

end

end OAI
