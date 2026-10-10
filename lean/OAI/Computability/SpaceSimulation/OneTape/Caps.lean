import OAI.Computability.SpaceSimulation.OneTape.Trial
import OAI.Computability.SpaceSimulation.OneTape.Sizes

namespace OAI

namespace Fifths.Single
open Entry Cost Fifths.Comp
variable {X I U : Type} (M : Single X)

def choiceSite (T a : ℕ) : Site :=
  let k := K T
  { T := T, k := k, positive := K_pos _
    left := ⟨a%(k*k),Nat.mod_lt _ (Nat.mul_pos (K_pos _) (K_pos _))⟩ }

theorem choice_at {T : ℕ} (a : Fin (K T * K T)) :
    choiceSite T a.val = Site.mk T (K T) (K_pos T) a := by
  have h : (choiceSite T a.val).left.val = a.val :=
    Nat.mod_eq_of_lt a.isLt
  exact congrArg (Site.mk T (K T) (K_pos T)) (Fin.ext h)

/-- Capped evaluator. All offsets, workspace reused. -/
theorem cappedRegister (A : M.Sym) (d : ℕ)
    {x : I → List X} {S T a : I → ℕ}
    (q : Comp x S a T) (h : Scaled S (fun i => Cost.bound d (T i)))
    (l : ∃ B, ∀ i, M.Gives A (x i) (T i) (B*(S i+1))) :
    Tells x S a (fun i => M.outcome (x i) (T i)) := by
  let n : I → ℕ := fun i => K (T i) * K (T i)
  let w := fun i j => choiceSite (T i) j
  let f := fun i j => M.complete (x i) (w i j)
  have u := Cost.ofT q
  have v : Comp x S a n := u.mul u
  have g : ∀ {U : Type} (r : U → I) {e o : U → ℕ},
      ReComp x S r e (fun i => a (r i)) →
      ReComp x S r e o →
      ReComp x S r e (fun i => (f (r i) (o i)).toNat) ∧
      Tells (fun i => x (r i)) (fun i => S (r i)) e
        (fun i => M.readout (x (r i)) (w (r i) (o i))) := by
    intro U r e o p l₀
    let W := fun i => w (r i) (o i)
    let X' := fun i => x (r i)
    let S' := fun i => S (r i)
    have est := M.estimate W X' d (fun _ => rfl)
    have c : M.Kit A X' S' e W :=
      { ofCap := p.trans (q.pull r)
        ofK := p.trans (u.pull r)
        ofPosition := l₀.mod (p.trans (v.pull r))
        budget := est.1.up (h.pull r)
        access := by obtain ⟨B,l⟩ := l; exact ⟨B,fun i => l (r i)⟩ }
    exact c.solves (est.2.trans (h.pull r))

  have k := scanPick f v (fun e p q =>
    (g (fun i : Before n => i.val.1) p q).1)

  have p i : f i (Scan.pick (f i) (n i)) = true := by
    obtain ⟨a,h⟩ := M.some_complete (x i) (T i) _ (K_pos _) (bigK _)
    apply (Scan.pick_spec _ _ ?_).2
    exact ⟨a.val,a.isLt,by rw [← choice_at] at h; exact h⟩
  refine Comp.congr ((g id (Comp.refl q.source) k).2) (fun i => ?_)
  exact congrArg code (M.if_complete _ _ (p i))

theorem capFits (d : ℕ) (T : I → ℕ) :
    Fits (fun i => Cost.bound d (T i)) T := by
  let S := fun i => Cost.bound d (T i)
  exact (Scaled.refl S).of_le (fun i => Nat.le_trans (Nat.le_succ _) (lg_le d (T i)))

theorem stable (x : List X) {t u}
    (p : (M.outcome x t).2) (q : (M.outcome x u).2) :
    M.outcome x t = M.outcome x u := by
  have h (t u : ℕ) (p : (M.outcome x t).2 = true) (q : t ≤ u) :
      M.outcome x u = M.outcome x t := by
    nth_rw 1 [show u=t+(u-t) by omega]
    unfold outcome
    rw [M.absorbed x p (u-t)]
  cases le_total t u with
  | inl r => exact (h t u p r).symm
  | inr r => exact h u t q r

/-- Unknown-time branch. Keep predicate is computed by a fully
charged invocation; `n` below is a proof index for the represented
call trajectory, not a program input. -/
theorem noCapRegister (A : M.Sym) (d c : ℕ)
    {x : I → List X} {t : I → ℕ}
    (h : ∀ i, (M.outcome (x i) (t i)).2 = true)
    (p : ∀ i T, T ≥ 2 → M.Gives A (x i) T (c*(Cost.bound d T+1))) :
    Tells x (fun i => Cost.bound d (t i+2)) (fun _ => 0)
      (fun i => M.outcome (x i) (t i)) := by
  classical
  let S i := Cost.bound d (t i+2)
  let cap (j : ℕ) := j+2
  let m i j := (M.outcome (x i) (cap j)).2 = true
  have l i : m i (t i) := by
    change (M.outcome (x i) (t i+2)).2 = true
    unfold outcome
    rw [M.absorbed (x i) (h i) 2]
    exact h i
  have v i : ∃ j, m i j := ⟨_,l i⟩
  let n i := Nat.find (v i)
  have b i : n i ≤ t i := Nat.find_min' (v i) (l i)
  have g i : m i (n i) := Nat.find_spec (v i)
  have fS : Fits S (fun i => t i+2) := capFits d (fun i => t i+2)
  have c' : ∀ {U : Type} (r : U → I) {a u : U → ℕ},
      ReComp x S r a (fun i => cap (u i)) → (∀ i, u i ≤ t (r i)) →
      Tells (fun i => x (r i)) (fun i => S (r i)) a
        (fun i => M.outcome (x (r i)) (cap (u i))) := by
    intro U r a u h l
    have j (i : U) : Cost.bound d (cap (u i)) ≤ S (r i) :=
      bound_mono d (Nat.add_le_add_right (l i) _)
    exact M.cappedRegister A d h ((Scaled.refl _).of_le j)
      ⟨c, fun i => (p (r i) (cap (u i)) (by unfold cap; omega)).mono
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (j i) _))⟩
  have w : Comp x S (fun _ => cap 0) (fun i => cap (n i)) := by
    apply Comp.loop n (fun _ j => cap j)
    · let f : Before n → I := fun i => i.1.1
      have e : Comp (fun i => x (f i)) (fun i => S (f i))
          (fun (i : Before n) => cap i.1.2) (fun i => cap i.1.2) :=
        Comp.refl ((fS.pull f).mono (fun i =>
          Nat.add_le_add_right (i.2.le.trans (b _)) _))
      exact e.plus1 -- cap(j+1)
    · let f : Through n → I := fun i => i.1.1
      let s := fun (i : Through n) => i.1.2
      have z (i : Through n) : s i ≤ t (f i) := i.2.trans (b _)
      have v₁ : Comp (fun i => x (f i)) (fun i => S (f i))
          (fun i => cap (s i)) (fun i => cap (s i)) := Comp.refl
        ((fS.pull f).mono (fun i => Nat.add_le_add_right (z i) _))
      apply (Entry.finite_map (fun v : M.Outcome => (!v.2).toNat) (c' f v₁ z)).congr
      intro i
      have w : s i ≤ n (f i) := i.2
      change (!(M.outcome (x (f i)) (cap (s i))).2).toNat =
        (decide (s i < n (f i))).toNat
      rcases w.lt_or_eq with e|e
      · have y := Nat.find_min (v (f i)) e
        change (M.outcome _ _).2 ≠ true at y
        simp [e,Bool.eq_false_iff.mpr y]
      · rw [e, g (f i)]
        simp
  have j := c' id w b
  refine (Comp.trans (Comp.constant (Fits.const S 0) (cap 0)) j).congr
    (fun i => congrArg code (M.stable (x i) (g i) (h i)))
end Fifths.Single

end OAI
