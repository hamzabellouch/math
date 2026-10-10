import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorIteration

namespace OAI

/-! Fresh mediator pairs give a simple unordered edge enumeration. This
supplies the cross-edge cancellation hypothesis in the global Hubbard model. -/

namespace ContinuumCoulomb.MediatorIteration
open MediatorGraph

def edgeMatches {α : Type*} (a b c d : α) : Prop :=
  (a = c ∧ b = d) ∨ (a = d ∧ b = c)

theorem edgeMatches_symm {α : Type*} {a b c d : α}
    (h : edgeMatches a b c d) : edgeMatches c d a b := by
  rcases h with h | h
  · exact Or.inl ⟨h.1.symm, h.2.symm⟩
  · exact Or.inr ⟨h.2.symm, h.1.symm⟩

def Bonds.Simple {n r : ℕ} (F : Bonds n r) : Prop :=
  ∀ e f, edgeMatches (F.left e) (F.right e) (F.left f) (F.right f) → e = f

theorem Bonds.Simple.hypothesis {n r : ℕ} {F : Bonds n r} (hF : F.Simple) :
    ∀ e f, e ≠ f →
      ¬(F.left e = F.left f ∧ F.right e = F.right f) ∧
      ¬(F.left e = F.right f ∧ F.right e = F.left f) := by
  intro e f hne
  exact ⟨fun h => hne (hF e f (Or.inl h)), fun h => hne (hF e f (Or.inr h))⟩

theorem lift_simple {n q : ℕ} (r : ℕ) (F : Bonds n q) (hF : F.Simple) :
    (lift r F).Simple := by
  intro e f h
  apply hF e f
  rcases h with h | h
  · exact Or.inl ⟨old_injective n r h.1, old_injective n r h.2⟩
  · exact Or.inr ⟨old_injective n r h.1, old_injective n r h.2⟩

theorem central_simple (n r : ℕ) (Delta : ℚ) : (central n r Delta).Simple := by
  intro e f h
  change edgeMatches (fresh n r e 0) (fresh n r e 1)
    (fresh n r f 0) (fresh n r f 1) at h
  rcases h with h | h
  · exact congrArg Prod.fst (fresh_injective n r (a₁ := (e, 0)) (a₂ := (f, 0)) h.1)
  · have hs := congrArg Prod.snd (fresh_injective n r (a₁ := (e, 0)) (a₂ := (f, 1)) h.1)
    norm_num at hs

theorem spokes_simple {n r : ℕ} (F : Bonds n r) (hF : F.NoLoops)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℚ) :
    (spokes F member amplitude).Simple := by
  intro e f h
  obtain ⟨⟨a, s⟩, rfl⟩ := finProdFinEquiv.surjective e
  obtain ⟨⟨b, t⟩, rfl⟩ := finProdFinEquiv.surjective f
  simp only [edgeMatches, spokes, Equiv.symm_apply_apply] at h
  rcases h with h | h
  · have hab := congrArg Prod.fst (fresh_injective n r
      (a₁ := (a, if s = 0 then 0 else member a))
      (a₂ := (b, if t = 0 then 0 else member b)) h.2)
    dsimp only at hab
    subst b
    fin_cases s <;> fin_cases t
    · rfl
    · exact False.elim (hF a (old_injective n r (by simpa using h.1)))
    · exact False.elim (hF a (old_injective n r (by simpa using h.1)).symm)
    · rfl
  · exact False.elim (old_ne_fresh n r _ _ _ h.1)

theorem join_simple {n q r : ℕ} (F : Bonds n q) (K : Bonds n r)
    (hF : F.Simple) (hK : K.Simple)
    (hcross : ∀ e f, ¬edgeMatches (F.left e) (F.right e) (K.left f) (K.right f)) :
    (join F K).Simple := by
  intro e f h
  obtain ⟨e, rfl⟩ := finSumFinEquiv.surjective e
  obtain ⟨f, rfl⟩ := finSumFinEquiv.surjective f
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      simp only [join, Equiv.symm_apply_apply, Sum.elim_inl] at h
      exact congrArg (fun i => finSumFinEquiv (Sum.inl i)) (hF e f h)
    | inr f =>
      simp only [join, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr] at h
      exact False.elim (hcross e f h)
  | inr e =>
    cases f with
    | inl f =>
      simp only [join, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr] at h
      exact False.elim (hcross f e (edgeMatches_symm h))
    | inr f =>
      simp only [join, Equiv.symm_apply_apply, Sum.elim_inr] at h
      exact congrArg (fun i => finSumFinEquiv (Sum.inr i)) (hK e f h)

theorem central_spokes_simple {n r : ℕ} (F : Bonds n r) (hF : F.NoLoops)
    (member : Fin r → Fin 2) (Delta : ℚ) (amplitude : Fin r → ℚ) :
    (join (central n r Delta) (spokes F member amplitude)).Simple := by
  apply join_simple _ _ (central_simple n r Delta) (spokes_simple F hF member amplitude)
  intro e f h
  rcases h with h | h
  · exact old_ne_fresh n r _ _ _ h.1.symm
  · exact old_ne_fresh n r _ _ _ h.2.symm

theorem lift_stage_simple {n q r : ℕ} (K : Bonds n q) (F : Bonds n r)
    (hK : K.Simple) (hF : F.NoLoops) (member : Fin r → Fin 2)
    (Delta : ℚ) (amplitude : Fin r → ℚ) :
    (join (lift r K) (join (central n r Delta) (spokes F member amplitude))).Simple := by
  apply join_simple _ _ (lift_simple r K hK) (central_spokes_simple F hF member Delta amplitude)
  intro e f h
  obtain ⟨f, rfl⟩ := finSumFinEquiv.surjective f
  cases f with
  | inl f =>
    simp only [join, Equiv.symm_apply_apply, Sum.elim_inl] at h
    rcases h with h | h
    · exact old_ne_fresh n r _ _ _ h.1
    · exact old_ne_fresh n r _ _ _ h.1
  | inr f =>
    simp only [join, Equiv.symm_apply_apply, Sum.elim_inr] at h
    rcases h with h | h
    · exact old_ne_fresh n r _ _ _ h.2
    · exact old_ne_fresh n r _ _ _ h.1

theorem firstGraph_simple {n r : ℕ} (F : Bonds n r) (hF : F.NoLoops) (W G : ℕ) :
    (firstGraph F W G).Simple :=
  central_spokes_simple F hF _ _ _

theorem secondPaths_simple {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (secondPaths F W G).Simple :=
  central_spokes_simple _ (spokes_noLoops F _ _) _ _ _

theorem finalGraph_simple {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (finalGraph F W G).Simple := by
  apply lift_stage_simple (retainedCentral F W G) (secondPaths F W G)
  · exact lift_simple _ _ (central_simple _ _ _)
  · exact join_noLoops _ _ (central_noLoops _ _ _) (spokes_noLoops _ _ _)

end ContinuumCoulomb.MediatorIteration

end OAI
