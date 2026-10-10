import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactGlobal

namespace OAI

/-! Uniform all-site and nonedge separation for the actual final graph. -/

noncomputable section
namespace ContinuumCoulomb.ContactMediator
open MediatorIteration

@[simp] theorem localVertex_old_zero {n r : ℕ} (a b : Fin n) (e : Fin r) :
    localVertex a b e (localOld 0) = siteEquiv n r (Sum.inl a) := by
  simp [localVertex, localOld]

@[simp] theorem localVertex_old_one {n r : ℕ} (a b : Fin n) (e : Fin r) :
    localVertex a b e (localOld 1) = siteEquiv n r (Sum.inl b) := by
  simp [localVertex, localOld]

@[simp] theorem localVertex_internal {n r : ℕ} (a b : Fin n) (e : Fin r) (u : LocalInternal) :
    localVertex a b e (Sum.inr u) = siteEquiv n r (Sum.inr (e, u)) := rfl

def Nonedge (d : SquareLatticeHeisenberg) (W G : ℕ) (x y : GlobalSite d) : Prop :=
  ¬∃ a, samePair ((finalGraph d.bonds W G).left a) ((finalGraph d.bonds W G).right a) x y

theorem Nonedge.symm {d : SquareLatticeHeisenberg} {W G : ℕ} {x y : GlobalSite d}
    (h : Nonedge d W G x y) : Nonedge d W G y x := by
  rintro ⟨a, ha⟩
  exact h ⟨a, samePair_swap_target ha⟩

theorem globalPosition_local_nonedge (d : SquareLatticeHeisenberg) (W G : ℕ)
    (P : Fin d.edges → LocalSite → ContactPoint)
    (h₀ : ∀ e, P e (localOld 0) = contactPoint 0 0)
    (h₁ : ∀ e, P e (localOld 1) = contactPoint 17 0)
    (hsep : ∀ e x y, x ≠ y → Nonedge d W G
      (localVertex (d.left e) (d.right e) e x)
      (localVertex (d.left e) (d.right e) e y) → 6 / 5 < dist (P e x) (P e y))
    (e : Fin d.edges) (x y : LocalSite) (hne : x ≠ y)
    (hn : Nonedge d W G (localVertex (d.left e) (d.right e) e x)
      (localVertex (d.left e) (d.right e) e y)) :
    6 / 5 < dist (globalPosition d P (localVertex (d.left e) (d.right e) e x))
      (globalPosition d P (localVertex (d.left e) (d.right e) e y)) := by
  rw [globalPosition_local d P h₀ h₁, globalPosition_local d P h₀ h₁,
    ContactGridEdge.place_dist]
  exact hsep e x y hne hn

/-- Combining the local nonedge theorem with distinct-strip and external
vertex estimates gives the fixed margin on every nonedge of finalGraph. -/
theorem globalPosition_nonedge (d : SquareLatticeHeisenberg) (W G : ℕ)
    (P : Fin d.edges → LocalSite → ContactPoint)
    (h₀ : ∀ e, P e (localOld 0) = contactPoint 0 0)
    (h₁ : ∀ e, P e (localOld 1) = contactPoint 17 0)
    (hsep : ∀ e x y, x ≠ y → Nonedge d W G
      (localVertex (d.left e) (d.right e) e x)
      (localVertex (d.left e) (d.right e) e y) → 6 / 5 < dist (P e x) (P e y))
    (hP : ∀ e x, dist (P e x)
      (contactBaseGadgetPosition (edgeNegative d.bonds e) (localToContact x)) < 1 / 20)
    (x y : GlobalSite d) (hne : x ≠ y) (hn : Nonedge d W G x y) :
    6 / 5 < dist (globalPosition d P x) (globalPosition d P y) := by
  obtain ⟨x, rfl⟩ := (siteEquiv d.vertices d.edges).surjective x
  obtain ⟨y, rfl⟩ := (siteEquiv d.vertices d.edges).surjective y
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      have hij : i ≠ j := fun h => hne (by subst j; rfl)
      simpa only [globalPosition_old] using
        lt_of_lt_of_le (by norm_num : (6 / 5 : ℝ) < 17)
          (contactGridPoint_separation (fun h => hij (d.coordinate_injective h)))
    | inr eu =>
      rcases eu with ⟨e, u⟩
      by_cases hi₀ : i = d.left e
      · subst i
        simpa only [localVertex_old_zero, localVertex_internal] using
          globalPosition_local_nonedge d W G P h₀ h₁ hsep e (localOld 0) (Sum.inr u)
            (by simp [localOld]) (by simpa only [localVertex_old_zero, localVertex_internal] using hn)
      · by_cases hi₁ : i = d.right e
        · subst i
          simpa only [localVertex_old_one, localVertex_internal] using
            globalPosition_local_nonedge d W G P h₀ h₁ hsep e (localOld 1) (Sum.inr u)
              (by simp [localOld]) (by simpa only [localVertex_old_one, localVertex_internal] using hn)
        · rw [dist_comm]
          exact globalPosition_nonincident d P hP i e hi₀ hi₁ u
  | inr eu =>
    rcases eu with ⟨e, u⟩
    cases y with
    | inl i =>
      by_cases hi₀ : i = d.left e
      · subst i
        simpa only [localVertex_old_zero, localVertex_internal] using
          globalPosition_local_nonedge d W G P h₀ h₁ hsep e (Sum.inr u) (localOld 0)
            (by simp [localOld]) (by simpa only [localVertex_old_zero, localVertex_internal] using hn)
      · by_cases hi₁ : i = d.right e
        · subst i
          simpa only [localVertex_old_one, localVertex_internal] using
            globalPosition_local_nonedge d W G P h₀ h₁ hsep e (Sum.inr u) (localOld 1)
              (by simp [localOld]) (by simpa only [localVertex_old_one, localVertex_internal] using hn)
        · exact globalPosition_nonincident d P hP i e hi₀ hi₁ u
    | inr fv =>
      rcases fv with ⟨f, v⟩
      by_cases hef : e = f
      · subst f
        have huv : u ≠ v := fun h => hne (by subst v; rfl)
        simpa only [localVertex_internal] using
          globalPosition_local_nonedge d W G P h₀ h₁ hsep e (Sum.inr u) (Sum.inr v)
            (by simpa using huv) (by simpa only [localVertex_internal] using hn)
      · exact globalPosition_distinct_gadgets d P hP e f hef u v

/-- With the prescribed local lengths, all distinct sites have at least the
smallest permitted edge length, whether or not they are adjacent. -/
theorem globalPosition_separation (d : SquareLatticeHeisenberg) (W G : ℕ)
    (P : Fin d.edges → LocalSite → ContactPoint)
    (h₀ : ∀ e, P e (localOld 0) = contactPoint 0 0)
    (h₁ : ∀ e, P e (localOld 1) = contactPoint 17 0)
    (ℓ : GlobalEdge d → ℝ)
    (hlen : ∀ e a, dist (P e (localLeft (member (d.coefficient e)) a))
      (P e (localRight a)) = ℓ (encodeEdge d.edges e a))
    (hℓ : ∀ a, 1 - contactLengthTolerance ≤ ℓ a)
    (hsep : ∀ x y, x ≠ y → Nonedge d W G x y →
      6 / 5 < dist (globalPosition d P x) (globalPosition d P y))
    (x y : GlobalSite d) (hne : x ≠ y) :
    1 - contactLengthTolerance ≤ dist (globalPosition d P x) (globalPosition d P y) := by
  by_cases hn : Nonedge d W G x y
  · have hs := hsep x y hne hn
    unfold contactLengthTolerance
    linarith
  · simp only [Nonedge, not_not] at hn
    obtain ⟨a, ha⟩ := hn
    have he := globalPosition_link_lengths d W G P h₀ h₁ ℓ hlen a
    rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [he]
      exact hℓ a
    · rw [dist_comm, he]
      exact hℓ a

end ContinuumCoulomb.ContactMediator

end

end OAI
