import OAI.MeasureTheory.Falconer.Recursion.SourceBranchDepth
import OAI.MeasureTheory.Falconer.Recursion.BranchRecursionOrder

namespace OAI

namespace PlanarFalconer

namespace PolicyBranch
variable {A : ℕ → ℝ} {N q n : ℕ} {sig : ℝ}

def extend (b : PolicyBranch A N q sig n) {u : BranchState} {l : BranchLabel}
    (hu : u.Valid N sig) (hstep : BranchStep A N q sig (b.state n) l u) :
    PolicyBranch A N q sig (n+1) where
  state j := if j ≤ n then b.state j else u
  label j := if j < n then b.label j else l
  valid j hj := by
    split_ifs with h
    · exact b.valid j h
    · exact hu
  step j hj := by
    by_cases h : j < n
    · simpa only [ite_eq_left h, ite_eq_left (show j ≤ n by omega),
        ite_eq_left (show j+1 ≤ n by omega)] using b.step j h
    · have he : j = n := by omega
      subst j
      simpa using hstep

@[simp] theorem extend_state_le (b : PolicyBranch A N q sig n)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q sig (b.state n) l u) {j : ℕ} (hj : j ≤ n) :
    (b.extend hu hstep).state j = b.state j := ite_eq_left hj

@[simp] theorem extend_label_lt (b : PolicyBranch A N q sig n)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q sig (b.state n) l u) {j : ℕ} (hj : j < n) :
    (b.extend hu hstep).label j = b.label j := ite_eq_left hj

@[simp] theorem extend_last_state (b : PolicyBranch A N q sig n)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q sig (b.state n) l u) :
    (b.extend hu hstep).state (n+1) = u := ite_eq_right (by omega)

@[simp] theorem extend_last_label (b : PolicyBranch A N q sig n)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q sig (b.state n) l u) :
    (b.extend hu hstep).label n = l := ite_eq_right (Nat.lt_irrefl n)

end PolicyBranch

theorem uniform_reached_branch_extension {sig kap : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1) (hgap : sig < kap/1000) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ, ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).index = 0 → ∀ u l,
      BranchStep A N (sourcePolicyBlock N kap) sig (b.state n) l u →
      ∃ b' : PolicyBranch A N (sourcePolicyBlock N kap) sig (n+1),
        (∀ j ≤ n, b'.state j = b.state j) ∧
        (∀ j < n, b'.label j = b.label j) ∧
        b'.state (n+1) = u ∧ b'.label n = l ∧
        (∀ j ≤ n+1, (b'.state j).index+1 < sourceSmoothingLevels sig kap) ∧
        u.finish-u.start < (b.state n).finish-(b.state n).start := by
  obtain ⟨N₁,hN₁,h₁⟩ := uniform_branch_successor_validity hsig hkap hgap
  obtain ⟨N₂,_,h₂⟩ := uniform_source_branch_depth hsig hkap hkap1 hgap
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro N hN A n b hi u l hstep
  have hu := (h₁ N (by omega) A (b.state n) u l (b.valid n le_rfl) hstep).1
  let b' := b.extend hu hstep
  have hi' : (b'.state 0).index = 0 := by simpa [b'] using hi
  have hd := h₂ N (by omega) A (n+1) b' hi'
  refine ⟨b',fun j hj => b.extend_state_le hu hstep hj,
    fun j hj => b.extend_label_lt hu hstep hj,
    b.extend_last_state hu hstep,b.extend_last_label hu hstep,
    fun j hj => (hd.2.2.2 j hj).2,?_⟩
  exact hstep.width_decreases (by omega) (sourcePolicyBlock_pos (by omega) hkap)
    hsig (b.valid n le_rfl) hu

def SourceReached (A : ℕ → ℝ) (N : ℕ) (sig kap : ℝ)
    (root s : BranchState) : Prop :=
  ∃ n, ∃ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
    b.state 0 = root ∧ b.state n = s

theorem SourceReached.valid {A : ℕ → ℝ} {N : ℕ} {sig kap : ℝ}
    {root s : BranchState} (h : SourceReached A N sig kap root s) : s.Valid N sig := by
  obtain ⟨n,b,_,hs⟩ := h
  rw [← hs]
  exact b.valid n le_rfl

theorem SourceReached.root {A : ℕ → ℝ} {N : ℕ} {sig kap : ℝ}
    {s : BranchState} (hs : s.Valid N sig) : SourceReached A N sig kap s s := by
  exact ⟨0,⟨fun _ => s,fun _ => .low,fun _ _ => hs,by omega⟩,rfl,rfl⟩

theorem uniform_source_reached_successor {sig kap : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1) (hgap : sig < kap/1000) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ, ∀ root s u l,
      root.index = 0 → SourceReached A N sig kap root s →
      BranchStep A N (sourcePolicyBlock N kap) sig s l u →
      SourceReached A N sig kap root u ∧ u.Valid N sig ∧
        u.index+1 < sourceSmoothingLevels sig kap ∧
        u.finish-u.start < s.finish-s.start := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_reached_branch_extension hsig hkap hkap1 hgap
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A root s u l hi hr hstep
  obtain ⟨n,b,hroot,hs⟩ := hr
  have hb : (b.state 0).index = 0 := by rw [hroot]; exact hi
  obtain ⟨b',hp,_,hu,_,hindex,hwidth⟩ :=
    h₀ N hN A n b hb u l (by simpa only [hs] using hstep)
  refine ⟨⟨n+1,b',by rw [hp 0 (Nat.zero_le _),hroot],hu⟩,?_,?_,?_⟩
  · simpa only [hu] using b'.valid (n+1) le_rfl
  · simpa only [hu] using hindex (n+1) le_rfl
  · simpa only [hs] using hwidth

theorem uniform_source_reached_induction {sig kap : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1) (hgap : sig < kap/1000) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ, ∀ root : BranchState,
      root.index = 0 → ∀ P : BranchState → Prop,
      (∀ s, SourceReached A N sig kap root s →
        s.index+1 < sourceSmoothingLevels sig kap →
        (∀ u l, BranchStep A N (sourcePolicyBlock N kap) sig s l u → P u) → P s) →
      ∀ s, SourceReached A N sig kap root s → P s := by
  obtain ⟨N₁,hN₁,h₁⟩ := uniform_source_reached_successor hsig hkap hkap1 hgap
  obtain ⟨N₂,_,h₂⟩ := uniform_source_branch_depth hsig hkap hkap1 hgap
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro N hN A root hi P hP s
  induction s using (measure (fun s : BranchState => s.finish-s.start)).wf.induction with
  | h s ih =>
    intro hs
    have hindex : s.index+1 < sourceSmoothingLevels sig kap := by
      obtain ⟨n,b,hroot,hstate⟩ := hs
      have hb : (b.state 0).index = 0 := by rw [hroot]; exact hi
      simpa only [hstate] using (h₂ N (by omega) A n b hb).2.2.2 n le_rfl |>.2
    apply hP s hs hindex
    intro u l hstep
    have hu := h₁ N (by omega) A root s u l hi hs hstep
    exact ih u hu.2.2.2 hu.1

end PlanarFalconer

end OAI
