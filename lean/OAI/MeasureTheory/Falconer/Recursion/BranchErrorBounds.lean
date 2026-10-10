import OAI.MeasureTheory.Falconer.Recursion.BranchExponent
import OAI.MeasureTheory.Falconer.Angular.AngularUniformAbsorption

namespace OAI

namespace PlanarFalconer

theorem DiscreteProfileLipschitz.increment_le_one {A : ℕ → ℝ} {N i j : ℕ}
    (hA : DiscreteProfileLipschitz A N) (hN : 0 < N) (hi : i ≤ N) (hj : j ≤ N) :
    |A i-A j| ≤ 1 := by
  apply (hA i hi j hj).trans
  apply (div_le_one (Nat.cast_pos.mpr hN)).mpr
  apply abs_le.mpr
  have hi' : (i:ℝ) ≤ N := Nat.cast_le.mpr hi
  have hj' : (j:ℝ) ≤ N := Nat.cast_le.mpr hj
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) i,Nat.cast_nonneg (α := ℝ) j]

theorem DiscreteProfileLipschitz.abs_le_one {A : ℕ → ℝ} {N i : ℕ}
    (hA : DiscreteProfileLipschitz A N) (hN : 0 < N) (hzero : A 0 = 0) (hi : i ≤ N) :
    |A i| ≤ 1 := by
  simpa only [hzero,sub_zero] using hA.increment_le_one hN hi (Nat.zero_le N)

theorem DiscreteProfileLipschitz.minimum_cost_le_one {A : ℕ → ℝ} {N a t i : ℕ}
    (hA : DiscreteProfileLipschitz A N) (hN : 0 < N)
    (hat : a ≤ t) (ht : t ≤ N) (hi : i ≤ N) :
    A i-intervalMin A a t ≤ 1 := by
  obtain ⟨j,_,hjt,hmin⟩ := intervalMin_attained A hat
  rw [hmin]
  exact (le_abs_self _).trans (hA.increment_le_one hN hi (hjt.trans ht))

theorem BranchStep.cost_le_one {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    (hA : DiscreteProfileLipschitz A N) (hN : 0 < N) (hq : 0 < q)
    {s u : BranchState} {l : BranchLabel} (h : BranchStep A N q sig s l u)
    (hs : s.Valid N sig) (hu : u.Valid N sig) : branchCost A s l u ≤ 1 := by
  have hn := h.nested hq hs
  have hsd := BranchState.valid_depths hs
  have hud := BranchState.valid_depths hu
  cases h <;> simp only [branchCost]
  · exact hA.minimum_cost_le_one hN hn.2 hsd.2 (hud.2.trans (le_refl _))
  · norm_num
  · exact hA.minimum_cost_le_one hN hn.1 (hud.1.trans hud.2) (hud.1.trans hud.2)
  · norm_num
  · norm_num
  · exact hA.minimum_cost_le_one hN hn.1 (hud.1.trans hud.2) (hud.1.trans hud.2)

theorem BranchStep.exponent_le_four {A : ℕ → ℝ} {N q : ℕ} {lam sig eps : ℝ}
    (hA : DiscreteProfileLipschitz A N) (hN : 0 < N) (hq : 0 < q)
    (hloss : 4000*(lam+sig) ≤ 1)
    {s u : BranchState} {l : BranchLabel} (h : BranchStep A N q sig s l u)
    (hs : s.Valid N sig) (hu : u.Valid N sig) :
    branchExponent A lam sig eps s l u ≤ 4+eps := by
  have hc := h.cost_le_one hA hN hq hs hu
  have hsd := BranchState.valid_depths hs
  have hud := BranchState.valid_depths hu
  have hi := abs_le.mp (hA.increment_le_one hN (hud.1.trans hud.2) (hsd.1.trans hsd.2))
  unfold branchExponent
  split_ifs <;> linarith

theorem PolicyBranch.ancestor_exponent_bound {A : ℕ → ℝ} {N q n : ℕ} {lam sig eps : ℝ}
    (b : PolicyBranch A N q sig n) (hA : DiscreteProfileLipschitz A N)
    (hN : 0 < N) (hq : 0 < q) (hloss : 4000*(lam+sig) ≤ 1) :
    (∑ j ∈ Finset.range n, branchExponent A lam sig eps (b.state j) (b.label j) (b.state (j+1))) ≤
      (n:ℝ)*(4+eps) := by
  calc
    _ ≤ ∑ _j ∈ Finset.range n, (4+eps) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj := Finset.mem_range.mp hj
      exact (b.step j hj).exponent_le_four hA hN hq hloss (b.valid j hj.le)
        (b.valid (j+1) (by omega))
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]

theorem source_error_exponent {sig kap T eps n : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hn : 0 ≤ n)
    (hdepth : n ≤ 20/kap+1/sig) (heps : eps ≤ 1)
    (hT : 1000*(1/sig+1/kap)+1000 < T) : -T+n*(4+eps) < -10 := by
  have hstep : n*(4+eps) ≤ 5*n := by nlinarith
  have hk : 0 < 1/kap := by positivity
  have hs : 0 < 1/sig := by positivity
  have he : 20/kap = 20*(1/kap) := by ring
  rw [he] at hdepth
  linarith

theorem uniform_source_error_branch {lam sig kap T eps : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1) (hgap : sig < kap/1000)
    (hloss : 4000*(lam+sig) ≤ 1) (heps : eps ≤ 1)
    (hT : 1000*(1/sig+1/kap)+1000 < T) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      DiscreteProfileLipschitz A N → ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).index = 0 →
      ((2:ℝ)^N)^(-T+(∑ j ∈ Finset.range n,
        branchExponent A lam sig eps (b.state j) (b.label j) (b.state (j+1)))) ≤
      ((2:ℝ)^N)^(-10:ℝ) := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_source_branch_depth hsig hkap hkap1 hgap
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A hA n b hi
  have hNp : 0 < N := hN₀.trans_le hN
  have hc := b.ancestor_exponent_bound (eps := eps) hA hNp (sourcePolicyBlock_pos hNp hkap) hloss
  have hd := (h₀ N hN A n b hi).2.2.1
  have he := source_error_exponent hsig hkap (Nat.cast_nonneg n) hd heps hT
  apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
  linarith

theorem source_profile_exponent_lower {A : ℕ → ℝ} {N a t Q : ℕ}
    (hA : DiscreteProfileLipschitz A N) (hN : 0 < N) (hzero : A 0 = 0)
    (hQ : 0 < Q) (hw : a+Q ≤ t) (ht : t ≤ N) :
    -4 ≤ 2*A a-potential A a t Q := by
  have ha := abs_le.mp (hA.abs_le_one hN hzero (show a ≤ N by omega))
  have hb := abs_le.mp (hA.abs_le_one hN hzero (show a+Q ≤ N by omega))
  have hp := potential_le A (Q := Q) (le_refl a) (by omega : a < a+Q) hw (le_refl _)
  linarith

theorem uniform_recursion_count_subpower (D : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (4*(N:ℝ)+1)^D ≤ ((2:ℝ)^N)^eta :=
  fixed_polynomial_subpower D heta

end PlanarFalconer

end OAI
