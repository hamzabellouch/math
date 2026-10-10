import OAI.MeasureTheory.Falconer.Recursion.ReachedBranchWeights
import OAI.MeasureTheory.Falconer.Recursion.ProfileExcess

namespace OAI

/-! # Branch weights for the ambient-dimensional profile

The excess profile is d-Lipschitz. These estimates retain that factor in
both the terminal potential payment and the accumulated error exponent.
-/

namespace Falconer
open PlanarFalconer

def DimensionalProfileLipschitz (d : ℕ) (A : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ i ≤ N, ∀ j ≤ N, |A i-A j| ≤ (d:ℝ)*|(i:ℝ)-j|/(N:ℝ)

theorem profileExcess_dimensional_lipschitz {d N : ℕ} {Q : DyadicCube d}
    {ρ : MeasureTheory.Measure (Space d)} {profile : ℝ → ℝ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam profile) (hN : 0 < N) :
    DimensionalProfileLipschitz d (profileExcess (d := d) profile N) N := by
  intro i hi j hj
  exact profileExcess_lipschitz Q ρ hreg hN i j hi hj

theorem dimensional_potential_le_final_start {A : ℕ → ℝ} {d N a t f Q : ℕ}
    (hN : 0 < N) (hA : DimensionalProfileLipschitz d A N)
    (hQ : 0 < Q) (hw : a+Q ≤ t) (ht : t ≤ N) (haf : a ≤ f) (hft : f ≤ t) :
    potential A a t Q ≤ 2*A f+2*d*(Q:ℝ)/N := by
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hb := potential_near_final A hQ hw haf hft (e := (d:ℝ)*(Q:ℝ)/N) ?_
  · simpa only [mul_div_assoc,mul_assoc] using hb
  intro j _ hjt hjf hfj
  have hd : |(j:ℝ)-f| ≤ (Q:ℝ) := by
    have hjR : (j:ℝ) ≤ (f:ℝ)+Q := by exact_mod_cast hjf
    have hfR : (f:ℝ) ≤ (j:ℝ)+Q := by exact_mod_cast hfj
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hh := (hA j (hjt.trans ht) f (hft.trans ht)).trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg d)) hNR.le)
  have hh' := (le_abs_self (A j-A f)).trans hh
  linarith

theorem _root_.OAI.PlanarFalconer.PolicyBranch.dimensional_costs_le_final_start {d N q n : ℕ} {A : ℕ → ℝ} {sig : ℝ}
    (b : PolicyBranch A N q sig n) (hN : 0 < N) (hq : 0 < q)
    (hslack : sig*(N:ℝ) ≤ q) (hA : DimensionalProfileLipschitz d A N)
    (hinit : (b.state 0).start+10*q ≤ (b.state 0).finish) :
    ∑ j ∈ Finset.range n, branchCost A (b.state j) (b.label j) (b.state (j+1)) ≤
      2*A (b.state n).start+20*d*(q:ℝ)/N-potential A (b.state 0).start (b.state 0).finish (10*q) := by
  have hQ : 0 < 10*q := by omega
  have hfinal := BranchState.valid_depths (b.valid n le_rfl)
  by_cases hw : (b.state n).start+10*q ≤ (b.state n).finish
  · have hc := b.costs_le_potential hq hslack hw
    have hf := dimensional_potential_le_final_start hN hA hQ hw hfinal.2 (le_refl _) hfinal.1
    norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hf
    linear_combination hc+hf
  · cases n with
    | zero => exact (hw hinit).elim
    | succ n =>
      have hs := b.step n (by omega)
      have hn := hs.nested hq (b.valid n (by omega))
      have hp := hs.nonterminal
      have hpwide : (b.state n).start+10*q ≤ (b.state n).finish := by omega
      have hd := BranchState.valid_depths (b.valid n (by omega))
      have hc := (b.initialSegment n (by omega)).costs_le_potential hq hslack hpwide
      dsimp only [PlanarFalconer.PolicyBranch.initialSegment] at hc
      have hz := hs.short_cost_zero hq (b.valid n (by omega)) hslack (by omega)
      have hf := dimensional_potential_le_final_start hN hA hQ hpwide hd.2 hn.1 (hfinal.1.trans hn.2)
      norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hf
      rw [Finset.sum_range_succ,hz,add_zero]
      linear_combination hc+hf

theorem DimensionalProfileLipschitz.increment_le {d N i j : ℕ} {A : ℕ → ℝ}
    (hA : DimensionalProfileLipschitz d A N) (hN : 0 < N) (hi : i ≤ N) (hj : j ≤ N) :
    |A i-A j| ≤ d := by
  apply (hA i hi j hj).trans
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
  apply abs_le.mpr
  have hi' : (i:ℝ) ≤ N := Nat.cast_le.mpr hi
  have hj' : (j:ℝ) ≤ N := Nat.cast_le.mpr hj
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) i,Nat.cast_nonneg (α := ℝ) j]

theorem DimensionalProfileLipschitz.abs_le {d N i : ℕ} {A : ℕ → ℝ}
    (hA : DimensionalProfileLipschitz d A N) (hN : 0 < N) (hzero : A 0 = 0) (hi : i ≤ N) :
    |A i| ≤ d := by
  simpa only [hzero,sub_zero] using hA.increment_le hN hi (Nat.zero_le N)

theorem DimensionalProfileLipschitz.minimum_cost_le {d N a t i : ℕ} {A : ℕ → ℝ}
    (hA : DimensionalProfileLipschitz d A N) (hN : 0 < N)
    (hat : a ≤ t) (ht : t ≤ N) (hi : i ≤ N) : A i-intervalMin A a t ≤ d := by
  obtain ⟨j,_,hjt,hmin⟩ := intervalMin_attained A hat
  rw [hmin]
  exact (le_abs_self _).trans (hA.increment_le hN hi (hjt.trans ht))

theorem _root_.OAI.PlanarFalconer.BranchStep.dimensional_cost_le {A : ℕ → ℝ} {d N q : ℕ} {sig : ℝ}
    (hA : DimensionalProfileLipschitz d A N) (hN : 0 < N) (hq : 0 < q)
    {s u : BranchState} {l : BranchLabel} (h : BranchStep A N q sig s l u)
    (hs : s.Valid N sig) (hu : u.Valid N sig) : branchCost A s l u ≤ d := by
  have hn := h.nested hq hs
  have hsd := BranchState.valid_depths hs
  have hud := BranchState.valid_depths hu
  cases h <;> simp only [branchCost]
  · exact hA.minimum_cost_le hN hn.2 hsd.2 (hud.2.trans (le_refl _))
  · norm_num
  · exact hA.minimum_cost_le hN hn.1 (hud.1.trans hud.2) (hud.1.trans hud.2)
  · norm_num
  · norm_num
  · exact hA.minimum_cost_le hN hn.1 (hud.1.trans hud.2) (hud.1.trans hud.2)

theorem _root_.OAI.PlanarFalconer.BranchStep.dimensional_exponent_le {A : ℕ → ℝ} {d N q : ℕ} {lam sig eps : ℝ}
    (hA : DimensionalProfileLipschitz d A N) (hN : 0 < N) (hq : 0 < q)
    (hloss : 4000*(lam+sig) ≤ 1)
    {s u : BranchState} {l : BranchLabel} (h : BranchStep A N q sig s l u)
    (hs : s.Valid N sig) (hu : u.Valid N sig) :
    branchExponent A lam sig eps s l u ≤ 3*(d:ℝ)+1+eps := by
  have hc := h.dimensional_cost_le hA hN hq hs hu
  have hsd := BranchState.valid_depths hs
  have hud := BranchState.valid_depths hu
  have hi := abs_le.mp (hA.increment_le hN (hud.1.trans hud.2) (hsd.1.trans hsd.2))
  unfold branchExponent
  split_ifs <;> linarith

theorem _root_.OAI.PlanarFalconer.PolicyBranch.dimensional_ancestor_exponent_bound {A : ℕ → ℝ} {d N q n : ℕ} {lam sig eps : ℝ}
    (b : PolicyBranch A N q sig n) (hA : DimensionalProfileLipschitz d A N)
    (hN : 0 < N) (hq : 0 < q) (hloss : 4000*(lam+sig) ≤ 1) :
    (∑ j ∈ Finset.range n, branchExponent A lam sig eps (b.state j) (b.label j) (b.state (j+1))) ≤
      (n:ℝ)*(3*(d:ℝ)+1+eps) := by
  calc
    _ ≤ ∑ _j ∈ Finset.range n, (3*(d:ℝ)+1+eps) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj := Finset.mem_range.mp hj
      exact (b.step j hj).dimensional_exponent_le hA hN hq hloss (b.valid j hj.le)
        (b.valid (j+1) (by omega))
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]

theorem dimensional_source_branch_exponent {A : ℕ → ℝ} {d N n : ℕ} {lam sig kap eta : ℝ}
    (hN : 0 < N) (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (heta : 0 < eta) (hceil : ⌈10*sig*(N:ℝ)⌉₊ < sourcePolicyBlock N kap)
    (hslack : sig*(N:ℝ) ≤ sourcePolicyBlock N kap)
    (hqratio : (sourcePolicyBlock N kap:ℝ)/(N:ℝ) ≤ 2*kap)
    (hA : DimensionalProfileLipschitz d A N)
    (b : PolicyBranch A N (sourcePolicyBlock N kap) sig n)
    (hinit : (b.state 0).start+10*sourcePolicyBlock N kap ≤ (b.state 0).finish) :
    let eps := eta/(2*(1+20/kap+1/sig))
    (∑ j ∈ Finset.range n, branchExponent A lam sig eps (b.state j) (b.label j) (b.state (j+1))) +
      (200*d*(sourcePolicyBlock N kap:ℝ)/N+12*lam+eta/2) ≤
      2*A (b.state 0).start-potential A (b.state 0).start (b.state 0).finish
        (10*sourcePolicyBlock N kap)+500*d*kap+10^6*(lam+sig)/kap+eta := by
  dsimp only
  have hq := sourcePolicyBlock_pos hN hkap
  have hc := b.dimensional_costs_le_final_start hN hq hslack hA hinit
  have hb := source_branch_count_bounds hN hsig hkap hkap1 hceil b
  let D : ℝ := 1+20/kap+1/sig
  have hD : 0 < D := by dsimp [D]; positivity
  have heps : 0 ≤ eta/(2*D) := by positivity
  have htime : (n:ℝ)*(eta/(2*D)) ≤ eta/2 := by
    have hn : (n:ℝ) ≤ D := by dsimp [D]; linarith [hb.2.2]
    calc
      _ ≤ D*(eta/(2*D)) := mul_le_mul_of_nonneg_right hn heps
      _ = eta/2 := by field_simp
  have hloss : (branchNonlowCount b.label n:ℝ)*(4000*(lam+sig)) ≤ 80000*(lam+sig)/kap := by
    calc
      _ ≤ (20/kap)*(4000*(lam+sig)) := mul_le_mul_of_nonneg_right hb.1 (by positivity)
      _ = _ := by ring
  have hlamK : lam ≤ (lam+sig)/kap := by
    apply (le_div_iff₀ hkap).mpr
    have hh := mul_le_mul_of_nonneg_left hkap1 hlam
    linarith
  have hbudget : 0 ≤ (lam+sig)/kap := by positivity
  have hqrd := mul_le_mul_of_nonneg_left hqratio (Nat.cast_nonneg (α := ℝ) d)
  rw [branch_exponent_sum]
  dsimp only [D] at htime
  simp only [mul_div_assoc] at hc hloss ⊢
  nlinarith

theorem uniform_dimensional_source_branch_exponent {d : ℕ} {lam sig kap eta : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (heta : 0 < eta) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      DimensionalProfileLipschitz d A N → ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).start+10*sourcePolicyBlock N kap ≤ (b.state 0).finish →
      (∑ j ∈ Finset.range n, branchExponent A lam sig (eta/(2*(1+20/kap+1/sig)))
        (b.state j) (b.label j) (b.state (j+1))) +
        (200*d*(sourcePolicyBlock N kap:ℝ)/N+12*lam+eta/2) ≤
      2*A (b.state 0).start-potential A (b.state 0).start (b.state 0).finish
        (10*sourcePolicyBlock N kap)+500*d*kap+10^6*(lam+sig)/kap+eta := by
  obtain ⟨N₁,hN₁,h₁⟩ := uniform_source_ceiling_slack hsig hgap
  obtain ⟨N₂,hN₂⟩ := exists_nat_gt (1/kap)
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro N hN A hA n b hi
  have hNp : 0 < N := by omega
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hNp
  have hkn : 1 < kap*(N:ℝ) := by
    have hh := (div_lt_iff₀ hkap).mp (hN₂.trans_le (Nat.cast_le.mpr (show N₂ ≤ N by omega)))
    linarith
  have hq : (sourcePolicyBlock N kap:ℝ) < kap*N+1 :=
    Nat.ceil_lt_add_one (mul_nonneg hkap.le hNR.le)
  have hqr : (sourcePolicyBlock N kap:ℝ)/(N:ℝ) ≤ 2*kap :=
    (div_le_iff₀ hNR).mpr (by linarith)
  exact dimensional_source_branch_exponent hNp hlam hsig hkap hkap1 heta
    (h₁ N (by omega)).1 (h₁ N (by omega)).2.2 hqr hA b hi

theorem dimensional_source_error_exponent {d : ℕ} {sig kap T eps n : ℝ}
    (hn : 0 ≤ n)
    (hdepth : n ≤ 20/kap+1/sig) (heps : eps ≤ 1)
    (hT : (20/kap+1/sig)*(3*(d:ℝ)+2)+10 < T) :
    -T+n*(3*(d:ℝ)+1+eps) < -10 := by
  have hstep : n*(3*(d:ℝ)+1+eps) ≤ n*(3*(d:ℝ)+2) := by nlinarith
  have hbound := mul_le_mul_of_nonneg_right hdepth
    (show 0 ≤ 3*(d:ℝ)+2 by positivity)
  linarith

theorem dimensional_uniform_source_error_branch {d : ℕ} {lam sig kap T eps : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1) (hgap : sig < kap/1000)
    (hloss : 4000*(lam+sig) ≤ 1) (heps : eps ≤ 1)
    (hT : (20/kap+1/sig)*(3*(d:ℝ)+2)+10 < T) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      DimensionalProfileLipschitz d A N → ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).index = 0 →
      ((2:ℝ)^N)^(-T+(∑ j ∈ Finset.range n,
        branchExponent A lam sig eps (b.state j) (b.label j) (b.state (j+1)))) ≤
      ((2:ℝ)^N)^(-10:ℝ) := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_source_branch_depth hsig hkap hkap1 hgap
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A hA n b hi
  have hNp : 0 < N := hN₀.trans_le hN
  have hc := b.dimensional_ancestor_exponent_bound (eps := eps) hA hNp (sourcePolicyBlock_pos hNp hkap) hloss
  have hd := (h₀ N hN A n b hi).2.2.1
  have he := dimensional_source_error_exponent (Nat.cast_nonneg n) hd heps hT
  apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
  linarith

theorem dimensional_source_profile_exponent_lower {A : ℕ → ℝ} {d N a t Q : ℕ}
    (hA : DimensionalProfileLipschitz d A N) (hN : 0 < N) (hzero : A 0 = 0)
    (hQ : 0 < Q) (hw : a+Q ≤ t) (ht : t ≤ N) :
    -4*(d:ℝ) ≤ 2*A a-potential A a t Q := by
  have ha := abs_le.mp (hA.abs_le hN hzero (show a ≤ N by omega))
  have hb := abs_le.mp (hA.abs_le hN hzero (show a+Q ≤ N by omega))
  have hp := potential_le A (Q := Q) (le_refl a) (by omega : a < a+Q) hw (le_refl _)
  linarith

theorem dimensional_uniform_source_weighted_terminal {d : ℕ} {lam sig kap eta : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (heta : 0 < eta) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      DimensionalProfileLipschitz d A N → ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).start+10*sourcePolicyBlock N kap ≤ (b.state 0).finish →
      b.weight lam (eta/(2*(1+20/kap+1/sig))) *
        ((2:ℝ)^N)^(200*d*(sourcePolicyBlock N kap:ℝ)/N+12*lam+eta/2) ≤
      ((2:ℝ)^N)^(2*A (b.state 0).start-potential A (b.state 0).start (b.state 0).finish
        (10*sourcePolicyBlock N kap)+500*d*kap+10^6*(lam+sig)/kap+eta) := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_dimensional_source_branch_exponent hlam hsig hkap hkap1 hgap heta
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A hA n b hi
  rw [PolicyBranch.weight,← Real.rpow_add (by positivity : 0 < (2:ℝ)^N)]
  exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (h₀ N hN A hA n b hi)

theorem dimensional_uniform_source_weighted_error {d : ℕ} {lam sig kap T eps : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1) (hgap : sig < kap/1000)
    (hloss : 4000*(lam+sig) ≤ 1) (heps : eps ≤ 1)
    (hT : (20/kap+1/sig)*(3*(d:ℝ)+2)+10 < T) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      DimensionalProfileLipschitz d A N → ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).index = 0 →
      b.weight lam eps*((2:ℝ)^N)^(-T) ≤ ((2:ℝ)^N)^(-10:ℝ) := by
  obtain ⟨N₀,hN₀,h₀⟩ := dimensional_uniform_source_error_branch hsig hkap hkap1 hgap hloss heps hT
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A hA n b hi
  rw [PolicyBranch.weight,← Real.rpow_add (by positivity : 0 < (2:ℝ)^N),add_comm]
  exact h₀ N hN A hA n b hi

end Falconer

end OAI
