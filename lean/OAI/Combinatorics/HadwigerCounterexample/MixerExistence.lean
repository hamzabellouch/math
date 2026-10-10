import OAI.Combinatorics.HadwigerCounterexample.PolarRankBounds

namespace OAI

/-! # Mixer Existence -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Filter
open scoped BigOperators Topology

theorem polar_likely (p : Shape) (K s0 : ℕ) (hA : profileA p K≤s0)
    (hg : 2≤p.g) (hj : s0≤p.J) :
    ∀ᶠ n : ℕ in atTop,
      pr unif (fun x : Draw p n => ¬unaryGood (drawn x) K s0)<1/4 := by
  classical
  let A := profileA p K
  let U := Tag p.g × Label p.b
  let c : ℝ := (prodBound p K+2*K:ℕ)
  let b := num U * bp (c*(s0+1))
  have h : Tendsto (fun n:ℕ => b*bp (-(n:ℝ))) atTop (𝓝 0) := by
    have h : Tendsto (fun n:ℕ=>bp (-(1:ℝ)*(n:ℝ))) atTop (𝓝 0) :=
      (bp_tendsto_zero zero_lt_one).comp tendsto_natCast_atTop_atTop
    simpa using h.const_mul b
  filter_upwards [h.eventually (gt_mem_nhds (show (0:ℝ)<1/4 by norm_num)),profile_count p K]
    with n hn hP
  let T := {x : Profile p n // totalRank x≤K}
  let bad (i : T × U) (d : Draw p n) := urBad K s0 i.1.val i.2.1 i.2.2 d
  apply lt_of_le_of_lt (le_trans (pr_mono unif_law.nz ?_) (pr_exists_le _ bad))
  show (∑ i,pr unif (bad i)) < 1/4
  · have hi i : pr unif (bad i) ≤ bp ((c-n)*(s0+1)) := by
      have hi := urBad_cap K s0 hg hj (i: T × U).1.val i.2.1 i.2.2
      unfold c; push_cast; exact hi
    apply lt_of_le_of_lt (Finset.sum_le_sum (s:=Finset.univ) fun i _ => hi i)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    apply lt_of_le_of_lt _ hn
    change _ ≤ b * bp _
    have hpc : num T ≤ bp (A*n) := by rw [nbr_eq_card] at hP; exact hP
    rw [Fintype.card_prod,Nat.cast_mul]
    change num T * num U * _ ≤ _
    have hh : (A:ℝ)*n - (s0+1:ℝ)*n ≤ -(n:ℝ) := by
      have hx : (A:ℝ) ≤ s0 := by exact_mod_cast hA
      have hd := mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg n : (0:ℝ) ≤ n)
      linarith only [hd]
    have hnum : (0:ℝ) ≤ num U := Nat.cast_nonneg _
    calc num T * num U * bp ((c-n)*(s0+1))
      _ ≤ bp (A*n) * num U * bp ((c-n)*(s0+1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpc hnum) (bp_pos _).le
      _ = b * bp ((A:ℝ)*n - (s0+1:ℝ)*n) := by
        dsimp only [b]
        rw [mul_comm _ (num U),mul_assoc, ← bp_add, mul_assoc, ← bp_add]; ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left (bp_le hh) (mul_nonneg hnum (bp_pos _).le)
  · intro x hx
    unfold unaryGood at hx
    push Not at hx
    obtain ⟨i,l,s,h1,h2,h3⟩ := hx
    exact ⟨(⟨i,h1⟩,l,s),h1,h2,h3⟩
  · exact unif_law.nz;

theorem goodMixers (p : Shape) (K s0 : ℕ) (hg : 2≤p.g)
    (hj : 1≤p.j) (h0 : profileA p K≤s0) (hJ : s0≤p.J) :
    ∀ᶠ n : ℕ in atTop,
      ∃ m : Mixer p n, unaryGood m K s0 ∧ binaryGood m := by
  classical
  filter_upwards [polar_likely p _ _ h0 hg hJ, binary_likely p hj] with n hn hm
  let q (x : Draw p n) := ¬ unaryGood (drawn x) K s0
  let r (x : Draw p n) := ¬ binaryGood (drawn x)
  have hh : 0<pr unif (fun x => ¬ (q x ∨ r x)) := by
    rw [pr_not,unif_law.total]
    have h := pr_or_le (w:=unif) (p:=q) (q:=r) unif_law.nz
    change pr unif q<_ at hn; change pr unif r<_ at hm
    linarith only [hn,hm,h]
  obtain ⟨x,hx,_⟩ := exists_of_pr_pos unif_law.nz hh
  unfold q r at hx
  exact ⟨drawn (p:=p) x, Classical.not_not.mp (fun h => hx (Or.inl h)), Classical.not_not.mp (fun h => hx (Or.inr h))⟩
end HadwigerCounterexample

end

end OAI
