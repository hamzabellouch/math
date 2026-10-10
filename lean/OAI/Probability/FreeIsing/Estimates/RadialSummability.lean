import OAI.Probability.FreeIsing.Trees.Shells

namespace OAI

noncomputable section

namespace Problem367

def treeShellSigmaEquiv (d : ℕ) : (Σ n : ℕ, TreeShell d n) ≃ TreeVertex d :=
  Equiv.sigmaFiberEquiv (fun v : TreeVertex d => v.1.length)

@[simp] theorem tsum_treeShell_radial (d n : ℕ) (f : ℕ → ℝ) :
    (∑' v : TreeShell d n, f v.1.1.length) =
      (Fintype.card (TreeShell d n) : ℝ) * f n := by
  calc
    (∑' v : TreeShell d n, f v.1.1.length) = ∑' _ : TreeShell d n, f n :=
      tsum_congr fun v => congrArg f v.2
    _ = _ := by simp [tsum_fintype]

theorem summable_radial_iff (d : ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    Summable (fun v : TreeVertex d => f v.1.length) ↔
      Summable (fun n : ℕ => (Fintype.card (TreeShell d n) : ℝ) * f n) := by
  rw [← (treeShellSigmaEquiv d).summable_iff]
  change Summable (fun s : Σ n : ℕ, TreeShell d n => f s.2.1.1.length) ↔ _
  rw [summable_sigma_of_nonneg
    (f := fun s : Σ n : ℕ, TreeShell d n => f s.2.1.1.length)
    (fun s => hf s.2.1.1.length)]
  simp only [tsum_treeShell_radial]
  exact and_iff_right (fun _ => (hasSum_fintype _).summable)

theorem tsum_radial (d : ℕ) (f : ℕ → ℝ)
    (hf : Summable (fun v : TreeVertex d => f v.1.length)) :
    (∑' v : TreeVertex d, f v.1.length) =
      ∑' n : ℕ, (Fintype.card (TreeShell d n) : ℝ) * f n := by
  have hs := (treeShellSigmaEquiv d).summable_iff.mpr hf
  calc
    (∑' v : TreeVertex d, f v.1.length) =
        ∑' s : Σ n : ℕ, TreeShell d n, f s.2.1.1.length :=
      ((treeShellSigmaEquiv d).tsum_eq (fun v : TreeVertex d => f v.1.length)).symm
    _ = ∑' n : ℕ, ∑' v : TreeShell d n, f v.1.1.length := hs.tsum_sigma
    _ = _ := by simp only [tsum_treeShell_radial]

theorem summable_geometric_radial (d : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hbranch : (d - 1 : ℕ) * q < 1) :
    Summable (fun v : TreeVertex d => q ^ v.1.length) := by
  apply (summable_radial_iff d (fun n => q ^ n) (fun _ => pow_nonneg hq _)).mpr
  apply (summable_nat_add_iff 1).mp
  have hgeom : Summable (fun n : ℕ => ((d - 1 : ℕ) * q) ^ n) :=
    summable_geometric_of_lt_one (mul_nonneg (Nat.cast_nonneg _) hq) hbranch
  have h := hgeom.mul_left ((d : ℝ) * q)
  refine h.congr fun n => ?_
  simp only [card_treeShell_succ, Nat.cast_mul, Nat.cast_pow, pow_succ, mul_pow]
  ring

theorem tsum_geometric_radial (d : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hbranch : (d - 1 : ℕ) * q < 1) :
    (∑' v : TreeVertex d, q ^ v.1.length) =
      1 + (d : ℝ) * q / (1 - (d - 1 : ℕ) * q) := by
  have hrad := summable_geometric_radial d hq hbranch
  rw [tsum_radial d (fun n => q ^ n) hrad]
  have hs := (summable_radial_iff d (fun n => q ^ n) (fun _ => pow_nonneg hq _)).mp hrad
  rw [hs.tsum_eq_zero_add]
  simp only [card_treeShell_zero, Nat.cast_one, pow_zero, one_mul]
  have hterm (n : ℕ) :
      (Fintype.card (TreeShell d (n + 1)) : ℝ) * q ^ (n + 1) =
        ((d : ℝ) * q) * (((d - 1 : ℕ) : ℝ) * q) ^ n := by
    simp only [card_treeShell_succ, Nat.cast_mul, Nat.cast_pow, pow_succ, mul_pow]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (mul_nonneg (Nat.cast_nonneg _) hq) hbranch]
  rw [div_eq_mul_inv]

theorem summable_geometric_radial_iff (d : ℕ) (hd : 1 ≤ d) {q : ℝ} (hq : 0 ≤ q) :
    Summable (fun v : TreeVertex d => q ^ v.1.length) ↔
      (d - 1 : ℕ) * q < 1 := by
  refine ⟨?_, summable_geometric_radial d hq⟩
  intro hrad
  by_contra hnot
  have hbranch : 1 ≤ ((d - 1 : ℕ) : ℝ) * q := le_of_not_gt hnot
  have hqpos : 0 < q := by
    by_contra h
    have hzero : q = 0 := le_antisymm (le_of_not_gt h) hq
    norm_num [hzero] at hbranch
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hcoeff : (d : ℝ) * q ≠ 0 := ne_of_gt (mul_pos hdpos hqpos)
  have hs := (summable_radial_iff d (fun n => q ^ n) (fun _ => pow_nonneg hq _)).mp hrad
  have hshift := (summable_nat_add_iff 1).mpr hs
  have hm : Summable (fun n : ℕ => ((d : ℝ) * q) *
      (((d - 1 : ℕ) : ℝ) * q) ^ n) := by
    refine hshift.congr fun n => ?_
    simp only [card_treeShell_succ, Nat.cast_mul, Nat.cast_pow, pow_succ, mul_pow]
    ring
  have hgeom : Summable (fun n : ℕ => (((d - 1 : ℕ) : ℝ) * q) ^ n) := by
    have h := hm.mul_left (((d : ℝ) * q)⁻¹)
    simpa only [← mul_assoc, inv_mul_cancel₀ hcoeff, one_mul] using h
  have hlt := summable_geometric_iff_norm_lt_one.mp hgeom
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hq)] at hlt
  exact (not_lt_of_ge hbranch) hlt

theorem not_summable_geometric_radial_of_critical (d : ℕ) (hd : 1 ≤ d)
    {q : ℝ} (hq : 0 ≤ q) (hcritical : (d - 1 : ℕ) * q = 1) :
    ¬ Summable (fun v : TreeVertex d => q ^ v.1.length) := by
  rw [summable_geometric_radial_iff d hd hq, hcritical]
  exact lt_irrefl _

theorem summable_norm_sq_of_radial_bound {E : Type*} [NormedAddCommGroup E]
    (d : ℕ) {theta : ℝ}
    (hbranch : (d - 1 : ℕ) * theta ^ 2 < 1)
    (c : TreeVertex d → E) (hc : ∀ v, ‖c v‖ ≤ theta ^ v.1.length) :
    Summable (fun v => ‖c v‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun v => sq_nonneg ‖c v‖) (fun v => ?_)
    (summable_geometric_radial d (sq_nonneg theta) hbranch)
  calc
    ‖c v‖ ^ 2 ≤ (theta ^ v.1.length) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hc v) 2
    _ = (theta ^ 2) ^ v.1.length := by simp only [← pow_mul, Nat.mul_comm]

theorem tsum_norm_sq_le_of_radial_bound {E : Type*} [NormedAddCommGroup E]
    (d : ℕ) {theta : ℝ}
    (hbranch : (d - 1 : ℕ) * theta ^ 2 < 1)
    (c : TreeVertex d → E) (hc : ∀ v, ‖c v‖ ≤ theta ^ v.1.length) :
    (∑' v, ‖c v‖ ^ 2) ≤ 1 + (d : ℝ) * theta ^ 2 / (1 - (d - 1 : ℕ) * theta ^ 2) := by
  rw [← tsum_geometric_radial d (sq_nonneg theta) hbranch]
  apply Summable.tsum_le_tsum (fun v => ?_)
    (summable_norm_sq_of_radial_bound d hbranch c hc)
    (summable_geometric_radial d (sq_nonneg theta) hbranch)
  calc
    ‖c v‖ ^ 2 ≤ (theta ^ v.1.length) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hc v) 2
    _ = (theta ^ 2) ^ v.1.length := by simp only [← pow_mul, Nat.mul_comm]

theorem memℓp_two_of_radial_bound {E : Type*} [NormedAddCommGroup E]
    (d : ℕ) {theta : ℝ}
    (hbranch : (d - 1 : ℕ) * theta ^ 2 < 1)
    (c : TreeVertex d → E) (hc : ∀ v, ‖c v‖ ≤ theta ^ v.1.length) :
    Memℓp c 2 := by
  apply (memℓp_gen_iff (p := 2) (by norm_num)).mpr
  simpa using summable_norm_sq_of_radial_bound d hbranch c hc

end Problem367

end

end OAI
