import OAI.NumberTheory.Ostmann.Construction.SelectedInitialPriorBounds
import OAI.NumberTheory.Ostmann.Construction.SmoothGiantActiveSupport

namespace OAI

/-! # Lower endpoints for every live prime in the original initial prior -/
namespace Ostmann
open Filter
open scoped Classical

theorem initial_selected_centers_lower
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y target H : ℝ}
    {D : Finset ℕ} {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y hi D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets)
    (hHtop : H ≤ target) (hHcenters : ∀ w ∈ targets, H ≤ w / 4) :
    ∀ j ∈ initialSmallCellList top centers, H ≤ (j : ℝ) := by
  apply initialSmallCellList_property top centers (fun j => H ≤ (j : ℝ))
    (hHtop.trans htop.1)
  induction hcenters with
  | nil => simp
  | @cons j w js ws hj hrest ih =>
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact (hHcenters w (by simp)).trans hj.1
    · exact ih (fun v hv => hHcenters v (by simp [hv])) i hi

theorem selected_initial_prior_lower
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G target H : ℝ}
    {D Qb Qd : Finset ℕ} {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y hi D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (b d : ℕ)
    (hG : H + 1 ≤ G) (hb : ∀ p ∈ Qb, Real.exp H ≤ (p : ℝ))
    (hd : ∀ p ∈ Qd, Real.exp H ≤ (p : ℝ))
    (hc : ∀ j ∈ initialSmallCellList top centers, H ≤ (j : ℝ)) :
    ∀ i (p : P), selectedInitialHalfPrior P A B N hi Y G D Qb Qd b d top centers i p ≠ 0 →
      Real.exp H ≤ (p : ℝ) := by
  have hcell (i : Fin (initialSmallCellList top centers).length) (p : P)
      (hp : primeSubsetPrior P (selectedTailCellPrimes A B N Y hi D
        ((initialSmallCellList top centers).get i)) p ≠ 0) : Real.exp H ≤ (p : ℝ) := by
    obtain ⟨t, ht⟩ := initial_selected_cells_valid htop hcenters _
      (List.get_mem (initialSmallCellList top centers) i)
    have hs := ht.2.2.2.2.2.2 p (primeSubsetPrior_support P _ p hp)
    exact (Real.exp_le_exp.mpr (hc _ (List.get_mem _ i))).trans hs.2.1.le
  intro i p
  refine Fin.cases ?_ (fun j => ?_) i
  · intro hp
    have hs := smoothGiantPrior_active_bounds P hP logCellProfile G
      logCellProfile_zero_outside p hp
    exact (Real.exp_le_exp.mpr (by linarith : H ≤ G - 1)).trans hs.1.le
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [selectedInitialHalfPrior, Fin.cons_succ, Fin.append_left]
      exact fun hp => hb p (primeSubsetPrior_support P Qb p hp)
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [selectedInitialHalfPrior, Fin.cons_succ, Fin.append_right, Fin.append_left]
        exact fun hp => hd p (primeSubsetPrior_support P Qd p hp)
      · simpa only [selectedInitialHalfPrior, Fin.cons_succ, Fin.append_right] using hcell j p

theorem eventual_initial_selected_centers_lower (k : ℕ) (hk : 2 ≤ k)
    (Bs BD Bz : ℝ) (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) :
    ∀ᶠ L : ℝ in atTop, ∀ {A B : Set ℕ} {N hi top : ℕ} {a C Y G lo : ℝ}
      {D : Finset ℕ} {centers : List ℕ} (cb cd : ℤ),
      cb ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊ →
      cd ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊ →
      2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y →
      Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 →
      lo - 2 ≤ G → G ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) →
      SelectedSmallTailCell A B N a C L Y hi D
        ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top →
      List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
        centers (movingCompensationTargets
          (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
          (movingCompensationGaps k BD Bz L)) →
      ∀ j ∈ initialSmallCellList top centers, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ) := by
  filter_upwards [eventual_initial_protected_target k hk Bs BD Bz hBs hBD hBz,
    eventual_protected_cell_target_range,
    eventual_prescribed_compensation_range k (by omega) BD Bz hBD hBz]
    with L hprotected htopRange hcompRange
  intro A B N hi top a C Y G lo D centers cb cd hcb hcd hYlo hYhi hGlo hGhi htop hcenters
  obtain ⟨hJlo, hJhi, hcb0, hcbJ⟩ := hprotected cb cd hcb hcd lo G Y hYlo hYhi hGlo hGhi
  apply initial_selected_centers_lower htop hcenters
    (htopRange _ _ hJlo hJhi hcb0 hcbJ).1
  intro w hw
  exact (hcompRange _ hJlo hJhi w hw).1

theorem eventual_selected_initial_prime_lower (k : ℕ) (hk : 2 ≤ k)
    (Bs BD Bz : ℝ) (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) :
    ∀ᶠ L : ℝ in atTop, ∀ {A B : Set ℕ} {N hi top : ℕ} {a C Y G lo : ℝ}
      {D Qd : Finset ℕ} {centers : List ℕ} (cb cd : ℤ),
      cb ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊ →
      cd ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊ →
      2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y →
      Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 →
      Real.exp ((1 / 20 : ℝ) * L) ≤ lo →
      lo - 2 ≤ G → G ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) →
      Qd ⊆ primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
        (Real.exp ((6 / 10000 : ℝ) * L)) \ D →
      SelectedSmallTailCell A B N a C L Y hi D
        ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top →
      List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
        centers (movingCompensationTargets
          (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
          (movingCompensationGaps k BD Bz L)) →
      ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → ∀ b d : ℕ,
      let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)) \ D
      ∀ i (p : P), selectedInitialHalfPrior P A B N hi Y G D Qb Qd b d top centers i p ≠ 0 →
        Real.exp (Real.exp ((4 / 10000 : ℝ) * L)) ≤ (p : ℝ) := by
  have ht : Tendsto (fun L : ℝ => Real.exp (((1 / 20 : ℝ) - 4 / 10000) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [eventual_initial_selected_centers_lower k hk Bs BD Bz hBs hBD hBz,
    ht.eventually (eventually_ge_atTop (4 : ℝ)), eventually_ge_atTop (0 : ℝ)]
    with L hcentersLower hratio hL
  intro A B N hi top a C Y G lo D Qd centers cb cd hcb hcd hYlo hYhi hlo hGlo hGhi
    hQd htop hcenters P hP b d Qb
  have hr := mul_le_mul_of_nonneg_right hratio
    (Real.exp_nonneg ((4 / 10000 : ℝ) * L))
  rw [← Real.exp_add] at hr
  have he : ((1 / 20 : ℝ) - 4 / 10000) * L + (4 / 10000) * L = (1 / 20) * L := by ring
  rw [he] at hr
  have hsmall : 1 ≤ Real.exp ((4 / 10000 : ℝ) * L) := Real.one_le_exp (by positivity)
  have hG : Real.exp ((4 / 10000 : ℝ) * L) + 1 ≤ G := by linarith
  apply selected_initial_prior_lower htop hcenters P hP b d hG
  · intro p hp
    have hs := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp hp).1
    have hh := (Real.lt_log_iff_exp_lt (by exact_mod_cast hs.1.pos)).mp hs.2.2.1
    exact (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith))).trans hh.le
  · intro p hp
    have hs := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp (hQd hp)).1
    exact ((Real.lt_log_iff_exp_lt (by exact_mod_cast hs.1.pos)).mp hs.2.2.1).le
  · intro j hj
    exact (Real.exp_le_exp.mpr (by linarith : (4 / 10000 : ℝ) * L ≤ (1 / 100) * L)).trans
      (hcentersLower cb cd hcb hcd hYlo hYhi hGlo hGhi htop hcenters j hj)

end Ostmann

end OAI
