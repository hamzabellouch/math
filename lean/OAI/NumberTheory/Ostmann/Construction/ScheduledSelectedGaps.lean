import OAI.NumberTheory.Ostmann.Construction.ScheduledCellGap
import OAI.NumberTheory.Ostmann.Construction.SelectedInitialAlphabet

namespace OAI

/-! # Every actual removal has its prescribed diagonal gap -/
namespace Ostmann
open scoped Classical BigOperators

theorem movingCompensationTargets_drop_gap (J : ℝ) (ds : List ℝ) (n : ℕ)
    (hn : n < ds.length) :
    J + ((movingCompensationTargets J ds).drop (n + 1)).sum -
      ((movingCompensationTargets J ds).drop n).headD 0 = (ds.drop n).headD 0 := by
  induction ds generalizing n with
  | nil => simp at hn
  | cons d ds ih =>
    cases n with
    | zero =>
      simp only [movingCompensationTargets, List.drop_zero, List.drop_succ_cons,
        List.headD_cons]
      ring
    | succ n =>
      simpa only [movingCompensationTargets, List.drop_succ_cons] using ih n (by simpa using hn)

theorem movingCompensationGaps_at (k n : ℕ) (BD Bz L : ℝ) (hn : n < k) :
    ((movingCompensationGaps k BD Bz L).drop n).headD 0 =
      spectatorStepGap BD Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ) (spectatorBulkCount k L) /
        (2 ^ n : ℕ) := by
  rw [list_headD_drop_get _ _ _ (by simpa using hn)]
  simp only [movingCompensationGaps, List.get_ofFn, Fin.val_cast, Nat.cast_pow,
    Nat.cast_ofNat]

theorem movingCompensationTargets_drop_balance (J BD Bz L : ℝ) (k n : ℕ)
    (hn : n < k) :
    let ws := movingCompensationTargets J (movingCompensationGaps k BD Bz L)
    (2 ^ n : ℕ) * (ws.drop n).headD 0 =
      (2 ^ n : ℕ) * (J + (ws.drop (n + 1)).sum) -
        spectatorStepGap BD Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ) (spectatorBulkCount k L) := by
  intro ws
  have hh := movingCompensationTargets_drop_gap J (movingCompensationGaps k BD Bz L)
    n (by simpa using hn)
  rw [movingCompensationGaps_at k n BD Bz L hn] at hh
  have hr : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have he := (eq_div_iff hr.ne').mp hh
  dsimp only [ws]
  nlinarith only [he]

theorem forall₂_headD_drop {R : ℕ → ℝ → Prop} {cs : List ℕ} {ws : List ℝ}
    (h : List.Forall₂ R cs ws) (n : ℕ) (hn : n < cs.length) :
    R ((cs.drop n).headD 0) ((ws.drop n).headD 0) := by
  induction h generalizing n with
  | nil => simp at hn
  | cons h hrest ih =>
    cases n with
    | zero => exact h
    | succ n => simpa only [List.drop_succ_cons] using ih n (by simpa using hn)

theorem selected_scheduled_drop_diagonal_gap
    {A B : Set ℕ} {N hi top : ℕ} {a C L X J cb cg BD Bz : ℝ}
    {D : Finset ℕ} {centers : List ℕ} (k n : ℕ) (hn : n < k)
    (hL : 1 ≤ L) (hX : 0 < X) (hXupper : X ≤ Real.exp L)
    (hk : 1024 * tailCellLinearRate a C + 52 ≤ (k : ℝ) ^ 4)
    (hcount : (8 + 4 * centers.length : ℕ) ≤ L)
    (hcg : cg ≤ (91 / 100 : ℝ) * L)
    (htop : SelectedSmallTailCell A B N a C L X hi D ((J - 2 * cb) / 6) top)
    (hcenters : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L X hi D (t / 4) j)
      centers (movingCompensationTargets J (movingCompensationGaps k BD Bz L))) :
    2 * cg + 1 + ((2 ^ n : ℕ) * 4) * (((centers.drop n).headD 0 : ℝ) + 1) -
        ((∑ i, scheduledSmallLower top (centers.drop (n + 1)) n i) +
          (2 ^ n : ℕ) * (2 * cb - 2)) ≤
      -spectatorStepGap (BD - 1) Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ)
        (spectatorBulkCount k L) := by
  have hlen : centers.length = k := by
    simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using
      hcenters.length_eq
  have hpivot := forall₂_headD_drop hcenters n (by omega)
  have htail := List.forall₂_drop (n + 1) hcenters
  have hcount' : (8 + 4 * (centers.drop (n + 1)).length : ℕ) ≤ L := by
    apply le_trans _ hcount
    exact_mod_cast (show 8 + 4 * (centers.drop (n + 1)).length ≤ 8 + 4 * centers.length by
      simp only [List.length_drop]; omega)
  exact selected_scheduled_initial_diagonal_gap k n hL hX hXupper hk hcount' hcg htop
    hpivot htail (movingCompensationTargets_drop_balance J BD Bz L k n hn)

end Ostmann

end OAI
