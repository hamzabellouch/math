import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PathBounds
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.StageCounts
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SpatialSlices
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.FiniteAddresses

namespace OAI

noncomputable section
namespace VelocityDetection.ExpandingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open Expanding Stacks FiniteAddresses

def K₀ (N b m : ℕ) : ℝ := N * (capacity b m 0 : ℝ) ^ 2

def D (b : ℕ) : ℝ := (b : ℝ) ^ 2

theorem K₀_nonneg (N b m : ℕ) : 0 ≤ K₀ N b m := by unfold K₀; positivity

theorem D_ge_one {b : ℕ} (hb : 0 < b) : 1 ≤ D b := by
  have : (1 : ℝ) ≤ b := by exact_mod_cast hb
  dsimp [D]
  nlinarith

theorem count_eq (N b m n : ℕ) : count (K₀ N b m) (D b) n = N * (capacity b m n : ℝ) ^ 2 := by
  have h := congrArg (fun q : ℕ => (q : ℝ)) (address_count_geometric N b m n)
  simpa only [Nat.cast_mul, Nat.cast_pow, count, K₀, D] using h.symm

end VelocityDetection.ExpandingArray
end

noncomputable section
namespace VelocityDetection.ExpandingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open Expanding Stacks FiniteAddresses
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))
    (terminal : Fin N)

def sign (i : Fin N) : ℝ := if i = terminal then 1 else -1

@[simp] theorem abs_sign (i : Fin N) : |sign terminal i| = 1 := by
  unfold sign
  split_ifs <;> norm_num

end VelocityDetection.ExpandingArray
end

noncomputable section
namespace VelocityDetection.ExpandingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open Expanding Stacks FiniteAddresses
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))
    (terminal : Fin N)
variable (ν : ℝ) (m : ℕ)

def path (n : ℕ) (c : Active hb table (capacity b m n)) : ℝ → Coord 2 :=
  CenterPaths.center (startTime ν (K₀ N b m) (D b) n)
    (duration ν (K₀ N b m) (D b) n)
    (spacing ν (K₀ N b m) (D b) n) (spacing ν (K₀ N b m) (D b) (n + 1))
    (sign terminal (target hb table c).state) (sourceAddress c.val) (targetAddress hb table c)

def stage (n : ℕ) : VectorField 2 := fun t X =>
  ∑ c : Active hb table (capacity b m n), TranslationGates.field
    (radius ν (K₀ N b m) (D b) n) (path hb table terminal ν m n c t)
    (deriv (path hb table terminal ν m n c) t) X

@[fun_prop] theorem contDiff_path (n : ℕ) (c : Active hb table (capacity b m n)) :
    ContDiff ℝ ∞ (path hb table terminal ν m n c) := by unfold path; fun_prop

@[fun_prop] theorem contDiff_stage (n : ℕ) :
    ContDiff ℝ ∞ (fun q : ℝ × Coord 2 => stage hb table terminal ν m n q.1 q.2) := by
  dsimp [stage]
  apply ContDiff.sum
  intro c _
  exact TranslationGates.contDiff_movingField _ (contDiff_path hb table terminal ν m n c)
    ((contDiff_infty_iff_deriv.mp (contDiff_path hb table terminal ν m n c)).2)

theorem divergence_stage (n : ℕ) (t : ℝ) (X : Coord 2) :
    divergence (stage hb table terminal ν m n) t X = 0 := by
  change divergence (fun t X => ∑ c : Active hb table (capacity b m n),
    TranslationGates.field (radius ν (K₀ N b m) (D b) n)
      (path hb table terminal ν m n c t) (deriv (path hb table terminal ν m n c) t) X) t X = 0
  rw [SpatialCalculus.divergence_sum]
  · apply Finset.sum_eq_zero
    intro c _
    exact TranslationGates.divergence_field (radius ν (K₀ N b m) (D b) n)
      (path hb table terminal ν m n c t) (deriv (path hb table terminal ν m n c) t) X
  · intro c _ s
    exact TranslationGates.contDiff_field _ _ _

theorem stage_zero_before (hν : 0 < ν) (n : ℕ) {t : ℝ}
    (ht : t ≤ startTime ν (K₀ N b m) (D b) n) (X : Coord 2) :
    stage hb table terminal ν m n t X = 0 := by
  apply Finset.sum_eq_zero
  intro c _
  change CenterPaths.gate _ _ _ _ _ _ _ _ t X = 0
  exact CenterPaths.gate_zero_before
    (lt_of_lt_of_le (by norm_num) (duration_ge_one hν (K₀_nonneg N b m) (D_ge_one hb) n))
    _ _ _ _ _ _ _ ht X

theorem stage_zero_after (hν : 0 < ν) (n : ℕ) {t : ℝ}
    (ht : startTime ν (K₀ N b m) (D b) (n + 1) ≤ t) (X : Coord 2) :
    stage hb table terminal ν m n t X = 0 := by
  apply Finset.sum_eq_zero
  intro c _
  change CenterPaths.gate _ _ _ _ _ _ _ _ t X = 0
  exact CenterPaths.gate_zero_after
    (lt_of_lt_of_le (by norm_num) (duration_ge_one hν (K₀_nonneg N b m) (D_ge_one hb) n))
    _ _ _ _ _ _ _ ht X

theorem compactSupport_stage (hν : 0 < ν) (n : ℕ) :
    HasCompactSupport (fun q : ℝ × Coord 2 => stage hb table terminal ν m n q.1 q.2) := by
  have h (c : Active hb table (capacity b m n)) : HasCompactSupport
      (fun q : ℝ × Coord 2 => TranslationGates.field
        (radius ν (K₀ N b m) (D b) n) (path hb table terminal ν m n c q.1)
        (deriv (path hb table terminal ν m n c) q.1) q.2) := by
    apply CenterPaths.compactSupport_gate
    · linarith [radius_ge_one hν (K₀_nonneg N b m) (D_ge_one hb) n]
    · linarith [duration_ge_one hν (K₀_nonneg N b m) (D_ge_one hb) n]
  simpa only [stage, Finset.sum_fn] using HasCompactSupport.finset_sum
    (s := Finset.univ) (fun c _ => h c)

def field : VectorField 2 := fun t X => ∑' n : ℕ, stage hb table terminal ν m n t X

theorem field_eq_finite (hν : 0 < ν) {Q : ℕ} {t : ℝ} (ht : t < Q) (X : Coord 2) :
    field hb table terminal ν m t X = ∑ n ∈ Finset.range Q, stage hb table terminal ν m n t X := by
  apply tsum_eq_sum
  intro n hn
  apply stage_zero_before hb table terminal ν m hν n _ X
  have hn' : Q ≤ n := by simpa using hn
  have hc : (Q : ℝ) ≤ n := by exact_mod_cast hn'
  linarith [startTime_ge hν (K₀_nonneg N b m) (D_ge_one hb) n]

@[fun_prop] theorem contDiff_field (hν : 0 < ν) :
    ContDiff ℝ ∞ (fun q : ℝ × Coord 2 => field hb table terminal ν m q.1 q.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  obtain ⟨Q, hQ⟩ := exists_nat_gt q.1
  have hs : ContDiff ℝ ∞ (fun p : ℝ × Coord 2 =>
      ∑ n ∈ Finset.range Q, stage hb table terminal ν m n p.1 p.2) :=
    ContDiff.sum (fun n _ => contDiff_stage hb table terminal ν m n)
  apply hs.contDiffAt.congr_of_eventuallyEq
  have hev : ∀ᶠ p : ℝ × Coord 2 in 𝓝 q, p.1 < Q :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds hQ
  exact hev.mono (fun p hp => field_eq_finite hb table terminal ν m hν hp p.2)

theorem field_at_rest (hν : 0 < ν) {t : ℝ} (ht : t ≤ 1) (X : Coord 2) :
    field hb table terminal ν m t X = 0 := by
  change (∑' n : ℕ, stage hb table terminal ν m n t X) = 0
  calc
    _ = ∑' n : ℕ, (0 : Coord 2) := by
      apply tsum_congr
      intro n
      apply stage_zero_before hb table terminal ν m hν n _ X
      linarith [startTime_ge hν (K₀_nonneg N b m) (D_ge_one hb) n, Nat.cast_nonneg (α := ℝ) n]
    _ = _ := tsum_zero

theorem field_eq_stage (hν : 0 < ν) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (startTime ν (K₀ N b m) (D b) n) (startTime ν (K₀ N b m) (D b) (n + 1)))
    (X : Coord 2) : field hb table terminal ν m t X = stage hb table terminal ν m n t X := by
  apply tsum_eq_single n
  intro k hk
  have hm := (startTime_strictMono hν (K₀_nonneg N b m) (D_ge_one hb)).monotone
  rcases lt_or_gt_of_ne hk with h | h
  · exact stage_zero_after hb table terminal ν m hν k ((hm (by omega)).trans ht.1) X
  · exact stage_zero_before hb table terminal ν m hν k (ht.2.trans (hm (by omega))) X

theorem divergence_field (hν : 0 < ν) (t : ℝ) (X : Coord 2) :
    divergence (field hb table terminal ν m) t X = 0 := by
  obtain ⟨Q, hQ⟩ := exists_nat_gt t
  have heq := funext (field_eq_finite hb table terminal ν m hν hQ)
  rw [SpatialCalculus.divergence_congr_at
    (v := fun s X => ∑ n ∈ Finset.range Q, stage hb table terminal ν m n s X) t X heq]
  have hs (n : ℕ) (_ : n ∈ Finset.range Q) (s : ℝ) :
      ContDiff ℝ ∞ (stage hb table terminal ν m n s) :=
    SpatialCalculus.contDiff_slice (contDiff_stage hb table terminal ν m n) s
  exact (SpatialCalculus.divergence_sum (Finset.range Q) (stage hb table terminal ν m) hs t X).trans
    (by simp only [divergence_stage, Finset.sum_const_zero])

theorem finiteCylinderSupport (hν : 0 < ν) (T : ℝ) :
    ∃ K : Set (Coord 2), IsCompact K ∧ ∀ t, 0 ≤ t → t ≤ T →
      ∀ X, X ∉ K → field hb table terminal ν m t X = 0 := by
  obtain ⟨Q, hQ⟩ := exists_nat_gt T
  let f : ℝ × Coord 2 → Coord 2 :=
    fun q => ∑ n ∈ Finset.range Q, stage hb table terminal ν m n q.1 q.2
  have hf : HasCompactSupport f := by
    simpa only [Finset.sum_fn, f] using HasCompactSupport.finset_sum
      (fun n (_ : n ∈ Finset.range Q) => compactSupport_stage hb table terminal ν m hν n)
  refine ⟨Prod.snd '' tsupport f, hf.image continuous_snd, ?_⟩
  intro t _ ht X hX
  rw [field_eq_finite hb table terminal ν m hν (ht.trans_lt hQ)]
  change f (t, X) = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hp
  exact hX ⟨(t, X), hp, rfl⟩

theorem paths_separated (hν : 0 < ν) (hm : 1 ≤ m)
    (hdir : IncomingDirection table) (hin : IncomingRule table) (n : ℕ)
    (c d : Active hb table (capacity b m n)) (hcd : c ≠ d) (t : ℝ) :
    ∃ i : Fin 2, 16 * radius ν (K₀ N b m) (D b) n ≤
      |path hb table terminal ν m n c t i - path hb table terminal ν m n d t i| := by
  have hB : 0 < capacity b m n := pow_pos hb _
  have hc : sourceAddress c.val ≠ sourceAddress d.val := by
    intro h
    exact hcd (Subtype.ext (sourceAddress_injective hB h))
  have hd : targetAddress hb table c ≠ targetAddress hb table d :=
    (targetAddress_injective hb table hB (capacity_dvd hm) hdir hin).ne hcd
  exact CenterPaths.separated (spacing_pos hν (K₀_nonneg N b m) (D_ge_one hb) n).le
    (spacing_next_ge hν (K₀_nonneg N b m) (D_ge_one hb) n) _ _ _ _ t hc hd

theorem stage_plateau (hν : 0 < ν) (hm : 1 ≤ m)
    (hdir : IncomingDirection table) (hin : IncomingRule table) (n : ℕ)
    (c : Active hb table (capacity b m n)) (t : ℝ) (X : Coord 2)
    (hX : ∀ i, |X i - path hb table terminal ν m n c t i| ≤ radius ν (K₀ N b m) (D b) n) :
    stage hb table terminal ν m n t X = deriv (path hb table terminal ν m n c) t := by
  apply TranslationGates.array_plateau
    (lt_of_lt_of_le (by norm_num) (radius_ge_one hν (K₀_nonneg N b m) (D_ge_one hb) n))
    (fun d => path hb table terminal ν m n d t)
    (fun d => deriv (path hb table terminal ν m n d) t)
    (fun d _ e _ h => paths_separated hb table terminal ν m hν hm hdir hin n d e h t)
    (Finset.mem_univ c) X hX

theorem field_plateau (hν : 0 < ν) (hm : 1 ≤ m)
    (hdir : IncomingDirection table) (hin : IncomingRule table) (n : ℕ)
    (c : Active hb table (capacity b m n)) {t : ℝ}
    (ht : t ∈ Icc (startTime ν (K₀ N b m) (D b) n) (startTime ν (K₀ N b m) (D b) (n + 1)))
    (X : Coord 2)
    (hX : ∀ i, |X i - path hb table terminal ν m n c t i| ≤ radius ν (K₀ N b m) (D b) n) :
    field hb table terminal ν m t X = deriv (path hb table terminal ν m n c) t := by
  rw [field_eq_stage hb table terminal ν m hν n ht]
  exact stage_plateau hb table terminal ν m hν hm hdir hin n c t X hX

theorem path_negative (hν : 0 < ν) (n : ℕ)
    (c : Active hb table (capacity b m n))
    (hc : (target hb table c).state ≠ terminal) (t : ℝ) :
    path hb table terminal ν m n c t 1 ≤ -spacing ν (K₀ N b m) (D b) n := by
  unfold path
  rw [sign, ite_eq_right hc]
  exact CenterPaths.negative_height (spacing_pos hν (K₀_nonneg N b m) (D_ge_one hb) n).le
    (spacing_next_ge hν (K₀_nonneg N b m) (D_ge_one hb) n) _ _ _ _ _

theorem path_end (hν : 0 < ν) (n : ℕ) (c : Active hb table (capacity b m n)) :
    path hb table terminal ν m n c (startTime ν (K₀ N b m) (D b) (n + 1)) =
      ![spacing ν (K₀ N b m) (D b) (n + 1) * targetAddress hb table c,
        sign terminal (target hb table c).state * spacing ν (K₀ N b m) (D b) (n + 1)] :=
  CenterPaths.center_end
    (lt_of_lt_of_le (by norm_num) (duration_ge_one hν (K₀_nonneg N b m) (D_ge_one hb) n))
    _ _ _ _ _ _

theorem path_coordinate_bounds (hν : 0 < ν) (hm : 1 ≤ m) (n : ℕ)
    (c : Active hb table (capacity b m n)) :
    |spacing ν (K₀ N b m) (D b) n| ≤ duration ν (K₀ N b m) (D b) n ∧
    |spacing ν (K₀ N b m) (D b) n * sourceAddress c.val| ≤ duration ν (K₀ N b m) (D b) n ∧
    |spacing ν (K₀ N b m) (D b) (n + 1) * targetAddress hb table c| ≤ duration ν (K₀ N b m) (D b) n ∧
    |CenterPaths.privateRow (spacing ν (K₀ N b m) (D b) n) (sourceAddress c.val)| ≤
      duration ν (K₀ N b m) (D b) n ∧
    |sign terminal (target hb table c).state * spacing ν (K₀ N b m) (D b) (n + 1)| ≤
      duration ν (K₀ N b m) (D b) n := by
  apply Expanding.path_coordinate_bounds hν (K₀_nonneg N b m) (D_ge_one hb) n
  · rw [count_eq]
    exact_mod_cast sourceAddress_count c.val
  · rw [count_eq, capacity_succ]
    exact_mod_cast targetAddress_count hb table (capacity_dvd hm) c
  · simp

theorem path_derivative_bounds (hν : 0 < ν) (hm : 1 ≤ m) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (c : Active hb table (capacity b m n)) (t : ℝ) (i : Fin 2),
      |iteratedDeriv (j + 1) (fun s => path hb table terminal ν m n c s i) t| ≤
        C / duration ν (K₀ N b m) (D b) n ^ j := by
  obtain ⟨C, hC, hc⟩ := CenterPaths.center_derivative_bound j
  refine ⟨C, hC, ?_⟩
  intro n c t i
  obtain ⟨hS, hSk, hSl, hY, hσ⟩ := path_coordinate_bounds hb table terminal ν m hν hm n c
  exact hc _ _ _ _ _ _ _
    (lt_of_lt_of_le (by norm_num) (duration_ge_one hν (K₀_nonneg N b m) (D_ge_one hb) n))
    hS hSk hSl hY hσ t i

end VelocityDetection.ExpandingArray
end

end OAI
