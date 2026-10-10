import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ExpandingArray
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.GateBounds
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.UniformDerivativesNormSumLeSparse
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.JointCalculusHorizontalLinear
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.RoutingData

namespace OAI

noncomputable section
namespace VelocityDetection.RoutingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open scoped Topology ContDiff BigOperators ZeroAtInfty
open Expanding UniformDerivatives JointCalculus SmoothProfiles
variable (A : RoutingData) (ν : ℝ)

def path (n : ℕ) (c : A.Instruction n) : ℝ → Coord 2 :=
  CenterPaths.center (startTime ν A.K A.D n)
    (duration ν A.K A.D n)
    (spacing ν A.K A.D n) (spacing ν A.K A.D (n + 1))
    (A.sign n c) (A.source n c) (A.target n c)

def stage (n : ℕ) : VectorField 2 := fun t X =>
  ∑ c : A.Instruction n, TranslationGates.field
    (radius ν A.K A.D n) (path A ν n c t)
    (deriv (path A ν n c) t) X

@[fun_prop] theorem contDiff_path (n : ℕ) (c : A.Instruction n) :
    ContDiff ℝ ∞ (path A ν n c) := by unfold path; fun_prop

@[fun_prop] theorem contDiff_stage (n : ℕ) :
    ContDiff ℝ ∞ (fun q : ℝ × Coord 2 => stage A ν n q.1 q.2) := by
  dsimp [stage]
  apply ContDiff.sum
  intro c _
  exact TranslationGates.contDiff_movingField _ (contDiff_path A ν n c)
    ((contDiff_infty_iff_deriv.mp (contDiff_path A ν n c)).2)

theorem divergence_stage (n : ℕ) (t : ℝ) (X : Coord 2) :
    divergence (stage A ν n) t X = 0 := by
  change divergence (fun t X => ∑ c : A.Instruction n,
    TranslationGates.field (radius ν A.K A.D n)
      (path A ν n c t) (deriv (path A ν n c) t) X) t X = 0
  rw [SpatialCalculus.divergence_sum]
  · apply Finset.sum_eq_zero
    intro c _
    exact TranslationGates.divergence_field (radius ν A.K A.D n)
      (path A ν n c t) (deriv (path A ν n c) t) X
  · intro c _ s
    exact TranslationGates.contDiff_field _ _ _

theorem stage_zero_before (hν : 0 < ν) (n : ℕ) {t : ℝ}
    (ht : t ≤ startTime ν A.K A.D n) (X : Coord 2) :
    stage A ν n t X = 0 := by
  apply Finset.sum_eq_zero
  intro c _
  change CenterPaths.gate _ _ _ _ _ _ _ _ t X = 0
  exact CenterPaths.gate_zero_before
    (lt_of_lt_of_le (by norm_num) (duration_ge_one hν A.K_nonneg A.D_ge_one n))
    _ _ _ _ _ _ _ ht X

theorem stage_zero_after (hν : 0 < ν) (n : ℕ) {t : ℝ}
    (ht : startTime ν A.K A.D (n + 1) ≤ t) (X : Coord 2) :
    stage A ν n t X = 0 := by
  apply Finset.sum_eq_zero
  intro c _
  change CenterPaths.gate _ _ _ _ _ _ _ _ t X = 0
  exact CenterPaths.gate_zero_after
    (lt_of_lt_of_le (by norm_num) (duration_ge_one hν A.K_nonneg A.D_ge_one n))
    _ _ _ _ _ _ _ ht X

theorem compactSupport_stage (hν : 0 < ν) (n : ℕ) :
    HasCompactSupport (fun q : ℝ × Coord 2 => stage A ν n q.1 q.2) := by
  have h (c : A.Instruction n) : HasCompactSupport
      (fun q : ℝ × Coord 2 => TranslationGates.field
        (radius ν A.K A.D n) (path A ν n c q.1)
        (deriv (path A ν n c) q.1) q.2) := by
    apply CenterPaths.compactSupport_gate
    · linarith [radius_ge_one hν A.K_nonneg A.D_ge_one n]
    · linarith [duration_ge_one hν A.K_nonneg A.D_ge_one n]
  simpa only [stage, Finset.sum_fn] using HasCompactSupport.finset_sum
    (s := Finset.univ) (fun c _ => h c)

def field : VectorField 2 := fun t X => ∑' n : ℕ, stage A ν n t X

theorem field_eq_finite (hν : 0 < ν) {Q : ℕ} {t : ℝ} (ht : t < Q) (X : Coord 2) :
    field A ν t X = ∑ n ∈ Finset.range Q, stage A ν n t X := by
  apply tsum_eq_sum
  intro n hn
  apply stage_zero_before A ν hν n _ X
  have hn' : Q ≤ n := by simpa using hn
  have hc : (Q : ℝ) ≤ n := by exact_mod_cast hn'
  linarith [startTime_ge hν A.K_nonneg A.D_ge_one n]

@[fun_prop] theorem contDiff_field (hν : 0 < ν) :
    ContDiff ℝ ∞ (fun q : ℝ × Coord 2 => field A ν q.1 q.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  obtain ⟨Q, hQ⟩ := exists_nat_gt q.1
  have hs : ContDiff ℝ ∞ (fun p : ℝ × Coord 2 =>
      ∑ n ∈ Finset.range Q, stage A ν n p.1 p.2) :=
    ContDiff.sum (fun n _ => contDiff_stage A ν n)
  apply hs.contDiffAt.congr_of_eventuallyEq
  have hev : ∀ᶠ p : ℝ × Coord 2 in 𝓝 q, p.1 < Q :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds hQ
  exact hev.mono (fun p hp => field_eq_finite A ν hν hp p.2)

theorem field_at_rest (hν : 0 < ν) {t : ℝ} (ht : t ≤ 1) (X : Coord 2) :
    field A ν t X = 0 := by
  change (∑' n : ℕ, stage A ν n t X) = 0
  calc
    _ = ∑' n : ℕ, (0 : Coord 2) := by
      apply tsum_congr
      intro n
      apply stage_zero_before A ν hν n _ X
      linarith [startTime_ge hν A.K_nonneg A.D_ge_one n, Nat.cast_nonneg (α := ℝ) n]
    _ = _ := tsum_zero

theorem field_eq_stage (hν : 0 < ν) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (startTime ν A.K A.D n) (startTime ν A.K A.D (n + 1)))
    (X : Coord 2) : field A ν t X = stage A ν n t X := by
  apply tsum_eq_single n
  intro k hk
  have hm := (startTime_strictMono hν A.K_nonneg A.D_ge_one).monotone
  rcases lt_or_gt_of_ne hk with h | h
  · exact stage_zero_after A ν hν k ((hm (by omega)).trans ht.1) X
  · exact stage_zero_before A ν hν k (ht.2.trans (hm (by omega))) X

theorem divergence_field (hν : 0 < ν) (t : ℝ) (X : Coord 2) :
    divergence (field A ν) t X = 0 := by
  obtain ⟨Q, hQ⟩ := exists_nat_gt t
  have heq := funext (field_eq_finite A ν hν hQ)
  rw [SpatialCalculus.divergence_congr_at
    (v := fun s X => ∑ n ∈ Finset.range Q, stage A ν n s X) t X heq]
  have hs (n : ℕ) (_ : n ∈ Finset.range Q) (s : ℝ) :
      ContDiff ℝ ∞ (stage A ν n s) :=
    SpatialCalculus.contDiff_slice (contDiff_stage A ν n) s
  exact (SpatialCalculus.divergence_sum (Finset.range Q) (stage A ν) hs t X).trans
    (by simp only [divergence_stage, Finset.sum_const_zero])

theorem finiteCylinderSupport (hν : 0 < ν) (T : ℝ) :
    ∃ K : Set (Coord 2), IsCompact K ∧ ∀ t, 0 ≤ t → t ≤ T →
      ∀ X, X ∉ K → field A ν t X = 0 := by
  obtain ⟨Q, hQ⟩ := exists_nat_gt T
  let f : ℝ × Coord 2 → Coord 2 :=
    fun q => ∑ n ∈ Finset.range Q, stage A ν n q.1 q.2
  have hf : HasCompactSupport f := by
    simpa only [Finset.sum_fn, f] using HasCompactSupport.finset_sum
      (fun n (_ : n ∈ Finset.range Q) => compactSupport_stage A ν hν n)
  refine ⟨Prod.snd '' tsupport f, hf.image continuous_snd, ?_⟩
  intro t _ ht X hX
  rw [field_eq_finite A ν hν (ht.trans_lt hQ)]
  change f (t, X) = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hp
  exact hX ⟨(t, X), hp, rfl⟩

theorem paths_separated (hν : 0 < ν)
    (n : ℕ)
    (c d : A.Instruction n) (hcd : c ≠ d) (t : ℝ) :
    ∃ i : Fin 2, 16 * radius ν A.K A.D n ≤
      |path A ν n c t i - path A ν n d t i| := by
  exact CenterPaths.separated (spacing_pos hν A.K_nonneg A.D_ge_one n).le
    (spacing_next_ge hν A.K_nonneg A.D_ge_one n) _ _ _ _ t
    ((A.source_injective n).ne hcd) ((A.target_injective n).ne hcd)

theorem stage_plateau (hν : 0 < ν)
    (n : ℕ)
    (c : A.Instruction n) (t : ℝ) (X : Coord 2)
    (hX : ∀ i, |X i - path A ν n c t i| ≤ radius ν A.K A.D n) :
    stage A ν n t X = deriv (path A ν n c) t := by
  apply TranslationGates.array_plateau
    (lt_of_lt_of_le (by norm_num) (radius_ge_one hν A.K_nonneg A.D_ge_one n))
    (fun d => path A ν n d t)
    (fun d => deriv (path A ν n d) t)
    (fun d _ e _ h => paths_separated A ν hν n d e h t)
    (Finset.mem_univ c) X hX

theorem field_plateau (hν : 0 < ν)
    (n : ℕ)
    (c : A.Instruction n) {t : ℝ}
    (ht : t ∈ Icc (startTime ν A.K A.D n) (startTime ν A.K A.D (n + 1)))
    (X : Coord 2)
    (hX : ∀ i, |X i - path A ν n c t i| ≤ radius ν A.K A.D n) :
    field A ν t X = deriv (path A ν n c) t := by
  rw [field_eq_stage A ν hν n ht]
  exact stage_plateau A ν hν n c t X hX

theorem path_negative (hν : 0 < ν) (n : ℕ)
    (c : A.Instruction n)
    (hc : A.sign n c = -1) (t : ℝ) :
    path A ν n c t 1 ≤ -spacing ν A.K A.D n := by
  unfold path
  rw [hc]
  exact CenterPaths.negative_height (spacing_pos hν A.K_nonneg A.D_ge_one n).le
    (spacing_next_ge hν A.K_nonneg A.D_ge_one n) _ _ _ _ _

theorem path_end (hν : 0 < ν) (n : ℕ) (c : A.Instruction n) :
    path A ν n c (startTime ν A.K A.D (n + 1)) =
      ![spacing ν A.K A.D (n + 1) * A.target n c,
        A.sign n c * spacing ν A.K A.D (n + 1)] :=
  CenterPaths.center_end
    (lt_of_lt_of_le (by norm_num) (duration_ge_one hν A.K_nonneg A.D_ge_one n))
    _ _ _ _ _ _

theorem path_coordinate_bounds (hν : 0 < ν) (n : ℕ)
    (c : A.Instruction n) :
    |spacing ν A.K A.D n| ≤ duration ν A.K A.D n ∧
    |spacing ν A.K A.D n * A.source n c| ≤ duration ν A.K A.D n ∧
    |spacing ν A.K A.D (n + 1) * A.target n c| ≤ duration ν A.K A.D n ∧
    |CenterPaths.privateRow (spacing ν A.K A.D n) (A.source n c)| ≤
      duration ν A.K A.D n ∧
    |A.sign n c * spacing ν A.K A.D (n + 1)| ≤
      duration ν A.K A.D n := by
  apply Expanding.path_coordinate_bounds hν A.K_nonneg A.D_ge_one n
  · exact A.source_count n c
  · exact A.target_count n c
  · exact (A.abs_sign n c).le

theorem path_derivative_bounds (hν : 0 < ν) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (c : A.Instruction n) (t : ℝ) (i : Fin 2),
      |iteratedDeriv (j + 1) (fun s => path A ν n c s i) t| ≤
        C / duration ν A.K A.D n ^ j := by
  obtain ⟨C, hC, hc⟩ := CenterPaths.center_derivative_bound j
  refine ⟨C, hC, ?_⟩
  intro n c t i
  obtain ⟨hS, hSk, hSl, hY, hσ⟩ := path_coordinate_bounds A ν hν n c
  exact hc _ _ _ _ _ _ _
    (lt_of_lt_of_le (by norm_num) (duration_ge_one hν A.K_nonneg A.D_ge_one n))
    hS hSk hSl hY hσ t i

def gate (n : ℕ) (c : A.Instruction n) (q : ℝ × Coord 2) : Coord 2 :=
  TranslationGates.field (radius ν A.K A.D n)
    (path A ν n c q.1) (deriv (path A ν n c) q.1) q.2

@[fun_prop] theorem contDiff_gate (n : ℕ) (c : A.Instruction n) :
    ContDiff ℝ ∞ (gate A ν n c) :=
  TranslationGates.contDiff_movingField _ (contDiff_path A ν n c)
    ((contDiff_infty_iff_deriv.mp (contDiff_path A ν n c)).2)

theorem gates_uniformly_bounded (hν : 0 < ν) (i : Fin 2) :
    Bounded (fun (a : (n : ℕ) × A.Instruction n) q =>
      gate A ν a.1 a.2 q i) := by
  unfold gate
  refine TranslationGates.bounded_movingField
    (I := (n : ℕ) × A.Instruction n)
    (fun a => radius ν A.K A.D a.1)
    (fun a => radius_ge_one hν A.K_nonneg A.D_ge_one a.1)
    (fun a => path A ν a.1 a.2)
    (fun a => contDiff_path A ν a.1 a.2) ?_ i
  intro j n hn
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨C, hC, hc⟩ := path_derivative_bounds A ν hν n
  refine ⟨C, hC, fun a t => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact (hc a.1 a.2 t j).trans
    (div_le_self hC (one_le_pow₀ (duration_ge_one hν A.K_nonneg A.D_ge_one a.1)))

theorem gate_jet_zero_outside (hν : 0 < ν) (n d : ℕ)
    (c : A.Instruction n) (q : ℝ × Coord 2) (i : Fin 2)
    (hq : ∃ j, 3 * radius ν A.K A.D n <
      |q.2 j - path A ν n c q.1 j|) :
    iteratedFDeriv ℝ d (fun q => gate A ν n c q i) q = 0 := by
  obtain ⟨j, hj⟩ := hq
  have hcont : Continuous (fun p : ℝ × Coord 2 =>
      |p.2 j - path A ν n c p.1 j|) :=
    ((continuous_apply j).comp continuous_snd |>.sub
      ((continuous_apply j).comp ((contDiff_path A ν n c).continuous.comp
        continuous_fst))).abs
  have heq : (fun p => gate A ν n c p i) =ᶠ[𝓝 q] 0 := by
    filter_upwards [(isOpen_lt continuous_const hcont).mem_nhds hj] with p hp
    have h := TranslationGates.field_zero_outside
      (lt_of_lt_of_le zero_lt_one (radius_ge_one hν A.K_nonneg A.D_ge_one n))
      (path A ν n c p.1) (deriv (path A ν n c) p.1) p.2 ⟨j, hp.le⟩
    exact congrFun h i
  simpa using (heq.iteratedFDeriv ℝ d).eq_of_nhds

theorem gate_jets_disjoint (hν : 0 < ν)
    (n d : ℕ)
    (c e : A.Instruction n) (hce : c ≠ e) (q : ℝ × Coord 2) (i : Fin 2) :
    iteratedFDeriv ℝ d (fun q => gate A ν n c q i) q = 0 ∨
      iteratedFDeriv ℝ d (fun q => gate A ν n e q i) q = 0 := by
  obtain ⟨j, hj⟩ := paths_separated A ν hν n c e hce q.1
  have hR : 0 < radius ν A.K A.D n :=
    lt_of_lt_of_le zero_lt_one (radius_ge_one hν A.K_nonneg A.D_ge_one n)
  by_cases hc : 3 * radius ν A.K A.D n <
      |q.2 j - path A ν n c q.1 j|
  · exact Or.inl (gate_jet_zero_outside A ν hν n d c q i ⟨j, hc⟩)
  · right
    apply gate_jet_zero_outside A ν hν n d e q i
    refine ⟨j, ?_⟩
    have htri : |path A ν n c q.1 j - path A ν n e q.1 j| ≤
        |q.2 j - path A ν n c q.1 j| +
          |q.2 j - path A ν n e q.1 j| := by
      simpa only [abs_sub_comm (path A ν n c q.1 j) (q.2 j)]
        using abs_sub_le (path A ν n c q.1 j) (q.2 j)
          (path A ν n e q.1 j)
    linarith

theorem stages_uniformly_bounded (hν : 0 < ν)
    (i : Fin 2) :
    Bounded (fun n (q : ℝ × Coord 2) => stage A ν n q.1 q.2 i) := by
  intro d
  obtain ⟨C, hC, hc⟩ := gates_uniformly_bounded A ν hν i d
  refine ⟨C, hC, fun n q => ?_⟩
  have heq : (fun q : ℝ × Coord 2 => stage A ν n q.1 q.2 i) =
      ∑ c : A.Instruction n, fun q => gate A ν n c q i := by
    ext q
    simp only [stage, gate, Finset.sum_apply]
  change ‖iteratedFDeriv ℝ d (fun q : ℝ × Coord 2 => stage A ν n q.1 q.2 i) q‖ ≤ C
  rw [heq, iteratedFDeriv_sum_apply]
  · apply norm_sum_le_sparse _ _ hC
    · intro c _
      exact hc ⟨n, c⟩ q
    · intro c _ e _ hce
      exact gate_jets_disjoint A ν hν n d c e hce q i
  · intro c _
    exact (contDiff_infty.mp ((contDiff_apply ℝ ℝ i).comp
      (contDiff_gate A ν n c)) d).contDiffAt

theorem stage_jet_zero_before (hν : 0 < ν) (n d : ℕ) (q : ℝ × Coord 2) (i : Fin 2)
    (hq : q.1 ≤ startTime ν A.K A.D n) :
    iteratedFDeriv ℝ d (fun q => stage A ν n q.1 q.2 i) q = 0 := by
  exact jet_zero_before ((contDiff_apply ℝ ℝ i).comp (contDiff_stage A ν n))
    (fun t ht X => congrFun (stage_zero_before A ν hν n ht X) i) d hq q.2

theorem stage_jet_zero_after (hν : 0 < ν) (n d : ℕ) (q : ℝ × Coord 2) (i : Fin 2)
    (hq : startTime ν A.K A.D (n + 1) ≤ q.1) :
    iteratedFDeriv ℝ d (fun q => stage A ν n q.1 q.2 i) q = 0 := by
  exact jet_zero_after ((contDiff_apply ℝ ℝ i).comp (contDiff_stage A ν n))
    (fun t ht X => congrFun (stage_zero_after A ν hν n ht X) i) d hq q.2

theorem stage_jets_disjoint (hν : 0 < ν) (n k d : ℕ) (hnk : n ≠ k) (q : ℝ × Coord 2) (i : Fin 2) :
    iteratedFDeriv ℝ d (fun q => stage A ν n q.1 q.2 i) q = 0 ∨
      iteratedFDeriv ℝ d (fun q => stage A ν k q.1 q.2 i) q = 0 := by
  wlog hnk' : n < k generalizing n k
  · exact (this k n hnk.symm (by omega)).symm
  by_cases hq : q.1 ≤ startTime ν A.K A.D k
  · exact Or.inr (stage_jet_zero_before A ν hν k d q i hq)
  · left
    apply stage_jet_zero_after A ν hν n d q i
    have hm := (startTime_strictMono hν A.K_nonneg A.D_ge_one).monotone (show n + 1 ≤ k by omega)
    linarith

theorem field_uniformly_bounded (hν : 0 < ν)
    (i : Fin 2) :
    Bounded (fun _ : Unit => fun q : ℝ × Coord 2 => field A ν q.1 q.2 i) := by
  intro d
  obtain ⟨C, hC, hc⟩ := stages_uniformly_bounded A ν hν i d
  refine ⟨C, hC, fun _ q => ?_⟩
  obtain ⟨Q, hQ⟩ := exists_nat_gt q.1
  have heq : (fun q : ℝ × Coord 2 => field A ν q.1 q.2 i) =ᶠ[𝓝 q]
      ∑ n ∈ Finset.range Q, fun q => stage A ν n q.1 q.2 i := by
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hQ] with p hp
    simpa only [Finset.sum_apply] using congrFun (field_eq_finite A ν hν hp p.2) i
  rw [(heq.iteratedFDeriv ℝ d).eq_of_nhds, iteratedFDeriv_sum_apply]
  · apply norm_sum_le_sparse _ _ hC
    · intro n _
      exact hc n q
    · intro n _ k _ hnk
      exact stage_jets_disjoint A ν hν n k d hnk q i
  · intro n _
    exact (contDiff_infty.mp ((contDiff_apply ℝ ℝ i).comp
      (contDiff_stage A ν n)) d).contDiffAt

def force (p : Coord 2) : VectorField 3 := fun t X =>
  lift (residual ν (uncurry (field A ν))) (uncurry (impulse p)) (t, X)

@[fun_prop] theorem contDiff_force (hν : 0 < ν) (p : Coord 2) :
    ContDiff ℝ ∞ (uncurry (force A ν p)) :=
  contDiff_lift (contDiff_residual ν (contDiff_field A ν hν))
    (contDiff_impulse p)

theorem force_uniformly_bounded (hν : 0 < ν)
    (p : Coord 2) :
    Bounded (fun _ : Unit => uncurry (force A ν p)) := by
  apply bounded_lift (contDiff_residual ν (contDiff_field A ν hν))
    (contDiff_impulse p)
  · exact Bounded.residual ν (contDiff_field A ν hν)
      (field_uniformly_bounded A ν hν)
  · exact compact (contDiff_impulse p) (compactSupport_impulse p)

theorem force_vertical_independent (p : Coord 2) (t : ℝ) (X : Coord 3) (z : ℝ) :
    force A ν p t (update X 2 z) = force A ν p t X := by
  simp only [force, lift, projection_apply, horizontal_update_two]

theorem force_eq_triangular (hν : 0 < ν) (p : Coord 2) {t : ℝ} (ht : 0 ≤ t) (X : Coord 3) :
    force A ν p t X =
      triangularForce ν (field A ν) (impulse p) t X := by
  simp only [force, lift, projection_apply,
    residual_eq_horizontalResidual ν (a := field A ν) (contDiff_field A ν hν) ht,
    triangularForce, liftVelocity, uncurry_apply_pair]

end VelocityDetection.RoutingArray
end

end OAI
