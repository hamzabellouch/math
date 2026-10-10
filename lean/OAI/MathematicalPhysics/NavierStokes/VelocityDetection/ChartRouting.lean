import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.HistoryRouting
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Periodization

namespace OAI

noncomputable section
namespace VelocityDetection.ChartRouting
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open Expanding CenterPaths SpatialCalculus
variable (A : RoutingData)

def scale (N : ℕ) : ℝ := (1024 * (count A.K A.D (N+1) + 4))⁻¹

theorem scale_pos (N : ℕ) : 0 < scale A N := by
  have hd : 0 ≤ count A.K A.D (N+1) := by
    unfold count
    exact mul_nonneg A.K_nonneg (pow_nonneg (by linarith [A.D_ge_one]) _)
  unfold scale
  positivity

theorem scale_small (N : ℕ) : scale A N ≤ (1/4096 : ℝ) := by
  have hd : 0 ≤ count A.K A.D (N+1) := by
    unfold count
    exact mul_nonneg A.K_nonneg (pow_nonneg (by linarith [A.D_ge_one]) _)
  change (1024 * (count A.K A.D (N+1) + 4))⁻¹ ≤ _
  have hp : 0 < 1024 * (count A.K A.D (N+1) + 4) := by positivity
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hp).mpr
  nlinarith

theorem scaled_address (N k : ℕ) (hk : (k:ℝ) ≤ count A.K A.D (N+1)) :
    scale A N * ((k:ℝ)+2) ≤ (1/1024 : ℝ) := by
  have hh : scale A N * (count A.K A.D (N+1)+4) = (1/1024:ℝ) := by
    unfold scale
    have hp : 0 < count A.K A.D (N+1)+4 := by
      have hd : 0 ≤ count A.K A.D (N+1) := by
        unfold count
        exact mul_nonneg A.K_nonneg (pow_nonneg (by linarith [A.D_ge_one]) _)
      linarith
    field_simp
  rw [← hh]
  exact mul_le_mul_of_nonneg_left (by linarith) (scale_pos A N).le

def origin : Coord 2 := ![1/4,1/2]

def targetHeight (N n : ℕ) (c : A.Instruction n) : ℝ :=
  if A.sign n c = 1 then -(7/16:ℝ) else -scale A N

def path (N n : ℕ) (c : A.Instruction n) (s : ℝ) : Coord 2 :=
  origin + center (n:ℝ) 1 (scale A N) (scale A N)
    (targetHeight A N n c / scale A N) (A.source n c) (A.target n c) s

@[fun_prop] theorem contDiff_path (N n : ℕ) (c : A.Instruction n) :
    ContDiff ℝ ∞ (path A N n c) := by unfold path; fun_prop

theorem path_source (N n : ℕ) (c : A.Instruction n) {s : ℝ} (hs : s ≤ n) :
    path A N n c s = origin + ![scale A N * A.source n c,-scale A N] := by
  unfold path
  rw [center_source_collar]
  norm_num only [div_one]
  linarith

theorem path_target (N n : ℕ) (c : A.Instruction n) {s : ℝ} (hs : n+1 ≤ s) :
    path A N n c s = origin + ![scale A N * A.target n c,targetHeight A N n c] := by
  unfold path
  rw [center_target_collar]
  · rw [div_mul_cancel₀ _ (ne_of_gt (scale_pos A N))]
  · norm_num only [div_one]
    linarith

theorem velocity_source (N n : ℕ) (c : A.Instruction n) {s : ℝ} (hs : s ≤ n) :
    deriv (path A N n c) s = 0 := by
  unfold path
  rw [deriv_const_add]
  · exact velocity_source_collar _ _ (by norm_num only [div_one]; linarith)

theorem velocity_target (N n : ℕ) (c : A.Instruction n) {s : ℝ} (hs : n+1 ≤ s) :
    deriv (path A N n c) s = 0 := by
  unfold path
  rw [deriv_const_add]
  · exact velocity_target_collar _ _ (by norm_num only [div_one]; linarith)

theorem theta_order (a T s : ℝ) : theta a T 2 s ≤ theta a T 0 s := by
  unfold theta ramp
  exact Real.smoothTransition.monotone (by norm_num only [Nat.cast_ofNat, Nat.cast_zero]; linarith)

theorem center_in_rectangle {S σ lo hi xmax : ℝ} {k l : ℕ}
    (hS0 : 0 ≤ S) (hk : S * k ≤ xmax) (hl : S * l ≤ xmax)
    (hrow : privateRow S k ∈ Icc lo hi) (hsource : -S ∈ Icc lo hi)
    (htarget : σ*S ∈ Icc lo hi) (a T s : ℝ) :
    (center a T S S σ k l s 0 ∈ Icc (0:ℝ) xmax) ∧
    (center a T S S σ k l s 1 ∈ Icc lo hi) := by
  have ht (j : ℕ) : theta a T j s ∈ Icc (0:ℝ) 1 :=
    ⟨ramp_nonneg _, ramp_le_one _⟩
  have hm := theta_order a T s
  constructor
  · change 0 ≤ (1-theta a T 1 s)*S*k+theta a T 1 s*S*l ∧
      (1-theta a T 1 s)*S*k+theta a T 1 s*S*l ≤ xmax
    have hp : 0 ≤ 1 - theta a T 1 s := by linarith [(ht 1).2]
    constructor
    · exact add_nonneg (mul_nonneg (mul_nonneg hp hS0) (Nat.cast_nonneg _))
        (mul_nonneg (mul_nonneg (ht 1).1 hS0) (Nat.cast_nonneg _))
    · have h₁ := mul_le_mul_of_nonneg_left hk hp
      have h₂ := mul_le_mul_of_nonneg_left hl (ht 1).1
      nlinarith
  · change lo ≤ -(1-theta a T 0 s)*S+
        (theta a T 0 s-theta a T 2 s)*privateRow S k+theta a T 2 s*σ*S ∧
      -(1-theta a T 0 s)*S+
        (theta a T 0 s-theta a T 2 s)*privateRow S k+theta a T 2 s*σ*S ≤ hi
    have hp : 0 ≤ 1-theta a T 0 s := by linarith [(ht 0).2]
    have hq : 0 ≤ theta a T 0 s-theta a T 2 s := sub_nonneg.mpr hm
    have h₁ := mul_le_mul_of_nonneg_left hsource.1 hp
    have h₂ := mul_le_mul_of_nonneg_left hrow.1 hq
    have h₃ := mul_le_mul_of_nonneg_left htarget.1 (ht 2).1
    have h₄ := mul_le_mul_of_nonneg_left hsource.2 hp
    have h₅ := mul_le_mul_of_nonneg_left hrow.2 hq
    have h₆ := mul_le_mul_of_nonneg_left htarget.2 (ht 2).1
    constructor <;> nlinarith

theorem path_bounds (N n : ℕ) (c : A.Instruction n) (hn : n < N) (s : ℝ) :
    path A N n c s 0 ∈ Icc (1/4:ℝ) (1/4+1/1024) ∧
    path A N n c s 1 ∈ Icc (1/16:ℝ) (1/2) := by
  have hk := scaled_address A N (A.source n c)
    ((A.source_count n c).trans (count_mono A.K_nonneg A.D_ge_one (by omega)))
  have hl := scaled_address A N (A.target n c)
    ((A.target_count n c).trans (count_mono A.K_nonneg A.D_ge_one (by omega)))
  have hS := scale_pos A N
  have hsmall := scale_small A N
  have hheight : targetHeight A N n c ∈ Icc (-(7/16):ℝ) 0 := by
    unfold targetHeight
    split_ifs <;> constructor <;> linarith
  have hh := center_in_rectangle hS.le
    (show scale A N * (A.source n c:ℝ) ≤ (1/1024:ℝ) by nlinarith)
    (show scale A N * (A.target n c:ℝ) ≤ (1/1024:ℝ) by nlinarith)
    (show privateRow (scale A N) (A.source n c) ∈ Icc (-(7/16):ℝ) 0 by
      dsimp [privateRow]; constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (A.source n c)])
    (show -scale A N ∈ Icc (-(7/16):ℝ) 0 by constructor <;> linarith)
    (show targetHeight A N n c / scale A N * scale A N ∈ Icc (-(7/16):ℝ) 0 by
      rwa [div_mul_cancel₀ _ (ne_of_gt hS)]) (n:ℝ) 1 s
  change 1/4+center _ _ _ _ _ _ _ s 0 ∈ Icc _ _ ∧
    1/2+center _ _ _ _ _ _ _ s 1 ∈ Icc _ _
  exact ⟨⟨by linarith [hh.1.1],by linarith [hh.1.2]⟩,
    ⟨by linarith [hh.2.1],by linarith [hh.2.2]⟩⟩

theorem nonterminal_bounds (N n : ℕ) (c : A.Instruction n) (hn : n < N)
    (hc : A.sign n c = -1) (s : ℝ) :
    (1/2-1/1024:ℝ) ≤ path A N n c s 1 := by
  have hk := scaled_address A N (A.source n c)
    ((A.source_count n c).trans (count_mono A.K_nonneg A.D_ge_one (by omega)))
  have hl := scaled_address A N (A.target n c)
    ((A.target_count n c).trans (count_mono A.K_nonneg A.D_ge_one (by omega)))
  have hS := scale_pos A N
  have hsmall := scale_small A N
  have he : targetHeight A N n c = -scale A N := by norm_num [targetHeight,hc]
  have hh := center_in_rectangle hS.le
    (show scale A N * (A.source n c:ℝ) ≤ (1/1024:ℝ) by nlinarith)
    (show scale A N * (A.target n c:ℝ) ≤ (1/1024:ℝ) by nlinarith)
    (show privateRow (scale A N) (A.source n c) ∈ Icc (-(1/1024):ℝ) 0 by
      dsimp [privateRow]; constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (A.source n c)])
    (show -scale A N ∈ Icc (-(1/1024):ℝ) 0 by constructor <;> linarith)
    (show targetHeight A N n c / scale A N * scale A N ∈ Icc (-(1/1024):ℝ) 0 by
      rw [div_mul_cancel₀ _ (ne_of_gt hS),he]; constructor <;> linarith) (n:ℝ) 1 s
  change _ ≤ 1/2+center _ _ _ _ _ _ _ s 1
  linarith [hh.2.1]

def radius (N : ℕ) : ℝ := scale A N / 16

theorem radius_pos (N : ℕ) : 0 < radius A N := div_pos (scale_pos A N) (by norm_num)

def stage (N n : ℕ) : VectorField 2 := fun s X =>
  ∑ c : A.Instruction n, TranslationGates.field (radius A N)
    (path A N n c s) (deriv (path A N n c) s) X

@[fun_prop] theorem contDiff_stage (N n : ℕ) : ContDiff ℝ ∞ (uncurry (stage A N n)) := by
  unfold stage
  apply ContDiff.sum
  intro c _
  exact TranslationGates.contDiff_movingField _ (contDiff_path A N n c)
    ((contDiff_infty_iff_deriv.mp (contDiff_path A N n c)).2)

theorem stage_zero_before (N n : ℕ) {s : ℝ} (hs : s ≤ n) (X : Coord 2) :
    stage A N n s X = 0 := by
  unfold stage
  apply Finset.sum_eq_zero
  intro c _
  rw [velocity_source A N n c hs,TranslationGates.field_zero_velocity]

theorem stage_zero_after (N n : ℕ) {s : ℝ} (hs : n+1 ≤ s) (X : Coord 2) :
    stage A N n s X = 0 := by
  unfold stage
  apply Finset.sum_eq_zero
  intro c _
  rw [velocity_target A N n c hs,TranslationGates.field_zero_velocity]

theorem stage_divergence (N n : ℕ) (s : ℝ) (X : Coord 2) :
    divergence (stage A N n) s X = 0 := by
  unfold stage
  rw [divergence_sum]
  · apply Finset.sum_eq_zero
    intro c _
    exact TranslationGates.divergence_field (radius A N) (path A N n c s)
      (deriv (path A N n c) s) X
  · intro c _ s
    exact TranslationGates.contDiff_field (radius A N) (path A N n c s)
      (deriv (path A N n c) s)

theorem paths_separated (N n : ℕ) (c d : A.Instruction n) (hcd : c ≠ d) (s : ℝ) :
    ∃ i : Fin 2, 16*radius A N ≤ |path A N n c s i - path A N n d s i| := by
  obtain ⟨i,hi⟩ := CenterPaths.separated (scale_pos A N).le le_rfl (n:ℝ) 1
    (targetHeight A N n c / scale A N) (targetHeight A N n d / scale A N) s
    ((A.source_injective n).ne hcd) ((A.target_injective n).ne hcd)
  refine ⟨i,?_⟩
  simpa only [path,Pi.add_apply,add_sub_add_left_eq_sub,radius,mul_div_cancel₀ _ (by norm_num : (16:ℝ) ≠ 0)] using hi

theorem stage_plateau (N n : ℕ) (c : A.Instruction n) (s : ℝ) (X : Coord 2)
    (hX : ∀ i, |X i - path A N n c s i| ≤ radius A N) :
    stage A N n s X = deriv (path A N n c) s := by
  exact TranslationGates.array_plateau (radius_pos A N)
    (fun c => path A N n c s) (fun c => deriv (path A N n c) s)
    (fun c _ d _ h => paths_separated A N n c d h s) (Finset.mem_univ c) X hX

end VelocityDetection.ChartRouting
end

noncomputable section
namespace VelocityDetection.ChartRouting
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open Expanding CenterPaths SpatialCalculus Periodization
variable (A : RoutingData)

def chartSet : Set (Coord 2) := Icc ![1/8,1/32] ![3/8,3/4]

theorem compact_chartSet : IsCompact chartSet := isCompact_Icc

theorem chartSet_interior {X : Coord 2} (hX : X ∈ chartSet) :
    ∀ i, X i ∈ Ioo (0:ℝ) 1 := by
  intro i
  fin_cases i
  · have h₁ := hX.1 (0 : Fin 2)
    have h₂ := hX.2 (0 : Fin 2)
    norm_num only [Matrix.cons_val_zero] at h₁ h₂
    change 0 < X 0 ∧ X 0 < 1
    constructor <;> linarith
  · have h₁ := hX.1 (1 : Fin 2)
    have h₂ := hX.2 (1 : Fin 2)
    norm_num only [Matrix.cons_val_one, Matrix.cons_val_zero] at h₁ h₂
    change 0 < X 1 ∧ X 1 < 1
    constructor <;> linarith

theorem path_neighborhood (N n : ℕ) (c : A.Instruction n) (hn : n < N)
    (s : ℝ) (X : Coord 2) (hX : ∀ i, |X i-path A N n c s i| ≤ 3*radius A N) :
    X ∈ chartSet := by
  have hb := path_bounds A N n c hn s
  have hR : 3*radius A N ≤ (3/65536:ℝ) := by
    unfold radius
    linarith [scale_small A N]
  have hx := abs_le.mp (hX 0)
  have hy := abs_le.mp (hX 1)
  constructor <;> intro i <;> fin_cases i
  · change (1/8:ℝ) ≤ X 0
    linarith [hb.1.1]
  · change (1/32:ℝ) ≤ X 1
    linarith [hb.2.1]
  · change X 0 ≤ (3/8:ℝ)
    linarith [hb.1.2]
  · change X 1 ≤ (3/4:ℝ)
    linarith [hb.2.2]

theorem stage_support (N n : ℕ) (hn : n < N) (s : ℝ) (X : Coord 2)
    (hX : stage A N n s X ≠ 0) : X ∈ chartSet := by
  unfold stage at hX
  obtain ⟨c,_,hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hX
  apply path_neighborhood A N n c hn s X
  intro i
  apply le_of_lt
  by_contra hi
  exact hc (TranslationGates.field_zero_outside (radius_pos A N) _ _ _ ⟨i,not_lt.mp hi⟩)

def finiteField (N : ℕ) : VectorField 2 := fun s X => ∑ n ∈ Finset.range N, stage A N n s X

@[fun_prop] theorem contDiff_prefix (N : ℕ) : ContDiff ℝ ∞ (uncurry (finiteField A N)) := by
  unfold finiteField
  exact ContDiff.sum (fun n _ => contDiff_stage A N n)

theorem prefix_divergence (N : ℕ) (s : ℝ) (X : Coord 2) :
    divergence (finiteField A N) s X = 0 := by
  unfold finiteField
  rw [divergence_sum]
  · apply Finset.sum_eq_zero
    intro n _
    exact stage_divergence A N n s X
  · intro n _ t
    exact contDiff_slice (contDiff_stage A N n) t

theorem prefix_support (N : ℕ) (s : ℝ) (X : Coord 2) (hX : finiteField A N s X ≠ 0) :
    X ∈ chartSet := by
  unfold finiteField at hX
  obtain ⟨n,hn,h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hX
  exact stage_support A N n (Finset.mem_range.mp hn) s X h

theorem prefix_zero_before (N : ℕ) {s : ℝ} (hs : s ≤ 0) (X : Coord 2) :
    finiteField A N s X = 0 := by
  unfold finiteField
  apply Finset.sum_eq_zero
  intro n _
  exact stage_zero_before A N n (hs.trans (Nat.cast_nonneg _)) X

theorem prefix_zero_after (N : ℕ) {s : ℝ} (hs : N ≤ s) (X : Coord 2) :
    finiteField A N s X = 0 := by
  unfold finiteField
  apply Finset.sum_eq_zero
  intro n hn
  apply stage_zero_after A N n _ X
  have h : (n:ℝ)+1 ≤ N := by exact_mod_cast Finset.mem_range.mp hn
  exact h.trans hs

theorem prefix_eq_stage (N n : ℕ) (hn : n < N) {s : ℝ} (hs : s ∈ Icc (n:ℝ) (n+1))
    (X : Coord 2) : finiteField A N s X = stage A N n s X := by
  unfold finiteField
  apply Finset.sum_eq_single n
  · intro k _ hkn
    rcases lt_or_gt_of_ne hkn with h | h
    · apply stage_zero_after A N k _ X
      have hh : (k:ℝ)+1 ≤ n := by exact_mod_cast h
      exact hh.trans hs.1
    · apply stage_zero_before A N k _ X
      have hh : (n:ℝ)+1 ≤ k := by exact_mod_cast h
      exact hs.2.trans hh
  · exact fun h => (h (Finset.mem_range.mpr hn)).elim

theorem compactSupport_prefix (N : ℕ) : HasCompactSupport (uncurry (finiteField A N)) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod compact_chartSet)
  intro q hq
  refine ⟨⟨?_,?_⟩,prefix_support A N q.1 q.2 hq⟩
  · exact (lt_of_not_ge (fun h => hq (prefix_zero_before A N h q.2))).le
  · exact (lt_of_not_ge (fun h => hq (prefix_zero_after A N h q.2))).le

def periodicPrefix (N : ℕ) : VectorField 2 := Periodization.extend (finiteField A N)

@[fun_prop] theorem contDiff_periodicPrefix (N : ℕ) :
    ContDiff ℝ ∞ (uncurry (periodicPrefix A N)) := by
  apply contDiff_extend (C := 1) (contDiff_prefix A N)
  intro s X hX i
  have hi := chartSet_interior (prefix_support A N s X hX) i
  rw [abs_of_pos hi.1]
  exact hi.2.le

theorem periodic_periodicPrefix (N : ℕ) (s : ℝ) :
    FactorsThrough (periodicPrefix A N s) PeriodicSpace.cover := periodic_extend _ _

theorem periodicPrefix_chart (N : ℕ) (s : ℝ) {X : Coord 2}
    (hX : ∀ i, X i ∈ Icc (0:ℝ) 1) : periodicPrefix A N s X = finiteField A N s X := by
  apply extend_eq_chart _ s hX
  intro t Y hY
  exact chartSet_interior (prefix_support A N t Y hY)

theorem periodicPrefix_plateau (N n : ℕ) (c : A.Instruction n) (hn : n < N)
    {s : ℝ} (hs : s ∈ Icc (n:ℝ) (n+1)) (X : Coord 2)
    (hX : ∀ i, |X i - path A N n c s i| ≤ radius A N) :
    periodicPrefix A N s X = deriv (path A N n c) s := by
  have hK := path_neighborhood A N n c hn s X
    (fun i => (hX i).trans (by linarith [radius_pos A N]))
  rw [periodicPrefix_chart A N s (fun i => ⟨(chartSet_interior hK i).1.le,
    (chartSet_interior hK i).2.le⟩),prefix_eq_stage A N n hn hs X]
  exact stage_plateau A N n c s X hX

end VelocityDetection.ChartRouting
end

end OAI
