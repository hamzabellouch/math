import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.BurstTotal
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.BurstBlockRawReferenceLaplacian

namespace OAI

noncomputable section
namespace VelocityDetection.BurstTotal
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open ChartRouting BurstSchedule Periodization SpatialCalculus
variable (A : RoutingData) (ν : ℝ) (tr : RoutingArray.Trace A)

def referenceSum (L : ℕ) : ScalarField 2 := fun t X =>
  ∑ k ∈ Finset.range L, BurstBlock.reference A ν tr k t X

def barrierSum (L : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range L, barrier A ν k t

theorem reference_rest (hν : 0 ≤ ν) (k : ℕ) {t : ℝ} (ht : t ≤ 1) :
    BurstBlock.reference A ν tr k t = 0 :=
  BurstBlock.reference_zero A ν tr k
    (Or.inl (localTime_before A ν hν k (ht.trans (by linarith [Nat.cast_nonneg (α := ℝ) k]))))

theorem reference_transport (hν : 0 ≤ ν) (k : ℕ)
    (h : ∀ n < k+1, tr.stopped n = false) (t : ℝ) (X : Coord 2) :
    deriv (fun s => BurstBlock.reference A ν tr k s X) t +
      advection (field A ν) (BurstBlock.reference A ν tr k) t X =
        BurstBlock.source A ν (tr.address 0) k t X := by
  have ha : advection (field A ν) (BurstBlock.reference A ν tr k) t X =
      advection (BurstBlock.field A ν k) (BurstBlock.reference A ν tr k) t X := by
    by_cases ht : t ∈ Icc ((k:ℝ)+1) ((k:ℝ)+2)
    · simp only [advection,congrFun (field_at_block A ν hν k ht) X]
    · have hz : BurstBlock.reference A ν tr k t = 0 := by
        apply BurstBlock.reference_zero A ν tr k
        rcases lt_or_ge t ((k:ℝ)+1) with hlt | hge
        · exact Or.inl (localTime_before A ν hν k hlt.le)
        · exact Or.inr (localTime_after A ν hν k (le_of_lt (lt_of_not_ge (fun hle => ht ⟨hge,hle⟩))))
      rw [congrFun (TimeBlocks.advection_zero (field A ν) hz) X,
        congrFun (TimeBlocks.advection_zero (BurstBlock.field A ν k) hz) X]
  rw [ha]
  exact BurstBlock.reference_transport A ν tr k h t X

@[fun_prop] theorem contDiff_referenceSum (L : ℕ)
    (h : ∀ n < L, tr.stopped n = false) :
    ContDiff ℝ ∞ (uncurry (referenceSum A ν tr L)) :=
  ContDiff.sum (fun k hk => BurstBlock.contDiff_reference A ν tr k
    (fun n hn => h n (lt_of_lt_of_le hn (Finset.mem_range.mp hk))))

theorem referenceSum_periodic (L : ℕ) (t : ℝ) :
    FactorsThrough (referenceSum A ν tr L t) PeriodicSpace.cover := by
  intro X Y hXY
  exact Finset.sum_congr rfl (fun k _ => BurstBlock.reference_periodic A ν tr k t hXY)

theorem referenceSum_transport (hν : 0 ≤ ν) (L : ℕ)
    (h : ∀ n < L, tr.stopped n = false) {t : ℝ} (ht : t ≤ (L:ℝ)+1) (X : Coord 2) :
    deriv (fun s => referenceSum A ν tr L s X) t +
      advection (field A ν) (referenceSum A ν tr L) t X = source A ν (tr.address 0) t X := by
  have hsm (k : ℕ) (hk : k ∈ Finset.range L) := BurstBlock.contDiff_reference A ν tr k
    (fun n hn => h n (lt_of_lt_of_le hn (Finset.mem_range.mp hk)))
  change deriv (fun s => ∑ k ∈ Finset.range L, BurstBlock.reference A ν tr k s X) t +
    advection (field A ν) (fun s Y => ∑ k ∈ Finset.range L, BurstBlock.reference A ν tr k s Y) t X = _
  have hd (k : ℕ) (hk : k ∈ Finset.range L) :
      DifferentiableAt ℝ (fun s => BurstBlock.reference A ν tr k s X) t :=
    ((hsm k hk).comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t
  rw [deriv_fun_sum hd,
    TimeBlocks.advection_sum (field A ν) (Finset.range L) (BurstBlock.reference A ν tr)
      (fun k hk s => ((hsm k hk).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)),
    ← Finset.sum_add_distrib]
  have he : source A ν (tr.address 0) t X =
      ∑ k ∈ Finset.range L, BurstBlock.source A ν (tr.address 0) k t X :=
    congrFun (TimeBlocks.eq_finite (sourceFamily A ν hν (tr.address 0)) ht) X
  rw [he]
  exact Finset.sum_congr rfl (fun k hk => reference_transport A ν tr hν k
    (fun n hn => h n (lt_of_lt_of_le hn (Finset.mem_range.mp hk))) t X)

@[fun_prop] theorem contDiff_barrierSum (L : ℕ) : ContDiff ℝ 2 (barrierSum A ν L) :=
  ContDiff.sum (fun k _ => contDiff_barrier A ν k)

theorem deriv_barrierSum (L : ℕ) (t : ℝ) : deriv (barrierSum A ν L) t =
    ∑ k ∈ Finset.range L, deriv (barrier A ν k) t :=
  deriv_fun_sum (fun k _ => (contDiff_barrier A ν k).differentiable (by norm_num) t)

theorem barrierSum_bounds (L : ℕ) (t : ℝ) : barrierSum A ν L t ∈ Icc (0:ℝ) (1/8) :=
  ⟨Finset.sum_nonneg (fun k _ => (barrier_bounds A ν k t).1),
    (Finset.sum_le_sum (fun k _ => (barrier_bounds A ν k t).2)).trans (error_sum_le L)⟩

theorem referenceSum_laplacian (hν : 0 ≤ ν) (L : ℕ)
    (h : ∀ n < L, tr.stopped n = false) (t : ℝ) (X : Coord 2) :
    ν*|laplacian (referenceSum A ν tr L) t X| ≤ deriv (barrierSum A ν L) t := by
  change ν*|laplacian (fun s Y => ∑ k ∈ Finset.range L, BurstBlock.reference A ν tr k s Y) t X| ≤ _
  rw [TimeBlocks.laplacian_sum (Finset.range L) (BurstBlock.reference A ν tr)
    (fun k hk => BurstBlock.contDiff_reference A ν tr k
      (fun n hn => h n (lt_of_lt_of_le hn (Finset.mem_range.mp hk)))),deriv_barrierSum]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hν).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun k hk => BurstBlock.reference_laplacian_barrier A ν tr hν k
    (fun n hn => h n (lt_of_lt_of_le hn (Finset.mem_range.mp hk))) t X)

theorem scalar_prefix_error (hν : 0 < ν) (L : ℕ)
    (h : ∀ n < L, tr.stopped n = false) {t : ℝ} (ht : t ∈ Icc (0:ℝ) ((L:ℝ)+1))
    (X : Coord 2) : |scalar A ν hν (tr.address 0) t X-referenceSum A ν tr L t X| ≤ 1/8 := by
  have hzero : referenceSum A ν tr L 0 X = 0 := by
    exact Finset.sum_eq_zero (fun k _ => congrFun (reference_rest A ν tr hν.le k (by norm_num)) X)
  have hh := PeriodicComparison.diffusion_error (g := source A ν (tr.address 0))
    hν.le (by positivity : (0:ℝ) ≤ (L:ℝ)+1)
    ((contDiff_scalar A ν hν (tr.address 0)).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    ((contDiff_referenceSum A ν tr L h).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    (scalar_periodic A ν hν (tr.address 0)) (referenceSum_periodic A ν tr L)
    (contDiff_barrierSum A ν L)
    (fun _ hs Y => scalar_residual A ν hν (tr.address 0) hs.1 Y)
    (fun _ hs Y => referenceSum_transport A ν tr hν.le L h hs.2 Y)
    (fun s _ Y => referenceSum_laplacian A ν tr hν.le L h s Y)
    (fun Y => by
      rw [scalar_initial,show referenceSum A ν tr L 0 Y = 0 from
        Finset.sum_eq_zero (fun k _ => congrFun (reference_rest A ν tr hν.le k (by norm_num)) Y),
        sub_self,abs_zero]
      exact (barrierSum_bounds A ν L 0).1)
  exact (hh t ht X).trans (barrierSum_bounds A ν L t).2

def velocity (hν : 0 < ν) (q : ℕ) : VectorField 3 :=
  liftVelocity (field A ν) (scalar A ν hν q)

theorem strip_representative (X : Coord 2) (hY : X 1 ∈ Icc (0:ℝ) 1) :
    ∃ Y : Coord 2, (∀ i, Y i ∈ Icc (0:ℝ) 1) ∧ Y 1 = X 1 ∧
      PeriodicSpace.cover X = PeriodicSpace.cover Y := by
  let Y : Coord 2 := ![Int.fract (X 0),X 1]
  refine ⟨Y,?_,rfl,?_⟩
  · intro i
    fin_cases i
    · exact ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
    · exact hY
  · apply cover_eq_iff.mpr
    refine ⟨![Int.floor (X 0),0],?_⟩
    ext i
    fin_cases i
    · change X 0 = Int.fract (X 0)+(Int.floor (X 0):ℝ)
      exact (sub_add_cancel _ _).symm
    · change X 1 = X 1+(0:ℤ)
      simp

theorem nonterminal_small (hν : 0 < ν) (hnever : ¬ tr.Stops)
    {t : ℝ} (ht : 0 ≤ t) (X : Coord 2) (hY : X 1 ∈ Ioo (1/32:ℝ) (1/8)) :
    scalar A ν hν (tr.address 0) t X ≤ 1/8 := by
  have hactive (n : ℕ) : tr.stopped n = false := by
    cases h : tr.stopped n
    · rfl
    · exact False.elim (hnever ⟨n,h⟩)
  obtain ⟨Y,hYcube,hYY,hXY⟩ := strip_representative X ⟨by linarith [hY.1],by linarith [hY.2]⟩
  rw [scalar_periodic A ν hν (tr.address 0) t hXY]
  obtain ⟨L,hL⟩ := exists_nat_gt t
  have he := scalar_prefix_error A ν tr hν L (fun n _ => hactive n) ⟨ht,by linarith⟩ Y
  have hz : referenceSum A ν tr L t Y = 0 := by
    exact Finset.sum_eq_zero (fun k _ => BurstBlock.reference_zero_detector A ν tr k
      (fun n _ => hactive n) t hYcube (by rw [hYY]; exact hY.2))
  rw [hz,sub_zero] at he
  exact (le_abs_self _).trans he

theorem terminal_large (hν : 0 < ν) (hinit : tr.stopped 0 = false)
    (hreach : tr.Stops) :
    ∃ t : ℝ, 0 ≤ t ∧ ∃ X : Coord 2, X 1 ∈ Ioo (1/32:ℝ) (1/8) ∧
      (3/4:ℝ) < scalar A ν hν (tr.address 0) t X := by
  let hex : ∃ n, tr.stopped n = true := hreach
  have hzero : Nat.find hex ≠ 0 := by
    intro hz
    have h := Nat.find_spec hex
    rw [hz,hinit] at h
    cases h
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hzero
  have hfirst : tr.stopped (k+1) = true := by simpa only [hk] using Nat.find_spec hex
  have hactive (n : ℕ) (hn : n < k+1) : tr.stopped n = false :=
    Bool.eq_false_iff.mpr (Nat.find_min hex (by omega))
  let t : ℝ := (k:ℝ)+1+duration A ν k/2
  have hdur := duration_pos A ν hν.le k
  have hdurs := duration_small A ν hν.le k
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htt : t ∈ Icc ((k:ℝ)+1) ((k:ℝ)+2) := by dsimp [t]; constructor <;> linarith
  have hlocal : localTime A ν k t = 1/2 := by
    unfold localTime
    dsimp [t]
    field_simp
    ring
  have hclock : clock A ν k t = k+1 := by
    change phase (k+1) (localTime A ν k t) = _
    rw [hlocal,phase_middle (k+1) (by norm_num : (1/2:ℝ) ∈ Icc (1/4:ℝ) (5/8))]
    push_cast
    rfl
  have hweight : weight A ν k t = 1 := by
    change amplitude (localTime A ν k t) = _
    rw [hlocal]
    exact amplitude_middle (by norm_num)
  let X := BurstBlock.center A ν tr k t
  have hX : X 1 = 1/16 := by
    change ChartTrace.route A tr (k+1) (clock A ν k t) 1 = _
    rw [hclock,ChartTrace.route_after A tr (k+1) (by simp)]
    simp [ChartTrace.vertex,ChartTrace.height,hfirst,origin]
    norm_num
  refine ⟨t,ht,X,by rw [hX]; norm_num,?_⟩
  have he := scalar_prefix_error A ν tr hν (k+1) hactive
    (t := t) ⟨ht,by push_cast; linarith [htt.2]⟩ X
  have href : referenceSum A ν tr (k+1) t X = 1 := by
    change (∑ j ∈ Finset.range (k+1), BurstBlock.reference A ν tr j t X) = _
    rw [Finset.sum_eq_single k]
    · exact (BurstBlock.reference_center A ν tr k hactive t).trans hweight
    · intro j hj hjk
      have hh : (j:ℝ)+2 ≤ t := by
        have hle : (j:ℝ)+1 ≤ k := by exact_mod_cast (show j < k by have := Finset.mem_range.mp hj; omega)
        linarith [htt.1]
      exact congrFun (BurstBlock.reference_zero A ν tr j
        (Or.inr (localTime_after A ν hν.le j hh))) X
    · exact fun h => (h (Finset.mem_range.mpr (Nat.lt_succ_self _))).elim
  rw [href] at he
  linarith [(abs_le.mp he).1]

theorem detection (hν : 0 < ν) (hinit : tr.stopped 0 = false) :
    Observation.torusEvent (velocity A ν hν (tr.address 0)) ↔ tr.Stops := by
  constructor
  · rintro ⟨t,ht,x,hy₀,hy₁,hbig⟩
    by_contra hn
    have hsmall := nonterminal_small A ν tr hν hn ht (horizontal x) ⟨hy₀,hy₁⟩
    change (1/2:ℝ) < scalar A ν hν (tr.address 0) t (horizontal x) at hbig
    linarith
  · intro h
    obtain ⟨t,ht,X,hX,hbig⟩ := terminal_large A ν tr hν hinit h
    refine ⟨t,ht,Observation.join X 0,hX.1,hX.2,?_⟩
    change (1/2:ℝ) < scalar A ν hν (tr.address 0) t (horizontal (Observation.join X 0))
    rw [Observation.horizontal_join]
    linarith

end VelocityDetection.BurstTotal
end

end OAI
