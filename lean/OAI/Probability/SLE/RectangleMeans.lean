import Mathlib
import OAI.Probability.SLE.StripKernels

namespace OAI

/-! Rectangle Means for chordal SLE. -/

section
section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal BigOperators NNReal
namespace SLEExactGauge
noncomputable def cellOrigin (k : ℕ) (i : Fin (2^k)) : ℝ := (i:ℝ)*scaleLength k
noncomputable def dyadicCell (k : ℕ) (p : Fin (2^k) × Fin (2^k)) : Set ℂ :=
  stripRectangle (cellOrigin k p.1) (Real.pi*cellOrigin k p.2) (scaleLength k)
noncomputable def dyadicInterior (k : ℕ) (p : Fin (2^k) × Fin (2^k)) : Set ℂ :=
  openStripRectangle (cellOrigin k p.1) (Real.pi*cellOrigin k p.2) (scaleLength k)

lemma dyadicCell_eq (k : ℕ) (p : Fin (2^k) × Fin (2^k)) :
    dyadicCell k p = dyadicStripRectangle 0 k p.1 p.2 := by
  simp [dyadicCell, dyadicStripRectangle, cellOrigin, scaleLength, div_eq_mul_inv]
lemma cellOrigin_nonneg (k : ℕ) (i : Fin (2^k)) : 0 ≤ cellOrigin k i := by
  exact mul_nonneg (Nat.cast_nonneg _) (scaleLength_pos k).le
lemma cellOrigin_right (k : ℕ) (i : Fin (2^k)) : cellOrigin k i + scaleLength k ≤ 1 := by
  have hh : (i:ℝ)+1 ≤ (2:ℝ)^k := by exact_mod_cast i.isLt
  dsimp [cellOrigin, scaleLength]
  calc
    _ = ((i:ℝ)+1)/(2:ℝ)^k := by ring
    _ ≤ 1 := (div_le_one (by positivity)).2 hh
lemma dyadicInterior_subset_unit (k : ℕ) (p : Fin (2^k) × Fin (2^k)) :
    dyadicInterior k p ⊆ openUnitStrip := by
  intro z hz
  have hr := cellOrigin_right k p.1
  have hi := mul_le_mul_of_nonneg_left (cellOrigin_right k p.2) Real.pi_pos.le
  have h0 := cellOrigin_nonneg k p.1
  have h0' := mul_nonneg Real.pi_pos.le (cellOrigin_nonneg k p.2)
  change _ < z.re ∧ z.re < _ ∧ _ < z.im ∧ z.im < _ at hz
  exact ⟨h0.trans_lt hz.1, hz.2.1.trans_le hr,
    h0'.trans_lt hz.2.2.1, by nlinarith [hz.2.2.2]⟩
lemma dyadicCell_subset_root (k : ℕ) (p : Fin (2^k) × Fin (2^k)) :
    dyadicCell k p ⊆ stripRectangle 0 0 1 := by
  intro z hz
  have hr := cellOrigin_right k p.1
  have hi := mul_le_mul_of_nonneg_left (cellOrigin_right k p.2) Real.pi_pos.le
  have h0 := cellOrigin_nonneg k p.1
  have h0' := mul_nonneg Real.pi_pos.le (cellOrigin_nonneg k p.2)
  change _ ≤ z.re ∧ z.re ≤ _ ∧ _ ≤ z.im ∧ z.im ≤ _ at hz
  change 0 ≤ z.re ∧ z.re ≤ 0+1 ∧ 0 ≤ z.im ∧ z.im ≤ 0+Real.pi*1
  exact ⟨h0.trans hz.1, by linarith [hz.2.1],
    h0'.trans hz.2.2.1, by nlinarith [hz.2.2.2]⟩

lemma cellOrigin_separated {k : ℕ} {i j : Fin (2^k)} (hij : i < j) :
    cellOrigin k i + scaleLength k ≤ cellOrigin k j := by
  have hh : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast hij
  have hm := mul_le_mul_of_nonneg_right hh (scaleLength_pos k).le
  dsimp [cellOrigin]
  nlinarith

lemma dyadicInterior_disjoint (k : ℕ) : Pairwise (fun p q => Disjoint (dyadicInterior k p) (dyadicInterior k q)) := by
  intro p q hpq
  rw [Set.disjoint_left]
  intro z hz hz'
  change _ < z.re ∧ z.re < _ ∧ _ < z.im ∧ z.im < _ at hz hz'
  by_cases h : p.1 = q.1
  · have hne : p.2 ≠ q.2 := by intro h'; exact hpq (Prod.ext h h')
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hh := mul_le_mul_of_nonneg_left (cellOrigin_separated hlt) Real.pi_pos.le
      nlinarith [hz.2.2.2, hz'.2.2.1]
    · have hh := mul_le_mul_of_nonneg_left (cellOrigin_separated hlt) Real.pi_pos.le
      nlinarith [hz'.2.2.2, hz.2.2.1]
  · rcases lt_or_gt_of_ne h with hlt | hlt
    · have hh := cellOrigin_separated hlt
      linarith [hz.2.1, hz'.1]
    · have hh := cellOrigin_separated hlt
      linarith [hz'.2.1, hz.1]

def leftChild (k : ℕ) (i : Fin (2^k)) : Fin (2^(k+1)) :=
  ⟨2*i.val, by have := i.isLt; rw [pow_succ]; omega⟩
def rightChild (k : ℕ) (i : Fin (2^k)) : Fin (2^(k+1)) :=
  ⟨2*i.val+1, by have := i.isLt; rw [pow_succ]; omega⟩
lemma cellOrigin_leftChild (k : ℕ) (i : Fin (2^k)) :
    cellOrigin (k+1) (leftChild k i) = cellOrigin k i := by
  simp only [cellOrigin, leftChild, Fin.val_mk, Nat.cast_mul, Nat.cast_ofNat, scaleLength_succ]
  ring
lemma cellOrigin_rightChild (k : ℕ) (i : Fin (2^k)) :
    cellOrigin (k+1) (rightChild k i) = cellOrigin k i + scaleLength k/2 := by
  simp only [cellOrigin, rightChild, Fin.val_mk, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one, scaleLength_succ]
  ring

noncomputable def branchIndex (x : ℝ) : (k : ℕ) → Fin (2^k)
  | 0 => 0
  | k+1 => if x ≤ cellOrigin k (branchIndex x k)+scaleLength k/2 then
      leftChild k (branchIndex x k) else rightChild k (branchIndex x k)

lemma branchIndex_step (x : ℝ) (k : ℕ) :
    cellOrigin k (branchIndex x k) ≤ cellOrigin (k+1) (branchIndex x (k+1)) ∧
    cellOrigin (k+1) (branchIndex x (k+1))+scaleLength k/2 ≤
      cellOrigin k (branchIndex x k)+scaleLength k := by
  rw [branchIndex]
  split
  · rw [cellOrigin_leftChild]
    constructor
    · rfl
    · linarith [scaleLength_pos k]
  · rw [cellOrigin_rightChild]
    constructor <;> linarith [scaleLength_pos k]

lemma branchIndex_contains {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    cellOrigin k (branchIndex x k) ≤ x ∧
    x ≤ cellOrigin k (branchIndex x k)+scaleLength k := by
  induction k with
  | zero => simpa [branchIndex, cellOrigin, scaleLength] using And.intro hx hx1
  | succ k ih =>
    rw [branchIndex]
    split_ifs with h
    · rw [cellOrigin_leftChild, scaleLength_succ]
      exact ⟨ih.1,h⟩
    · rw [cellOrigin_rightChild, scaleLength_succ]
      exact ⟨(not_le.mp h).le, by linarith [ih.2]⟩

noncomputable def pointBranch (z : ℂ) (k : ℕ) : Fin (2^k) × Fin (2^k) :=
  (branchIndex z.re k, branchIndex (z.im/Real.pi) k)
lemma pointBranch_contains {z : ℂ} (hz : z ∈ stripRectangle 0 0 1) (k : ℕ) :
    z ∈ dyadicCell k (pointBranch z k) := by
  have hzr : 0 ≤ z.re ∧ z.re ≤ 1 := by simpa [stripRectangle] using And.intro hz.1 hz.2.1
  have hzi : 0 ≤ z.im/Real.pi ∧ z.im/Real.pi ≤ 1 := by
    refine ⟨div_nonneg hz.2.2.1 Real.pi_pos.le, (div_le_one Real.pi_pos).2 ?_⟩
    simpa using hz.2.2.2
  have hr := branchIndex_contains hzr.1 hzr.2 k
  have hi := branchIndex_contains hzi.1 hzi.2 k
  have hi₁ := mul_le_mul_of_nonneg_left hi.1 Real.pi_pos.le
  have hi₂ := mul_le_mul_of_nonneg_left hi.2 Real.pi_pos.le
  rw [mul_div_cancel₀ _ Real.pi_ne_zero] at hi₁ hi₂
  change _ ≤ z.re ∧ z.re ≤ _ ∧ Real.pi*cellOrigin k (branchIndex (z.im/Real.pi) k) ≤ z.im ∧
    z.im ≤ Real.pi*cellOrigin k (branchIndex (z.im/Real.pi) k)+Real.pi*scaleLength k
  exact ⟨hr.1, hr.2, hi₁, by nlinarith⟩

lemma stripRectangle_convex (a b l : ℝ) : Convex ℝ (stripRectangle a b l) := by
  have he : stripRectangle a b l =
      Complex.reCLM ⁻¹' Icc a (a+l) ∩ Complex.imCLM ⁻¹' Icc b (b+Real.pi*l) := by
    ext z
    simp only [stripRectangle, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_Icc, Complex.reCLM_apply, Complex.imCLM_apply]
    tauto
  rw [he]
  exact ((convex_Icc a (a+l)).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Icc b (b+Real.pi*l)).linear_preimage Complex.imCLM.toLinearMap)

lemma stripRectangle_compact (a b l : ℝ) : IsCompact (stripRectangle a b l) := by
  rw [stripRectangle_eq_preimage]
  change IsCompact (Complex.equivRealProdCLM.toHomeomorph ⁻¹' _)
  exact Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr
    (isCompact_Icc.prod isCompact_Icc)

lemma stripRectangle_nonempty (a b l : ℝ) (hl : 0 ≤ l) : (stripRectangle a b l).Nonempty := by
  refine ⟨⟨a,b⟩, ?_⟩
  change a ≤ a ∧ a ≤ a+l ∧ b ≤ b ∧ b ≤ b+Real.pi*l
  exact ⟨le_rfl,le_add_of_nonneg_right hl,le_rfl,
    le_add_of_nonneg_right (mul_nonneg Real.pi_pos.le hl)⟩

lemma spatialAverage_eq_setAverage (u : ℂ → ℝ) (Q : Set ℂ) :
    spatialAverage u Q = ⨍ z in Q, u z := by
  rw [spatialAverage, setAverage_eq, Measure.real]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma stripRectangle_average_attained {u : ℂ → ℝ} {a b l : ℝ}
    (hu : ContinuousOn u (stripRectangle a b l)) (hl : 0 < l) :
    ∃ z ∈ stripRectangle a b l, u z = spatialAverage u (stripRectangle a b l) := by
  rw [spatialAverage_eq_setAverage]
  apply exists_eq_setAverage ((stripRectangle_convex a b l).isConnected
    (stripRectangle_nonempty a b l hl.le)) hu
    (hu.integrableOn_compact (stripRectangle_compact a b l))
    (stripRectangle_compact a b l).measure_lt_top.ne
  rw [stripRectangle_volume]
  exact mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hl)
    (ENNReal.ofReal_ne_zero_iff.mpr (mul_pos Real.pi_pos hl))

lemma dyadicCell_dist_le {k : ℕ} {p : Fin (2^k) × Fin (2^k)} {z w : ℂ}
    (hz : z ∈ dyadicCell k p) (hw : w ∈ dyadicCell k p) :
    dist z w ≤ 5*scaleLength k := by
  change _ ≤ z.re ∧ z.re ≤ _ ∧ _ ≤ z.im ∧ z.im ≤ _ at hz
  change _ ≤ w.re ∧ w.re ≤ _ ∧ _ ≤ w.im ∧ w.im ≤ _ at hw
  have hre : |z.re-w.re| ≤ scaleLength k := by rw [abs_le]; constructor <;> linarith
  have him : |z.im-w.im| ≤ Real.pi*scaleLength k := by rw [abs_le]; constructor <;> linarith
  rw [dist_eq_norm]
  have hn := Complex.norm_le_abs_re_add_abs_im (z-w)
  simp only [Complex.sub_re, Complex.sub_im] at hn
  nlinarith [scaleLength_pos k, Real.pi_lt_four]

lemma scaleLength_tendsto : Tendsto scaleLength atTop (𝓝 0) := by
  have hh := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1:ℝ)/2 < 1)
  change Tendsto (fun n => 1/(2:ℝ)^n) atTop (𝓝 0)
  simpa only [div_pow, one_pow] using hh

lemma branch_means_tendsto {u : ℂ → ℝ} (hu : ContinuousOn u (stripRectangle 0 0 1))
    {z : ℂ} (hz : z ∈ stripRectangle 0 0 1) :
    Tendsto (fun k => spatialAverage u (dyadicCell k (pointBranch z k))) atTop (𝓝 (u z)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, huδ⟩ := (Metric.continuousWithinAt_iff.1 (hu z hz)) ε hε
  have hs : ∀ᶠ k in atTop, 5*scaleLength k < δ :=
    ((scaleLength_tendsto.const_mul 5).eventually (eventually_lt_nhds (by simpa using hδ)))
  obtain ⟨N,hN⟩ := eventually_atTop.1 hs
  refine ⟨N,fun k hk => ?_⟩
  obtain ⟨w,hw,hew⟩ := stripRectangle_average_attained
    (hu.mono (dyadicCell_subset_root k (pointBranch z k))) (scaleLength_pos k)
  change u w = spatialAverage u (dyadicCell k (pointBranch z k)) at hew
  rw [← hew]
  apply huδ (dyadicCell_subset_root k (pointBranch z k) hw)
  exact (dyadicCell_dist_le hw (pointBranch_contains hz k)).trans_lt (hN k hk)

noncomputable def cellEnergy (D : ℂ → ℂ) (k : ℕ) (p : Fin (2^k) × Fin (2^k)) : ℝ :=
  ∫ z in dyadicInterior k p, ‖D z‖^2
lemma cellEnergy_nonneg (D : ℂ → ℂ) (k : ℕ) (p : Fin (2^k) × Fin (2^k)) :
    0 ≤ cellEnergy D k p := integral_nonneg (fun _ => sq_nonneg _)

lemma branch_mean_step_le {u : ℂ → ℝ} {D : ℂ → ℂ}
    (hu : SourceIsStripWeakGradient u D) (z : ℂ) (k : ℕ) :
    |spatialAverage u (dyadicCell (k+1) (pointBranch z (k+1))) -
      spatialAverage u (dyadicCell k (pointBranch z k))| ≤
      12*Real.sqrt (cellEnergy D k (pointBranch z k)) := by
  have hs₁ := branchIndex_step z.re k
  have hs₂ := branchIndex_step (z.im/Real.pi) k
  have hh := local_means_le hu
    (cellOrigin k (branchIndex z.re k)) (Real.pi*cellOrigin k (branchIndex (z.im/Real.pi) k))
    (scaleLength k) (scaleLength_pos k)
    (cellOrigin_nonneg ..) (cellOrigin_right ..)
    (mul_nonneg Real.pi_pos.le (cellOrigin_nonneg ..))
    (by nlinarith [cellOrigin_right k (branchIndex (z.im/Real.pi) k), Real.pi_pos])
    (cellOrigin (k+1) (branchIndex z.re (k+1)))
    (Real.pi*cellOrigin (k+1) (branchIndex (z.im/Real.pi) (k+1)))
    hs₁.1 hs₁.2 (mul_le_mul_of_nonneg_left hs₂.1 Real.pi_pos.le)
    (by have := mul_le_mul_of_nonneg_left hs₂.2 Real.pi_pos.le; nlinarith)
  simpa only [dyadicCell, pointBranch, cellEnergy, dyadicInterior, scaleLength_succ] using hh

lemma sum_cellEnergy_le {D : ℂ → ℂ} (hD : MemLp D 2 (volume.restrict openUnitStrip)) (k : ℕ) :
    ∑ p : Fin (2^k) × Fin (2^k), cellEnergy D k p ≤ stripDirichletEnergy D := by
  have hs : (⋃ p : Fin (2^k) × Fin (2^k), dyadicInterior k p) ⊆ openUnitStrip :=
    iUnion_subset (fun p => dyadicInterior_subset_unit k p)
  have hi : IntegrableOn (fun z => ‖D z‖^2) openUnitStrip volume := hD.norm.integrable_sq
  have he := integral_iUnion
    (fun p : Fin (2^k) × Fin (2^k) => openStripRectangle_measurable _ _ _)
    (dyadicInterior_disjoint k) (hi.mono_set hs)
  rw [tsum_fintype] at he
  change (∫ z in ⋃ p : Fin (2^k) × Fin (2^k), dyadicInterior k p, ‖D z‖^2) =
    ∑ p : Fin (2^k) × Fin (2^k), ∫ z in dyadicInterior k p, ‖D z‖^2 at he
  change (∑ p : Fin (2^k) × Fin (2^k), ∫ z in dyadicInterior k p, ‖D z‖^2) ≤ _
  rw [← he]
  exact setIntegral_mono_set hi (Eventually.of_forall (fun _ => sq_nonneg _))
    (Eventually.of_forall (fun z hz => hs hz))

lemma exists_large_increment {a : ℕ → ℝ} {H : ℝ} (hH : 0 < H)
    (ha : Tendsto a atTop (𝓝 H)) (ha0 : a 0 ≤ 3*H/4) :
    ∃ j : ℕ, H/(8*((j:ℝ)+1)*((j:ℝ)+2)) < |a (j+1)-a j| := by
  by_contra! hn
  have hpartial (n : ℕ) : a n ≤ a 0 + H/8*(1-1/((n:ℝ)+1)) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      have hstep := (le_abs_self (a (n+1)-a n)).trans (hn n)
      have htel : H/8*(1-1/((n:ℝ)+1)) + H/(8*((n:ℝ)+1)*((n:ℝ)+2)) =
          H/8*(1-1/(((n+1:ℕ):ℝ)+1)) := by
        push_cast
        field_simp
        ring
      linarith
  have hb (n : ℕ) : a n ≤ a 0+H/8 := by
    have hp : 0 ≤ H/8*(1/((n:ℝ)+1)) := by positivity
    have hh := hpartial n
    nlinarith
  have hh := le_of_tendsto ha (Eventually.of_forall hb)
  linarith

lemma large_increment_energy {H e : ℝ} (hH : 0 < H) (he : 0 ≤ e) (j : ℕ)
    (h : H/(8*((j:ℝ)+1)*((j:ℝ)+2)) ≤ 12*Real.sqrt e) :
    H^2/(9216*((j:ℝ)+2)^4) ≤ e := by
  have hd : 0 < 8*((j:ℝ)+1)*((j:ℝ)+2) := by positivity
  have hh := (div_le_iff₀ hd).1 h
  have hj : ((j:ℝ)+1)*((j:ℝ)+2) ≤ ((j:ℝ)+2)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hm := mul_le_mul_of_nonneg_right hj (show 0 ≤ 96*Real.sqrt e by positivity)
  have hlinear : H ≤ 96*((j:ℝ)+2)^2*Real.sqrt e := by nlinarith
  have hsq := (sq_le_sq₀ hH.le (by positivity)).2 hlinear
  rw [mul_pow, mul_pow, Real.sq_sqrt he] at hsq
  apply (div_le_iff₀ (by positivity)).2
  nlinarith [show (((j:ℝ)+2)^2)^2 = ((j:ℝ)+2)^4 by ring]

noncomputable def exceptionalParents (D : ℂ → ℂ) (H : ℝ) (N j : ℕ) :
    Finset (Fin (2^(N+j)) × Fin (2^(N+j))) := by
  classical
  exact Finset.univ.filter (fun p => H^2/(9216*((j:ℝ)+2)^4) ≤ cellEnergy D (N+j) p)

lemma mem_exceptionalParents (D : ℂ → ℂ) (H : ℝ) (N j : ℕ)
    (p : Fin (2^(N+j)) × Fin (2^(N+j))) :
    p ∈ exceptionalParents D H N j ↔ H^2/(9216*((j:ℝ)+2)^4) ≤ cellEnergy D (N+j) p := by
  classical
  simp [exceptionalParents]

lemma exceptional_cover {u : ℂ → ℝ} {D : ℂ → ℂ} {H : ℝ} (hH : 0 < H)
    (hu : SourceIsStripWeakGradient u D) (hc : ContinuousOn u (stripRectangle 0 0 1))
    (N : ℕ) (hN : ∀ p, spatialAverage u (dyadicCell N p) ≤ 3*H/4) :
    {z | z ∈ stripRectangle 0 0 1 ∧ u z = H} ⊆
      ⋃ j : ℕ, ⋃ p ∈ exceptionalParents D H N j, dyadicCell (N+j) p := by
  intro z hz
  have ht : Tendsto (fun j => spatialAverage u (dyadicCell (N+j) (pointBranch z (N+j))))
      atTop (𝓝 H) := by
    simpa only [Function.comp_def, Nat.add_comm, hz.2] using
      (branch_means_tendsto hc hz.1).comp (tendsto_add_atTop_nat N)
  obtain ⟨j,hj⟩ := exists_large_increment hH ht (by simpa using hN (pointBranch z N))
  have hstep := branch_mean_step_le hu z (N+j)
  have he : H^2/(9216*((j:ℝ)+2)^4) ≤ cellEnergy D (N+j) (pointBranch z (N+j)) := by
    apply large_increment_energy hH (cellEnergy_nonneg ..) j
    have hnj : N+(j+1) = N+j+1 := by omega
    rw [hnj] at hj
    exact hj.le.trans hstep
  exact mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨pointBranch z (N+j), mem_iUnion.2
    ⟨(mem_exceptionalParents ..).2 he, pointBranch_contains hz.1 (N+j)⟩⟩⟩

lemma exceptional_count {D : ℂ → ℂ} (hD : MemLp D 2 (volume.restrict openUnitStrip))
    {H : ℝ} (hH : 0 < H) (N j : ℕ) :
    ((exceptionalParents D H N j).card : ℝ) ≤
      9216*(stripDirichletEnergy D/H^2)*((j:ℝ)+2)^4 := by
  classical
  have hl := Finset.card_nsmul_le_sum (exceptionalParents D H N j)
    (cellEnergy D (N+j)) (H^2/(9216*((j:ℝ)+2)^4))
    (fun p hp => (mem_exceptionalParents ..).1 hp)
  simp only [nsmul_eq_mul] at hl
  have hs : ∑ p ∈ exceptionalParents D H N j, cellEnergy D (N+j) p ≤
      stripDirichletEnergy D := by
    apply le_trans _ (sum_cellEnergy_le hD (N+j))
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun p _ _ => cellEnergy_nonneg ..)
  have hd : 0 < 9216*((j:ℝ)+2)^4 := by positivity
  have hh : ((exceptionalParents D H N j).card : ℝ)*H^2 ≤
      stripDirichletEnergy D*(9216*((j:ℝ)+2)^4) := by
    apply (div_le_iff₀ hd).1
    simpa only [mul_div_assoc] using hl.trans hs
  calc
    ((exceptionalParents D H N j).card : ℝ) ≤
        (stripDirichletEnergy D*(9216*((j:ℝ)+2)^4))/H^2 :=
      (le_div_iff₀ (sq_pos_of_pos hH)).2 hh
    _ = 9216*(stripDirichletEnergy D/H^2)*((j:ℝ)+2)^4 := by ring

noncomputable def polyGeometricSum (q : ℝ) : ℝ := ∑' j : ℕ, ((j:ℝ)+2)^4*q^j

lemma summable_polyGeometric {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Summable (fun j : ℕ => ((j:ℝ)+2)^4*q^j) := by
  have hs₀ : Summable (fun n : ℕ => (n:ℝ)^4*q^n) :=
    summable_pow_mul_geometric_of_norm_lt_one 4 (by simpa [Real.norm_eq_abs, abs_of_pos hq] using hq1)
  have hs : Summable (fun n : ℕ => ((n+2:ℕ):ℝ)^4*q^(n+2)) :=
    (summable_nat_add_iff 2).2 hs₀
  apply (hs.mul_right (q^2)⁻¹).congr
  intro j
  push_cast
  rw [pow_add]
  field_simp

lemma polyGeometricSum_pos {q : ℝ} (hq : 0 < q) (hq1 : q < 1) : 0 < polyGeometricSum q := by
  have hh := (summable_polyGeometric hq hq1).le_tsum 0
    (fun j _ => by positivity : ∀ j : ℕ, j ≠ 0 → 0 ≤ ((j:ℝ)+2)^4*q^j)
  norm_num at hh
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 16) hh

lemma decay_factor (α : ℝ) (N j : ℕ) :
    (2:ℝ)^(-α*((N+j:ℕ):ℝ)) = ((2:ℝ)^(-α))^N * ((2:ℝ)^(-α))^j := by
  push_cast
  rw [mul_add, Real.rpow_add (by norm_num), Real.rpow_mul_natCast (by norm_num),
    Real.rpow_mul_natCast (by norm_num)]

lemma summable_weighted_decay (α : ℝ) (hα : 0 < α) (N : ℕ) (A : ℝ) :
    Summable (fun j : ℕ => A*((j:ℝ)+2)^4*(2:ℝ)^(-α*((N+j:ℕ):ℝ))) := by
  have hq : 0 < (2:ℝ)^(-α) := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : (2:ℝ)^(-α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  apply ((summable_polyGeometric hq hq1).mul_left (A*((2:ℝ)^(-α))^N)).congr
  intro j
  rw [decay_factor]
  ring

lemma tsum_weighted_decay (α : ℝ) (_hα : 0 < α) (N : ℕ) (A : ℝ) :
    (∑' j : ℕ, A*((j:ℝ)+2)^4*(2:ℝ)^(-α*((N+j:ℕ):ℝ))) =
      A*polyGeometricSum ((2:ℝ)^(-α))*((2:ℝ)^(-α))^N := by
  simp_rw [decay_factor]
  have he : (fun j : ℕ => A*((j:ℝ)+2)^4*(((2:ℝ)^(-α))^N*((2:ℝ)^(-α))^j)) =
      (fun j : ℕ => (A*((2:ℝ)^(-α))^N)*(((j:ℝ)+2)^4*((2:ℝ)^(-α))^j)) := by
    ext j
    ring
  rw [he, tsum_mul_left]
  dsimp [polyGeometricSum]
  ring

lemma finite_union_hit_bound {Ω I : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Q : I → Set ℂ) (X : Ω → Set ℂ) (S : Finset I) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ p ∈ S, P {ξ | (X ξ ∩ Q p).Nonempty} ≤ ENNReal.ofReal B) :
    P (⋃ p ∈ S, {ξ | (X ξ ∩ Q p).Nonempty}) ≤ ENNReal.ofReal ((S.card:ℝ)*B) := by
  calc
    _ ≤ ∑ p ∈ S, P {ξ | (X ξ ∩ Q p).Nonempty} := measure_biUnion_finset_le S _
    _ ≤ ∑ p ∈ S, ENNReal.ofReal B := Finset.sum_le_sum h
    _ = ENNReal.ofReal ((S.card:ℝ)*B) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hB)]
      simp

lemma rectangle_bound_at_depth {u : ℂ → ℝ} {D : ℂ → ℂ} {H C0 α : ℝ}
    (hH : 0 < H) (hC0 : 0 < C0) (hα : 0 < α)
    (hu : SourceIsStripWeakGradient u D) (hc : ContinuousOn u (stripRectangle 0 0 1))
    (N : ℕ) (hN : ∀ p, spatialAverage u (dyadicCell N p) ≤ 3*H/4)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Set ℂ)
    (hhit : ∀ (k : ℕ) (p : Fin (2^k) × Fin (2^k)),
      P {ξ | (X ξ ∩ dyadicCell k p).Nonempty} ≤ ENNReal.ofReal (C0*(2:ℝ)^(-α*(k:ℝ)))) :
    P {ξ | (X ξ ∩ {z | z ∈ stripRectangle 0 0 1 ∧ u z = H}).Nonempty} ≤
      ENNReal.ofReal (9216*C0*(stripDirichletEnergy D/H^2)*
        polyGeometricSum ((2:ℝ)^(-α))*((2:ℝ)^(-α))^N) := by
  have hE : 0 ≤ stripDirichletEnergy D := integral_nonneg (fun _ => sq_nonneg _)
  have hsub : {ξ | (X ξ ∩ {z | z ∈ stripRectangle 0 0 1 ∧ u z = H}).Nonempty} ⊆
      ⋃ j : ℕ, ⋃ p ∈ exceptionalParents D H N j, {ξ | (X ξ ∩ dyadicCell (N+j) p).Nonempty} := by
    intro ξ hξ
    obtain ⟨z, hzX, hz⟩ := hξ
    have hz' := exceptional_cover hH hu hc N hN hz
    simp only [mem_iUnion] at hz' ⊢
    obtain ⟨j,p,hp,hzp⟩ := hz'
    exact ⟨j,p,hp, z,hzX,hzp⟩
  have hlevel (j : ℕ) :
      P (⋃ p ∈ exceptionalParents D H N j, {ξ | (X ξ ∩ dyadicCell (N+j) p).Nonempty}) ≤
      ENNReal.ofReal (9216*C0*(stripDirichletEnergy D/H^2)*((j:ℝ)+2)^4*
        (2:ℝ)^(-α*((N+j:ℕ):ℝ))) := by
    apply (finite_union_hit_bound P (dyadicCell (N+j)) X (exceptionalParents D H N j)
      (by positivity) (fun p _ => hhit (N+j) p)).trans
    apply ENNReal.ofReal_le_ofReal
    have hh := mul_le_mul_of_nonneg_right (exceptional_count hu.2.1 hH N j)
      (show 0 ≤ C0*(2:ℝ)^(-α*((N+j:ℕ):ℝ)) by positivity)
    calc
      _ ≤ (9216*(stripDirichletEnergy D/H^2)*((j:ℝ)+2)^4)*
          (C0*(2:ℝ)^(-α*((N+j:ℕ):ℝ))) := hh
      _ = _ := by ring
  calc
    _ ≤ P (⋃ j : ℕ, ⋃ p ∈ exceptionalParents D H N j,
        {ξ | (X ξ ∩ dyadicCell (N+j) p).Nonempty}) := measure_mono hsub
    _ ≤ ∑' j : ℕ, P (⋃ p ∈ exceptionalParents D H N j,
        {ξ | (X ξ ∩ dyadicCell (N+j) p).Nonempty}) := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (9216*C0*(stripDirichletEnergy D/H^2)*((j:ℝ)+2)^4*
        (2:ℝ)^(-α*((N+j:ℕ):ℝ))) := ENNReal.tsum_le_tsum hlevel
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
        (summable_weighted_decay α hα N (9216*C0*(stripDirichletEnergy D/H^2))),
        tsum_weighted_decay α hα N]

noncomputable def energyDepth (H E : ℝ) : ℕ := ⌊H^2/(25600*E)⌋₊

lemma energyDepth_mean_bound {H E : ℝ} (hH : 0 < H) (hE : 0 < E)
    (hsmall : E ≤ H^2/51200) :
    20*Real.sqrt ((((energyDepth H E:ℕ):ℝ)+1)*E) ≤ H/4 := by
  have hf : ((energyDepth H E:ℕ):ℝ) ≤ H^2/(25600*E) := Nat.floor_le (by positivity)
  have hm := (le_div_iff₀ (show 0 < 25600*E by positivity)).1 hf
  have hn : 0 ≤ (((energyDepth H E:ℕ):ℝ)+1)*E := by positivity
  change 20*Real.sqrt ((((energyDepth H E:ℕ):ℝ)+1)*E) ≤ H/4
  apply (sq_le_sq₀ (by positivity) (by positivity)).1
  rw [mul_pow, Real.sq_sqrt hn, div_pow]
  norm_num
  nlinarith [sq_nonneg H]

lemma energyDepth_lower {H E : ℝ} (_hH : 0 < H) (hE : 0 < E)
    (hsmall : E ≤ H^2/51200) :
    H^2/(51200*E) ≤ ((energyDepth H E:ℕ):ℝ) := by
  have hf : H^2/(25600*E) < ((energyDepth H E:ℕ):ℝ)+1 := Nat.lt_floor_add_one _
  have hx : 2 ≤ H^2/(25600*E) := by
    apply (le_div_iff₀ (by positivity)).2
    linarith
  have he : H^2/(51200*E) = (H^2/(25600*E))/2 := by ring
  rw [he]
  linarith

lemma energyDepth_decay {H E α : ℝ} (hH : 0 < H) (hE : 0 < E) (hα : 0 < α)
    (hsmall : E ≤ H^2/51200) :
    ((2:ℝ)^(-α))^(energyDepth H E) ≤ Real.exp (-(α*Real.log 2/51200)*H^2/E) := by
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2), Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.mpr
  have hn := energyDepth_lower hH hE hsmall
  have hh := mul_le_mul_of_nonneg_left hn (show 0 ≤ α*Real.log 2 by positivity)
  calc
    Real.log 2 * (-α*((energyDepth H E:ℕ):ℝ)) = -(α*Real.log 2*((energyDepth H E:ℕ):ℝ)) := by ring
    _ ≤ -(α*Real.log 2*(H^2/(51200*E))) := neg_le_neg hh
    _ = _ := by ring

universe u

 

def SourceStripRectangleEnergyTarget : Prop :=
  ∀ C0 α : ℝ, 0 < C0 → 0 < α →
    ∃ C c c0 : ℝ, 0 < C ∧ 0 < c ∧ 0 < c0 ∧
      ∀ (H : ℝ), 0 < H → ∀ (u : ℂ → ℝ) (D : ℂ → ℂ),
      SourceIsStripWeakGradient u D → ContinuousOn u (stripRectangle 0 0 1) →
      (∀ z ∈ stripRectangle 0 0 1, 0 ≤ u z ∧ u z ≤ H) →
      spatialAverage u (stripRectangle 0 0 1) ≤ H/2 →
      ∀ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω),
      IsProbabilityMeasure P → ∀ X : Ω → Set ℂ,
      (∀ (k : ℕ) (i m : Fin (2^k)),
        P {ξ | (X ξ ∩ dyadicStripRectangle 0 k i m).Nonempty} ≤
          ENNReal.ofReal (C0 * (2:ℝ)^(-α*(k:ℝ)))) →
      stripDirichletEnergy D ≤ c0*H^2 →
      P {ξ | (X ξ ∩ {z | z ∈ stripRectangle 0 0 1 ∧ u z = H}).Nonempty} ≤
        ENNReal.ofReal (C * (stripDirichletEnergy D/H^2) *
          Real.exp (-c*H^2/stripDirichletEnergy D))

lemma critical_cell_means_le {u : ℂ → ℝ} {D : ℂ → ℂ}
    (hu : SourceIsStripWeakGradient u D) (k : ℕ) (p : Fin (2^k) × Fin (2^k)) :
    |spatialAverage u (dyadicCell k p) - spatialAverage u (stripRectangle 0 0 1)| ≤
      20*Real.sqrt (((k:ℝ)+1)*stripDirichletEnergy D) := by
  rw [dyadicCell_eq]
  by_cases hk : k = 0
  · subst k
    have hi : p.1 = 0 := by apply Fin.ext; have := p.1.isLt; norm_num at this ⊢
    have hm : p.2 = 0 := by apply Fin.ext; have := p.2.isLt; norm_num at this ⊢
    simp [hi, hm, dyadicStripRectangle]
  · obtain ⟨t, ht, ht1, hit⟩ := dyadic_position_param k hk p.1
    obtain ⟨s, hs, hs1, hms⟩ := dyadic_position_param k hk p.2
    have hh := chain_means_le hu ht ht1 hs hs1 k
    simpa only [dyadicStripRectangle, Int.cast_zero, zero_add, hit, hms, scaleLength] using hh

lemma high_set_empty_of_energy_zero {u : ℂ → ℝ} {D : ℂ → ℂ} {H : ℝ}
    (hH : 0 < H) (hu : SourceIsStripWeakGradient u D)
    (hc : ContinuousOn u (stripRectangle 0 0 1))
    (hmean : spatialAverage u (stripRectangle 0 0 1) ≤ H/2)
    (hzero : stripDirichletEnergy D = 0) :
    {z | z ∈ stripRectangle 0 0 1 ∧ u z = H} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hb (k : ℕ) : spatialAverage u (dyadicCell k (pointBranch z k)) ≤ H/2 := by
    have hh := critical_cell_means_le hu k (pointBranch z k)
    rw [hzero, mul_zero, Real.sqrt_zero, mul_zero] at hh
    have hh' := (le_abs_self _).trans hh
    linarith
  have hh := le_of_tendsto (branch_means_tendsto hc hz.1) (Eventually.of_forall hb)
  rw [hz.2] at hh
  linarith

theorem sourceStripRectangleEnergy : SourceStripRectangleEnergyTarget := by
  intro C0 α hC0 hα
  have hq : 0 < (2:ℝ)^(-α) := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : (2:ℝ)^(-α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨9216*C0*polyGeometricSum ((2:ℝ)^(-α)), α*Real.log 2/51200, 1/51200,
    by positivity [polyGeometricSum_pos hq hq1], by positivity, by norm_num, ?_⟩
  intro H hH u D hu hc _hrange hmean Ω mΩ P _hP X hhit hsmall
  have hE : 0 ≤ stripDirichletEnergy D := integral_nonneg (fun _ => sq_nonneg _)
  have hsmall' : stripDirichletEnergy D ≤ H^2/51200 := by linarith
  by_cases hz : stripDirichletEnergy D = 0
  · rw [high_set_empty_of_energy_zero hH hu hc hmean hz]
    simp [hz]
  · have hEpos : 0 < stripDirichletEnergy D := lt_of_le_of_ne hE (Ne.symm hz)
    let N := energyDepth H (stripDirichletEnergy D)
    have hN : ∀ p, spatialAverage u (dyadicCell N p) ≤ 3*H/4 := by
      intro p
      have hh := critical_cell_means_le hu N p
      have hs := energyDepth_mean_bound hH hEpos hsmall'
      change 20*Real.sqrt (((N:ℝ)+1)*stripDirichletEnergy D) ≤ H/4 at hs
      have hh' := (le_abs_self _).trans (hh.trans hs)
      linarith
    have hh := rectangle_bound_at_depth hH hC0 hα hu hc N hN P X
      (fun k p => by simpa only [dyadicCell_eq] using hhit k p.1 p.2)
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    have hl := mul_le_mul_of_nonneg_left (energyDepth_decay hH hEpos hα hsmall')
      (show 0 ≤ 9216*C0*(stripDirichletEnergy D/H^2)*polyGeometricSum ((2:ℝ)^(-α)) by
        exact mul_nonneg (by positivity) (polyGeometricSum_pos hq hq1).le)
    calc
      _ ≤ (9216*C0*(stripDirichletEnergy D/H^2)*polyGeometricSum ((2:ℝ)^(-α)))*
          Real.exp (-(α*Real.log 2/51200)*H^2/stripDirichletEnergy D) := hl
      _ = _ := by ring

lemma source_local_lipschitz_weak_derivative {D : Set ℂ} (hD : IsOpen D) {u : ℂ → ℝ}
    (hlocal : ∀ x ∈ D, ∃ (K : ℝ≥0) (U : Set ℂ), IsOpen U ∧ x ∈ U ∧ LipschitzOnWith K u U)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ D) (v : ℂ) :
    (∫ z in D, u z * (fderiv ℝ φ z) v) =
      -(∫ z in D, (fderiv ℝ u z) v * φ z) := by
  obtain ⟨S,hSc,hφS,hSD⟩ := exists_compact_between hcφ hD hsφ
  have huS : LocallyLipschitzOn S u := by
    intro x hx
    obtain ⟨K,U,hUo,hxU,hU⟩ := hlocal x (hSD hx)
    exact ⟨K,U,mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hxU),hU⟩
  obtain ⟨K,hK⟩ := huS.exists_lipschitzOnWith_of_compact hSc
  obtain ⟨g,hglip,hug⟩ := hK.extend_real
  obtain ⟨C,hφlip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcφ hφ (by simp)
  have hφdiff : ∀ z, DifferentiableAt ℝ φ z := fun z => (hφ.differentiable (by simp)).differentiableAt
  have ht (z : ℂ) (hz : z ∈ tsupport φ) : u =ᶠ[𝓝 z] g := by
    filter_upwards [mem_interior_iff_mem_nhds.mp (hφS hz)] with w hw
    exact hug hw
  have hid := hglip.integral_lineDeriv_mul_eq (μ := volume) hφlip hcφ v
  have hfull : (∫ z, (fderiv ℝ g z) v * φ z) = -(∫ z, g z * (fderiv ℝ φ z) v) := by
    calc
      _ = ∫ z, lineDeriv ℝ g z v * φ z := by
        apply integral_congr_ae
        filter_upwards [hglip.ae_differentiableAt (μ := volume)] with z hz
        rw [hz.lineDeriv_eq_fderiv]
      _ = ∫ z, lineDeriv ℝ φ z (-v) * g z := hid
      _ = _ := by
        simp_rw [(hφdiff _).lineDeriv_eq_fderiv,map_neg,neg_mul,mul_comm _ (g _)]
        rw [integral_neg]
  have he1 : (fun z => u z * (fderiv ℝ φ z) v) = (fun z => g z * (fderiv ℝ φ z) v) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [hug (interior_subset (hφS hz))]
    · simp [fderiv_of_notMem_tsupport ℝ hz]
  have he2 : (fun z => (fderiv ℝ u z) v * φ z) = (fun z => (fderiv ℝ g z) v * φ z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [(ht z hz).fderiv_eq]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hs1 : (∫ z in D, u z * (fderiv ℝ φ z) v) = ∫ z, u z * (fderiv ℝ φ z) v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hn : z ∉ tsupport φ := fun h => hz (hsφ h)
    simp [fderiv_of_notMem_tsupport ℝ hn]
  have hs2 : (∫ z in D, (fderiv ℝ u z) v * φ z) = ∫ z, (fderiv ℝ u z) v * φ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hn : z ∉ tsupport φ := fun h => hz (hsφ h)
    simp [image_eq_zero_of_notMem_tsupport hn]
  rw [hs1,hs2,he1,he2,hfull]
  simp

lemma real_gradient_re (u : ℂ → ℝ) (z : ℂ) : (gradient u z).re = (fderiv ℝ u z) (1:ℂ) := by
  have hh := inner_gradient_left (f := u) (x := z) (y := (1:ℂ))
  rw [Complex.inner] at hh
  simpa using hh

lemma real_gradient_im (u : ℂ → ℝ) (z : ℂ) : (gradient u z).im = (fderiv ℝ u z) Complex.I := by
  have hh := inner_gradient_left (f := u) (x := z) (y := Complex.I)
  rw [Complex.inner] at hh
  simpa using hh

lemma locallyLipschitz_source_weakGradient {u : ℂ → ℝ}
    (hl : LocallyLipschitzOn openUnitStrip u)
    (hu : MemLp u 2 (volume.restrict openUnitStrip))
    (hg : MemLp (gradient u) 2 (volume.restrict openUnitStrip)) :
    SourceIsStripWeakGradient u (gradient u) := by
  refine ⟨hu,hg,?_⟩
  have hlocal (z : ℂ) (hz : z ∈ openUnitStrip) :
      ∃ (K : ℝ≥0) (U : Set ℂ), IsOpen U ∧ z ∈ U ∧ LipschitzOnWith K u U := by
    obtain ⟨K,t,ht,htl⟩ := hl hz
    rw [nhdsWithin_eq_nhds.mpr (openUnitStrip_isOpen.mem_nhds hz)] at ht
    obtain ⟨U,hUt,hUo,hzU⟩ := _root_.mem_nhds_iff.mp ht
    exact ⟨K,U,hUo,hzU,htl.mono hUt⟩
  intro φ hφ hc hs
  constructor
  · simpa only [real_gradient_re] using
      source_local_lipschitz_weak_derivative openUnitStrip_isOpen hlocal φ hφ hc hs 1
  · simpa only [real_gradient_im] using
      source_local_lipschitz_weak_derivative openUnitStrip_isOpen hlocal φ hφ hc hs Complex.I

 

end SLEExactGauge
end
end

end OAI
