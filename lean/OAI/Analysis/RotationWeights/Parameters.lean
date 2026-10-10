import OAI.Analysis.RotationWeights.NestedAngles

namespace OAI

noncomputable section

namespace CircleSampling

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set

section
open Set Filter MeasureTheory ContinuousCircleWeight.Sampling
open scoped Topology

def blockLength (j : ℕ) : ℕ := (scaleStep j).m
def blockEnd (j : ℕ) : ℕ := (scaleState j).1.d
def polynomialWindow (j : ℕ) : ℕ := (scaleState j).1.K
def dropSize (j : ℕ) : ℝ := (scaleStep j).C
def crossingBudget (j : ℕ) : ℝ := (scaleStep j).L
def bridgeSize (j : ℕ) : ℝ := (scaleState j).1.G
def frequency (i : ℕ) : ℕ := (scaleState i).1.q i

def blocks : BlockPartition where
  m := blockLength
  d := blockEnd
  zero := rfl
  step := fun _ => rfl
  positive := fun j => (scaleStep j).mpos

lemma blockEnd_strictMono : StrictMono blockEnd := blocks.strictMono
lemma blockEnd_ge (j : ℕ) : j≤blockEnd j := blocks.ge j
lemma state_prefix (j i : ℕ) (hi : i≤blockEnd j) : (scaleState (j+1)).1.q i=(scaleState j).1.q i :=
  extendPrefix_old _ _ _ hi
lemma frequency_eq_state {j i : ℕ} (hi : i≤blockEnd j) : frequency i=(scaleState j).1.q i :=
  diagonal_prefix_eq blockEnd (fun j => (scaleState j).1.q)
    blockEnd_strictMono.monotone blockEnd_ge state_prefix hi

lemma frequency_block (j : ℕ) {k : ℕ} (hk : k≤blockLength j) :
    frequency (blockEnd j+k)=(scaleStep j).q k := by
  rw [frequency_eq_state (j:=j+1) (show blockEnd j+k≤blockEnd (j+1) by
    change blockEnd j+k≤blockEnd j+blockLength j; omega)]
  exact extendPrefix_block _ _ _ (scaleStep j).qzero k
lemma frequency_zero : frequency 0=1 := rfl
lemma frequency_pos (i : ℕ) : 0 < frequency i := (scaleState i).2.qpos i (blockEnd_ge i)
lemma frequency_dvd (i : ℕ) : frequency i∣frequency (i+1) := by
  rw [frequency_eq_state (j:=i+1) (by have := blockEnd_ge (i+1); omega),frequency_eq_state (j:=i+1) (blockEnd_ge _)]
  exact (scaleState (i+1)).2.qdvd i (by change i<blockEnd (i+1); have := blockEnd_ge (i+1); omega)
lemma frequency_strictMono : StrictMono frequency := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [frequency_eq_state (j:=i+1) (by have := blockEnd_ge (i+1); omega),frequency_eq_state (j:=i+1) (blockEnd_ge _)]
  exact (scaleState (i+1)).2.qlt i (by change i<blockEnd (i+1); have := blockEnd_ge (i+1); omega)
lemma frequency_one_gt : 1<frequency 1 := by simpa [frequency_zero] using frequency_strictMono (by omega : 0<1)

lemma polynomialWindow_zero : polynomialWindow 0=100 := rfl
lemma polynomialWindow_succ (j : ℕ) : polynomialWindow (j+1)=nextWindow (blockLength j) := rfl
lemma polynomialWindow_pos (j : ℕ) : 0<polynomialWindow j := (scaleState j).2.Kpos
lemma polynomialWindow_growth (j : ℕ) : 2*polynomialWindow j<polynomialWindow (j+1) :=
  (scaleStep j).numeric.2.2.2.2.2.2.1
lemma polynomialWindow_gt_length (j : ℕ) : blockLength j<polynomialWindow (j+1) :=
  (scaleStep j).numeric.2.2.2.2.2.2.2.1
lemma polynomialWindow_le_length (j : ℕ) : polynomialWindow j≤blockLength j :=
  (scaleStep j).numeric.2.2.1
lemma blockLength_strictMono : StrictMono blockLength :=
  strictMono_nat_of_lt_succ fun j => (polynomialWindow_gt_length j).trans_le (polynomialWindow_le_length (j+1))
lemma blockLength_ge (j : ℕ) : 200≤blockLength j := (scaleStep j).numeric.1
lemma crossingBudget_mono : Monotone crossingBudget :=
  monotone_nat_of_le_succ fun j => (scaleStep (j+1)).Lprev
lemma dropSize_ge_budget (j : ℕ) : crossingBudget j≤dropSize j := le_max_left _ _
lemma dropSize_nonneg (j : ℕ) : 0≤dropSize j :=
  (by change 0≤(scaleStep j).L; linarith [(scaleStep j).Lge] : 0≤crossingBudget j).trans (dropSize_ge_budget j)
lemma exponent_prefix (j : ℕ) : (scaleState j).1.E=∑ t∈Finset.range j,dropSize t*blockLength t := by
  induction j with
  | zero => simp [scaleState,initialScaleState]
  | succ j ih =>
    change (scaleState j).1.E+dropSize j*blockLength j=_
    rw [Finset.sum_range_succ,ih]

lemma polynomialWindow_geometric (j n : ℕ) : 2^n*polynomialWindow j≤polynomialWindow (j+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hg := (polynomialWindow_growth (j+n)).le
    calc
      2^(n+1)*polynomialWindow j = 2*(2^n*polynomialWindow j) := by ring
      _ ≤ 2*polynomialWindow (j+n) := Nat.mul_le_mul_left _ ih
      _ ≤ polynomialWindow (j+(n+1)) := by simpa only [Nat.add_assoc] using hg

lemma frequency_block_ratio (j : ℕ) {k : ℕ} (hk : k<blockLength j) :
    100*(blockLength j:ℝ) < (frequency (blockEnd j+k+1):ℝ)/frequency (blockEnd j+k) := by
  rw [show blockEnd j+k+1=blockEnd j+(k+1) by omega,
    frequency_block j (by omega),frequency_block j hk.le]
  exact ((scaleStep j).qratio k hk).2

lemma frequency_radix_bound (j : ℕ) {k : ℕ} (hk : k≤blockLength j) :
    100*(blockLength j:ℝ) < (frequency (blockEnd j+k+1):ℝ)/frequency (blockEnd j+k) := by
  by_cases hlt : k<blockLength j
  · exact frequency_block_ratio j hlt
  · have he : k=blockLength j := by omega
    subst k
    have h := frequency_block_ratio (j+1) (k:=0) (scaleStep (j+1)).mpos
    have hlen : (blockLength j:ℝ) ≤ blockLength (j+1) :=
      Nat.cast_le.mpr (blockLength_strictMono.monotone (Nat.le_succ j))
    change 100*(blockLength (j+1):ℝ) < (frequency (blockEnd j+blockLength j+1):ℝ)/frequency (blockEnd j+blockLength j) at h
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hlen (by norm_num)) h

def modelFrequency (i : ℕ) : ℕ := frequency (i+1)
def coordinateBlock (i : ℕ) : ℕ := blocks.number i
def coordinateDrop (i : ℕ) : ℝ := dropSize (coordinateBlock i)

def parameterAngle : ℝ := exists_global_angle.choose
lemma parameterAngle_spec : 0<parameterAngle ∧ parameterAngle<1 ∧ Irrational parameterAngle ∧
    ∀ j, parameterAngle∈Icc (scaleStep j).a (scaleStep j).b := exists_global_angle.choose_spec
lemma block_phase (j : ℕ) (i : Fin (blockLength j)) :
    Int.fract ((frequency (blockEnd j+i.val+1):ℝ)*parameterAngle)∈
      Ioo (1/((blockLength j:ℝ)*polynomialWindow j)) (2/((blockLength j:ℝ)*polynomialWindow j)) := by
  have hh := (scaleStep j).phases parameterAngle (parameterAngle_spec.2.2.2 j) i
  rw [show blockEnd j+i.val+1=blockEnd j+(i.val+1) by omega,frequency_block j (by omega)]
  exact hh
end

open Set Filter MeasureTheory
open scoped Topology BigOperators

def coordinatePhase (i : ℕ) : ℝ := Int.fract ((modelFrequency i:ℝ)*parameterAngle)

lemma coordinatePhase_block (j : ℕ) (i : Fin (blockLength j)) :
    coordinatePhase (blocks.equiv ⟨j,i⟩)∈
      Ioo (1/((blockLength j:ℝ)*polynomialWindow j)) (2/((blockLength j:ℝ)*polynomialWindow j)) :=
  block_phase j i
lemma coordinatePhase_pos (i : ℕ) : 0<coordinatePhase i := by
  obtain ⟨⟨j,k⟩,rfl⟩ := blocks.equiv.surjective i
  exact lt_trans (by
    have hm : 0<(blockLength j:ℝ) := Nat.cast_pos.mpr (scaleStep j).mpos
    have hK : 0<(polynomialWindow j:ℝ) := Nat.cast_pos.mpr (polynomialWindow_pos j)
    positivity) (coordinatePhase_block j k).1

lemma window_inverse_bound (j n : ℕ) :
    1/(polynomialWindow (j+n):ℝ) ≤ (1/(polynomialWindow j:ℝ))*(1/2:ℝ)^n := by
  have hK : 0<(polynomialWindow j:ℝ) := Nat.cast_pos.mpr (polynomialWindow_pos j)
  have hg : (2:ℝ)^n*(polynomialWindow j:ℝ) ≤ polynomialWindow (j+n) := by
    exact_mod_cast polynomialWindow_geometric j n
  calc
    1/(polynomialWindow (j+n):ℝ) ≤ 1/((2:ℝ)^n*(polynomialWindow j:ℝ)) :=
      one_div_le_one_div_of_le (by positivity) hg
    _ = (1/(polynomialWindow j:ℝ))*(1/2:ℝ)^n := by rw [div_pow,one_pow]; field_simp

lemma summable_window_inverse (j : ℕ) : Summable (fun n => 1/(polynomialWindow (j+n):ℝ)) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (window_inverse_bound j)
  exact (summable_geometric_of_norm_lt_one (x:=(1/2:ℝ)) (by norm_num)).mul_left _

lemma tsum_window_inverse (j : ℕ) :
    (∑' n,1/(polynomialWindow (j+n):ℝ)) ≤ 2/(polynomialWindow j:ℝ) := by
  have hs := (summable_geometric_of_norm_lt_one (x:=(1/2:ℝ)) (by norm_num)).mul_left (1/(polynomialWindow j:ℝ))
  calc
    _ ≤ ∑' n,(1/(polynomialWindow j:ℝ))*(1/2:ℝ)^n :=
      (summable_window_inverse j).tsum_le_tsum (window_inverse_bound j) hs
    _ = 2/(polynomialWindow j:ℝ) := by
      rw [tsum_mul_left,tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)]
      ring

lemma sum_phase_block (j : ℕ) :
    (∑ i : Fin (blockLength j), coordinatePhase (blocks.equiv ⟨j,i⟩)) ≤ 2/(polynomialWindow j:ℝ) := by
  have hm : (blockLength j:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (scaleStep j).mpos.ne'
  calc
    _ ≤ ∑ _i : Fin (blockLength j),2/((blockLength j:ℝ)*polynomialWindow j) :=
      Finset.sum_le_sum (fun i _ => (coordinatePhase_block j i).2.le)
    _ = 2/(polynomialWindow j:ℝ) := by simp; field_simp

lemma summable_coordinatePhase : Summable coordinatePhase := by
  have hs : Summable (fun j => 2/(polynomialWindow j:ℝ)) := by
    simpa only [Nat.zero_add,div_eq_mul_inv,one_mul] using (summable_window_inverse 0).mul_left 2
  have ht : Summable (fun j => ∑ i : Fin (blockLength j), coordinatePhase (blocks.equiv ⟨j,i⟩)) :=
    Summable.of_nonneg_of_le (fun _ => Finset.sum_nonneg (fun _ _ => (coordinatePhase_pos _).le))
      sum_phase_block hs
  apply blocks.equiv.summable_iff.mp
  apply (summable_sigma_of_nonneg (fun x : Σ j, Fin (blocks.m j) => (coordinatePhase_pos (blocks.equiv x)).le)).mpr
  refine ⟨fun _ => Summable.of_finite,?_⟩
  convert ht using 1
  ext j
  rw [tsum_fintype]
  rfl

lemma block_number_equiv (j : ℕ) (i : Fin (blockLength j)) :
    coordinateBlock (blocks.equiv ⟨j,i⟩)=j := by
  exact blocks.number_eq (by change blockEnd j≤blockEnd j+i.val; omega)
    (by change blockEnd j+i.val<blockEnd j+blockLength j; omega)

lemma summable_block_reciprocal : Summable (fun j => 1/(blockLength j:ℝ)) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun j => one_div_le_one_div_of_le (Nat.cast_pos.mpr (polynomialWindow_pos j))
      (Nat.cast_le.mpr (polynomialWindow_le_length j)))
  simpa using summable_window_inverse 0

lemma dropSize_ge_window_sq (j : ℕ) : (polynomialWindow j:ℝ)^2≤dropSize j := le_max_right _ _

lemma phase_drop_block_lower (j : ℕ) :
    (polynomialWindow j:ℝ) ≤ ∑ i : Fin (blockLength j),
      coordinateDrop (blocks.equiv ⟨j,i⟩)*coordinatePhase (blocks.equiv ⟨j,i⟩) := by
  have hK : 0<(polynomialWindow j:ℝ) := Nat.cast_pos.mpr (polynomialWindow_pos j)
  have hm : 0<(blockLength j:ℝ) := Nat.cast_pos.mpr (scaleStep j).mpos
  calc
    _ = (blockLength j:ℝ)*((polynomialWindow j:ℝ)^2/((blockLength j:ℝ)*polynomialWindow j)) := by field_simp
    _ = ∑ _i : Fin (blockLength j),(polynomialWindow j:ℝ)^2/((blockLength j:ℝ)*polynomialWindow j) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      change _≤dropSize (coordinateBlock (blocks.equiv ⟨j,i⟩))*_
      rw [block_number_equiv]
      calc
        _ = (polynomialWindow j:ℝ)^2*(1/((blockLength j:ℝ)*polynomialWindow j)) := by ring
        _ ≤ dropSize j*coordinatePhase (blocks.equiv ⟨j,i⟩) := by
          exact mul_le_mul (dropSize_ge_window_sq j) (coordinatePhase_block j i).1.le (by positivity) (dropSize_nonneg j)

lemma not_summable_phase_drop : ¬Summable (fun i => coordinateDrop i*coordinatePhase i) := by
  intro hs
  have hn : ∀ i,0≤coordinateDrop i*coordinatePhase i :=
    fun i => mul_nonneg (dropSize_nonneg _) (coordinatePhase_pos i).le
  have ht := (summable_sigma_of_nonneg (fun x => hn (blocks.equiv x))).mp (blocks.equiv.summable_iff.mpr hs)
  have hone : Summable (fun _j : ℕ => (1:ℝ)) := by
    apply Summable.of_nonneg_of_le (fun _ => by norm_num) (fun j => ?_) ht.2
    calc
      1 ≤ (polynomialWindow j:ℝ) := by exact_mod_cast polynomialWindow_pos j
      _ ≤ ∑' i : Fin (blockLength j), coordinateDrop (blocks.equiv ⟨j,i⟩)*coordinatePhase (blocks.equiv ⟨j,i⟩) := by
        simpa only [tsum_fintype] using phase_drop_block_lower j
  have hzero := (summable_const_iff (1:ℝ)).mp hone
  norm_num at hzero


end CircleSampling

end

end OAI
