import Mathlib
import OAI.Geometry.BallPacking.Compactness.ResidualCauchy

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
section
variable {n : ℕ}
local instance ihInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance ihInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

lemma compatible_interpolateJ_initial {J : End n} (hJ : Compatible J) {t : ℝ}
    (ht : -1<t ∧ t≤1) : Compatible (interpolateJ J t) := by
  have ha : 0<1+t := by linarith [ht.1]
  have hb : 0≤1-t := by linarith [ht.2]
  have hQ := cayleyP_invertible hJ ha hb
  apply compatible_of_sq_symmetric_positive
  · intro v
    change standardJ n (cayleyOperator J (1+t) (1-t)
      (standardJ n (cayleyOperator J (1+t) (1-t) v))) = -v
    rw [cayleyOperator_J_identity hJ hQ,standardJ_sq]
  · intro v w
    change standardForm v (standardJ n (cayleyOperator J (1+t) (1-t) w)) =
      standardForm w (standardJ n (cayleyOperator J (1+t) (1-t) v))
    rw [standardForm_J_right,standardForm_J_right,←cayleyOperator_selfadjoint hJ hQ,stdDot_symm]
  · intro v hv
    change 0<standardForm v (standardJ n (cayleyOperator J (1+t) (1-t) v))
    rw [standardForm_J_right]
    exact cayleyOperator_positive hJ ha hb hv

lemma interpolateJ_standard_initial {t : ℝ} (ht : -1<t ∧ t≤1) : interpolateJ (standardJ n) t=standardJ n := by
  have ha : 0<1+t := by linarith [ht.1]
  have hb : 0≤1-t := by linarith [ht.2]
  obtain ⟨e,he⟩ := cayleyP_invertible (compatible_standardJ n) ha hb
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := e.surjective v
  change standardJ n (cayleyOperator (standardJ n) (1+t) (1-t) ((e : End n) x)) =
    standardJ n ((e : End n) x)
  rw [he,cayleyOperator_on_denominator ⟨e,he⟩]
  congr 1
  change (1+t) • relativeOperator (standardJ n) x+(1-t) • x =
    (1-t) • relativeOperator (standardJ n) x+(1+t) • x
  simp only [relativeOperator_apply,standardJ_sq,neg_neg]
  module

lemma contDiffAt_interpolateJ_initial {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {J : D → End n} {t : D → ℝ} {x : D}
    (hJs : ContDiffAt ℝ ∞ J x) (hts : ContDiffAt ℝ ∞ t x)
    (hJ : Compatible (J x)) (ht : -1<t x ∧ t x≤1) :
    ContDiffAt ℝ ∞ (fun y => interpolateJ (J y) (t y)) x := by
  have hA : ContDiffAt ℝ ∞ (fun y => relativeOperator (J y)) x :=
    (contDiffAt_const.clm_comp hJs).neg
  have ha : ContDiffAt ℝ ∞ (fun y => 1+t y) x := contDiffAt_const.add hts
  have hb : ContDiffAt ℝ ∞ (fun y => 1-t y) x := contDiffAt_const.sub hts
  have hP : ContDiffAt ℝ ∞ (fun y => cayleyP (J y) (1+t y) (1-t y)) x :=
    (ha.smul hA).add (hb.smul contDiffAt_const)
  have hQ : ContDiffAt ℝ ∞ (fun y => cayleyP (J y) (1-t y) (1+t y)) x :=
    (hb.smul hA).add (ha.smul contDiffAt_const)
  have hQi := cayleyP_invertible hJ (show 0<1+t x by linarith [ht.1]) (show 0≤1-t x by linarith [ht.2])
  have hI : ContDiffAt ℝ ∞ (fun y => (cayleyP (J y) (1-t y) (1+t y)).inverse) x :=
    ContDiffAt.comp x (g := ContinuousLinearMap.inverse)
      (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (n := ∞) hQi) hQ
  exact contDiffAt_const.clm_comp (hP.clm_comp hI)

def initialTime (t : ℝ) : ℝ := Real.sin t/2
lemma initialTime_range (t : ℝ) : -1 < initialTime t ∧ initialTime t≤1 := by
  constructor <;> unfold initialTime <;> linarith [Real.neg_one_le_sin t,Real.sin_le_one t]
lemma initialTime_smooth : ContDiff ℝ ∞ initialTime := Real.contDiff_sin.div_const 2
@[simp] lemma initialTime_zero : initialTime 0=0 := by simp [initialTime]

def initialTimeBump : ContDiffBump (0:ℝ) := ⟨1,2,by norm_num,by norm_num⟩

def initialCoefficient (J : Phase n → End n) (v : ℝ × Phase n) : End n :=
  initialTimeBump v.1 • (interpolateJ (J v.2) (initialTime v.1)-standardJ n)

variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))

include hJs hJ in
lemma initialCoefficient_smooth : ContDiff ℝ ∞ (initialCoefficient J) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  have hh := contDiffAt_interpolateJ_initial (hJs.contDiffAt.comp v contDiffAt_snd)
    (initialTime_smooth.contDiffAt.comp v contDiffAt_fst) (hJ v.2) (initialTime_range v.1)
  exact (initialTimeBump.contDiff.contDiffAt.comp v contDiffAt_fst).smul (hh.sub contDiffAt_const)

include hJ in
lemma initialCoefficient_zero (x : Phase n) : initialCoefficient J (0,x)=0 := by
  simp only [initialCoefficient,initialTime_zero,interpolateJ_zero (hJ x),sub_self,smul_zero]

lemma initialCoefficient_compact (hJc : HasCompactSupport (fun x => J x-standardJ n)) :
    HasCompactSupport (initialCoefficient J) := by
  apply (initialTimeBump.hasCompactSupport.prod hJc).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport _ |>.prod (isClosed_tsupport _))
  intro v hv
  constructor
  · by_contra hn
    have hz := image_eq_zero_of_notMem_tsupport hn
    apply hv
    change initialTimeBump v.1 • (interpolateJ (J v.2) (initialTime v.1)-standardJ n)=0
    rw [hz,zero_smul]
  · by_contra hn
    have hz : J v.2=standardJ n := sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun x => J x-standardJ n) hn)
    apply hv
    change initialTimeBump v.1 • (interpolateJ (J v.2) (initialTime v.1)-standardJ n)=0
    rw [hz,interpolateJ_standard_initial (initialTime_range _),sub_self,smul_zero]

lemma initialCoefficient_outside {B : ℝ} (hstd : ∀ x, B<‖x‖ → J x=standardJ n) :
    ∀ t x, B<‖x‖ → initialCoefficient J (t,x)=0 := by
  intro t x hx
  simp only [initialCoefficient,hstd x hx,interpolateJ_standard_initial (initialTime_range _),sub_self,smul_zero]

lemma initialCoefficient_near : ∀ᶠ t in 𝓝 (0:ℝ), ∀ x : Phase n,
    standardJ n+initialCoefficient J (t,x)=interpolateJ (J x) (initialTime t) := by
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) (show (0:ℝ)<1 by norm_num)] with t ht
  intro x
  have ht' : t∈Metric.closedBall (0:ℝ) initialTimeBump.rIn := by
    exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp ht).le
  rw [initialCoefficient,initialTimeBump.one_of_mem_closedBall ht',one_smul]
  abel

include hJ in
lemma initialCoefficient_compatible_near : ∀ᶠ t in 𝓝 (0:ℝ), ∀ x,
    Compatible (standardJ n+initialCoefficient J (t,x)) := by
  filter_upwards [initialCoefficient_near (J := J)] with t ht
  intro x
  rw [ht x]
  exact compatible_interpolateJ_initial (hJ x) (initialTime_range t)

end

variable {n : ℕ}
local instance ghInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance ghInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

def fullTime : ℝ → ℝ := Real.smoothTransition
lemma fullTime_range (t : ℝ) : fullTime t∈Icc (0:ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg t,Real.smoothTransition.le_one t⟩
lemma fullTime_smooth : ContDiff ℝ ∞ fullTime := by
  apply contDiff_infty.mpr
  intro m
  exact Real.smoothTransition.contDiff
@[simp] lemma fullTime_zero : fullTime 0=0 := Real.smoothTransition.zero
@[simp] lemma fullTime_one : fullTime 1=1 := Real.smoothTransition.one

def fullTimeBump : ContDiffBump (0:ℝ) := ⟨2,3,by norm_num,by norm_num⟩
def fullCoefficient (J : Phase n → End n) (v : ℝ × Phase n) : End n :=
  fullTimeBump v.1 • (interpolateJ (J v.2) (fullTime v.1)-standardJ n)

variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
include hJs hJ in
lemma fullCoefficient_smooth : ContDiff ℝ ∞ (fullCoefficient J) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  have ht : -1<fullTime v.1 ∧ fullTime v.1≤1 :=
    ⟨lt_of_lt_of_le (by norm_num) (fullTime_range v.1).1,(fullTime_range v.1).2⟩
  have hh := contDiffAt_interpolateJ_initial (hJs.contDiffAt.comp v contDiffAt_snd)
    (fullTime_smooth.contDiffAt.comp v contDiffAt_fst) (hJ v.2) ht
  exact (fullTimeBump.contDiff.contDiffAt.comp v contDiffAt_fst).smul (hh.sub contDiffAt_const)

include hJ in
lemma fullCoefficient_zero (x : Phase n) : fullCoefficient J (0,x)=0 := by
  simp only [fullCoefficient,fullTime_zero,interpolateJ_zero (hJ x),sub_self,smul_zero]

lemma fullCoefficient_compact (hJc : HasCompactSupport (fun x => J x-standardJ n)) :
    HasCompactSupport (fullCoefficient J) := by
  apply (fullTimeBump.hasCompactSupport.prod hJc).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport _ |>.prod (isClosed_tsupport _))
  intro v hv
  constructor
  · by_contra hn
    have hz := image_eq_zero_of_notMem_tsupport hn
    apply hv
    change fullTimeBump v.1 • (interpolateJ (J v.2) (fullTime v.1)-standardJ n)=0
    rw [hz,zero_smul]
  · by_contra hn
    have hz : J v.2=standardJ n := sub_eq_zero.mp
      (image_eq_zero_of_notMem_tsupport (f := fun x => J x-standardJ n) hn)
    apply hv
    change fullTimeBump v.1 • (interpolateJ (J v.2) (fullTime v.1)-standardJ n)=0
    rw [hz,interpolateJ_standard_initial
      ⟨lt_of_lt_of_le (by norm_num) (fullTime_range _).1,(fullTime_range _).2⟩,sub_self,smul_zero]

lemma fullCoefficient_outside {B : ℝ} (hstd : ∀ x, B<‖x‖ → J x=standardJ n) :
    ∀ t x, B<‖x‖ → fullCoefficient J (t,x)=0 := by
  intro t x hx
  simp only [fullCoefficient,hstd x hx,interpolateJ_standard_initial
    ⟨lt_of_lt_of_le (by norm_num) (fullTime_range _).1,(fullTime_range _).2⟩,sub_self,smul_zero]

lemma fullCoefficient_exact {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x : Phase n) :
    standardJ n+fullCoefficient J (t,x)=lineHomotopy J (fullTime t) x := by
  have hb : t∈Metric.closedBall (0:ℝ) fullTimeBump.rIn := by
    rw [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact ht.2.trans (by norm_num [fullTimeBump])
  rw [fullCoefficient,fullTimeBump.one_of_mem_closedBall hb,one_smul]
  change standardJ n+(interpolateJ (J x) (fullTime t)-standardJ n)=_
  abel

include hJ in
lemma fullCoefficient_compatible {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x : Phase n) :
    Compatible (standardJ n+fullCoefficient J (t,x)) := by
  rw [fullCoefficient_exact ht]
  exact lineHomotopy_compatible hJ (fullTime_range t) x

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance cmn1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance cmn2 : NormedSpace ℝ (COne ℂ E) := inferInstance

omit [CompleteSpace E] in
lemma compact_marked_bounds [CompleteSpace E] {K : Set (COne ℂ E)} (hK : IsCompact K) (p q : E)
    (ha : ∀ w∈K,markedSlope p q w≠0) :
    ∃ M δ : ℝ,0<M ∧ 0<δ ∧ ∀ w∈K,‖w‖<M ∧ δ<‖markedSlope p q w‖ := by
  obtain ⟨M,hM,hMb⟩ := hK.isBounded.exists_pos_norm_le
  by_cases hn : K.Nonempty
  · obtain ⟨w,hw,hmin⟩ := hK.exists_isMinOn hn (markedSlope_continuous p q).norm.continuousOn
    have hp : 0<‖markedSlope p q w‖ := norm_pos_iff.mpr (ha w hw)
    refine ⟨M+1,‖markedSlope p q w‖/2,by linarith,half_pos hp,?_⟩
    intro v hv
    exact ⟨lt_of_le_of_lt (hMb v hv) (by linarith),
      (half_lt_self hp).trans_le (hmin hv)⟩
  · exact ⟨1,1,by norm_num,by norm_num,fun w hw => (hn ⟨w,hw⟩).elim⟩

def markedBoundedDomain (p q : E) (M δ : ℝ) : Set (COne ℂ E) :=
  {w | ‖w‖<M ∧ δ<‖markedSlope p q w‖}

omit [CompleteSpace E] in
lemma markedBoundedDomain_open [CompleteSpace E] (p q : E) (M δ : ℝ) : IsOpen (markedBoundedDomain p q M δ) :=
  (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const (markedSlope_continuous p q).norm)

omit [CompleteSpace E] in
lemma markedBoundedDomain_slope [CompleteSpace E] {p q : E} {M δ : ℝ} (hδ : 0<δ)
    {w : COne ℂ E} (hw : w∈markedBoundedDomain p q M δ) : markedSlope p q w≠0 :=
  norm_pos_iff.mp (hδ.trans hw.2)

omit [CompleteSpace E] in
lemma bounded_marked_uniform_escape [CompleteSpace E] (p q : E) {M δ B : ℝ}
    (hM : 0<M) (hδ : 0<δ) (hB : 0≤B) :
    ∃ R : ℝ,0<R ∧ ∀ w∈markedBoundedDomain p q M δ,
      ∀ h : COne ℂ E,‖h‖<δ/2 →∀ z : ℂ,R≤‖z‖ →
        B<‖markedCurve p q (w+h) z‖ ∧
        ∀ b : ContDiffBump (0:ℂ),B<‖truncatedCurve b p q w h z‖ := by
  let ε := δ/2
  have hε : 0<ε := half_pos hδ
  let R := (B+‖p‖+M+ε+1)/ε
  have hR : 0<R := by dsimp [R]; positivity
  refine ⟨R,hR,?_⟩
  intro w hw h hh z hz
  have hsl : ε≤‖markedSlope p q w‖-‖h‖ := by
    dsimp only [ε]
    linarith [hw.2]
  have hm : R*ε≤‖z‖*(‖markedSlope p q w‖-‖h‖) :=
    mul_le_mul hz hsl hε.le (norm_nonneg z)
  have he : R*ε=B+‖p‖+M+ε+1 := div_mul_cancel₀ _ hε.ne'
  rw [he] at hm
  have hl : B<‖z‖*(‖markedSlope p q w‖-‖h‖)-‖p‖-‖w‖-‖h‖ := by
    change ‖h‖<ε at hh
    linarith [hw.1]
  exact ⟨hl.trans_le (markedCurve_norm_lower p q w h z),
    fun b => hl.trans_le (truncatedCurve_norm_lower b p q w h z)⟩

lemma bounded_marked_escape_neighborhood (p q : E) {M δ B R : ℝ} (hδ : 0<δ)
    (he : ∀ w∈markedBoundedDomain p q M δ,∀ h : COne ℂ E,‖h‖<δ/2 →∀ z : ℂ,R≤‖z‖ →
      B<‖markedCurve p q (w+h) z‖ ∧ ∀ b : ContDiffBump (0:ℂ),B<‖truncatedCurve b p q w h z‖)
    (b : ContDiffBump (0:ℂ)) (hRb : R≤b.rIn)
    {w : COne ℂ E} (hw : w∈markedBoundedDomain p q M δ) :
    MarkedEscapeNeighborhood b p q w B :=
  markedEscape_of_uniform p q w B (δ/2) R (half_pos hδ) (he w hw) b hRb

omit [CompleteSpace E] in
lemma marked_escape_neighborhood_base [CompleteSpace E] (b : ContDiffBump (0:ℂ)) (p q : E)
    {w : COne ℂ E} {B : ℝ} (he : MarkedEscapeNeighborhood b p q w B) :
    ∀ z,b.rIn≤‖z‖ →B<‖markedCurve p q w z‖ := by
  intro z hz
  have hh := (he.self_of_nhds z hz).1
  simpa only [Submodule.coe_zero,add_zero] using hh

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion

private lemma normed_t2 (X : Type*) [NormedAddCommGroup X] : T2Space X := inferInstance

variable {n : ℕ}
local instance fmp1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance fmp2 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance

local instance fmp3 : MetricSpace (COne ℂ (Phase n)) := (fmp1 (n := n)).toMetricSpace
local instance fmp4 : T2Space (COne ℂ (Phase n)) := normed_t2 _

def fullMarkedZeroSet (J : Phase n → End n) (p q : Phase n) : Set (ℝ × COne ℂ (Phase n)) :=
  {v | v.1∈Icc (0:ℝ) 1 ∧ (fullTime v.1,v.2)∈exactMarkedZeroSet J p q}

lemma full_marked_compact_of_exact {J : Phase n → End n} {p q : Phase n}
    (hc : IsCompact (exactMarkedZeroSet J p q)) : IsCompact (fullMarkedZeroSet J p q) := by
  have hK := hc.image continuous_snd
  have hg : Continuous (fun v : ℝ × COne ℂ (Phase n) => (fullTime v.1,v.2)) :=
    (fullTime_smooth.continuous.comp continuous_fst).prodMk continuous_snd
  have hcl : IsClosed (fullMarkedZeroSet J p q) :=
    (isClosed_Icc.preimage continuous_fst).inter (hc.isClosed.preimage hg)
  apply (isCompact_Icc.prod hK).of_isClosed_subset hcl
  intro v hv
  exact ⟨hv.1,⟨(fullTime v.1,v.2),hv.2,rfl⟩⟩

variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n))
  {S T : ℝ} (hST : S<T) (hT : T<1) (hout : ∀ x,S<capacity x →J x=standardJ n)
  {p q : Phase n} (hpq : p≠q)

include hJs hJ hJc hST hT hout hpq in
lemma full_marked_zeroSet_compact : IsCompact (fullMarkedZeroSet J p q) :=
  full_marked_compact_of_exact (exact_marked_zeroSet_compact hJs hJ hJc hST hT hout hpq)

include hJs hJ hJc hST hT hout hpq in
lemma exact_marked_common_neighborhood :
    ∃ (B M δ : ℝ) (b : ContDiffBump (0:ℂ)),0≤B ∧ 0<M ∧ 0<δ ∧
      (∀ x,B<‖x‖ →J x=standardJ n) ∧
      (∀ v∈exactMarkedZeroSet J p q,
        v.2∈markedBoundedDomain p q M δ ∧
        v.2∈markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) ∧
      (∀ w∈markedBoundedDomain p q M δ,MarkedEscapeNeighborhood b p q w B) := by
  obtain ⟨B₀,hB₀⟩ := compact_structure_norm_standard hJc
  let B := max B₀ 0
  have hB : 0≤B := le_max_right _ _
  have hstd : ∀ x,B<‖x‖ →J x=standardJ n := fun x hx => hB₀ x ((le_max_left _ _).trans_lt hx)
  let K := Prod.snd '' exactMarkedZeroSet J p q
  have hK : IsCompact K := (exact_marked_zeroSet_compact hJs hJ hJc hST hT hout hpq).image continuous_snd
  have hKa : ∀ w∈K,markedSlope p q w≠0 := by
    rintro w ⟨v,hv,rfl⟩
    exact represented_line_slope_nonzero v.2 hv.2.2
  obtain ⟨M,δ,hM,hδ,hbound⟩ := compact_marked_bounds hK p q hKa
  obtain ⟨R,hR,hesc⟩ := bounded_marked_uniform_escape p q hM hδ hB
  let b : ContDiffBump (0:ℂ) := ⟨R,R+1,hR,by linarith⟩
  have hn : ∀ w∈markedBoundedDomain p q M δ,MarkedEscapeNeighborhood b p q w B :=
    fun w hw => bounded_marked_escape_neighborhood p q hδ hesc b (le_refl R) hw
  refine ⟨B,M,δ,b,hB,hM,hδ,hstd,?_,hn⟩
  intro v hv
  have hw : v.2∈markedBoundedDomain p q M δ := hbound v.2 ⟨v,hv,rfl⟩
  refine ⟨hw,hv.2.1,?_⟩
  have hstd' : ∀ x,B<‖x‖ →lineHomotopy J v.1 x=complexI (E := Phase n) := by
    intro x hx
    change interpolateJ (J x) v.1=standardJ n
    rw [hstd x hx]
    exact interpolateJ_standard hv.1
  have hcr : ∀ z,fderiv ℝ (markedCurve p q v.2) z Complex.I=
      lineHomotopy J v.1 (markedCurve p q v.2 z) (fderiv ℝ (markedCurve p q v.2) z 1) := by
    intro z
    simpa only [mul_one] using (hv.2.2.2.1 z).2 1
  have he0 : ∀ z,b.rOut≤‖z‖ → B<‖markedCurve p q v.2 z‖ := by
    intro z hz
    exact marked_escape_neighborhood_base b p q (hn v.2 hw) z
      (b.rIn_lt_rOut.le.trans hz)
  exact freeModel_of_elliptic hstd' p (markedSlope p q v.2) v.2 hcr he0

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
section RealConstant
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
local instance pcConst1 : NormedAddCommGroup (COne ℂ F) := inferInstance
local instance pcConst2 : NormedSpace ℝ (COne ℂ F) := inferInstance
local instance pcConst3 : NormedAddCommGroup (HMap ℂ F) := inferInstance
local instance pcConst4 : NormedSpace ℝ (HMap ℂ F) := inferInstance
local instance pcConst5 : NormedAddCommGroup (HMap ℂ (ℂ →L[ℝ] F)) := inferInstance
local instance pcConst6 : NormedSpace ℝ (HMap ℂ (ℂ →L[ℝ] F)) := inferInstance

def realConstantJet (v : F) : COne ℂ F :=
  ⟨(const _ v,0),fun z => hasFDerivAt_const v z⟩
@[simp] lemma realConstantJet_value (v : F) (z : ℂ) : cValue (realConstantJet v) z=v := rfl
lemma realConstantJet_norm (v : F) : ‖realConstantJet v‖≤‖v‖ := by
  change max ‖const _ v‖ ‖(0 : HMap ℂ (ℂ →L[ℝ] F))‖≤‖v‖
  rw [norm_zero]
  exact max_le (const_norm_le v) (norm_nonneg v)

def realConstantJetCLM : F →L[ℝ] COne ℂ F :=
  LinearMap.mkContinuous
    { toFun := realConstantJet
      map_add' := fun u v => by apply cValue_ext; intro z; rfl
      map_smul' := fun c v => by apply cValue_ext; intro z; rfl }
    1 (by intro v; change ‖realConstantJet v‖≤1*‖v‖; rw [one_mul]; exact realConstantJet_norm v)
end RealConstant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance pcInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance pcInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance pcInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance pcInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance pcInst5 : NormedAddCommGroup (COne ℂ (ℝ × E)) := inferInstance
local instance pcInst6 : NormedSpace ℝ (COne ℂ (ℝ × E)) := inferInstance
local instance pcInst7 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance pcInst8 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance pcInst9 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance pcInst10 : NormedSpace ℝ (HMap ℂ E) := inferInstance
variable (b : ContDiffBump (0:ℂ)) (p q : E)
local instance pcInst11 : NormedAddCommGroup (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance pcInst12 : NormedSpace ℝ (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance pcInst13 : NormedAddCommGroup (ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance pcInst14 : NormedSpace ℝ (ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance pcInst15 : AddCommGroup (ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (pcInst13 b).toAddCommGroup
local instance pcInst16 : Module ℝ (ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (pcInst14 b).toModule

def parameterJet : ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut) →L[ℝ] COne ℂ (ℝ × E) :=
  ((realConstantJetCLM (F := ℝ × E)).comp (ContinuousLinearMap.inl ℝ ℝ E)).comp
      (ContinuousLinearMap.fst ℝ ℝ (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))) +
    ((mapJetBilinear (D := ℂ) (E := E) (F := ℝ × E) (ContinuousLinearMap.inr ℝ ℝ E)).comp (truncateShift (E := E) b)).comp
      ((markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)).subtypeL.comp
        (ContinuousLinearMap.snd ℝ ℝ (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))))

omit [CompleteSpace E] in
lemma parameterJet_value [CompleteSpace E] (v : ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) (z : ℂ) :
    cValue (parameterJet (E := E) b v) z=(v.1,cValue (truncateShift b v.2.val) z) := by
  change (v.1,0)+(0,cValue (truncateShift b v.2.val) z)=(v.1,cValue (truncateShift b v.2.val) z)
  simp only [Prod.mk_add_mk,zero_add,add_zero]

def parameterSlope : ℂ →L[ℝ] ℝ × E :=
  (ContinuousLinearMap.inr ℝ ℝ E).comp (complexSlope (q-p))

variable {P : ℝ × E → E →L[ℝ] E} (hP : BoundedCThree P)

def parameterCoefficient (v : ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) : HMap ℂ (E →L[ℝ] E) :=
  superpose hP (affine_differentiable (0,p) (parameterSlope p q)) (norm_nonneg _)
    (affine_fderiv_bound (0,p) (parameterSlope p q)) (parameterJet (E := E) b v)

lemma parameterCoefficient_value (v : ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) (z : ℂ) :
    valueCLM _ (parameterCoefficient b p q hP v) z=P (v.1,truncatedCurve b p q 0 v.2.val z) := by
  change P (affine (0,p) (parameterSlope p q) z+cValue (parameterJet (E := E) b v) z)=_
  rw [parameterJet_value]
  congr 1
  have hz0 : cValue (0 : COne ℂ E) 1=0 := rfl
  simp only [affine,parameterSlope,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,
    complexSlope_apply,Prod.mk_add_mk,zero_add,truncatedCurve,affineCurve,
    markedSlope,hz0,sub_zero]

omit [CompleteSpace E] in
lemma parameterCoefficient_contDiff [CompleteSpace E] (hPc : HasCompactSupport P) : ContDiff ℝ ∞ (parameterCoefficient b p q hP) := by
  have hs := superpose_contDiff hP (affine_differentiable (0,p) (parameterSlope p q)) (norm_nonneg _)
    (affine_fderiv_bound (0,p) (parameterSlope p q)) 0 (by simpa only [sub_zero] using hPc)
  exact hs.comp (parameterJet (E := E) b).contDiff

end
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance gmc1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance gmc2 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance gmc3 : NormedAddCommGroup (COne ℂ (ℝ × E)) := inferInstance
local instance gmc4 : NormedSpace ℝ (COne ℂ (ℝ × E)) := inferInstance
local instance gmc5 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance gmc6 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance gmc7 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance gmc8 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
variable (b₁ : ContDiffBump (0:ℂ)) (p q : E)

def globalMarkedJet (w : COne ℂ E) : COne ℂ E :=
  realConstantJet p+cutoffSlope b₁ (markedSlope p q w)+w

omit [CompleteSpace E] in
lemma globalMarkedJet_contDiff [CompleteSpace E] : ContDiff ℝ ∞ (globalMarkedJet b₁ p q) := by
  have hs : ContDiff ℝ ∞ (markedSlope p q : COne ℂ E → E) :=
    contDiff_const.sub (jetEval (E := E) 1).contDiff
  exact (contDiff_const.add ((cutoffSlope (E := E) b₁).contDiff.comp hs)).add contDiff_id

omit [CompleteSpace E] in
lemma globalMarkedJet_value [CompleteSpace E] (w : COne ℂ E) (z : ℂ) :
    cValue (globalMarkedJet b₁ p q w) z=p+b₁ z • (z • markedSlope p q w)+cValue w z := by
  change p+cValue (cutoffSlope b₁ (markedSlope p q w)) z+cValue w z=_
  rw [cutoffSlope_value]

lemma globalMarkedJet_eq_marked (w : COne ℂ E) {z : ℂ}
    (hz : z∈Metric.closedBall (0:ℂ) b₁.rIn) :
    cValue (globalMarkedJet b₁ p q w) z=markedCurve p q w z := by
  rw [globalMarkedJet_value,b₁.one_of_mem_closedBall hz,one_smul]
  rfl

def globalParameterJet (v : ℝ × COne ℂ E) : COne ℂ (ℝ × E) :=
  realConstantJet (v.1,0)+
    mapJetBilinear (D := ℂ) (E := E) (F := ℝ × E)
      (ContinuousLinearMap.inr ℝ ℝ E) (globalMarkedJet b₁ p q v.2)

lemma globalParameterJet_contDiff : ContDiff ℝ ∞ (globalParameterJet b₁ p q) := by
  have ht : ContDiff ℝ ∞ (fun v : ℝ × COne ℂ E =>
      realConstantJet (v.1,(0:E))) :=
    (realConstantJetCLM (F := ℝ × E)).contDiff.comp
      ((ContinuousLinearMap.inl ℝ ℝ E).contDiff.comp contDiff_fst)
  have hw : ContDiff ℝ ∞ (fun v : ℝ × COne ℂ E =>
      mapJetBilinear (D := ℂ) (E := E) (F := ℝ × E)
      (ContinuousLinearMap.inr ℝ ℝ E) (globalMarkedJet b₁ p q v.2)) :=
    (mapJetBilinear (D := ℂ) (E := E) (F := ℝ × E)
      (ContinuousLinearMap.inr ℝ ℝ E)).contDiff.comp ((globalMarkedJet_contDiff b₁ p q).comp contDiff_snd)
  exact ht.add hw

omit [CompleteSpace E] in
lemma globalParameterJet_value [CompleteSpace E] (v : ℝ × COne ℂ E) (z : ℂ) :
    cValue (globalParameterJet b₁ p q v) z=(v.1,cValue (globalMarkedJet b₁ p q v.2) z) := by
  change (v.1,0)+(0,cValue (globalMarkedJet b₁ p q v.2) z)=_
  simp only [Prod.mk_add_mk,zero_add,add_zero]

omit [CompleteSpace E] in
lemma global_zero_derivative_bound [CompleteSpace E] (z : ℂ) :
    ‖fderiv ℝ (fun _ : ℂ => (0 : ℝ × E)) z‖≤0 := by simp

variable {P : ℝ × E → E →L[ℝ] E} (hP : BoundedCThree P)
def globalCoefficient (v : ℝ × COne ℂ E) : HMap ℂ (E →L[ℝ] E) :=
  superpose hP (differentiable_const (0 : ℝ × E)) (le_refl (0:ℝ))
    (global_zero_derivative_bound (E := E)) (globalParameterJet b₁ p q v)

lemma globalCoefficient_value (v : ℝ × COne ℂ E) (z : ℂ) :
    valueCLM _ (globalCoefficient b₁ p q hP v) z=P (v.1,cValue (globalMarkedJet b₁ p q v.2) z) := by
  change P (0+cValue (globalParameterJet b₁ p q v) z)=_
  rw [zero_add,globalParameterJet_value]

lemma globalCoefficient_contDiff (hPc : HasCompactSupport P) :
    ContDiff ℝ ∞ (globalCoefficient b₁ p q hP) := by
  have hs : ContDiff ℝ ∞ (superpose (D := ℂ) hP (differentiable_const (0 : ℝ × E))
      (le_refl (0:ℝ)) (global_zero_derivative_bound (E := E))) := superpose_contDiff hP (differentiable_const (0 : ℝ × E)) (le_refl (0:ℝ))
    (global_zero_derivative_bound (E := E)) 0 (by simpa only [sub_zero] using hPc)
  exact hs.comp (globalParameterJet_contDiff b₁ p q)

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
