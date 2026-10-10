import OAI.Analysis.RotationWeights.SamplingStage

namespace OAI

noncomputable section

namespace CircleSampling

universe uS

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
section

def enumeratedRat (n : ℕ) : ℝ := ((Encodable.decode (α := ℚ) n).getD 0:ℚ)
lemma enumeratedRat_encode (r : ℚ) : enumeratedRat (Encodable.encode r) = (r:ℝ) := by
  simp [enumeratedRat,Encodable.encodek]

lemma closed_interval_avoiding (r : ℝ) {a b : ℝ} (hab : a<b) :
    ∃ d e : ℝ, d<e ∧ Icc d e ⊆ Ioo a b ∧ r∉Icc d e := by
  by_cases hr : r ≤ (a+b)/2
  · refine ⟨(a+3*b)/4,(a+7*b)/8,by linarith,?_,?_⟩
    · intro x hx; constructor <;> linarith [hx.1,hx.2]
    · intro hr'; linarith [hr'.1]
  · refine ⟨(7*a+b)/8,(3*a+b)/4,by linarith,?_,?_⟩
    · intro x hx; constructor <;> linarith [hx.1,hx.2]
    · intro hr'; linarith [hr'.2]

lemma irrational_in_nested_intervals (a b : ℕ → ℝ)
    (hab : ∀ n, a n < b n) (hnest : ∀ n, Icc (a (n+1)) (b (n+1)) ⊆ Ioo (a n) (b n))
    (havoid : ∀ n, enumeratedRat n ∉ Icc (a (n+1)) (b (n+1))) :
    ∃ θ : ℝ, Irrational θ ∧ (∀ n, θ∈Icc (a n) (b n)) ∧ θ∈Ioo (a 0) (b 0) := by
  obtain ⟨θ,hθ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => Icc (a n) (b n)) (fun n => (hnest n).trans Ioo_subset_Icc_self)
    (fun n => nonempty_Icc.mpr (hab n).le) isCompact_Icc (fun _ => isClosed_Icc)
  have hm : ∀ n, θ∈Icc (a n) (b n) := Set.mem_iInter.mp hθ
  refine ⟨θ,?_,hm,hnest 0 (hm 1)⟩
  rintro ⟨r,hr⟩
  apply havoid (Encodable.encode r)
  rw [enumeratedRat_encode,hr]
  exact hm _

lemma exists_recursive_chain {S : Type uS} (V : ℕ → S → Prop) (R : ℕ → S → S → Prop)
    (s0 : S) (h0 : V 0 s0)
    (step : ∀ n s, V n s → ∃ t, V (n+1) t ∧ R n s t) :
    ∃ s : ℕ → S, s 0=s0 ∧ (∀ n,V n (s n)) ∧ ∀ n,R n (s n) (s (n+1)) := by
  let next (n : ℕ) (s : {s // V n s}) : {s // V (n+1) s} :=
    ⟨(step n s.1 s.2).choose,(step n s.1 s.2).choose_spec.1⟩
  let seq : (n : ℕ) → {s // V n s} := Nat.rec ⟨s0,h0⟩ next
  refine ⟨fun n => (seq n).1,rfl,fun n => (seq n).2,?_⟩
  intro n
  exact (step n (seq n).1 (seq n).2).choose_spec.2

lemma prefix_persistent (d : ℕ → ℕ) (q : ℕ → ℕ → ℕ)
    (hd : Monotone d) (hq : ∀ j i, i≤d j → q (j+1) i=q j i)
    {j n i : ℕ} (hjn : j≤n) (hi : i≤d j) : q n i=q j i := by
  induction n,hjn using Nat.le_induction with
  | base => rfl
  | succ n hjn ih => rw [hq n i (hi.trans (hd hjn)),ih]

lemma diagonal_prefix_eq (d : ℕ → ℕ) (q : ℕ → ℕ → ℕ)
    (hd : Monotone d) (hlen : ∀ j,j≤d j) (hq : ∀ j i, i≤d j → q (j+1) i=q j i)
    {j i : ℕ} (hi : i≤d j) : q i i=q j i := by
  rcases le_total j i with hji|hij
  · exact prefix_persistent d q hd hq hji hi
  · exact (prefix_persistent d q hd hq hij (hlen i)).symm

lemma endpoints_sum (m : ℕ → ℕ) (d : ℕ → ℕ) (h0 : d 0=0)
    (hs : ∀ j,d (j+1)=d j+m j) (j : ℕ) : d j=∑ s∈Finset.range j,m s := by
  induction j with
  | zero => simpa using h0
  | succ j ih => rw [hs,Finset.sum_range_succ,ih]

lemma endpoints_growth (m d : ℕ → ℕ) (hm : ∀ j, 0 < m j) (hs : ∀ j,d (j+1)=d j+m j) :
    StrictMono d ∧ ∀ j,j≤d j := by
  have hd : StrictMono d := strictMono_nat_of_lt_succ (fun j => by rw [hs]; exact Nat.lt_add_of_pos_right (hm j))
  refine ⟨hd,?_⟩
  intro j
  induction j with
  | zero => omega
  | succ j ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hd (Nat.lt_succ_self j)))


def extendPrefix (d : ℕ) (old block : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i≤ d then old i else block (i-d)
lemma extendPrefix_old (d : ℕ) (old block : ℕ → ℕ) {i : ℕ} (hi : i≤ d) :
    extendPrefix d old block i=old i := ite_eq_left hi
lemma extendPrefix_block (d : ℕ) (old block : ℕ → ℕ) (h0 : block 0=old d) (k : ℕ) :
    extendPrefix d old block (d+k)=block k := by
  by_cases hk : k=0
  · subst k; simp [extendPrefix,h0]
  · rw [extendPrefix,ite_eq_right (by omega),Nat.add_sub_cancel_left]
lemma extendPrefix_pos (d m : ℕ) (old block : ℕ → ℕ)
    (ho : ∀ i≤ d,0< old i) (hb : ∀ i≤ m,0< block i) {i : ℕ} (hi : i≤ d+m) :
    0< extendPrefix d old block i := by
  by_cases h : i≤ d
  · rw [extendPrefix_old d old block h]; exact ho i h
  · rw [extendPrefix,ite_eq_right h]; exact hb _ (by omega)
lemma extendPrefix_dvd (d m : ℕ) (old block : ℕ → ℕ) (h0 : block 0=old d)
    (ho : ∀ i< d,old i∣old (i+1)) (hb : ∀ i< m,block i∣block (i+1)) {i : ℕ} (hi : i< d+m) :
    extendPrefix d old block i∣extendPrefix d old block (i+1) := by
  by_cases h : i< d
  · rw [extendPrefix_old d old block (by omega),extendPrefix_old d old block (by omega)]
    exact ho i h
  · have he : i=d+(i-d) := by omega
    rw [he,extendPrefix_block d old block h0]
    rw [show d+(i-d)+1=d+((i-d)+1) by omega,extendPrefix_block d old block h0]
    exact hb _ (by omega)
lemma extendPrefix_lt (d m : ℕ) (old block : ℕ → ℕ) (h0 : block 0=old d)
    (ho : ∀ i< d,old i< old (i+1)) (hb : ∀ i< m,block i< block (i+1)) {i : ℕ} (hi : i< d+m) :
    extendPrefix d old block i< extendPrefix d old block (i+1) := by
  by_cases h : i< d
  · rw [extendPrefix_old d old block (by omega),extendPrefix_old d old block (by omega)]
    exact ho i h
  · have he : i=d+(i-d) := by omega
    rw [he,extendPrefix_block d old block h0]
    rw [show d+(i-d)+1=d+((i-d)+1) by omega,extendPrefix_block d old block h0]
    exact hb _ (by omega)
end

open Set
section
def positiveArc (h : CircleX) (r : ℝ) : Set CircleX :=
  {x | x-h ∈ ((↑) : ℝ → CircleX) '' Ioo 0 r}
lemma positiveArc_open (h : CircleX) (r : ℝ) : IsOpen (positiveArc h r) := by
  exact (QuotientAddGroup.isOpenMap_coe (Ioo 0 r) isOpen_Ioo).preimage (continuous_id.sub continuous_const)
lemma positiveArc_nonempty (h : CircleX) {r : ℝ} (hr : 0<r) : (positiveArc h r).Nonempty := by
  refine ⟨((r/2:ℝ):CircleX)+h,?_⟩
  change (((r/2:ℝ):CircleX)+h)-h ∈ ((↑) : ℝ → CircleX) '' Ioo 0 r
  rw [add_sub_cancel_right]
  exact ⟨r/2,⟨by linarith,by linarith⟩,rfl⟩
lemma positiveArc_mem {h x : CircleX} {r : ℝ} (hx : x∈positiveArc h r) (hr : r≤1) :
    ∃ t : ℝ, t∈Ioo 0 r ∧ (t:CircleX)=x-h ∧ Int.fract t=t := by
  obtain ⟨t,ht,he⟩ := hx
  exact ⟨t,ht,he,(Int.fract_eq_self).mpr ⟨ht.1.le,ht.2.trans_le hr⟩⟩

open Set Filter MeasureTheory ContinuousCircleWeight ContinuousCircleWeight.Sampling
open scoped Topology

structure ScaleState where
  K : ℕ
  d : ℕ
  G : ℝ
  E : ℝ
  Lprev : ℝ
  a : ℝ
  b : ℝ
  q : ℕ → ℕ

structure ScaleState.Valid (s : ScaleState) : Prop where
  Kpos : 0 < s.K
  Gge : 1 ≤ s.G
  Ege : 0 ≤ s.E
  Lge : 1 ≤ s.Lprev
  qzero : s.q 0=1
  qpos : ∀ i≤ s.d, 0 < s.q i
  qdvd : ∀ i< s.d, s.q i∣s.q (i+1)
  qlt : ∀ i< s.d, s.q i< s.q (i+1)
  ab : s.a< s.b

def gridTolerance (j : ℕ) (s : ScaleState) : ℝ :=
  1/(10*((j:ℝ)+1)^2*(1+(s.d:ℝ))*(s.q s.d:ℝ))
def gridPoint (s : ScaleState) (a : Fin (s.q s.d)) : CircleX := ((a.val:ℝ)/(s.q s.d:ℝ):ℝ)

def CoefficientBudget (j : ℕ) (s : ScaleState) (ε : ℝ) : Prop :=
  ∀ A : CoefficientPair s.K,
    (∀ i, ‖A.1 i‖ ≤ Real.exp (((s.K:ℝ)+1)*s.E)) →
    (∀ i, ‖A.2 i‖ ≤ Real.exp (((s.K:ℝ)+1)*s.E)) →
    1/((j:ℝ)+1) ≤ ‖A.1 (centerIndex s.K)‖ →
    1/((j:ℝ)+1) ≤ ‖A.2 (centerIndex s.K)‖ →
    ∃ n : Fin (2*s.K+1), ε≤‖lowProduct s.K A n‖

structure ScaleStep (j : ℕ) (s : ScaleState) where
  ε : ℝ
  L : ℝ
  Gnext : ℝ
  εpos : 0 < ε
  coefficients : CoefficientBudget j s ε
  Lge : 1 ≤ L
  Lprev : s.Lprev ≤ L
  exponential : (2*(s.K:ℝ)+1)*3*Real.exp (-L/10000) ≤ ε/((j:ℝ)+1)
  Gge : 1 ≤ Gnext
  bridge : L ≤ kappa (j+1)*Real.sqrt Gnext
  m : ℕ
  numeric : StageNumerics j s.K s.G L Gnext m
  samples : Fin (s.q s.d) → Finset ℤ
  samples_nonempty : ∀ t, (samples t).Nonempty
  samples_bounds : ∀ t n, n∈samples t →
    (m:ℝ)^((7:ℝ)/10*m)/2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ (m:ℝ)^((7:ℝ)/10*m)
  q : ℕ → ℕ
  qzero : q 0=s.q s.d
  qpos : ∀ i≤ m, 0 < q i
  qratio : ∀ i< m, q i∣q (i+1) ∧ 100*(m:ℝ) < (q (i+1):ℝ)/q i
  a : ℝ
  b : ℝ
  ab : a< b
  interval : Icc a b ⊆ Ioo s.a s.b
  avoid : enumeratedRat j∉Icc a b
  phases : ∀ θ∈Icc a b, ∀ i : Fin m,
    Int.fract ((q (i+1):ℝ)*θ)∈Ioo (1/((m:ℝ)*s.K)) (2/((m:ℝ)*s.K))
  cover : ∀ θ∈Icc a b, ∀ k : ℤ,
    ((m:ℝ)*s.K)/4 ≤ |(k:ℝ)| → |(k:ℝ)| ≤ (m:ℝ)^((4:ℝ)/5*m) →
    (m:ℝ)/20 ≤ ((Finset.univ.filter fun i : Fin m =>
      Int.fract ((q (i+1):ℝ)*θ) ∉ phaseFailure ((m:ℝ)^(-(19:ℝ)/20)) k).card:ℝ)
  orbits : ∀ θ∈Icc a b, ∀ t n, n∈samples t → n•(θ:CircleX)∈positiveArc (gridPoint s t) (gridTolerance j s)
  energies : ∀ θ∈Icc a b, ∀ t (positive : Bool),
    (∫ x : CircleX, (idealAverage positive (scaleEll m) (scaleAlpha m)
      (fun n : samples t => (n.val:ℝ))
      (characterCurve (fun i : Fin m => (q (i+1):ℤ)) x)
      (fun i => Int.fract ((q (i+1):ℝ)*θ))-1)^2) < 1/((j:ℝ)+1)^2

def ScaleStep.C {j : ℕ} {s : ScaleState} (t : ScaleStep j s) : ℝ := max t.L ((s.K:ℝ)^2)

def ScaleStep.next {j : ℕ} {s : ScaleState} (t : ScaleStep j s) : ScaleState where
  K := nextWindow t.m
  d := s.d+t.m
  G := t.Gnext
  E := s.E+t.C*t.m
  Lprev := t.L
  a := t.a
  b := t.b
  q := extendPrefix s.d s.q t.q

lemma ScaleStep.mpos {j : ℕ} {s : ScaleState} (t : ScaleStep j s) : 0 < t.m :=
  lt_of_lt_of_le (by norm_num) t.numeric.1

lemma ScaleStep.qstrict {j : ℕ} {s : ScaleState} (t : ScaleStep j s) {i : ℕ} (hi : i< t.m) :
    t.q i< t.q (i+1) := by
  have hp : 0 < (t.q i:ℝ) := Nat.cast_pos.mpr (t.qpos i hi.le)
  have hm : 1 ≤ (t.m:ℝ) := by exact_mod_cast t.mpos
  have hh : 1 < (t.q (i+1):ℝ)/t.q i := by linarith [(t.qratio i hi).2]
  have hh' : (t.q i:ℝ)< t.q (i+1) := by simpa using (lt_div_iff₀ hp).mp hh
  exact_mod_cast hh'

lemma ScaleStep.next_valid {j : ℕ} {s : ScaleState} (t : ScaleStep j s) (hs : s.Valid) : t.next.Valid := by
  refine ⟨?_,t.Gge,?_,t.Lge,?_,?_,?_,?_,t.ab⟩
  · have hh := t.numeric.2.2.2.2.2.2.1
    change 0 < nextWindow t.m
    omega
  · change 0≤ s.E+t.C*t.m
    have hC : 0 ≤ t.C := by
      change 0 ≤ max t.L ((s.K:ℝ)^2)
      exact le_trans (show (0:ℝ) ≤ t.L by linarith [t.Lge]) (le_max_left t.L ((s.K:ℝ)^2))
    exact add_nonneg hs.Ege (mul_nonneg hC (Nat.cast_nonneg _))
  · change extendPrefix s.d s.q t.q 0=1
    rw [extendPrefix_old _ _ _ (Nat.zero_le _),hs.qzero]
  · intro i hi
    exact extendPrefix_pos s.d t.m s.q t.q hs.qpos t.qpos hi
  · intro i hi
    exact extendPrefix_dvd s.d t.m s.q t.q t.qzero hs.qdvd (fun i hi => (t.qratio i hi).1) hi
  · intro i hi
    exact extendPrefix_lt s.d t.m s.q t.q t.qzero hs.qlt (fun _ hi => t.qstrict hi) hi

lemma exists_scale_step (j : ℕ) (s : ScaleState) (hs : s.Valid) : Nonempty (ScaleStep j s) := by
  have hδ : 0 < 1/((j:ℝ)+1) := by positivity
  obtain ⟨ε,hε,hcoeff⟩ := finite_coefficient_bound s.K _ (Real.exp (((s.K:ℝ)+1)*s.E)) hδ (Real.exp_pos _).le
  obtain ⟨L,hL,hLp,hLb⟩ := exists_exponential_budget j s.K hε s.Lprev
  obtain ⟨G,hG,hGb⟩ := exists_bridge_budget j L
  have hr : 0 < gridTolerance j s := by
    unfold gridTolerance
    have hq : 0 < (s.q s.d:ℝ) := Nat.cast_pos.mpr (hs.qpos s.d le_rfl)
    positivity
  obtain ⟨m,hm,_,S,hSn,hSb,q,hq0,hqp,hqr,a,b,hab,hsub,hstage⟩ := exists_sampling_stage
    (fun t : Fin (s.q s.d) => positiveArc (gridPoint s t) (gridTolerance j s))
    (fun _ => positiveArc_open _ _) (fun _ => positiveArc_nonempty _ hr)
    hs.Kpos (show 0 < 1/((j:ℝ)+1)^2 by positivity)
    (StageNumerics j s.K s.G L G) (eventually_StageNumerics j s.K s.G L G)
    hs.ab (hs.qpos s.d le_rfl) (fun m => 100*(m:ℝ))
  obtain ⟨a',b',hab',hsub',havoid⟩ := closed_interval_avoiding (enumeratedRat j) hab
  have hinc : Icc a' b' ⊆ Icc a b := hsub'.trans Ioo_subset_Icc_self
  exact ⟨{
    ε := ε, L := L, Gnext := G, εpos := hε, coefficients := hcoeff,
    Lge := hL, Lprev := hLp, exponential := hLb, Gge := hG, bridge := hGb,
    m := m, numeric := hm, samples := S, samples_nonempty := hSn, samples_bounds := hSb,
    q := q, qzero := hq0, qpos := hqp, qratio := hqr,
    a := a', b := b', ab := hab', interval := hinc.trans hsub, avoid := havoid,
    phases := fun θ hθ => (hstage θ (hinc hθ)).1,
    cover := fun θ hθ => (hstage θ (hinc hθ)).2.1,
    orbits := fun θ hθ => (hstage θ (hinc hθ)).2.2.1,
    energies := fun θ hθ => (hstage θ (hinc hθ)).2.2.2 }⟩

def initialScaleState : ScaleState where
  K := 100
  d := 0
  G := 1
  E := 0
  Lprev := 1
  a := 0
  b := 1
  q := fun _ => 1
lemma initialScaleState_valid : initialScaleState.Valid := by
  constructor <;> simp [initialScaleState]

def chosenScaleStep (j : ℕ) (s : {s : ScaleState // s.Valid}) : ScaleStep j s.1 :=
  Classical.choice (exists_scale_step j s.1 s.2)
def scaleState : ℕ → {s : ScaleState // s.Valid} :=
  Nat.rec ⟨initialScaleState,initialScaleState_valid⟩
    (fun j s => ⟨(chosenScaleStep j s).next,(chosenScaleStep j s).next_valid s.2⟩)
def scaleStep (j : ℕ) : ScaleStep j (scaleState j).1 := chosenScaleStep j (scaleState j)
lemma scaleState_succ (j : ℕ) : (scaleState (j+1)).1=(scaleStep j).next := rfl

lemma exists_global_angle : ∃ θ : ℝ, 0< θ ∧ θ<1 ∧ Irrational θ ∧
    ∀ j,θ∈Icc (scaleStep j).a (scaleStep j).b := by
  obtain ⟨θ,hθ,hmem,h01⟩ := irrational_in_nested_intervals
    (fun j => (scaleState j).1.a) (fun j => (scaleState j).1.b)
    (fun j => (scaleState j).2.ab)
    (fun j => (scaleStep j).interval) (fun j => (scaleStep j).avoid)
  refine ⟨θ,h01.1,h01.2,hθ,?_⟩
  intro j
  exact hmem (j+1)
end

open Set

structure BlockPartition where
  m : ℕ → ℕ
  d : ℕ → ℕ
  zero : d 0=0
  step : ∀ j,d (j+1)=d j+m j
  positive : ∀ j,0 < m j

lemma BlockPartition.strictMono (B : BlockPartition) : StrictMono B.d :=
  strictMono_nat_of_lt_succ (fun j => by rw [B.step]; exact Nat.lt_add_of_pos_right (B.positive j))
lemma BlockPartition.ge (B : BlockPartition) (j : ℕ) : j≤ B.d j := by
  induction j with
  | zero => omega
  | succ j ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (B.strictMono (Nat.lt_succ_self j)))

lemma BlockPartition.exists_unique (B : BlockPartition) (i : ℕ) :
    ∃! j, B.d j≤ i ∧ i< B.d (j+1) := by
  have hex : ∃ j,i< B.d (j+1) := ⟨i,(Nat.lt_succ_self i).trans_le (B.ge (i+1))⟩
  let j := Nat.find hex
  have hj : i< B.d (j+1) := Nat.find_spec hex
  have hlo : B.d j≤ i := by
    by_cases h0 : j=0
    · rw [h0,B.zero]; omega
    · have hfalse : ¬ i< B.d ((j-1)+1) := Nat.find_min hex (by omega : j-1< j)
      have he : j-1+1=j := by omega
      rw [he] at hfalse
      omega
  refine ⟨j,⟨hlo,hj⟩,?_⟩
  intro k hk
  apply le_antisymm
  · by_contra hn
    have hd := B.strictMono.monotone (show j+1≤ k by omega)
    omega
  · by_contra hn
    have hd := B.strictMono.monotone (show k+1≤ j by omega)
    omega

def BlockPartition.number (B : BlockPartition) (i : ℕ) : ℕ := (B.exists_unique i).choose
lemma BlockPartition.number_spec (B : BlockPartition) (i : ℕ) :
    B.d (B.number i)≤ i ∧ i< B.d (B.number i+1) := (B.exists_unique i).choose_spec.1
lemma BlockPartition.number_eq (B : BlockPartition) {i j : ℕ} (hlo : B.d j≤ i) (hhi : i< B.d (j+1)) :
    B.number i=j := ((B.exists_unique i).choose_spec.2 j ⟨hlo,hhi⟩).symm

def BlockPartition.position (B : BlockPartition) (i : ℕ) : Fin (B.m (B.number i)) :=
  ⟨i-B.d (B.number i),by have hh := B.number_spec i; rw [B.step] at hh; omega⟩

def BlockPartition.equiv (B : BlockPartition) : (Σ j,Fin (B.m j)) ≃ ℕ where
  toFun x := B.d x.1+x.2.val
  invFun i := ⟨B.number i,B.position i⟩
  left_inv x := by
    have hn : B.number (B.d x.1+x.2.val)=x.1 := by
      apply B.number_eq (by omega)
      rw [B.step]
      exact Nat.add_lt_add_left x.2.isLt _
    apply Sigma.ext hn
    apply (Fin.heq_ext_iff (congrArg B.m hn)).mpr
    simp [position,hn]
  right_inv i := by
    change B.d (B.number i)+(i-B.d (B.number i))=i
    exact Nat.add_sub_of_le (B.number_spec i).1

lemma BlockPartition.equiv_apply (B : BlockPartition) (j : ℕ) (k : Fin (B.m j)) :
    B.equiv ⟨j,k⟩ = B.d j+k.val := rfl
lemma BlockPartition.number_mono (B : BlockPartition) : Monotone B.number := by
  intro i k hik
  by_contra hh
  have hn : B.number k+1≤ B.number i := by omega
  have hd := B.strictMono.monotone hn
  have hi := B.number_spec i
  have hk := B.number_spec k
  omega

lemma BlockPartition.number_tendsto (B : BlockPartition) : Filter.Tendsto B.number Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro j
  refine ⟨B.d j,fun i hi => ?_⟩
  by_contra hh
  have hn : B.number i+1≤ j := by omega
  have hd := B.strictMono.monotone hn
  have hh' := B.number_spec i
  omega


end CircleSampling

end

end OAI
