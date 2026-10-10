import Mathlib
import OAI.Probability.SKFluctuations.SegmentTest

namespace OAI

/-! Projection Root Estimate. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Hierarchy
open scoped Topology NNReal ENNReal BigOperators

noncomputable def projectionLpConstant (k : ℕ) : ℝ :=
  (1+projectionOrderConstant k)^((2*k+2:ℕ)⁻¹:ℝ)

theorem projectionLpConstant_pos (k : ℕ) : 0 < projectionLpConstant k := by
  apply Real.rpow_pos_of_pos
  dsimp [projectionOrderConstant,subgaussianMomentConstant]
  positivity

theorem projectionLpConstant_pow (k : ℕ) :
    (projectionLpConstant k)^(2*k+2) = 1+projectionOrderConstant k := by
  apply Real.rpow_inv_natCast_pow
  · dsimp [projectionOrderConstant,subgaussianMomentConstant]; positivity
  · omega

 

theorem eventually_finiteSK_projection_root (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Fin n → ℝ)
      (tail : List (GaussianStep (FeatureIndex n)))
      (blocks : List (List (GaussianStep (FeatureIndex n)))) (a D : ℝ),
      0 < a → 0 < D → D ≤ B →
      OrderedSteps a (blocks.flatten++tail) →
      blocks.length = projectionLogBlocks n →
      (∀pre∈blocks, AlignedFieldClock (fieldProjectionDirection n V)
        (D/(projectionLogBlocks n:ℝ)) pre) →
      ∀ x : FeatureIndex n → ℝ,
      ((∫ p, hierarchyCenteredEvenMoment (uniformWeight n) (finiteFeature n)
        (spinProjection n V) tail k
        (forwardEnd blocks.flatten.length (hierarchyIncrements blocks.flatten) x p)
        ∂segmentLaw (uniformWeight n) (finiteFeature n) tail blocks.flatten x)^((2*k+2:ℕ)⁻¹:ℝ)) ≤
      projectionLpConstant k*(Real.log (n:ℝ))^2*projectionEuclideanNorm n V/
        (a*Real.sqrt ((n:ℝ)*D)) := by
  filter_upwards [eventually_finiteSK_projection_log k B,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro V tail blocks a D ha0 hD hDB ha hlen hc x
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn0
  have htail := ha.suffix blocks.flatten tail
  have htest := hierarchyCenteredEvenMoment_smooth_zero (uniformWeight_pos n) (finiteFeature n)
    (spinProjection n V) tail htail k
  rw [integral_segmentLaw_test (uniformWeight_pos n) (finiteFeature n) htest tail blocks.flatten ha]
  let M : ℝ := prefixTest blocks.flatten (finiteSKHierarchy n tail)
    (hierarchyCenteredEvenMoment (uniformWeight n) (finiteFeature n) (spinProjection n V) tail k) x
  let U : ℝ := ∑i, (V i)^2
  let scale : ℝ := (Real.log (n:ℝ))^2*projectionEuclideanNorm n V/(a*Real.sqrt ((n:ℝ)*D))
  have hU : 0 ≤ U := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hscale : 0 ≤ scale := by dsimp [scale,projectionEuclideanNorm]; positivity
  have hM : 0 ≤ M := by
    dsimp [M,finiteSKHierarchy]
    rw [← integral_segmentLaw_test (uniformWeight_pos n) (finiteFeature n) htest tail blocks.flatten ha]
    apply integral_nonneg
    intro p
    apply Finset.sum_nonneg
    intro s _
    exact mul_nonneg (hierarchyAtom_nonneg (uniformWeight_pos n) (finiteFeature n) tail htail s _)
      (pow_nonneg (abs_nonneg _) _)
  have hsq : scale^2 = (Real.log (n:ℝ))^4*U/((n:ℝ)*a^2*D) := by
    dsimp [scale,projectionEuclideanNorm,U]
    rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt (mul_nonneg hn'.le hD.le),Real.sq_sqrt hU]
    ring
  have hbound : M ≤ (projectionLpConstant k*scale)^(2*k+2) := by
    have hh := hn V tail blocks a D ha0 hD hDB ha hlen hc x
    change M ≤ _ at hh
    rw [mul_pow,projectionLpConstant_pow,show 2*k+2 = 2*(k+1) by omega,pow_mul,hsq]
    exact hh
  have hh := Real.rpow_le_rpow hM hbound (by positivity : (0:ℝ) ≤ ((2*k+2:ℕ)⁻¹:ℝ))
  rw [Real.pow_rpow_inv_natCast (mul_nonneg (projectionLpConstant_pos k).le hscale) (by omega)] at hh
  change M^((2*k+2:ℕ)⁻¹:ℝ) ≤ _
  exact hh.trans_eq (by dsimp [scale]; ring)

end SKFluctuations

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

 

inductive ClockRefinement : List (GaussianStep ι) → List (GaussianStep ι) → Prop
  | refl (L) : ClockRefinement L L
  | split (pre post : List (GaussianStep ι)) (m : ℝ) (q r : ι → ℝ≥0) :
      ClockRefinement (pre++(m,q+r)::post) (pre++(m,q)::(m,r)::post)
  | trans {L M N} : ClockRefinement L M → ClockRefinement M N → ClockRefinement L N

omit [Fintype ι] in
theorem orderedSteps_split (pre post : List (GaussianStep ι)) (m : ℝ) (q r : ι → ℝ≥0)
    {a : ℝ} (ha : OrderedSteps a (pre++(m,q+r)::post)) :
    OrderedSteps a (pre++(m,q)::(m,r)::post) := by
  induction pre generalizing a with
  | nil => exact ⟨ha.1,ha.2.1,ha.2.2.1,ha.2.2.1.le,le_refl m,ha.2.2.1,ha.2.2.2⟩
  | cons st pre ih => exact ⟨ha.1,ha.2.1,ha.2.2.1,ih ha.2.2.2⟩

omit [Fintype ι] in
theorem ClockRefinement.ordered {L M : List (GaussianStep ι)} (h : ClockRefinement L M)
    {a : ℝ} (ha : OrderedSteps a L) : OrderedSteps a M := by
  induction h generalizing a with
  | refl => exact ha
  | split pre post m q r => exact orderedSteps_split pre post m q r ha
  | trans h₁ h₂ ih₁ ih₂ => exact ih₂ (ih₁ ha)

omit [Fintype ι] in
theorem ClockRefinement.append {L M : List (GaussianStep ι)} (h : ClockRefinement L M)
    (pre post : List (GaussianStep ι)) : ClockRefinement (pre++L++post) (pre++M++post) := by
  induction h with
  | refl => exact .refl _
  | split p s m q r => simpa only [List.append_assoc,List.cons_append] using
      ClockRefinement.split (pre++p) (s++post) m q r
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

omit [Fintype ι] in
theorem ClockRefinement.cons {L M : List (GaussianStep ι)} (h : ClockRefinement L M)
    (p : GaussianStep ι) : ClockRefinement (p::L) (p::M) := by
  simpa only [List.singleton_append,List.append_nil] using h.append [p] []

open GaussianCalculus

theorem ClockRefinement.continuation_test {L M : List (GaussianStep ι)} (h : ClockRefinement L M)
    {a : ℝ} (ha : OrderedSteps a L) {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) :
    prefixContinuation L F = prefixContinuation M F ∧ prefixTest L F A = prefixTest M F A := by
  induction h with
  | refl => exact ⟨rfl,rfl⟩
  | split pre post m q r =>
    have hm : 0 < m := ha.mem_pos (m,q+r) (List.mem_append_right pre List.mem_cons_self)
    have hp : ∀st∈post, 0 < st.1 := fun st hs =>
      ha.mem_pos st (List.mem_append_right pre (List.mem_cons_of_mem _ hs))
    have hcont := prefixContinuation_lipschitz hF post hp
    have htest := prefixTest_smooth0 hF hA post hp
    have he₁ : prefixContinuation ((m,q)::(m,r)::post) F =
        prefixContinuation ((m,q+r)::post) F :=
      funext (shiftedContinuation_productGaussian_add hcont hm.ne' q r)
    have he₂ : prefixTest ((m,q)::(m,r)::post) F A =
        prefixTest ((m,q+r)::post) F A :=
      funext (shiftedMean_productGaussian_add hcont htest hm.ne' q r)
    simp only [prefixContinuation_append,prefixTest_append,he₁,he₂,and_self]
  | trans h₁ h₂ ih₁ ih₂ =>
    have hfirst := ih₁ ha
    have hsecond := ih₂ (h₁.ordered ha)
    exact ⟨hfirst.1.trans hsecond.1,hfirst.2.trans hsecond.2⟩

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*}

abbrev ClockedStep (ι : Type*) := ℝ≥0 × GaussianStep ι

def forgetClock (L : List (ClockedStep ι)) : List (GaussianStep ι) := L.map Prod.snd

def clockDuration (L : List (ClockedStep ι)) : ℝ≥0 := (L.map Prod.fst).sum

 

def ClockAligned (u : ι → ℝ) (L : List (ClockedStep ι)) : Prop :=
  ∀p∈L, ∀j, u j ≠ 0 → p.2.2 j = p.1

@[simp] theorem forgetClock_nil : forgetClock ([] : List (ClockedStep ι)) = [] := rfl
@[simp] theorem forgetClock_cons (p : ClockedStep ι) (L : List (ClockedStep ι)) :
    forgetClock (p::L) = p.2::forgetClock L := rfl
@[simp] theorem forgetClock_append (L M : List (ClockedStep ι)) :
    forgetClock (L++M) = forgetClock L++forgetClock M := List.map_append
@[simp] theorem clockDuration_nil : clockDuration ([] : List (ClockedStep ι)) = 0 := rfl
@[simp] theorem clockDuration_cons (p : ClockedStep ι) (L : List (ClockedStep ι)) :
    clockDuration (p::L) = p.1+clockDuration L := rfl
@[simp] theorem clockDuration_append (L M : List (ClockedStep ι)) :
    clockDuration (L++M) = clockDuration L+clockDuration M := by simp [clockDuration]

theorem ClockAligned.append {u : ι → ℝ} {L M : List (ClockedStep ι)}
    (hL : ClockAligned u L) (hM : ClockAligned u M) : ClockAligned u (L++M) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hL p hp
  · exact hM p hp

theorem ClockAligned.of_append_left {u : ι → ℝ} {L M : List (ClockedStep ι)}
    (h : ClockAligned u (L++M)) : ClockAligned u L :=
  fun p hp => h p (List.mem_append_left M hp)

theorem ClockAligned.of_append_right {u : ι → ℝ} {L M : List (ClockedStep ι)}
    (h : ClockAligned u (L++M)) : ClockAligned u M :=
  fun p hp => h p (List.mem_append_right L hp)

 

theorem exists_clock_cut {u : ι → ℝ} (L : List (ClockedStep ι))
    (hL : ClockAligned u L) (t : ℝ≥0) (ht : t ≤ clockDuration L) :
    ∃P Q : List (ClockedStep ι), clockDuration P = t ∧
      clockDuration Q = clockDuration L-t ∧ ClockAligned u (P++Q) ∧
      ClockRefinement (forgetClock L) (forgetClock (P++Q)) := by
  induction L generalizing t with
  | nil =>
    have ht0 : t = 0 := le_antisymm ht bot_le
    subst t
    exact ⟨[],[],rfl,by simp,by simpa using hL,.refl _⟩
  | cons p L ih =>
    rcases p with ⟨d,m,q⟩
    have htail : ClockAligned u L := fun p hp => hL p (List.mem_cons_of_mem _ hp)
    have hhead : ∀j, u j ≠ 0 → q j = d := hL (d,m,q) List.mem_cons_self
    by_cases ht0 : t = 0
    · exact ⟨[],(d,m,q)::L,ht0.symm,by simp [ht0],by simpa using hL,.refl _⟩
    by_cases htd : t ≤ d
    · have hd : 0 < d := (pos_iff_ne_zero.mpr ht0).trans_le htd
      let q₁ : ι → ℝ≥0 := fun j => (t/d)*q j
      let q₂ : ι → ℝ≥0 := fun j => q j-q₁ j
      have hr : t/d ≤ 1 := (div_le_one hd).mpr htd
      have hq (j) : q₁ j ≤ q j := by
        dsimp [q₁]
        exact (mul_le_mul_of_nonneg_right hr bot_le).trans_eq (one_mul _)
      have hqr : q₁+q₂ = q := by
        funext j
        exact add_tsub_cancel_of_le (hq j)
      have hc₁ (j) (hj : u j ≠ 0) : q₁ j = t := by
        dsimp [q₁]
        rw [hhead j hj,div_mul_cancel₀ _ hd.ne']
      have hc₂ (j) (hj : u j ≠ 0) : q₂ j = d-t := by
        dsimp [q₂]
        rw [hhead j hj,hc₁ j hj]
      refine ⟨[(t,m,q₁)],(d-t,m,q₂)::L,by simp,?_,?_,?_⟩
      · simp only [clockDuration_cons]
        simpa only [add_comm] using (add_tsub_assoc_of_le htd (clockDuration L)).symm
      · intro p hp j hj
        simp only [List.singleton_append,List.mem_cons] at hp
        rcases hp with rfl | rfl | hp
        · exact hc₁ j hj
        · exact hc₂ j hj
        · exact htail p hp j hj
      · simpa only [List.nil_append,forgetClock_cons,forgetClock_append,List.append_nil,
          List.singleton_append,hqr] using ClockRefinement.split [] (forgetClock L) m q₁ q₂
    · have hdt : d ≤ t := (le_of_not_ge htd)
      have htt : t-d ≤ clockDuration L := by
        exact tsub_le_iff_right.mpr (by simpa only [clockDuration_cons,add_comm] using ht)
      obtain ⟨P,Q,hP,hQ,hA,hR⟩ := ih htail (t-d) htt
      refine ⟨(d,m,q)::P,Q,?_,?_,?_,?_⟩
      · simp only [clockDuration_cons,hP]
        exact add_tsub_cancel_of_le hdt
      · rw [hQ,clockDuration_cons]
        apply NNReal.coe_injective
        rw [NNReal.coe_sub htt,NNReal.coe_sub hdt,
          NNReal.coe_sub (show t ≤ d+clockDuration L from ht),NNReal.coe_add]
        ring
      · intro p hp j hj
        simp only [List.cons_append,List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact hhead j hj
        · exact hA p hp j hj
      · simpa only [List.cons_append,forgetClock_cons] using hR.cons (m,q)

 
theorem exists_equal_clock_partition {u : ι → ℝ} (L : List (ClockedStep ι))
    (hL : ClockAligned u L) (N : ℕ) (hN : 0 < N) (t : ℝ≥0)
    (ht : clockDuration L = N*t) :
    ∃blocks : List (List (ClockedStep ι)), blocks.length = N ∧
      (∀P∈blocks, clockDuration P = t ∧ ClockAligned u P) ∧
      ClockRefinement (forgetClock L) (forgetClock blocks.flatten) := by
  induction N generalizing L with
  | zero => omega
  | succ N ih =>
    cases N with
    | zero =>
      refine ⟨[L],rfl,?_,?_⟩
      · intro P hp
        have hPL : P = L := List.mem_singleton.mp hp
        subst P
        exact ⟨by simpa using ht,hL⟩
      · simpa using ClockRefinement.refl (forgetClock L)
    | succ N =>
      have htt : t ≤ clockDuration L := by
        rw [ht]
        have hcount : (1:ℝ≥0) ≤ ((N+1+1:ℕ):ℝ≥0) := by exact_mod_cast (by omega : 1 ≤ N+1+1)
        simpa using mul_le_mul_of_nonneg_right hcount (show 0 ≤ t from bot_le)
      obtain ⟨P,Q,hP,hQ,hA,hR⟩ := exists_clock_cut L hL t htt
      have hQt : clockDuration Q = (N+1)*t := by
        rw [hQ,ht]
        have he : ((Nat.succ (Nat.succ N):ℕ):ℝ≥0)*t = t+(N+1)*t := by push_cast; ring
        rw [he,add_tsub_cancel_left]
      obtain ⟨blocks,hlen,hblocks,hRef⟩ := ih Q hA.of_append_right (by omega) (by simpa using hQt)
      refine ⟨P::blocks,by simp [hlen],?_,?_⟩
      · intro R hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact ⟨hP,hA.of_append_left⟩
        · exact hblocks R hmem
      · apply hR.trans
        simpa only [List.flatten_cons,forgetClock_append,List.append_nil,List.nil_append] using
          hRef.append (forgetClock P) []

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι : Type*}

theorem hierarchyClocks_get (pre : List (GaussianStep ι)) (i : Fin pre.length) :
    hierarchyClocks pre i = (pre.get i).2 := by
  induction pre with
  | nil => exact Fin.elim0 i
  | cons st pre ih =>
    rcases st with ⟨m,q⟩
    refine Fin.cases rfl (fun j => ?_) i
    exact ih j

theorem ClockAligned.toAligned {u : ι → ℝ} {L : List (ClockedStep ι)}
    (h : ClockAligned u L) : AlignedFieldClock u (clockDuration L) (forgetClock L) := by
  induction L with
  | nil =>
    refine ⟨Fin.elim0,fun i => Fin.elim0 i,?_,fun i => Fin.elim0 i⟩
    change (∑i : Fin 0, (Fin.elim0 i:ℝ)) = 0
    exact Fin.sum_univ_zero _
  | cons p L ih =>
    obtain ⟨d,hd,hD,hq⟩ := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
    refine ⟨Fin.cons (p.1:ℝ) d,?_,?_,?_⟩
    · intro i
      refine Fin.cases p.1.property (fun j => hd j) i
    · change (∑i : Fin ((forgetClock L).length+1), Fin.cons (p.1:ℝ) d i) = (p.1:ℝ)+(clockDuration L:ℝ)
      simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,hD]
    · intro i j hj
      refine Fin.cases ?_ (fun i => ?_) i
      · exact congrArg NNReal.toReal (h p List.mem_cons_self j hj)
      · exact hq i j hj

theorem exists_clocked_of_aligned {u : ι → ℝ} {D : ℝ} {pre : List (GaussianStep ι)}
    (h : AlignedFieldClock u D pre) :
    ∃L : List (ClockedStep ι), forgetClock L = pre ∧ (clockDuration L:ℝ) = D ∧ ClockAligned u L := by
  obtain ⟨d,hd,hD,hq⟩ := h
  let L : List (ClockedStep ι) := List.ofFn (fun i : Fin pre.length => (⟨d i,hd i⟩,pre.get i))
  refine ⟨L,?_,?_,?_⟩
  · dsimp [L,forgetClock]
    rw [List.map_ofFn]
    exact List.ofFn_get pre
  · dsimp [L,clockDuration]
    rw [List.map_ofFn,List.sum_ofFn,NNReal.coe_sum]
    exact hD
  · intro p hp j hj
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    apply NNReal.coe_injective
    change ((pre.get i).2 j:ℝ) = d i
    rw [← hierarchyClocks_get]
    exact hq i j hj

theorem forgetClock_flatten (blocks : List (List (ClockedStep ι))) :
    forgetClock blocks.flatten = (blocks.map forgetClock).flatten := by
  induction blocks with
  | nil => rfl
  | cons L blocks ih => simp only [List.flatten_cons,forgetClock_append,List.map_cons,ih]

theorem exists_aligned_refinement {u : ι → ℝ} {D : ℝ} {pre : List (GaussianStep ι)}
    (h : AlignedFieldClock u D pre) (N : ℕ) (hN : 0 < N) :
    ∃blocks : List (List (GaussianStep ι)), blocks.length = N ∧
      (∀P∈blocks, AlignedFieldClock u (D/(N:ℝ)) P) ∧
      ClockRefinement pre blocks.flatten := by
  obtain ⟨L,hL,hD,hA⟩ := exists_clocked_of_aligned h
  have hN' : (N:ℝ≥0) ≠ 0 := by exact_mod_cast hN.ne'
  have ht : clockDuration L = (N:ℝ≥0)*(clockDuration L/(N:ℝ≥0)) := by
    rw [mul_div_cancel₀ _ hN']
  obtain ⟨blocks,hlen,hblocks,hRef⟩ := exists_equal_clock_partition L hA N hN
    (clockDuration L/(N:ℝ≥0)) ht
  refine ⟨blocks.map forgetClock,by simpa using hlen,?_,?_⟩
  · intro P hp
    obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hp
    obtain ⟨hQd,hQa⟩ := hblocks Q hQ
    have he : (clockDuration Q:ℝ) = D/(N:ℝ) := by rw [hQd,NNReal.coe_div,hD]; simp
    rw [← he]
    exact hQa.toAligned
  · simpa only [hL,forgetClock_flatten] using hRef

theorem OrderedSteps.prefix {a : ℝ} (pre tail : List (GaussianStep ι))
    (ha : OrderedSteps a (pre++tail)) : OrderedSteps a pre := by
  induction pre generalizing a with
  | nil => exact ha.bounds
  | cons st pre ih => exact ⟨ha.1,ha.2.1,ha.2.2.1,ih ha.2.2.2⟩

end SKFluctuations.Hierarchy

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Hierarchy
open scoped Topology NNReal ENNReal BigOperators

 

theorem eventually_finiteSK_projection (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Fin n → ℝ)
      (tail pre : List (GaussianStep (FeatureIndex n))) (a D : ℝ),
      0 < a → 0 < D → D ≤ B → OrderedSteps a (pre++tail) →
      AlignedFieldClock (fieldProjectionDirection n V) D pre →
      ∀ x : FeatureIndex n → ℝ,
      ((∫ p, hierarchyCenteredEvenMoment (uniformWeight n) (finiteFeature n)
        (spinProjection n V) tail k
        (forwardEnd pre.length (hierarchyIncrements pre) x p)
        ∂segmentLaw (uniformWeight n) (finiteFeature n) tail pre x)^((2*k+2:ℕ)⁻¹:ℝ)) ≤
      projectionLpConstant k*(Real.log (n:ℝ))^2*projectionEuclideanNorm n V/
        (a*Real.sqrt ((n:ℝ)*D)) := by
  filter_upwards [eventually_finiteSK_projection_root k B,eventually_projectionLogBlocks 0 1] with n hn hN
  intro V tail pre a D ha0 hD hDB ha hc x
  obtain ⟨blocks,hlen,hblocks,hRef⟩ := exists_aligned_refinement hc (projectionLogBlocks n) hN.2.2.1
  have hrefall : ClockRefinement (pre++tail) (blocks.flatten++tail) := by
    simpa only [List.nil_append] using hRef.append [] tail
  have hb := hrefall.ordered ha
  have htail := ha.suffix pre tail
  obtain ⟨C,hF⟩ := gaussianHierarchy_lipschitz (uniformWeight_pos n) (finiteFeature n) tail htail
  have htest := hierarchyCenteredEvenMoment_smooth_zero (uniformWeight_pos n) (finiteFeature n)
    (spinProjection n V) tail htail k
  have he := (hRef.continuation_test (ha.prefix pre tail) hF htest).2
  rw [integral_segmentLaw_test (uniformWeight_pos n) (finiteFeature n) htest tail pre ha,he,
    ← integral_segmentLaw_test (uniformWeight_pos n) (finiteFeature n) htest tail blocks.flatten hb]
  exact hn V tail blocks a D ha0 hD hDB hb hlen hblocks x

end SKFluctuations

 

 
namespace SKFluctuations.Scalar
open Set Filter
open scoped Topology

theorem contDiffOn_succ_of_partials {f f₁ f₂ : ℝ → ℝ → ℝ}
    {S : Set (ℝ × ℝ)} (hS : IsOpen S) (k : ℕ)
    (h₁ : ∀ p ∈ S, HasDerivAt (fun r => f r p.2) (f₁ p.1 p.2) p.1)
    (h₂ : ∀ p ∈ S, HasDerivAt (fun r => f p.1 r) (f₂ p.1 p.2) p.2)
    (hc₁ : ContDiffOn ℝ k (fun p : ℝ × ℝ => f₁ p.1 p.2) S)
    (hc₂ : ContDiffOn ℝ k (fun p : ℝ × ℝ => f₂ p.1 p.2) S) :
    ContDiffOn ℝ (k+1 : ℕ) (fun p : ℝ × ℝ => f p.1 p.2) S := by
  let D : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ := fun p =>
    f₁ p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
    f₂ p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ
  rw [Nat.cast_add, Nat.cast_one]
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hS.uniqueDiffOn).2
  refine ⟨by simp, D, (hc₁.smul contDiffOn_const).add (hc₂.smul contDiffOn_const), ?_⟩
  intro p hp
  have hpS : S ∈ 𝓝 p := hS.mem_nhds hp
  have hh := hasStrictFDerivAt_uncurry_coprod
    (f := f)
    (f₁ := fun a b => ContinuousLinearMap.toSpanSingleton ℝ (f₁ a b))
    (f₂ := fun a b => ContinuousLinearMap.toSpanSingleton ℝ (f₂ a b))
    ((show ∀ᶠ q in 𝓝 p, q ∈ S from hpS).mono fun q hq => (h₁ q hq).hasFDerivAt)
    ((show ∀ᶠ q in 𝓝 p, q ∈ S from hpS).mono fun q hq => (h₂ q hq).hasFDerivAt)
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.comp
      (hc₁.continuousOn.continuousAt hpS))
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.comp
      (hc₂.continuousOn.continuousAt hpS))
  have he : (ContinuousLinearMap.toSpanSingleton ℝ (f₁ p.1 p.2)).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ (f₂ p.1 p.2)) = D p := by
    apply ContinuousLinearMap.ext
    intro q
    change q.1*f₁ p.1 p.2+q.2*f₂ p.1 p.2 = f₁ p.1 p.2*q.1+f₂ p.1 p.2*q.2
    ring
  change HasStrictFDerivAt (fun p : ℝ × ℝ => f p.1 p.2)
    ((ContinuousLinearMap.toSpanSingleton ℝ (f₁ p.1 p.2)).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ (f₂ p.1 p.2))) p at hh
  rw [he] at hh
  exact hh.hasFDerivAt.hasFDerivWithinAt

end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Set Filter GaussianCalculus
open scoped Topology NNReal BigOperators ContDiff

private theorem ClockJointSmooth_clockTest_scalar_source {F A : (Fin 1 → ℝ) → ℝ}
    {G A₁ : Fin 1 → (Fin 1 → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A)
    (hG : ∀ i, BddSmooth 0 (G i)) (hA₁ : ∀ i, BddSmooth 0 (A₁ i))
    (hdF : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v))
      (∑ i, v i*G i (x+t • v)) t)
    (hdA : ∀ x v t, HasDerivAt (fun s : ℝ => A (x+s • v))
      (∑ i, v i*A₁ i (x+t • v)) t)
    (m t x : ℝ) :
    HasDerivAt (fun y => clockTest m F A t (fun _ => y))
      (clockGradient m F (G 0) A (A₁ 0) t (fun _ => x)) x := by
  have hh := hasDerivAt_clockTest_source_vector hF hA hG hA₁ hdF hdA m t
    (0 : Fin 1 → ℝ) (fun _ => 1) x
  have he (r : ℝ) : (0 : Fin 1 → ℝ)+r • (fun _ => 1) = fun _ => r := by
    ext i; simp
  simp only [he] at hh
  change HasDerivAt (fun y => clockTest m F A t (fun _ => y))
    (∑ i : Fin 1, 1*clockGradient m F (G i) A (A₁ i) t (fun _ => x)) x at hh
  simpa only [Fin.sum_univ_one,one_mul] using hh

 

theorem clockTest_scalar_contDiffOn {F : (Fin 1 → ℝ) → ℝ}
    {G H : Fin 1 → (Fin 1 → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F)
    (hG : ∀ k i, BddSmooth k (G i)) (hH : ∀ k i, BddSmooth k (H i))
    (hdF : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v))
      (∑ i, v i*G i (x+t • v)) t)
    (hdG : ∀ i x t, HasDerivAt (fun s : ℝ => G i (x+s • Pi.single i 1))
      (H i (x+t • Pi.single i 1)) t)
    (m : ℝ) (k : ℕ) {A : (Fin 1 → ℝ) → ℝ} (hA : ∀ r, BddSmooth r A) :
    ContDiffOn ℝ k (fun p : ℝ × ℝ => clockTest m F A p.1 (fun _ => p.2))
      {p : ℝ × ℝ | 0 < p.1} := by
  induction k generalizing A with
  | zero =>
    apply contDiffOn_zero.mpr
    exact ((clockTest_continuous hF (hA 0) m).comp
      (continuous_fst.prodMk (continuous_pi fun _ => continuous_snd))).continuousOn
  | succ k ih =>
    let A₁ : Fin 1 → (Fin 1 → ℝ) → ℝ := fun i y => lineDeriv ℝ A y (Pi.single i 1)
    let A₂ : Fin 1 → (Fin 1 → ℝ) → ℝ := fun i y => lineDeriv ℝ (A₁ i) y (Pi.single i 1)
    have hs₁ (r i) : BddSmooth r (A₁ i) := (hA (r+1)).lineDeriv_smooth _
    have hs₂ (r i) : BddSmooth r (A₂ i) := (hs₁ (r+1) i).lineDeriv_smooth _
    have hdA (x v : Fin 1 → ℝ) (t : ℝ) :
        HasDerivAt (fun s : ℝ => A (x+s • v)) (∑ i, v i*A₁ i (x+t • v)) t := by
      have hh := (hA 1).hasDerivAt_line x v t
      rw [(hA 1).lineDeriv_pi] at hh
      exact hh
    have hd₁ (i) (x : Fin 1 → ℝ) (t : ℝ) :
        HasDerivAt (fun s : ℝ => A₁ i (x+s • Pi.single i 1))
          (A₂ i (x+t • Pi.single i 1)) t := (hs₁ 1 i).hasDerivAt_line _ _ _
    apply Scalar.contDiffOn_succ_of_partials
      (f := fun t x => clockTest m F A t (fun _ => x))
      (S := {p : ℝ × ℝ | 0 < p.1})
      (f₁ := fun t x => clockTestDerivative m F G H A A₁ A₂ t (fun _ => x))
      (f₂ := fun t x => clockGradient m F (G 0) A (A₁ 0) t (fun _ => x))
      (isOpen_lt continuous_const continuous_fst) k
    · intro p hp
      exact (hasDerivWithinAt_clockTest hF (hA 0) (hG 0) (hH 0) (hs₁ 0) (hs₂ 0)
        hdF hdG hdA hd₁ m (fun _ => p.2) hp.le).hasDerivAt (Ici_mem_nhds hp)
    · intro p _
      exact ClockJointSmooth_clockTest_scalar_source hF (hA 0) (hG 0) (hs₁ 0) hdF hdA m p.1 p.2
    · exact contDiffOn_const.mul ((ih (fun r => testedHeatTrace_bddSmooth (hG r) (hH r) (hA r) (hs₁ r) (hs₂ r) m)).sub
        ((ih hA).mul (ih fun r => potentialHeatTrace_bddSmooth (hG r) (hH r) m)))
    · exact (ih (fun r => hs₁ r 0)).add (contDiffOn_const.mul
        ((ih fun r => (hA r).mul (hG r 0)).sub ((ih hA).mul (ih fun r => hG r 0))))

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem clockTest_mono {ι : Type*} [Fintype ι] {F A B : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) (hB : BddSmooth 0 B)
    (hab : ∀ y, A y ≤ B y) (m t : ℝ) (x : ι → ℝ) :
    clockTest m F A t x ≤ clockTest m F B t x :=
  shiftedMean_mono hA hB hab
    ((exponentialIncrement_gaussian (fun _ : ι => Real.toNNReal t)).integrable_shift hF m x)

 theorem clockTest_const {ι : Type*} [Fintype ι] {F : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (c m t : ℝ) (x : ι → ℝ) :
    clockTest m F (fun _ => c) t x = c :=
  shiftedMean_const c
    ((exponentialIncrement_gaussian (fun _ : ι => Real.toNNReal t)).integrable_shift hF m x)

 theorem clockTest_variance_nonneg {ι : Type*} [Fintype ι] {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) (m t : ℝ) (x : ι → ℝ) :
    0 ≤ clockTest m F (fun y => (A y)^2) t x-(clockTest m F A t x)^2 :=
  shiftedMean_square_sub_nonneg hF.continuous hA
    ((exponentialIncrement_gaussian (fun _ : ι => Real.toNNReal t)).integrable_shift hF m x)

 

def HeatJet.ScalarAdmissible (J : HeatJet 0) : Prop :=
  ∀ x, 0 ≤ J.H 0 x ∧ J.H 0 x+(J.G 0 x)^2 ≤ 1

 theorem HeatJet.ScalarAdmissible.gradient {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    (x : Fin 1 → ℝ) : |J.G 0 x| ≤ 1 := by
  apply (sq_le_one_iff_abs_le_one _).mp
  linarith [(hJ x).1,(hJ x).2]

 theorem HeatJet.ScalarAdmissible.curvature {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    (x : Fin 1 → ℝ) : J.H 0 x ≤ 1 := by
  linarith [(hJ x).2,sq_nonneg (J.G 0 x)]

 theorem HeatJet.ScalarAdmissible.evolve {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (t : ℝ) : (J.evolve hm t).ScalarAdmissible := by
  intro x
  have hv := clockTest_variance_nonneg J.lipschitz (J.smoothG 0) m t x
  have hp := clockTest_nonneg J.lipschitz (fun y => (hJ y).1) m t x
  have hsq : BddSmooth 0 (fun y => (J.G 0 y)^2) := by
    simpa only [pow_two] using (J.smoothG 0).mul (J.smoothG 0)
  have hu := clockTest_mono J.lipschitz ((J.smoothH 0).add hsq)
    (BddSmooth.const 0 1) (fun y => (hJ y).2) m t x
  rw [clockTest_add_test J.lipschitz (J.smoothH 0) hsq,clockTest_const J.lipschitz] at hu
  change 0 ≤ clockGradient m J.F (J.G 0) (J.G 0) (J.H 0) t x ∧
    clockGradient m J.F (J.G 0) (J.G 0) (J.H 0) t x+(clockTest m J.F (J.G 0) t x)^2 ≤ 1
  simp only [clockGradient,← pow_two]
  constructor
  · exact add_nonneg hp (mul_nonneg hm.le hv)
  · nlinarith [mul_nonneg (sub_nonneg.mpr hm1) hv]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Scalar
open Hierarchy
open scoped Topology NNReal

 theorem third_abs_le_curvature (x : ℝ) : |third x| ≤ 2*curvature x := by
  rw [third,abs_mul,abs_mul,abs_neg,abs_of_pos (by norm_num : (0:ℝ) < 2),abs_of_pos (curvature_pos x)]
  nlinarith [mul_le_mul_of_nonneg_right (Real.abs_tanh_lt_one x).le (curvature_pos x).le]

 theorem fourth_lower (x : ℝ) : -2*curvature x ≤ fourth x := by
  have h := mul_nonneg (sq_nonneg (Real.tanh x)) (curvature_bounds x).1
  dsimp [curvature,fourth] at *
  nlinarith

 theorem curvature_pi_bddSmooth : Hierarchy.BddSmooth 0 (fun x : Fin 1 → ℝ => curvature (x 0)) := by
  refine ⟨curvature_continuous.comp (continuous_apply 0),1,by norm_num,?_⟩
  intro x
  rw [abs_of_pos (curvature_pos _)]
  exact (curvature_bounds _).2

 theorem third_bddSmooth : Hierarchy.BddSmooth 0 (fun x : Fin 1 → ℝ => third (x 0)) := by
  refine ⟨third_continuous.comp (continuous_apply 0),2,by norm_num,?_⟩
  intro x
  exact (third_abs_le_curvature _).trans (by linarith [(curvature_bounds (x 0)).2])

 theorem fourth_bddSmooth : Hierarchy.BddSmooth 0 (fun x : Fin 1 → ℝ => fourth (x 0)) := by
  refine ⟨fourth_continuous.comp (continuous_apply 0),16,by norm_num,?_⟩
  intro x
  have h₂ : (Real.tanh (x 0))^2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr (Real.abs_tanh_lt_one _).le
  have h₄ : (Real.tanh (x 0))^4 ≤ 1 := by nlinarith [sq_nonneg ((Real.tanh (x 0))^2-1),sq_nonneg (Real.tanh (x 0))]
  apply abs_le.mpr
  dsimp [fourth]
  constructor <;> nlinarith [sq_nonneg (Real.tanh (x 0)),pow_nonneg (sq_nonneg (Real.tanh (x 0))) 2]

end SKFluctuations.Scalar

end

end OAI
