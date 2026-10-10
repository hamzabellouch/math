import Mathlib
import OAI.Probability.SKFluctuations.CumulativeIncrements

namespace OAI

/-! Chain. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem ExpClose.chain (p : ℕ → ℝ) (E : ℕ → ℝ) (N : ℕ) (hp : 0 ≤ p 0)
    (hE : ∀ j < N, ExpClose (E j) (p j) (p (j+1))) :
    ExpClose (∑ j ∈ Finset.range N, E j) (p 0) (p N) := by
  induction N with
  | zero => simpa only [Finset.range_zero,Finset.sum_empty] using ExpClose.refl hp
  | succ N ih =>
    simpa only [Finset.sum_range_succ] using
      (ih (fun j hj => hE j (Nat.lt_succ_of_lt hj))).trans (hE N (Nat.lt_succ_self _))

variable {S : Type*} {as : List PositiveMass}
variable [Fintype S] [Nonempty S] {n : ℕ}

 

 theorem ClockTree.cumulative_lowering_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (T : ClockTree S as)
    (ho : MassOrdered 0 as) (D M : Fin (n+1) → ℝ)
    (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (l : Fin (n+1) → ℝ) (q r : ℕ → Fin (n+1) → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hql : ∀ i, l i ≤ q 0 i) (hrl : ∀ i, l i ≤ r 0 i)
    (hM : ∀ i, 0 ≤ M i) (hm : ∀ i j, j < as.length → |q j i-r j i| ≤ M i)
    (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    ExpClose ((7*(T.leaves:ℝ)+8*(T.leaves:ℝ)^2*(T.leaves+1:ℝ))*∑ i, M i*(D i)^2)
      (T.weight w φ (cumulativeIncrements l q) σ x)
      (T.weight w φ (cumulativeIncrements l (loweredBoundary (as.length-1) q r)) σ x) := by
  let K : ℝ := ∑ i, M i*(D i)^2
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => mul_nonneg (hM i) (sq_nonneg _)
  let E := fun j => (7*(T.leaves:ℝ)*massGap as j+8*(T.leaves:ℝ)*(T.leaves+1:ℝ)*T.forksAt (j+1))*K
  have hstep (j : ℕ) (hj : j < as.length-1) :
      ExpClose (E j) (T.weight w φ (cumulativeIncrements l (loweredBoundary j q r)) σ x)
        (T.weight w φ (cumulativeIncrements l (loweredBoundary (j+1) q r)) σ x) := by
    have hh := T.cumulative_boundary_close_at hw φ ho j (by omega) D hD hB l (loweredBoundary j q r)
      (fun i => min (q j i) (r j i)) (loweredBoundary_previous hq hr hql hrl j)
      (fun i => by simp only [loweredBoundary,lt_self_iff_false,ite_false]; exact min_le_left _ _)
      (fun i => loweredBoundary_mono hq hr j i (Nat.le_succ j)) σ x
    rw [←loweredBoundary_update] at hh
    apply hh.mono
    apply mul_le_mul_of_nonneg_left _ (by
      have hg := massGap_nonneg as j
      positivity)
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
      ((loweredBoundary_difference j i).trans (hm i j (by omega))) (sq_nonneg _)
  have hh := ExpClose.chain
    (fun j => T.weight w φ (cumulativeIncrements l (loweredBoundary j q r)) σ x)
    E (as.length-1) ((T.weight_probability hw φ ho _ x).1 σ) hstep
  rw [loweredBoundary_zero] at hh
  apply hh.mono
  have hg := massGap_sum_prefix_le_one ho (as.length-1) (by omega)
  have hf := T.forks_sum_shift_le (as.length-1) (by omega)
  have hgm := mul_le_mul_of_nonneg_left hg (show 0 ≤ 7*(T.leaves:ℝ) by positivity)
  have hfm := mul_le_mul_of_nonneg_left hf (show 0 ≤ 8*(T.leaves:ℝ)*(T.leaves+1:ℝ) by positivity)
  dsimp only [E]
  rw [←Finset.sum_mul,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
  apply mul_le_mul_of_nonneg_right _ hK
  nlinarith

 

 theorem ClockTree.cumulative_uniform_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (T : ClockTree S as)
    (ho : MassOrdered 0 as) (D M : Fin (n+1) → ℝ)
    (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (l : Fin (n+1) → ℝ) (q r : ℕ → Fin (n+1) → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hql : ∀ i, l i ≤ q 0 i) (hrl : ∀ i, l i ≤ r 0 i)
    (hend : q (as.length-1) = r (as.length-1))
    (hM : ∀ i, 0 ≤ M i) (hm : ∀ i j, j < as.length → |q j i-r j i| ≤ M i)
    (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    ExpClose (2*(7*(T.leaves:ℝ)+8*(T.leaves:ℝ)^2*(T.leaves+1:ℝ))*∑ i, M i*(D i)^2)
      (T.weight w φ (cumulativeIncrements l q) σ x) (T.weight w φ (cumulativeIncrements l r) σ x) := by
  have hQ := T.cumulative_lowering_close hw φ ho D M hD hB l q r hq hr hql hrl hM hm σ x
  have hR := T.cumulative_lowering_close hw φ ho D M hD hB l r q hr hq hrl hql hM
    (fun i j hj => by rw [abs_sub_comm]; exact hm i j hj) σ x
  have he (σ : T.Assignment) :
      T.weight w φ (cumulativeIncrements l (loweredBoundary (as.length-1) q r)) σ x =
      T.weight w φ (cumulativeIncrements l (loweredBoundary (as.length-1) r q)) σ x := by
    apply T.cumulative_weight_congr w φ l _ σ x
    intro k hk
    funext i
    by_cases hkl : k < as.length-1
    · simp only [loweredBoundary,hkl,ite_true,min_comm]
    · have hek : k=as.length-1 := by omega
      subst k
      simp only [loweredBoundary,lt_self_iff_false,ite_false]
      exact congrFun hend i
  rw [he σ] at hQ
  convert hQ.trans hR.symm using 1
  ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

 theorem ReplicaTree.linearClock_mass_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : ReplicaTree ι S steps) {a b : ℝ}
    (hoa : OrderedSteps a steps) (hob : OrderedSteps b steps) {P : R.Assignment → ℝ} (hp : ∀ σ, 0 ≤ P σ)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) (x : ι → ℝ) :
    ExpClose ((|a-b| *(2*(R.leaves:ℝ)+3)*∑ i, (D i)^2)*t)
      (linearClockTest L a (gaussianHierarchy w φ steps) (R.expect w φ P) t x)
      (linearClockTest L b (gaussianHierarchy w φ steps) (R.expect w φ P) t x) := by
  apply ExpClose.of_bounds (R.clock_nonneg hw φ L hoa hp t x) (R.clock_nonneg hw φ L hob hp t x)
  let J := replicaFeatureJet hw φ L R hob P x
  have hh := J.massSplit_exp_comparison D hD
    (fun y => R.expect_nonneg hw φ hob hp (x+L y))
    (replicaFeatureJet_G_abs_le hw φ L R hob P x D hB)
    (replicaFeatureJet_A₁_relative_abs_le hw φ L R hob hp x D hD hB) ha ha1 hb hb1
    (show (0:ℝ) ∈ Icc 0 t from ⟨le_rfl,ht⟩) (show t ∈ Icc 0 t from ⟨ht,le_rfl⟩) 0
  rw [J.massSplit_zero,J.massSplit_terminal,sub_zero,abs_of_nonneg ht] at hh
  have hF := (gaussianHierarchy_regular hw φ steps hob 0).1.choose_spec.continuous
  have hA := (R.expect_smooth hw φ hob P 0).continuous
  simpa only [J,replicaFeatureJet_F,replicaFeatureJet_A,← linearClockTest_eq L hF hA,neg_mul] using hh

 theorem ClockTree.atomicHead_mass_close_nonneg {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a b : ℝ} (hoa : MassOrdered a as) (hob : MassOrdered b as)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0) (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    ExpClose (|a-b| *(2*(T.leaves:ℝ)+3)*∑ i, (v i:ℝ)*(D i)^2)
      (T.atomicHead w φ q v a σ x) (T.atomicHead w φ q v b σ x) := by
  classical
  have hd (i : Fin (n+1)) (σ : S) : |φ σ (diagonalDriver v (Pi.single i 1))| ≤ Real.sqrt (v i)*D i := by
    rw [diagonalDriver_single,map_smul,smul_eq_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hB i σ) (Real.sqrt_nonneg _)
  have hh := (T.realize q).linearClock_mass_close hw φ (diagonalDriver v)
    (clockSteps_ordered hoa q) (clockSteps_ordered hob q)
    (P := fun τ => if τ = T.assignmentEquiv q σ then 1 else 0)
    (by intro τ; split_ifs <;> norm_num) (fun i => Real.sqrt (v i)*D i)
    (fun i => mul_nonneg (Real.sqrt_nonneg _) (hD i)) hd ha ha1 hb hb1
    (by norm_num : (0:ℝ) ≤ 1) x
  rw [T.atomicHead_eq_clock,T.atomicHead_eq_clock]
  simpa only [ReplicaTree.atomicClock,mul_one,mul_pow,Real.sq_sqrt (v _).coe_nonneg,ClockTree.realize_leaves] using hh

 

 theorem ClockTree.atomicHead_root_transfer_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {b : PositiveMass} {bs : List PositiveMass}
    (T : ClockTree S (b::bs)) (ho : MassOrdered b.val bs)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0) (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    ExpClose ((b.val*(2*(T.leaves:ℝ)+3)+8*(T.leaves:ℝ)*(T.leaves+1:ℝ)*T.rootForks)*
        ∑ i, (v i:ℝ)*(D i)^2)
      (T.atomicHead w φ q v 0 σ x) (T.weight w φ (addHeadClock q v) σ x) := by
  have hb1 : b.val ≤ 1 := (massOrdered_bounds ho).2
  have h₁ := T.atomicHead_mass_close_nonneg hw φ ⟨le_rfl,b.property.le,ho⟩ ⟨b.property.le,le_rfl,ho⟩
    le_rfl (by norm_num) b.property hb1 D hD hB q v σ x
  have h₂ := T.atomicHead_crossing_close hw φ rfl ho D hD hB q v σ x
  simp only [zero_sub,abs_neg,abs_of_pos b.property] at h₁
  convert h₁.trans h₂ using 1
  ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem ExpClose.integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {c : ℝ} {p q : Ω → ℝ} (hp : Integrable p μ) (hq : Integrable q μ)
    (h : ∀ x, ExpClose c (p x) (q x)) : ExpClose c (∫ x, p x ∂μ) (∫ x, q x ∂μ) := by
  refine ⟨integral_nonneg fun x => (h x).left_nonneg,integral_nonneg fun x => (h x).right_nonneg,?_,?_⟩
  · calc
      _ ≤ ∫ x, Real.exp c*q x ∂μ := integral_mono hp (hq.const_mul _) fun x => (h x).le_mul
      _ = _ := integral_const_mul _ _
  · calc
      _ ≤ ∫ x, Real.exp c*p x ∂μ := integral_mono hq (hp.const_mul _) fun x => (h x).rev_le_mul
      _ = _ := integral_const_mul _ _

variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ} {as : List PositiveMass}

omit [Nonempty S] in
 theorem ClockTree.expect_close (w : S → ℝ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (T : ClockTree S as) (q r : ℕ → Fin (n+1) → ℝ≥0) (P : T.Assignment → ℝ)
    (hP : ∀ σ, 0 ≤ P σ) {C : ℝ} (x : Fin (n+1) → ℝ)
    (h : ∀ σ, ExpClose C (T.weight w φ q σ x) (T.weight w φ r σ x)) :
    ExpClose C (T.expect w φ q P x) (T.expect w φ r P x) := by
  unfold ClockTree.expect
  apply ExpClose.finset_sum
  intro σ _
  simpa only [add_zero] using (h σ).mul (ExpClose.refl (hP σ))

 

 theorem ClockTree.root_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (T : ClockTree S as) (ho : MassOrdered 0 as)
    (q r : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0) {C : ℝ}
    (h : ∀ σ x, ExpClose C (T.weight w φ q σ x) (T.weight w φ r σ x))
    (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    ExpClose C (T.atomicHead w φ q v 0 σ x) (T.atomicHead w φ r v 0 σ x) := by
  simp only [ClockTree.atomicHead,shiftedMean_zero,zeroContinuation]
  exact ExpClose.integral ((T.weight_smooth hw φ ho q σ 0).integrable_zero_shift x)
    ((T.weight_smooth hw φ ho r σ 0).integrable_zero_shift x) (fun z => h σ (x+z))

 theorem ClockTree.cumulative_uniform_expect_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (T : ClockTree S as)
    (ho : MassOrdered 0 as) (D M : Fin (n+1) → ℝ)
    (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (l : Fin (n+1) → ℝ) (q r : ℕ → Fin (n+1) → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hql : ∀ i, l i ≤ q 0 i) (hrl : ∀ i, l i ≤ r 0 i)
    (hend : q (as.length-1) = r (as.length-1))
    (hM : ∀ i, 0 ≤ M i) (hm : ∀ i j, j < as.length → |q j i-r j i| ≤ M i)
    (P : T.Assignment → ℝ) (hP : ∀ σ, 0 ≤ P σ) (x : Fin (n+1) → ℝ) :
    ExpClose (2*(7*(T.leaves:ℝ)+8*(T.leaves:ℝ)^2*(T.leaves+1:ℝ))*∑ i, M i*(D i)^2)
      (T.expect w φ (cumulativeIncrements l q) P x) (T.expect w φ (cumulativeIncrements l r) P x) :=
  T.expect_close w φ _ _ P hP x (fun σ => T.cumulative_uniform_close hw φ ho D M hD hB l q r
    hq hr hql hrl hend hM hm σ x)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem ExpClose.limit_cost {α : Type*} {l : Filter α} [NeBot l]
    {c : α → ℝ} {C p q : ℝ} (hc : Tendsto c l (𝓝 C))
    (h : ∀ᶠ a in l, ExpClose (c a) p q) : ExpClose C p q := by
  obtain ⟨a,ha⟩ := h.exists
  refine ⟨ha.left_nonneg,ha.right_nonneg,?_,?_⟩
  · exact ge_of_tendsto (((Real.continuous_exp.tendsto C).comp hc).mul_const q) (h.mono fun _ hs => hs.le_mul)
  · exact ge_of_tendsto (((Real.continuous_exp.tendsto C).comp hc).mul_const p) (h.mono fun _ hs => hs.rev_le_mul)

 theorem MassOrdered.exists_positive_lower {as : List PositiveMass} (ho : MassOrdered 0 as) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ e : ℝ, 0 ≤ e → e ≤ δ → MassOrdered e as := by
  cases as with
  | nil => exact ⟨1,by norm_num,fun _ he he1 => ⟨he,he1⟩⟩
  | cons a as => exact ⟨a.val,a.property,fun _ he hea => ⟨he,hea,ho.2.2⟩⟩

variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ} {as : List PositiveMass}

 

def ClockTree.rootWeight (w : S → ℝ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (T : ClockTree S as) (l : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (σ : T.Assignment) (x : Fin (n+1) → ℝ) : ℝ :=
  T.atomicHead w φ (cumulativeIncrements (q 0) (fun k => q (k+1)))
    (fun i => Real.toNNReal (q 0 i-l i)) 0 σ x

 

 theorem ClockTree.rootCumulative_uniform_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (T : ClockTree S as)
    (ho : MassOrdered 0 as) (D M : Fin (n+1) → ℝ)
    (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (l : Fin (n+1) → ℝ) (q r : ℕ → Fin (n+1) → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hql : ∀ i, l i ≤ q 0 i) (hrl : ∀ i, l i ≤ r 0 i)
    (hend : q as.length = r as.length)
    (hM : ∀ i, 0 ≤ M i) (hm : ∀ i j, j ≤ as.length → |q j i-r j i| ≤ M i)
    (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    ExpClose (2*(7*(T.leaves:ℝ)+8*(T.leaves:ℝ)^2*(T.leaves+1:ℝ))*∑ i, M i*(D i)^2)
      (T.rootWeight w φ l q σ x) (T.rootWeight w φ l r σ x) := by
  let C := 2*(7*(T.leaves:ℝ)+8*(T.leaves:ℝ)^2*(T.leaves+1:ℝ))*∑ i, M i*(D i)^2
  let Kq := (2*(T.leaves:ℝ)+3)*∑ i, (Real.toNNReal (q 0 i-l i):ℝ)*(D i)^2
  let Kr := (2*(T.leaves:ℝ)+3)*∑ i, (Real.toNNReal (r 0 i-l i):ℝ)*(D i)^2
  obtain ⟨δ,hδ,hd⟩ := ho.exists_positive_lower
  have hc : Continuous (fun e : ℝ => (e*Kq+C)+e*Kr) := by fun_prop
  apply ExpClose.limit_cost (l := 𝓝[>] (0:ℝ))
    (c := fun e => (e*Kq+C)+e*Kr)
    (by simpa only [zero_mul,zero_add,add_zero] using
      ((hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds))
  filter_upwards [self_mem_nhdsWithin,
    (Iio_mem_nhds hδ : Iio δ ∈ 𝓝 (0:ℝ)) |> mem_nhdsWithin_of_mem_nhds] with e he heδ
  have hep : 0 < e := he
  have hoe := hd e hep.le heδ.le
  have he1 := (massOrdered_bounds hoe).2
  let a : PositiveMass := ⟨e,hep⟩
  have hQ := T.atomicHead_mass_close_nonneg hw φ ho hoe le_rfl (by norm_num) hep he1 D hD hB
    (cumulativeIncrements (q 0) (fun k => q (k+1))) (fun i => Real.toNNReal (q 0 i-l i)) σ x
  have hR := T.atomicHead_mass_close_nonneg hw φ ho hoe le_rfl (by norm_num) hep he1 D hD hB
    (cumulativeIncrements (r 0) (fun k => r (k+1))) (fun i => Real.toNNReal (r 0 i-l i)) σ x
  have hE := (T.step a).cumulative_uniform_close hw φ ⟨le_rfl,hep.le,hoe⟩ D M hD hB l q r
    hq hr hql hrl (by simpa only [List.length_cons,Nat.add_sub_cancel] using hend) hM
    (fun i j hj => hm i j (by simpa only [List.length_cons,Nat.lt_add_one_iff] using hj)) σ x
  simp only [ClockTree.weight_step,cumulativeIncrements_shift,ClockTree.leaves] at hE
  change ExpClose C (T.atomicHead w φ _ _ e σ x) (T.atomicHead w φ _ _ e σ x) at hE
  simp only [zero_sub,abs_neg,abs_of_pos hep] at hQ hR
  convert (hQ.trans hE).trans hR.symm using 1 <;>
  dsimp only [Kq,Kr,ClockTree.rootWeight]
  ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E}

omit [NormedSpace ℝ E] [BorelSpace E] in
 theorem shiftedMean_add_const (F A : E → ℝ) (m c : ℝ) (x : E) :
    shiftedMean ν m (fun y => F y+c) A x = shiftedMean ν m F A x := by
  simp only [shiftedMean,tiltedMean,mul_add,Real.exp_add,← mul_assoc]
  rw [integral_mul_const,integral_mul_const]
  exact mul_div_mul_right _ _ (Real.exp_ne_zero _)

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [Nonempty S]

 theorem spinWeight_mass_one {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ι → ℝ≥0) (C : ι → ℝ)
    (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i) (σ : S) (x : ι → ℝ) :
    shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) 1 (spinLogPartition w φ)
      (fun y => spinWeight w φ y σ) x = spinWeight w φ x σ := by
  have hd := exp_mul_shiftedContinuation (by norm_num : (1:ℝ) ≠ 0) x
    ((exponentialIncrement_gaussian q).integrable_shift (lipschitzWith_spinLogPartition hw φ) 1 x)
  rw [spinLogPartition_mass_one hw φ q C hC x,one_mul,Real.exp_add,spinLogPartition,
    Real.exp_log (spinPartition_pos hw φ x)] at hd
  unfold shiftedMean tiltedMean
  rw [← hd]
  have hn : (∫ z, spinWeight w φ (x+z) σ*Real.exp (1*spinLogPartition w φ (x+z))
      ∂Measure.pi fun i => gaussianReal 0 (q i)) =
      w σ*Real.exp (φ σ x)*Real.exp ((1/2:ℝ)*∑ i, (q i:ℝ)*C i) := by
    simp only [one_mul,spinLogPartition,Real.exp_log (spinPartition_pos hw φ _),spinWeight,
      div_mul_cancel₀ _ (spinPartition_pos hw φ _).ne']
    simp_rw [map_add,Real.exp_add]
    rw [integral_const_mul,integral_const_mul,integral_exp_finiteLinear]
    simp_rw [hC]
    ring
  rw [hn,mul_div_mul_right _ _ (Real.exp_ne_zero _)]
  rfl

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
universe vC
variable {S : Type vC} {ι : Type*}

def terminalMass : PositiveMass := ⟨1,by norm_num⟩

 
def ClockTree.extendOne : {as : List PositiveMass} → ClockTree S as → ClockTree S (as++[terminalMass])
  | _,.leaf => .step terminalMass .leaf
  | _,.step a T => .step a T.extendOne
  | _,.fork T U => .fork T.extendOne U.extendOne

noncomputable def ClockTree.extendOneEquiv : {as : List PositiveMass} → (T : ClockTree S as) →
    T.Assignment ≃ T.extendOne.Assignment
  | _,.leaf => Equiv.refl S
  | _,.step _ T => T.extendOneEquiv
  | _,.fork T U => Equiv.prodCongr T.extendOneEquiv U.extendOneEquiv

 theorem ClockTree.extendOne_leaves {as : List PositiveMass} (T : ClockTree S as) :
    T.extendOne.leaves = T.leaves := by
  induction T with
  | leaf => rfl
  | step a T ih => exact ih
  | fork T U ihT ihU => exact congrArg₂ (·+·) ihT ihU

 theorem MassOrdered.append_one {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as) :
    MassOrdered a (as++[terminalMass]) := by
  induction as generalizing a with
  | nil => exact ⟨ho.1,ho.2,by norm_num [MassOrdered,terminalMass]⟩
  | cons b bs ih => exact ⟨ho.1,ho.2.1,ih ho.2.2⟩

variable [Fintype ι] [DecidableEq ι] [Fintype S] [Nonempty S]

 

 theorem ClockTree.weight_extendOne {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (C : ι → ℝ)
    (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    {as : List PositiveMass} (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → ι → ℝ≥0) (σ : T.Assignment) (x : ι → ℝ) :
    T.extendOne.weight w φ q (T.extendOneEquiv σ) x = T.weight w φ q σ x := by
  induction T generalizing a q x with
  | leaf => exact spinWeight_mass_one hw φ (q 0) C hC σ x
  | @step b bs T ih =>
    change (T.extendOne.step b).weight w φ q (T.extendOneEquiv σ) x = (T.step b).weight w φ q σ x
    rw [ClockTree.weight_step,ClockTree.weight_step]
    have he : T.extendOne.weight w φ (fun j => q (j+1)) (T.extendOneEquiv σ) =
        T.weight w φ (fun j => q (j+1)) σ := funext (ih ho.2.2 _ σ)
    rw [he,clockSteps_append]
    simp only [clockSteps,Nat.add_zero,terminalMass]
    have hg := gaussianHierarchy_append_mass_one hw φ (q (bs.length+1)) C hC
      (clockSteps bs (fun j => q (j+1))) (clockSteps_ordered ho.2.2 _)
    rw [show gaussianHierarchy w φ (clockSteps bs (fun j => q (j+1)) ++ [(1,q (bs.length+1))]) =
      (fun y => gaussianHierarchy w φ (clockSteps bs (fun j => q (j+1))) y+
        (1/2:ℝ)*∑ i, (q (bs.length+1) i:ℝ)*C i) from funext hg]
    exact shiftedMean_add_const _ _ _ _ _
  | fork T U ihT ihU =>
    change T.extendOne.weight w φ q (T.extendOneEquiv σ.1) x*
      U.extendOne.weight w φ q (U.extendOneEquiv σ.2) x = T.weight w φ q σ.1 x*U.weight w φ q σ.2 x
    rw [ihT ho,ihU ho]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ} {as : List PositiveMass}

 omit [Nonempty S] in
 theorem ClockTree.rootWeight_congr (w : S → ℝ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (T : ClockTree S as) (l : Fin (n+1) → ℝ) {q r : ℕ → Fin (n+1) → ℝ}
    (he : ∀ j ≤ as.length, q j = r j) (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    T.rootWeight w φ l q σ x = T.rootWeight w φ l r σ x := by
  simp only [ClockTree.rootWeight,ClockTree.atomicHead,shiftedMean_zero,zeroContinuation]
  rw [he 0 (Nat.zero_le _)]
  apply integral_congr_ae
  filter_upwards [] with z
  exact T.cumulative_weight_congr w φ (r 0) (fun j hj => he (j+1) (by omega)) σ (x+z)

 theorem ClockTree.rootWeight_extendOne {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (C : Fin (n+1) → ℝ)
    (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    (T : ClockTree S as) (ho : MassOrdered 0 as)
    (l : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    T.extendOne.rootWeight w φ l q (T.extendOneEquiv σ) x = T.rootWeight w φ l q σ x := by
  simp only [ClockTree.rootWeight,ClockTree.atomicHead,shiftedMean_zero,zeroContinuation]
  apply integral_congr_ae
  filter_upwards [] with z
  exact T.weight_extendOne hw φ C hC ho _ σ (x+z)

 

 theorem ClockTree.rootCumulative_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (C : Fin (n+1) → ℝ)
    (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    (T : ClockTree S as) (ho : MassOrdered 0 as) (D M : Fin (n+1) → ℝ)
    (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (l : Fin (n+1) → ℝ) (q r : ℕ → Fin (n+1) → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hql : ∀ i, l i ≤ q 0 i) (hrl : ∀ i, l i ≤ r 0 i)
    (hM : ∀ i, 0 ≤ M i) (hm : ∀ i j, j ≤ as.length → |q j i-r j i| ≤ M i)
    (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    ExpClose (2*(7*(T.leaves:ℝ)+8*(T.leaves:ℝ)^2*(T.leaves+1:ℝ))*∑ i, M i*(D i)^2)
      (T.rootWeight w φ l q σ x) (T.rootWeight w φ l r σ x) := by
  let t := fun i => max (q as.length i) (r as.length i)
  let Q := extendBoundary q as.length t
  let R := extendBoundary r as.length t
  have hQ : ∀ j ≤ as.length, Q j = q j := fun j hj => extendBoundary_le _ _ _ hj
  have hR : ∀ j ≤ as.length, R j = r j := fun j hj => extendBoundary_le _ _ _ hj
  have hQT : ∀ j, as.length < j → Q j = t := fun j hj => extendBoundary_gt _ _ _ hj
  have hRT : ∀ j, as.length < j → R j = t := fun j hj => extendBoundary_gt _ _ _ hj
  have hE := T.extendOne.rootCumulative_uniform_close hw φ ho.append_one D M hD hB l Q R
    (extendBoundary_monotone hq (fun i => le_max_left _ _))
    (extendBoundary_monotone hr (fun i => le_max_right _ _))
    (fun i => by rw [hQ 0 (Nat.zero_le _)]; exact hql i)
    (fun i => by rw [hR 0 (Nat.zero_le _)]; exact hrl i)
    (by rw [hQT _ (by simp),hRT _ (by simp)]) hM
    (fun i j _ => by
      by_cases hj : j ≤ as.length
      · rw [hQ j hj,hR j hj]; exact hm i j hj
      · rw [hQT j (lt_of_not_ge hj),hRT j (lt_of_not_ge hj),sub_self,abs_zero]; exact hM i)
    (T.extendOneEquiv σ) x
  rw [T.rootWeight_extendOne hw φ C hC ho,T.rootWeight_extendOne hw φ C hC ho,
    T.rootWeight_congr w φ l hQ σ x,T.rootWeight_congr w φ l hR σ x,ClockTree.extendOne_leaves] at hE
  exact hE

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*}

 

@[reducible] def Slot : {steps : List (GaussianStep ι)} → ReplicaTree ι S steps → Type
  | _, .leaf => Unit
  | _, .step _ T => T.Slot
  | _, .fork T U => T.Slot ⊕ U.Slot

def atSlot : {steps : List (GaussianStep ι)} → (T : ReplicaTree ι S steps) → T.Assignment → T.Slot → S
  | _, .leaf => fun σ _ => σ
  | _, .step _ T => T.atSlot
  | _, .fork T U => fun σ s => Sum.elim (T.atSlot σ.1) (U.atSlot σ.2) s

def singleSlot : (steps : List (GaussianStep ι)) → (single (S := S) steps).Slot
  | [] => ()
  | _::tail => singleSlot tail

 theorem atSlot_single (steps : List (GaussianStep ι)) (σ : (single (S := S) steps).Assignment) :
    (single steps).atSlot σ (singleSlot steps) = singleEquiv (S := S) steps σ := by
  induction steps with
  | nil => rfl
  | cons st tail ih => exact ih σ

 

structure MarkedPlacement {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) extends Placement T where
  embed : T.Slot → tree.Slot
  mark : tree.Slot
  restrict_at : ∀ σ s, T.atSlot (restrict σ) s = tree.atSlot σ (embed s)
  spin_at : ∀ σ, spin σ = tree.atSlot σ mark

namespace MarkedPlacement

def fresh {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (c : ℝ) : MarkedPlacement T where
  toPlacement := Placement.fresh T c
  embed := Sum.inl
  mark := Sum.inr (singleSlot steps)
  restrict_at := fun _ _ => rfl
  spin_at := fun σ => (atSlot_single steps σ.2).symm

def coincide : MarkedPlacement (ReplicaTree.leaf (ι := ι) (S := S)) where
  toPlacement := Placement.coincide
  embed := id
  mark := ()
  restrict_at := fun _ _ => rfl
  spin_at := fun _ => rfl

def step (st : GaussianStep ι) {tail : List (GaussianStep ι)} {T : ReplicaTree ι S tail}
    (p : MarkedPlacement T) : MarkedPlacement (T.step st) where
  toPlacement := p.toPlacement.step st
  embed := p.embed
  mark := p.mark
  restrict_at := p.restrict_at
  spin_at := p.spin_at

def left {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    (U : ReplicaTree ι S steps) (p : MarkedPlacement T) : MarkedPlacement (T.fork U) where
  toPlacement := p.toPlacement.left U
  embed := Sum.map p.embed id
  mark := Sum.inl p.mark
  restrict_at := by intro σ s; cases s with
    | inl s => exact p.restrict_at σ.1 s
    | inr s => rfl
  spin_at := fun σ => p.spin_at σ.1

def right {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {U : ReplicaTree ι S steps} (p : MarkedPlacement U) : MarkedPlacement (T.fork U) where
  toPlacement := p.toPlacement.right T
  embed := Sum.map id p.embed
  mark := Sum.inr p.mark
  restrict_at := by intro σ s; cases s with
    | inl s => rfl
    | inr s => exact p.restrict_at σ.2 s
  spin_at := fun σ => p.spin_at σ.2
end MarkedPlacement

def markedAttach : {steps : List (GaussianStep ι)} → (T : ReplicaTree ι S steps) → ℝ → List (MarkedPlacement T)
  | _, .leaf, a => [MarkedPlacement.coincide,MarkedPlacement.fresh .leaf (a-1)]
  | _, @ReplicaTree.step _ _ st tail T, a =>
      MarkedPlacement.fresh (.step st T) (a-st.1) :: (T.markedAttach st.1).map (MarkedPlacement.step st)
  | _, .fork T U, a => MarkedPlacement.fresh (T.fork U) (-a) ::
      ((T.markedAttach a).map (MarkedPlacement.left U) ++ (U.markedAttach a).map (MarkedPlacement.right T))

 theorem markedAttach_forget {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ) :
    (T.markedAttach a).map MarkedPlacement.toPlacement = T.attach a := by
  induction T generalizing a with
  | leaf => rfl
  | step st T ih =>
    simp only [markedAttach,attach,List.map_cons,List.map_map]
    rw [← ih st.1,List.map_map]
    rfl
  | fork T U ihT ihU =>
    simp only [markedAttach,attach,List.map_cons,List.map_append,List.map_map]
    rw [← ihT a,← ihU a,List.map_map,List.map_map]
    rfl

 theorem markedAttach_mass {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ) :
    ((T.markedAttach a).map fun p => p.coeff).sum = a := by
  have h := T.attach_mass a
  rw [← T.markedAttach_forget a] at h
  simpa only [mass,List.map_map,Function.comp_def] using h

noncomputable def MarkedPlacement.hit {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    (p : MarkedPlacement T) (s : T.Slot) : ℝ := by
  classical
  exact if p.mark = p.embed s then 1 else 0

 theorem MarkedPlacement.hit_fresh {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (c : ℝ) (s : T.Slot) : (MarkedPlacement.fresh T c).hit s = 0 := by
  classical
  unfold MarkedPlacement.hit
  apply ite_eq_right
  intro h
  cases h

 theorem MarkedPlacement.hit_step {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    (st : GaussianStep ι) (p : MarkedPlacement T) (s : T.Slot) : (p.step st).hit s = p.hit s := rfl

 theorem MarkedPlacement.coeff_step {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    (st : GaussianStep ι) (p : MarkedPlacement T) : (p.step st).coeff = p.coeff := rfl

 

 theorem markedAttach_hit {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ) (s : T.Slot) :
    ((T.markedAttach a).map fun p => p.coeff*p.hit s).sum = 1 := by
  classical
  induction T generalizing a with
  | leaf => cases s; simp [markedAttach,MarkedPlacement.hit,MarkedPlacement.coincide,
      MarkedPlacement.fresh,Placement.coincide,Placement.fresh]
  | step st T ih =>
    simp only [markedAttach,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,
      MarkedPlacement.hit_fresh,mul_zero,zero_add,MarkedPlacement.hit_step,MarkedPlacement.coeff_step]
    exact ih st.1 s
  | fork T U ihT ihU =>
    cases s with
    | inl s =>
      simpa only [markedAttach,List.map_cons,List.sum_cons,List.map_append,List.sum_append,List.map_map,
        Function.comp_def,MarkedPlacement.fresh,MarkedPlacement.left,MarkedPlacement.right,
        Placement.fresh,Placement.left,Placement.right,MarkedPlacement.hit,Sum.map_inl,id_eq,
        Sum.inr_ne_inl,Sum.inl.injEq,ite_false,mul_zero,List.map_const',List.sum_replicate,nsmul_zero,
        zero_add,add_zero] using ihT a s
    | inr s =>
      simpa only [markedAttach,List.map_cons,List.sum_cons,List.map_append,List.sum_append,List.map_map,
        Function.comp_def,MarkedPlacement.fresh,MarkedPlacement.left,MarkedPlacement.right,
        Placement.fresh,Placement.left,Placement.right,MarkedPlacement.hit,Sum.map_inr,id_eq,
        Sum.inr_ne_inl,Sum.inl_ne_inr,Sum.inr.injEq,ite_false,mul_zero,List.map_const',List.sum_replicate,nsmul_zero,
        zero_add,add_zero] using ihU a s

 

 theorem markedAttach_diagonal {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ) :
    ((T.markedAttach a).map fun p => p.coeff *
      ((p.tree.markedAttach a).map fun q => q.coeff*q.hit p.mark).sum).sum = a := by
  simp only [markedAttach_hit,mul_one,markedAttach_mass]

end SKFluctuations.Hierarchy.ReplicaTree

end

end OAI
