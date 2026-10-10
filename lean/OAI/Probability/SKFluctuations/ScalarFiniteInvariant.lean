import Mathlib
import OAI.Probability.SKFluctuations.InvariantPropagation

namespace OAI

/-! Scalar Finite Invariant. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open Set GaussianCalculus Scalar
open scoped NNReal

theorem scalarClock_realJet_zero (cs : List HeatClock) {m : ℝ} (hm : 0 < m)
    (ho : OrderedSteps m (heatSteps (ι := Fin 1) cs)) (k : ℕ) (x : ℝ) :
    realSpatialJet ((scalarTerminal.schedule cs).scalarClockPlane m) k (0,x) =
      scalarSourceJet (heatSteps cs) k x := by
  have hs := (scalarTerminal.schedule cs).scalarClockPlane_spatialRegular
    (scalar_schedule_smoothG cs (ho.lower (le_refl 0) hm.le)) hm
  induction k generalizing x with
  | zero =>
    change clockContinuation m (scalarTerminal.schedule cs).F 0 (fun _ => x) = _
    rw [clockContinuation_zero hm.ne']
    exact scalar_schedule_eq_hierarchy _ _
  | succ k ih =>
    have hd := realSpatialJet_hasDerivAt hs k 0 x
    have he : (fun y => realSpatialJet ((scalarTerminal.schedule cs).scalarClockPlane m) k (0,y)) =
        scalarSourceJet (heatSteps cs) k := funext ih
    rw [he] at hd
    exact hd.unique (scalarSourceJet_hasDerivAt (ho.lower (le_refl 0) hm.le) k x)

theorem scalarSourceJet_schedule_curvature_pos (cs : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) cs)) (x : ℝ) :
    0 < scalarSourceJet (heatSteps cs) 2 x := by
  rw [scalarSourceJet_two_schedule cs ho]
  have hl := scalar_schedule_curvature_lower cs
    (fun c hc => (scalar_schedule_ordered_masses ho c hc).2) (fun _ => x)
  exact (mul_pos (Real.exp_pos _) (curvature_pos x)).trans_le hl

theorem scalarSourceJet_schedule_curvature_le_one (cs : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) cs)) (x : ℝ) :
    scalarSourceJet (heatSteps cs) 2 x ≤ 1 := by
  rw [scalarSourceJet_two_schedule cs ho]
  have ha := scalarTerminal_admissible.schedule cs
    (fun c hc => (scalar_schedule_ordered_masses ho c hc).2) (fun _ => x)
  nlinarith [sq_nonneg ((scalarTerminal.schedule cs).G 0 (fun _ => x))]

theorem scalarClock_polynomialSigns (cs : List HeatClock) {m : ℝ} (hm : 0 < m)
    (ho : OrderedSteps m (heatSteps (ι := Fin 1) cs))
    (hi : PolynomialSigns m (scalarSourceJet (heatSteps cs))) (t : ℝ≥0) :
    PolynomialSigns m (scalarSourceJet (heatSteps (clockPrepend cs m hm t))) := by
  let u := (scalarTerminal.schedule cs).scalarClockPlane m
  let C3 : ℝ := (ReplicaTree.attachmentCount 1 2:ℝ)/m
  let C4 : ℝ := (ReplicaTree.attachmentCount 1 3:ℝ)/m
  let K := 1+C3+C4
  have hC3 : 0 ≤ C3 := by dsimp only [C3]; positivity
  have hC4 : 0 ≤ C4 := by dsimp only [C4]; positivity
  have ho0 := ho.lower (le_refl 0) hm.le
  have hG := scalar_schedule_smoothG cs ho0
  have hH := scalar_schedule_smoothH cs ho0
  have he (s : ℝ) (hs : 0 ≤ s) (k : ℕ) (x : ℝ) :
      realSpatialJet u k (s,x) = scalarSourceJet (heatSteps (clockPrepend cs m hm ⟨s,hs⟩)) k x :=
    scalarClock_realJet_eq_sourceJet cs hm ho ⟨s,hs⟩ k x
  have hh (s : ℝ) (hs : 0 ≤ s) (x : ℝ) : 0 < realSpatialJet u 2 (s,x) := by
    rw [he s hs]
    exact scalarSourceJet_schedule_curvature_pos _ (clockPrepend_ordered cs hm ho _) x
  have hb (s : ℝ) (hs : 0 ≤ s) (k : ℕ) (x : ℝ) :
      |realSpatialJet u (k+2) (s,x)/realSpatialJet u 2 (s,x)| ≤
        (ReplicaTree.attachmentCount 1 (k+1):ℝ)/m := by
    rw [abs_div,abs_of_pos (hh s hs x),div_le_iff₀ (hh s hs x),he s hs,he s hs]
    apply scalarSourceJet_relative_curvature _ (clockPrepend_ordered cs hm ho _)
      (fun c hc => (scalar_schedule_ordered_masses (clockPrepend_ordered cs hm ho _) c hc).2)
      hm ho.bounds.2
    intro c hc
    change c ∈ ⟨m,hm,⟨s,hs⟩⟩::cs at hc
    rcases List.mem_cons.mp hc with rfl|hc
    · exact le_rfl
    · exact (scalar_schedule_ordered_masses ho c hc).1
  have hp := polynomialSigns_evolve (u := u) (R := t) (K := K) hm.le (by dsimp only [K]; positivity)
    ((scalarTerminal.schedule cs).scalarClockPlane_spatialRegular hG hm)
    ((scalarTerminal.schedule cs).scalarClockPlane_contDiffOn hG hH hm)
    (fun _ x ht => (scalarTerminal.schedule cs).scalarClockPlane_timePDE hG hH hm ht x)
    (fun s hs x => hh s hs.1.le x) (by
      intro s hs x
      refine ⟨?_,(hb s hs.1.le 1 x).trans ?_,(hb s hs.1.le 2 x).trans ?_⟩
      · rw [abs_of_pos (hh s hs.1.le x),he s hs.1.le]
        exact (scalarSourceJet_schedule_curvature_le_one _ (clockPrepend_ordered cs hm ho _) x).trans
          (by dsimp only [K]; linarith)
      · change C3 ≤ K; dsimp only [K]; linarith
      · change C4 ≤ K; dsimp only [K]; linarith)
    (scalarClock_realJet_uniform_tail cs hm ho t) (by
      intro s hs
      rw [he s hs.1,he s hs.1]
      have h3 := scalarSourceJet_schedule_parity _ (clockPrepend_ordered cs hm ho ⟨s,hs.1⟩) 3 0
      have h5 := scalarSourceJet_schedule_parity _ (clockPrepend_ordered cs hm ho ⟨s,hs.1⟩) 5 0
      norm_num only [neg_zero,neg_pow,one_pow,one_mul] at h3 h5
      constructor <;> linarith) (by
      simpa only [u,scalarClock_realJet_zero cs hm ho] using hi)
  have ht := hp t ⟨t.coe_nonneg,le_rfl⟩
  simpa only [u,scalarClock_realJet_eq_sourceJet cs hm ho] using ht

 
theorem scalar_schedule_polynomialSigns (cs : List HeatClock) {a : ℝ}
    (ho : OrderedSteps a (heatSteps (ι := Fin 1) cs)) :
    PolynomialSigns a (scalarSourceJet (heatSteps cs)) := by
  induction cs generalizing a with
  | nil => exact scalar_nil_polynomialSigns ho.bounds.2
  | cons c cs ih =>
    change 0 ≤ a ∧ a ≤ c.mass ∧ 0 < c.mass ∧ OrderedSteps c.mass (heatSteps cs) at ho
    have ht := scalarClock_polynomialSigns cs c.positive ho.2.2.2 (ih ho.2.2.2) c.time
    exact ht.decrease ho.2.1 (fun x => (scalarSourceJet_schedule_curvature_pos
      (c::cs) ⟨le_rfl,ho.1.trans ho.2.1,c.positive,ho.2.2.2⟩ x).le)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Scalar
open Set
open scoped Topology ContDiff

theorem UniformSpatialTail.bounded_mul {R B : ℝ} {f g : ℝ × ℝ → ℝ}
    (hf : UniformSpatialTail R f) (hg : ∀ t ∈ Icc 0 R, ∀ x, |g (t,x)| ≤ B) :
    UniformSpatialTail R (fun p => g p*f p) := by
  intro ε hε
  obtain ⟨L,hL⟩ := hf (ε/(|B|+1)) (div_pos hε (by positivity))
  refine ⟨L,fun t ht x hx => ?_⟩
  rw [abs_mul]
  have hh := (le_div_iff₀ (show 0 < |B|+1 by positivity)).mp (hL t ht x hx)
  have hm := mul_le_mul_of_nonneg_right ((hg t ht x).trans (le_abs_self B)) (abs_nonneg (f (t,x)))
  nlinarith [abs_nonneg (f (t,x))]

theorem third_barrier_source_nonpos {a g h x : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hg : 0 ≤ g) (hg1 : g ≤ 1) (hh : 0 ≤ h) (hx : 0 ≤ x) :
    (1/2:ℝ)*fifth x+a*g*fourth x+(3*a*h+6)*third x ≤ 0 := by
  have hz : 0 ≤ Real.tanh x := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.cosh_pos x).le
  have hz1 : Real.tanh x ≤ 1 := (le_abs_self _).trans (Real.abs_tanh_lt_one x).le
  have hf := third_nonpos hx
  have h5 : (1/2:ℝ)*fifth x+4*third x ≤ 0 := by
    have he : (1/2:ℝ)*fifth x+4*third x = 6*(Real.tanh x)^2*third x := by
      dsimp only [fifth,third,curvature]; ring
    rw [he]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hf
  have h4 : fourth x+2*third x ≤ 0 := by
    have he : fourth x+2*third x = -2*curvature x*(1-Real.tanh x)*(3*Real.tanh x+1) := by
      dsimp only [fourth,third,curvature]; ring
    rw [he]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num)
        (curvature_bounds x).1) (sub_nonneg.mpr hz1)) (by positivity)
  have hag : 0 ≤ a*g := mul_nonneg ha hg
  have hag1 : a*g ≤ 1 := (mul_le_of_le_one_left hg ha1).trans hg1
  have hm := mul_le_mul_of_nonneg_left (show fourth x ≤ -2*third x by linarith) hag
  have hm2 := mul_le_mul_of_nonneg_right hag1 (show 0 ≤ -2*third x by linarith)
  have hm3 := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 3*a*h by positivity) hf
  nlinarith

theorem third_uniform_tail (R : ℝ) : UniformSpatialTail R (fun p => third p.2) := by
  intro ε hε
  let C : ℝ := (Hierarchy.ReplicaTree.attachmentCount 1 2:ℝ)*Real.log 2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C/ε+1,fun _ _ x hx => ?_⟩
  have hh := Hierarchy.scalarSourceJet_schedule_jet_tail [] (by constructor <;> norm_num) 1 x
  simp only [Hierarchy.heatSteps,List.map_nil,List.sum_nil,add_zero] at hh
  change |x| *|Hierarchy.scalarSourceJet [] 3 x| ≤ C at hh
  rw [Hierarchy.scalar_nil_jet_three] at hh
  have hb : |x| *|third x| ≤ C := hh
  have hxp : 0 < |x| := by linarith [div_nonneg hC hε.le]
  have hc : C ≤ |x| *ε := (div_le_iff₀ hε).mp (show C/ε ≤ |x| by linarith)
  exact (mul_le_mul_iff_right₀ hxp).mp (hb.trans hc)

theorem third_barrier_evolve {u : ℝ × ℝ → ℝ} {a R κ : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hκ : 0 ≤ κ)
    (hs : ∀ k, SpatialRegular k u)
    (hu : ∀ k : ℕ, ContDiffOn ℝ k u {p : ℝ × ℝ | 0 < p.1})
    (hPDE : ∀ t x, 0 < t → HasDerivAt (fun s => u (s,x))
      ((1/2:ℝ)*(spatialJet u 2 (t,x)+a*(spatialJet u 1 (t,x))^2)) t)
    (hb : ∀ t ∈ Ioc 0 R, ∀ x, 0 < x →
      0 ≤ realSpatialJet u 1 (t,x) ∧ realSpatialJet u 1 (t,x) ≤ 1 ∧
      0 ≤ realSpatialJet u 2 (t,x) ∧ realSpatialJet u 2 (t,x) ≤ 1)
    (htail : UniformSpatialTail R (realSpatialJet u 3))
    (hodd : ∀ t ∈ Icc 0 R, realSpatialJet u 3 (t,0) = 0)
    (hinit : ∀ x, 0 ≤ x → realSpatialJet u 3 (0,x) ≤ κ*third x) :
    ∀ t ∈ Icc 0 R, ∀ x, 0 ≤ x → realSpatialJet u 3 (t,x) ≤ κ*Real.exp (-6*t)*third x := by
  let j := realSpatialJet u
  let E : ℝ → ℝ := fun s => κ*Real.exp (-6*s)
  let v : ℝ → ℝ → ℝ := fun s y => -j 3 (s,y)+E s*third y
  have hE (s : ℝ) : 0 ≤ E s := mul_nonneg hκ (Real.exp_nonneg _)
  have hEderiv (s : ℝ) : HasDerivAt E (-6*E s) s := by
    have hh := (((hasDerivAt_id s).const_mul (-6)).exp).const_mul κ
    convert hh using 1 <;> first | rfl | (dsimp only [E,id]; ring)
  have hvx (s x : ℝ) : HasDerivAt (v s) (-j 4 (s,x)+E s*fourth x) x :=
    (realSpatialJet_hasDerivAt hs 3 s x).neg.add ((third_derivative x).const_mul (E s))
  have hvxx (s x : ℝ) : HasDerivAt (fun y => -j 4 (s,y)+E s*fourth y)
      (-j 5 (s,x)+E s*fifth x) x :=
    (realSpatialJet_hasDerivAt hs 4 s x).neg.add ((fourth_derivative x).const_mul (E s))
  have he (s : ℝ) : deriv (v s) = fun y => -j 4 (s,y)+E s*fourth y := funext (fun y => (hvx s y).deriv)
  have hvtail : UniformSpatialTail R (fun p => v p.1 p.2) := by
    apply htail.neg.add
    apply (third_uniform_tail R).bounded_mul (B := κ)
    intro s hs x
    rw [abs_of_nonneg (hE s)]
    exact mul_le_of_le_one_right hκ (Real.exp_le_one_iff.mpr (by linarith [hs.1]))
  have hv := parabolic_nonneg_halfline (v := v) (d := fun _ _ => 1/2)
    (b := fun s x => a*j 1 (s,x)) (c := fun s x => 3*a*j 2 (s,x))
    (F := fun s x => -E s*((1/2:ℝ)*fifth x+a*j 1 (s,x)*fourth x+(3*a*j 2 (s,x)+6)*third x))
    (M := 3) (by
      apply Continuous.continuousOn
      exact (realSpatialJet_continuous hs 3).neg.add
        (((continuous_iff_continuousAt.mpr (fun s => (hEderiv s).continuousAt)).comp continuous_fst).mul
          (third_continuous.comp continuous_snd))) (by
      intro s hs x _
      have hd := (realJet_three_time hu hPDE (x := x) hs.1).neg.add ((hEderiv s).mul_const (third x))
      rw [he s,(hvxx s x).deriv]
      convert hd using 1
      first | rfl | (dsimp only [v]; ring))
    (by intros; norm_num) (by
      intro s hs x hx
      have hh := (mul_le_of_le_one_left (hb s hs x hx).2.2.1 ha1).trans
        (hb s hs x hx).2.2.2
      nlinarith) (by
      intro s hs x hx
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (hE s))
        (third_barrier_source_nonpos ha ha1 (hb s hs x hx).1 (hb s hs x hx).2.1
          (hb s hs x hx).2.2.1 hx.le)) (by
      intro x hx
      have hh := hinit x hx
      simpa only [v,E,mul_zero,Real.exp_zero,mul_one,neg_add_le_iff_le_add,add_zero] using
        (show 0 ≤ -j 3 (0,x)+κ*third x by linarith)) (by
      intro s hs
      simp only [v,j,hodd s hs,third,Real.tanh_zero,mul_zero,zero_mul,neg_zero,add_zero,le_refl])
    hvtail.lower_half
  intro t ht x hx
  have hh := hv t ht x hx
  change 0 ≤ -j 3 (t,x)+κ*Real.exp (-6*t)*third x at hh
  linarith

end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Scalar
open Filter
open scoped Topology

theorem PolynomialSigns.limit {α : Type*} {l : Filter α} [NeBot l]
    {a : ℝ} {js : α → ℕ → ℝ → ℝ} {j : ℕ → ℝ → ℝ}
    (ht : ∀ k x, Tendsto (fun n => js n k x) l (𝓝 (j k x)))
    (hs : ∀ n, PolynomialSigns a (js n)) : PolynomialSigns a j := by
  have hP (x : ℝ) : Tendsto (fun n => invariantP a (js n 2 x) (js n 3 x) (js n 4 x)) l
      (𝓝 (invariantP a (j 2 x) (j 3 x) (j 4 x))) :=
    (((ht 2 x).pow 3 |>.const_mul (-a)).sub (((ht 2 x).mul (ht 4 x)).div_const 2)).add
      (((ht 3 x).pow 2).div_const 2)
  have hQ (x : ℝ) : Tendsto (fun n => invariantQ (js n 2 x) (js n 3 x) (js n 4 x) (js n 5 x)) l
      (𝓝 (invariantQ (j 2 x) (j 3 x) (j 4 x) (j 5 x))) :=
    (((((ht 2 x).pow 2).neg.mul (ht 5 x)).div_const 2).add
      ((((ht 2 x).const_mul 2).mul (ht 3 x)).mul (ht 4 x))).sub
      ((((ht 3 x).pow 3).const_mul 3).div_const 2)
  have hR (x : ℝ) : Tendsto (fun n => invariantR a (js n 2 x) (js n 3 x) (js n 4 x) (js n 5 x)) l
      (𝓝 (invariantR a (j 2 x) (j 3 x) (j 4 x) (j 5 x))) :=
    (hQ x).add ((((ht 3 x).const_mul 3).mul (hP x)).div_const 2)
  exact ⟨fun x hx => le_of_tendsto (ht 3 x) (Eventually.of_forall fun n => (hs n).third x hx),
    fun x => ge_of_tendsto (hP x) (Eventually.of_forall fun n => (hs n).P x),
    fun x hx => ge_of_tendsto (hQ x) (Eventually.of_forall fun n => (hs n).Q x hx),
    fun x hx => le_of_tendsto (hR x) (Eventually.of_forall fun n => (hs n).R x hx)⟩

end SKFluctuations.Scalar

namespace SKFluctuations.Hierarchy
open Scalar
open scoped NNReal

 

theorem scalarProfileJet_polynomialSigns (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) : PolynomialSigns (α.mass l) (scalarProfileJet α l t) := by
  apply PolynomialSigns.limit
    (fun k x => (scalarProfileJet_tendstoUniformly α hα l t k).tendsto_at x)
  intro n
  exact scalar_schedule_polynomialSigns ((α.cappedApprox n).grid l t n)
    ((α.cappedApprox n).grid_ordered l t n (α.nonneg l) (le_max_left _ _)
      (α.cappedApprox_le_one hα n (l+t)))

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open Set Scalar Filter
open scoped NNReal Topology

theorem scalarSourceJet_schedule_gradient_zero (cs : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) cs)) :
    scalarSourceJet (heatSteps cs) 1 0 = 0 := by
  have hh := scalarSourceJet_schedule_parity cs ho 1 0
  norm_num only [neg_zero,pow_one,neg_one_mul] at hh
  linarith

theorem scalarSourceJet_schedule_gradient_nonneg (cs : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) cs)) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ scalarSourceJet (heatSteps cs) 1 x := by
  have hh := scalarSourceJet_schedule_gradient_monotone cs ho hx
  rwa [scalarSourceJet_schedule_gradient_zero cs ho] at hh

theorem scalarClock_third_barrier (cs : List HeatClock) {m κ : ℝ} (hm : 0 < m)
    (ho : OrderedSteps m (heatSteps (ι := Fin 1) cs)) (hκ : 0 ≤ κ)
    (hi : ∀ x, 0 ≤ x → scalarSourceJet (heatSteps cs) 3 x ≤ κ*third x) (t : ℝ≥0) :
    ∀ x, 0 ≤ x → scalarSourceJet (heatSteps (clockPrepend cs m hm t)) 3 x ≤
      κ*Real.exp (-6*(t:ℝ))*third x := by
  let u := (scalarTerminal.schedule cs).scalarClockPlane m
  have ho0 := ho.lower (le_refl 0) hm.le
  have hG := scalar_schedule_smoothG cs ho0
  have hH := scalar_schedule_smoothH cs ho0
  have he (s : ℝ) (hs : 0 ≤ s) (k : ℕ) (x : ℝ) :
      realSpatialJet u k (s,x) = scalarSourceJet (heatSteps (clockPrepend cs m hm ⟨s,hs⟩)) k x :=
    scalarClock_realJet_eq_sourceJet cs hm ho ⟨s,hs⟩ k x
  have hb := third_barrier_evolve (u := u) (R := t) hm.le ho.bounds.2 hκ
    ((scalarTerminal.schedule cs).scalarClockPlane_spatialRegular hG hm)
    ((scalarTerminal.schedule cs).scalarClockPlane_contDiffOn hG hH hm)
    (fun _ x ht => (scalarTerminal.schedule cs).scalarClockPlane_timePDE hG hH hm ht x)
    (by
      intro s hs x hx
      rw [he s hs.1.le,he s hs.1.le]
      refine ⟨scalarSourceJet_schedule_gradient_nonneg _ (clockPrepend_ordered cs hm ho _) hx.le,
        ?_,(scalarSourceJet_schedule_curvature_pos _ (clockPrepend_ordered cs hm ho _) x).le,
        scalarSourceJet_schedule_curvature_le_one _ (clockPrepend_ordered cs hm ho _) x⟩
      have hg := scalarSourceJet_bound (clockPrepend_ordered cs hm ho ⟨s,hs.1.le⟩) 0 x
      norm_num only [ReplicaTree.attachmentCount,Nat.cast_one,Nat.zero_add] at hg
      exact (le_abs_self _).trans hg)
    (scalarClock_realJet_uniform_tail cs hm ho t 1) (by
      intro s hs
      rw [he s hs.1]
      have h3 := scalarSourceJet_schedule_parity _ (clockPrepend_ordered cs hm ho ⟨s,hs.1⟩) 3 0
      norm_num only [neg_zero,neg_pow,one_pow,one_mul] at h3
      linarith) (by
      simpa only [u,scalarClock_realJet_zero cs hm ho] using hi)
  intro x hx
  have hh := hb t ⟨t.coe_nonneg,le_rfl⟩ x hx
  simpa only [u,scalarClock_realJet_eq_sourceJet cs hm ho] using hh

 
theorem scalar_schedule_third_barrier (cs : List HeatClock) {a : ℝ}
    (ho : OrderedSteps a (heatSteps (ι := Fin 1) cs)) {x : ℝ} (hx : 0 ≤ x) :
    scalarSourceJet (heatSteps cs) 3 x ≤
      Real.exp (-6*(cs.map (fun c => (c.time:ℝ))).sum)*third x := by
  induction cs generalizing a x with
  | nil => simp only [heatSteps,List.map_nil,List.sum_nil,mul_zero,Real.exp_zero,one_mul,
      scalar_nil_jet_three,le_refl]
  | cons c cs ih =>
    change 0 ≤ a ∧ a ≤ c.mass ∧ 0 < c.mass ∧ OrderedSteps c.mass (heatSteps cs) at ho
    have hh := scalarClock_third_barrier cs c.positive ho.2.2.2 (Real.exp_nonneg _)
      (fun y hy => ih ho.2.2.2 hy) c.time x hx
    change scalarSourceJet (heatSteps (c::cs)) 3 x ≤ _ at hh
    have he : Real.exp (-6*(cs.map (fun c => (c.time:ℝ))).sum)*Real.exp (-6*(c.time:ℝ)) =
        Real.exp (-6*((c.time:ℝ)+(cs.map (fun c => (c.time:ℝ))).sum)) := by
      rw [← Real.exp_add]; congr 1; ring
    simpa only [List.map_cons,List.sum_cons,he] using hh

 

theorem scalarProfileJet_third_barrier (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    scalarProfileJet α l t 3 x ≤ Real.exp (-6*(t:ℝ))*third x := by
  apply le_of_tendsto ((scalarProfileJet_tendstoUniformly α hα l t 3).tendsto_at x)
  apply Eventually.of_forall
  intro n
  have hh := scalar_schedule_third_barrier ((α.cappedApprox n).grid l t n)
    (scalarCappedJets_ordered α hα l t n) hx
  rw [PositiveMassProfile.grid_total_time] at hh
  exact hh

theorem scalarProfileJet_four_zero_upper (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) : scalarProfileJet α l t 4 0 ≤ -2*Real.exp (-6*(t:ℝ)) := by
  have hzero : scalarProfileJet α l t 3 0 = 0 := by
    have hh := scalarProfileJet_parity α hα l t 3 0
    norm_num only [neg_zero,neg_pow,one_pow,one_mul] at hh
    linarith
  have hd := ((third_derivative 0).const_mul (Real.exp (-6*(t:ℝ)))).sub
    (scalarProfileJet_hasDerivAt α hα l t 3 0)
  have hlim := hd.tendsto_slope_zero_right
  have hn : 0 ≤ Real.exp (-6*(t:ℝ))*fourth 0-scalarProfileJet α l t 4 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [mem_Ioi] at hx
    change 0 ≤ x⁻¹*((Real.exp (-6*(t:ℝ))*third (0+x)-scalarProfileJet α l t 3 (0+x))-
      (Real.exp (-6*(t:ℝ))*third 0-scalarProfileJet α l t 3 0))
    have ht0 : third 0 = 0 := by simp only [third,Real.tanh_zero,mul_zero,zero_mul]
    simp only [zero_add,ht0,mul_zero,hzero,sub_zero]
    exact mul_nonneg (inv_nonneg.mpr hx.le) (sub_nonneg.mpr (scalarProfileJet_third_barrier α hα l t hx.le))
  norm_num only [fourth,Real.tanh_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),
    zero_pow (by norm_num : (4:ℕ) ≠ 0),mul_zero,add_zero,sub_zero] at hn
  linarith

theorem scalarProfileJet_four_zero_neg (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) : scalarProfileJet α l t 4 0 < 0 :=
  (scalarProfileJet_four_zero_upper α hα l t).trans_lt (mul_neg_of_neg_of_pos (by norm_num) (Real.exp_pos _))

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Scalar
open Filter Set
open scoped Topology

theorem jet_tendstoUniformly_of_limit (J : ℕ → ℕ → ℝ → ℝ) (j : ℕ → ℝ → ℝ)
    (hd : ∀ n k x, HasDerivAt (J n k) (J n (k+1) x) x)
    (hb : ∀ k, ∃ M : ℝ, ∀ n x, |J n (k+1) x| ≤ M)
    (hj : ∀ k x, HasDerivAt (j k) (j (k+1) x) x)
    (h0 : TendstoUniformly (fun n => J n 0) (j 0) atTop) (k : ℕ) :
    TendstoUniformly (fun n => J n k) (j k) atTop := by
  have hc : UniformCauchySeqOn (fun n => J n 0) atTop univ := h0.tendstoUniformlyOn.uniformCauchySeqOn
  have he : ∀ k, jetLimit J k = j k := by
    intro k
    induction k with
    | zero =>
      exact funext fun x => tendsto_nhds_unique
        ((jet_tendstoUniformly J hd hb hc 0).tendsto_at x) (h0.tendsto_at x)
    | succ k ih =>
      funext x
      have hh := jetLimit_hasDerivAt J hd hb hc k x
      rw [ih] at hh
      exact hh.unique (hj k x)
  simpa only [he] using jet_tendstoUniformly J hd hb hc k
end SKFluctuations.Scalar

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

noncomputable def scalarClockCappedJets (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0)
    (m : ℝ) (hm : 0 < m) (r : ℝ≥0) (n k : ℕ) (x : ℝ) : ℝ :=
  scalarSourceJet (heatSteps (clockPrepend ((α.cappedApprox n).grid l t n) m hm r)) k x

section
variable (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0)
    {m : ℝ} (hm : 0 < m) (hmα : m ≤ α.mass l) (r : ℝ≥0)

include hα hm hmα

 theorem scalarClockCappedJets_ordered (n : ℕ) :
    OrderedSteps m (heatSteps (ι := Fin 1) ((α.cappedApprox n).grid l t n)) :=
  (α.cappedApprox n).grid_ordered l t n hm.le
    (hmα.trans (le_max_left _ _)) (α.cappedApprox_le_one hα n (l+t))

omit hmα in
 theorem scalarClockCappedJets_zero_tendsto :
    TendstoUniformly (fun n => scalarClockCappedJets α l t m hm r n 0)
      (fun x => (scalarProfileHeatJet α hα l t).scalarClockJet m 0 r (fun _ => x)) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hp : Tendsto (fun k : ℕ => (t:ℝ)*(1/2:ℝ)^k) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul (t:ℝ)
  filter_upwards [hp.eventually (gt_mem_nhds hε)] with n hn x
  have hb := clockContinuation_abs_sub_le
    (scalarTerminal.schedule ((α.cappedApprox n).grid l t n)).lipschitz
    (scalarProfileHeatJet α hα l t).lipschitz hm (K := (t:ℝ)*(1/2:ℝ)^n)
    (fun y => by rw [scalarProfileHeatJet_F]; exact scalar_capped_grid_error α hα n l t y) (r:ℝ) (fun _ => x)
  rw [Real.dist_eq,abs_sub_comm]
  apply (show |scalarClockCappedJets α l t m hm r n 0 x-
    (scalarProfileHeatJet α hα l t).scalarClockJet m 0 r (fun _ => x)| ≤ (t:ℝ)*(1/2:ℝ)^n from ?_).trans_lt hn
  change |scalarSourceJet (heatSteps (clockPrepend ((α.cappedApprox n).grid l t n) m hm r)) 0 x-_| ≤ _
  dsimp only [scalarSourceJet]
  rw [← scalar_schedule_eq_hierarchy]
  exact hb

 theorem scalarClockCappedJets_tendstoUniformly (k : ℕ) :
    TendstoUniformly (fun n => scalarClockCappedJets α l t m hm r n k)
      (fun x => (scalarProfileHeatJet α hα l t).scalarClockJet m k r (fun _ => x)) atTop := by
  apply jet_tendstoUniformly_of_limit (scalarClockCappedJets α l t m hm r) _
  · intro n k x
    exact scalarSourceJet_hasDerivAt (clockPrepend_ordered _ hm
      (scalarClockCappedJets_ordered α hα l t hm hmα n) r) k x
  · intro k
    exact ⟨_,fun n x => scalarSourceJet_bound (clockPrepend_ordered _ hm
      (scalarClockCappedJets_ordered α hα l t hm hmα n) r) k x⟩
  · intro k x
    exact realSpatialJet_hasDerivAt
      ((scalarProfileHeatJet α hα l t).scalarClockPlane_spatialRegular
        (fun k _ => scalarProfileJet_bddSmooth_all α hα l t k 0) hm) k r x
  · exact scalarClockCappedJets_zero_tendsto α hα l t hm r

 theorem scalarClockProfile_polynomialSigns :
    PolynomialSigns m (fun k x => (scalarProfileHeatJet α hα l t).scalarClockJet m k r (fun _ => x)) := by
  apply PolynomialSigns.limit (fun k x => (scalarClockCappedJets_tendstoUniformly α hα l t hm hmα r k).tendsto_at x)
  intro n
  exact scalar_schedule_polynomialSigns _
    (show OrderedSteps m (heatSteps (ι := Fin 1) (clockPrepend ((α.cappedApprox n).grid l t n) m hm r)) from
      ⟨hm.le,le_rfl,hm,scalarClockCappedJets_ordered α hα l t hm hmα n⟩)

 theorem scalarClockProfile_relative_spin (k : ℕ) (x : ℝ) :
    |(scalarProfileHeatJet α hα l t).scalarClockJet m (k+2) r (fun _ => x)| ≤
      (ReplicaTree.attachmentCount 1 (k+1):ℝ)*
        (1-|(scalarProfileHeatJet α hα l t).scalarClockJet m 1 r (fun _ => x)|) := by
  have ht (j) := (scalarClockCappedJets_tendstoUniformly α hα l t hm hmα r j).tendsto_at x
  apply le_of_tendsto_of_tendsto (ht (k+2)).abs (((ht 1).abs.const_sub 1).const_mul _)
  exact Eventually.of_forall fun n => scalarSourceJet_relative_spin
    (clockPrepend_ordered _ hm (scalarClockCappedJets_ordered α hα l t hm hmα n) r) k x

 theorem scalarClockProfile_third_barrier {x : ℝ} (hx : 0 ≤ x) :
    (scalarProfileHeatJet α hα l t).scalarClockJet m 3 r (fun _ => x) ≤
      Real.exp (-6*((t:ℝ)+(r:ℝ)))*third x := by
  apply le_of_tendsto ((scalarClockCappedJets_tendstoUniformly α hα l t hm hmα r 3).tendsto_at x)
  apply Eventually.of_forall
  intro n
  have hh := scalar_schedule_third_barrier _
    (clockPrepend_ordered _ hm (scalarClockCappedJets_ordered α hα l t hm hmα n) r) hx
  simpa only [scalarClockCappedJets,clockPrepend,List.map_cons,List.sum_cons,PositiveMassProfile.grid_total_time,add_comm] using hh

 theorem scalarClockProfile_relative_curvature (k : ℕ) (x : ℝ) :
    |(scalarProfileHeatJet α hα l t).scalarClockJet m (k+2) r (fun _ => x)| ≤
      ((ReplicaTree.attachmentCount 1 (k+1):ℝ)/m)*
        (scalarProfileHeatJet α hα l t).scalarClockJet m 2 r (fun _ => x) := by
  have ht (j) := (scalarClockCappedJets_tendstoUniformly α hα l t hm hmα r j).tendsto_at x
  apply le_of_tendsto_of_tendsto (ht (k+2)).abs ((ht 2).const_mul _)
  apply Eventually.of_forall
  intro n
  have ho := scalarClockCappedJets_ordered α hα l t hm hmα n
  have hc := clockPrepend_ordered _ hm ho r
  apply scalarSourceJet_relative_curvature _ hc
    (fun c h => (scalar_schedule_ordered_masses hc c h).2) hm (hmα.trans (hα l))
  intro c hc
  rcases List.mem_cons.mp hc with rfl|hc
  · exact le_rfl
  · exact (scalar_schedule_ordered_masses ho c hc).1

end
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem scalarProfileJet_window_tendsto (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    {l : ℕ → ℝ} {t : ℕ → ℝ≥0} {L : ℝ} {T : ℝ≥0}
    (hl : Tendsto l atTop (𝓝 L)) (ht : Tendsto t atTop (𝓝 T)) (k : ℕ) :
    TendstoUniformly (fun n => scalarProfileJet α (l n) (t n) k)
      (scalarProfileJet α L T k) atTop := by
  apply jet_tendstoUniformly_of_limit (fun n j => scalarProfileJet α (l n) (t n) j)
    (scalarProfileJet α L T)
    (fun n j x => scalarProfileJet_hasDerivAt α hα (l n) (t n) j x)
    (fun j => ⟨(ReplicaTree.attachmentCount 1 j:ℝ),fun n x => scalarProfileJet_bound α hα (l n) (t n) j x⟩)
    (scalarProfileJet_hasDerivAt α hα L T)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hb : Tendsto (fun n => |l n-L|+(3/2:ℝ)*|(t n:ℝ)-T|) atTop (𝓝 0) := by
    have hc : Tendsto (fun n => (t n:ℝ)) atTop (𝓝 (T:ℝ)) := (NNReal.continuous_coe.tendsto T).comp ht
    simpa only [sub_self,abs_zero,mul_zero,add_zero] using
      ((hl.sub_const L).abs.add ((hc.sub_const (T:ℝ)).abs.const_mul (3/2:ℝ)))
  filter_upwards [hb.eventually (gt_mem_nhds hε)] with n hn x
  rw [Real.dist_eq,scalarProfileJet_zero α hα,scalarProfileJet_zero α hα,abs_sub_comm]
  exact (HeatJet.profile_window_stability scalarTerminal_admissible α hα (l n) L (t n) T (fun _ => x)).trans_lt hn

theorem scalarProfileJet_window_continuous (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ → ℝ) (t : ℝ → ℝ≥0) (hl : Continuous l) (ht : Continuous t) (k : ℕ) :
    Continuous (fun p : ℝ × ℝ => scalarProfileJet α (l p.1) (t p.1) k p.2) := by
  rw [continuous_iff_seqContinuous]
  intro u p hu
  have hr := continuous_fst.tendsto p |>.comp hu
  have hx := continuous_snd.tendsto p |>.comp hu
  have hj := scalarProfileJet_window_tendsto α hα ((hl.tendsto p.1).comp hr) ((ht.tendsto p.1).comp hr) k
  have hc := ((scalarProfileJet_hasDerivAt α hα (l p.1) (t p.1) k p.2).continuousAt).tendsto.comp hx
  apply Filter.Tendsto.congr_dist hc
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he := (Metric.tendstoUniformly_iff.mp hj) ε hε
  filter_upwards [he] with n hn
  simp only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg dist_nonneg]
  exact hn (u n).2

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem scalarTailJet_spatial_continuous {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (k : ℕ) :
    Continuous (fun p : ℝ × (Fin 1 → ℝ) =>
      scalarProfileJet (rescaledMassProfile α hT) (T*p.1) (Real.toNNReal (T*(1-p.1))) k (p.2 0)) := by
  have hl : Continuous (fun q : ℝ => T*q) := continuous_const.mul continuous_id
  have ht : Continuous (fun q : ℝ => Real.toNNReal (T*(1-q))) :=
    continuous_real_toNNReal.comp (continuous_const.mul (continuous_const.sub continuous_id))
  exact (scalarProfileJet_window_continuous (rescaledMassProfile α hT)
      (fun s => (α.property.1 (s/T)).2) _ _ hl ht k).comp
      (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))

theorem scalarTailJet_F_continuous {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) :
    Continuous (fun p : ℝ × (Fin 1 → ℝ) => (scalarTailJet hT α p.1).F p.2) := by
  exact scalarTailJet_spatial_continuous hT α 0

theorem scalarTailJet_square_continuous {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) :
    Continuous (fun p : ℝ × (Fin 1 → ℝ) => (scalarTailJet hT α p.1).square.A p.2) := by
  exact (scalarTailJet_spatial_continuous hT α 1).pow 2

theorem scalarTailJet_square_bound {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) (q : ℝ)
    (y : Fin 1 → ℝ) : |(scalarTailJet hT α q).square.A y| ≤ 1 := by
  change |((scalarTailJet hT α q).G 0 y)^2| ≤ 1
  rw [abs_of_nonneg (sq_nonneg _)]
  have hh := abs_le.mp (scalarTailJet_G_bound hT α q 0 y)
  nlinarith

theorem scalarTailJet_lipschitz {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) (q : ℝ) :
    LipschitzWith 1 (scalarTailJet hT α q).F := (scalarTailJet hT α q).lipschitz

theorem HeatJet.observedSquare_continuous {n : ℕ} {J : ℝ → HeatJet n} {C : ℝ≥0} {K : ℝ}
    (hL : ∀ r, LipschitzWith C (J r).F)
    (hF : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => (J p.1).F p.2))
    (hA : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => (J p.1).square.A p.2))
    (hb : ∀ r y, |(J r).square.A y| ≤ K) (m T : ℝ) (x : Fin (n+1) → ℝ) :
    Continuous (fun r => (J r).observedSquare m (T*r) x) := by
  have hh := dynamic_clockTest_continuous hL hF hA hb m x
  exact hh.comp ((continuous_const.mul continuous_id).prodMk continuous_id)

 

theorem scalarTailJet_observedSquare_continuous {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (m : ℝ) :
    Continuous (fun q => (scalarTailJet hT α q).observedSquare m (T*q) 0) := by
  exact HeatJet.observedSquare_continuous (J:=scalarTailJet hT α)
    (scalarTailJet_lipschitz hT α) (scalarTailJet_F_continuous hT α)
    (scalarTailJet_square_continuous hT α) (scalarTailJet_square_bound hT α) m T 0

 

theorem scalarMinimizer_endpoint_le {T q m : ℝ} (hT : 0 < T) (hq : q ∈ Ioo (0:ℝ) 1)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles) (hm : 0 < m) (hm1 : m ≤ 1)
    (hf : ∀ s ∈ Ico (0:ℝ) q, α.val s = m)
    (hnext : ∀ r ∈ Ioo q 1, m < α.val r)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    (scalarTailJet hT α q).observedSquare m (T*q) 0 ≤ q := by
  have he : Tendsto (fun r => (scalarTailJet hT α r).observedSquare m (T*r) 0)
      (𝓝[>] q) (𝓝 ((scalarTailJet hT α q).observedSquare m (T*q) 0)) :=
    (scalarTailJet_observedSquare_continuous hT α m).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun r : ℝ => r+4*T*(r-q)) (𝓝[>] q) (𝓝 q) := by
    have hc : Continuous (fun r : ℝ => r+4*T*(r-q)) := by fun_prop
    simpa only [sub_self,mul_zero,add_zero] using
      (hc.tendsto q).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto he hr
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ r : ℝ in 𝓝[>] q, r < 1 from
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hq.2))] with r hqr hr1
  apply scalarMinimizer_flatten_endpoint_bound hT hq.1 hqr.le hr1.le α hα hm hm1 hf _ hmin
  have hpos : ∀ s ∈ Ioo q r, 0 < α.val s-m := fun s hs => sub_pos.mpr (hnext s ⟨hs.1,hs.2.trans hr1⟩)
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    (α.property.2.intervalIntegrable.sub intervalIntegrable_const) hpos hqr

end SKFluctuations.Hierarchy

end

end OAI
