import Mathlib
import OAI.Probability.SKFluctuations.ClockPairForkLedger
import OAI.Probability.SKFluctuations.UniformActualLaterProjection

namespace OAI

/-! Clock Pair Representation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory
open scoped NNReal
variable {S : Type*}

 

def pairClock : (as : List PositiveMass) → ℕ → ClockTree S as
  | [], _ => leaf.fork leaf
  | a::as, 0 => (single (a::as)).fork (single (a::as))
  | a::as, j+1 => (pairClock as j).step a

def pairSpin : (as : List PositiveMass) → (j : ℕ) → (pairClock (S:=S) as j).Assignment → S × S
  | [], _, σ => σ
  | a::as, 0, σ => (singleEquiv (S:=S) (a::as) σ.1,singleEquiv (S:=S) (a::as) σ.2)
  | _::as, j+1, σ => pairSpin as j σ

variable [Fintype S] [Nonempty S] {ι : Type*} [Fintype ι]

theorem pairClock_expect {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (as : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0) (j : ℕ) (P : S → S → ℝ) (x : ι → ℝ) :
    (pairClock as j).expect w φ q (fun σ => P (pairSpin as j σ).1 (pairSpin as j σ).2) x =
      pairMean w φ as q j P x := by
  induction as generalizing a q j x with
  | nil =>
    cases j <;>
      change (leaf.fork leaf).expect w φ q (fun σ => P σ.1 σ.2) x =
        leaf.expect w φ q (fun σ => leaf.expect w φ q (fun τ => P σ τ) x) x
    all_goals exact expect_fork w φ leaf leaf q (fun σ => P σ.1 σ.2) x
  | cons b as ih =>
    cases j with
    | zero =>
      simpa only [pairClock,pairSpin,pairMean,singleMean] using
        (expect_fork w φ (single (b::as)) (single (b::as)) q
          (fun σ => P (singleEquiv (S:=S) (b::as) σ.1) (singleEquiv (S:=S) (b::as) σ.2)) x)
    | succ j =>
      rw [pairMean]
      change ((pairClock as j).step b).expect w φ q
        (fun σ => P (pairSpin as j σ).1 (pairSpin as j σ).2) x = _
      rw [expect_step hw φ b _ ho.2.2]
      congr 1
      funext y
      exact ih ho.2.2 _ j y

variable {n : ℕ}

theorem pairRootMean_eq_rootExpect {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (as : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a as) (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (j : ℕ) (P : S → S → ℝ) (x : Fin (n+1) → ℝ) :
    pairRootMean w φ as q₀ q j P x =
      (pairClock as j).rootExpect w φ (fun σ => P (pairSpin as j σ).1 (pairSpin as j σ).2) q₀ q x := by
  simp only [rootExpect_eq_integral,pairClock_expect hw φ as ho,pairRootMean]

theorem pairRootMean_rpow_from_second {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (as : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a as) (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (j : ℕ) (E : S → S → ℝ) (x : Fin (n+1) → ℝ)
    {p B D : ℝ} (hp : 2 ≤ p) (hB : 0 ≤ B) (hE : ∀ σ τ, |E σ τ| ≤ B)
    (h₂ : pairRootMean w φ as q₀ q j (fun σ τ => (E σ τ)^2) x ≤ D^2) :
    pairRootMean w φ as q₀ q j (fun σ τ => |E σ τ|^p) x ≤ B^(p-2)*D^2 := by
  simp only [pairRootMean_eq_rootExpect hw φ as ho] at h₂ ⊢
  exact (pairClock as j).rootExpect_rpow_from_second hw φ ho _ q₀ q x hp hB
    (fun σ => hE _ _) h₂

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy.ClockTree
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

theorem rootExpect_pair_sq_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (E : ℕ → S → S → ℝ) {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j)
    {d : ℝ} (hd : 0 ≤ d) (hdiag : ∀ σ, |E as.length σ σ| ≤ d)
    (x : Fin (n+1) → ℝ)
    (he : ∀ j, pairRootMean w φ as q₀ q j (fun σ τ => (E j σ τ)^2) x ≤ (f j)^2)
    (s t : T.Slot) :
    T.rootExpect w φ (fun σ => (E (T.splitIndex s t) (T.atSlot σ s) (T.atSlot σ t))^2) q₀ q x ≤
      (T.forkCost f+d)^2 := by
  have hF := T.forkCost_nonneg hf
  by_cases hst : s = t
  · subst t
    rw [T.splitIndex_self]
    have hb (σ : T.Assignment) : (E as.length (T.atSlot σ s) (T.atSlot σ s))^2 ≤ d^2 := by
      have h := hdiag (T.atSlot σ s)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hd).2 h
    have h := T.rootExpect_mono hw φ ho hb q₀ q x
    rw [T.rootExpect_const hw φ ho] at h
    nlinarith
  · rw [T.rootExpect_pairAtSlot hw φ ho q₀ q s t hst
      (fun σ τ => (E (T.splitIndex s t) σ τ)^2) x]
    have hs := T.split_le_forkCost hf s t hst
    have hn := hf (T.splitIndex s t)
    exact (he _).trans (by nlinarith)

 

theorem profilePairTest_root_L2_envelope {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (P : T.Assignment → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (E : ℕ → S → S → ℝ) {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j)
    {d : ℝ} (hd : 0 ≤ d) (hdiag : ∀ σ, |E as.length σ σ| ≤ d)
    (x : Fin (n+1) → ℝ)
    (hP : T.rootExpect w φ (fun σ => (P σ)^2) q₀ q x ≤ C^2)
    (he : ∀ j, pairRootMean w φ as q₀ q j (fun σ τ => (E j σ τ)^2) x ≤ (f j)^2)
    (p : MarkedPlacement T) (hp : p ∈ T.markedAttach a)
    (r : MarkedPlacement p.tree) (hr : r ∈ p.tree.markedAttach a) :
    r.tree.rootExpect w φ (fun σ => |profilePairTest P E p r σ|) q₀ q x ≤
      C*(r.tree.forkCost f+d) := by
  have hb : r.tree.rootExpect w φ (fun σ => (P (p.restrict (r.restrict σ)))^2) q₀ q x ≤ C^2 := by
    rw [p.tree.markedAttach_rootPreserves hw φ ho r hr q₀ q
      (fun τ => (P (p.restrict τ))^2) x,
      T.markedAttach_rootPreserves hw φ ho p hp q₀ q (fun τ => (P τ)^2) x]
    exact hP
  have h := r.tree.rootExpect_abs_mul_le hw φ ho
    (fun σ => P (p.restrict (r.restrict σ)))
    (fun σ => E (r.tree.splitIndex (r.embed p.mark) r.mark)
      (r.tree.atSlot σ (r.embed p.mark)) (r.tree.atSlot σ r.mark)) q₀ q x hC
    (add_nonneg (r.tree.forkCost_nonneg hf) hd) hb
    (r.tree.rootExpect_pair_sq_le hw φ ho q₀ q E hf hd hdiag x he _ _)
  simpa only [profilePairTest,p.spin_at,r.restrict_at,r.spin_at] using h

 

theorem profilePairTest_sq_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hK : ∀ j σ τ, |K j σ τ| ≤ M) (x : Fin (n+1) → ℝ)
    (p : MarkedPlacement T) (hp : p ∈ T.markedAttach a)
    (r : MarkedPlacement p.tree) (hr : r ∈ p.tree.markedAttach a) :
    r.tree.rootExpect w φ (fun σ => (profilePairTest P K p r σ)^2) q₀ q x ≤
      M^2*T.rootExpect w φ (fun σ => (P σ)^2) q₀ q x := by
  calc
    _ ≤ r.tree.rootExpect w φ (fun σ => M^2*(P (p.restrict (r.restrict σ)))^2) q₀ q x := by
      apply r.tree.rootExpect_mono hw φ ho
      intro σ
      rw [profilePairTest,mul_pow,mul_comm (M^2)]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have h := hK (r.tree.splitIndex (r.embed p.mark) r.mark) (p.spin (r.restrict σ)) (r.spin σ)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).2 h
    _ = _ := by
      rw [r.tree.rootExpect_const_mul,p.tree.markedAttach_rootPreserves hw φ ho r hr q₀ q
        (fun τ => (P (p.restrict τ))^2) x,
        T.markedAttach_rootPreserves hw φ ho p hp q₀ q (fun τ => (P τ)^2) x]

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy.ClockTree
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 

theorem rootAbsProfileJets_poweredError_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (pre post : List (ℕ → S → S → ℝ))
    (E : ℕ → S → S → ℝ) (T : ClockTree S as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment → ℝ) {C M B d p : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hB : 0 ≤ B) (hd : 0 ≤ d) (hp : 2 ≤ p)
    (hP : ∀ σ, |P σ| ≤ C)
    (hpre : ∀ K ∈ pre, ∀ j σ τ, |K j σ τ| ≤ M)
    (hsuf : ∀ K ∈ post, ∀ j σ τ, |K j σ τ| ≤ M)
    (hE : ∀ j σ τ, |E j σ τ| ≤ B) (hdiag : ∀ σ, |E as.length σ σ| ≤ d)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (D : ℕ → ℝ)
    (x : Fin (n+1) → ℝ)
    (he : ∀ j, pairRootMean w φ as q₀ q j (fun σ τ => (E j σ τ)^2) x ≤ (D j)^2) :
    rootAbsProfileJets w φ q₀ q x (pre++(fun j σ τ => |E j σ τ|^p)::post) T P ≤
      absErrorJetVariation r pre.length post.length*C*M^(pre.length+post.length)*
        (T.forkCost (fun j => B^(p-2)*(D j)^2)+
          edgeBudget 0 as (fun j => B^(p-2)*(D j)^2)+d^p) := by
  apply rootAbsProfileJets_oneError_le hw φ ho pre post _ T hT P hC hM hP hpre hsuf
    q₀ q (fun j => mul_nonneg (Real.rpow_nonneg hB _) (sq_nonneg _))
    (Real.rpow_nonneg hd _) _ x
  · intro j
    simpa only [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using
      pairRootMean_rpow_from_second hw φ as ho q₀ q j (E j) x hp hB (hE j) (he j)
  · intro σ
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hdiag σ) (by linarith)

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

theorem relative_derivative_exp_comparison {f f' : ℝ → ℝ} {a b C : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Ioo a b, |f' t| ≤ C*f t)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    Real.exp (-C*(t-s))*f s ≤ f t ∧ f t ≤ Real.exp (C*(t-s))*f s := by
  have dm (u : ℝ) (hu : u ∈ Ioo a b) :
      HasDerivAt (fun v => f v*Real.exp (-C*v))
        ((f' u-C*f u)*Real.exp (-C*u)) u := by
    apply ((hd u hu).mul (((hasDerivAt_id u).const_mul (-C)).exp)).congr_deriv
    dsimp only [id_eq]
    ring
  have dp (u : ℝ) (hu : u ∈ Ioo a b) :
      HasDerivAt (fun v => f v*Real.exp (C*v))
        ((f' u+C*f u)*Real.exp (C*u)) u := by
    apply ((hd u hu).mul (((hasDerivAt_id u).const_mul C).exp)).congr_deriv
    dsimp only [id_eq]
    ring
  have hm : AntitoneOn (fun u => f u*Real.exp (-C*u)) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (hf.mul ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn))
    · intro u hu
      exact (dm u (by simpa only [interior_Icc] using hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' : u ∈ Ioo a b := by simpa only [interior_Icc] using hu
      change deriv (fun v => f v*Real.exp (-C*v)) u ≤ 0
      rw [(dm u hu').deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_abs_self _ |>.trans (hb u hu')))
        (Real.exp_pos _).le
  have hp : MonotoneOn (fun u => f u*Real.exp (C*u)) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (hf.mul ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn))
    · intro u hu
      exact (dp u (by simpa only [interior_Icc] using hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' : u ∈ Ioo a b := by simpa only [interior_Icc] using hu
      change 0 ≤ deriv (fun v => f v*Real.exp (C*v)) u
      rw [(dp u hu').deriv]
      apply mul_nonneg _ (Real.exp_pos _).le
      have h := (abs_le.mp (hb u hu')).1
      linarith
  constructor
  · have h := mul_le_mul_of_nonneg_right (hp hs ht hst) (Real.exp_pos (-C*t)).le
    have hl : (f s*Real.exp (C*s))*Real.exp (-C*t) = Real.exp (-C*(t-s))*f s := by
      rw [mul_assoc,← Real.exp_add,mul_comm]
      congr 2; ring
    have hr : (f t*Real.exp (C*t))*Real.exp (-C*t) = f t := by
      rw [mul_assoc,← Real.exp_add]
      simp
    rwa [hl,hr] at h
  · have h := mul_le_mul_of_nonneg_right (hm hs ht hst) (Real.exp_pos (C*t)).le
    have hl : (f t*Real.exp (-C*t))*Real.exp (C*t) = f t := by
      rw [mul_assoc,← Real.exp_add]
      simp
    have hr : (f s*Real.exp (-C*s))*Real.exp (C*t) = Real.exp (C*(t-s))*f s := by
      rw [mul_assoc,← Real.exp_add,mul_comm]
      congr 2; ring
    rwa [hl,hr] at h

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]

 

theorem ClockTree.disorderExpect_exp_comparison {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) {r : ℕ} (hT : T.leaves ≤ r)
    (v : ι → ℝ) (q K : ℕ → ι → ℝ) {a b : ℝ}
    (hp : ∀ u ∈ Ioo a b, ∀ i, Monotone (fun j => q j i+u*K j i))
    (hr : ∀ u ∈ Ioo a b, ∀ i, v i ≤ q 0 i+u*K 0 i)
    (P : T.Assignment → ℝ) (hP : ∀ σ, 0 ≤ P σ) {M : ℝ} (hM : 0 ≤ M)
    (hK : ∀ j σ τ, |ReplicaTree.coordinateProfile φ K j σ τ| ≤ M)
    (x : ι → ℝ) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    Real.exp (-ClockTree.jetVariation r 1*M*(t-s))*
        T.disorderExpect w φ v (fun j i => q j i+s*K j i) P x ≤
      T.disorderExpect w φ v (fun j i => q j i+t*K j i) P x ∧
    T.disorderExpect w φ v (fun j i => q j i+t*K j i) P x ≤
      Real.exp (ClockTree.jetVariation r 1*M*(t-s))*
        T.disorderExpect w φ v (fun j i => q j i+s*K j i) P x := by
  have hc := T.disorderExpect_continuous hw φ ho v
    (fun u j i => q j i+u*K j i) (by intro j; fun_prop) P (fun _ => x) continuous_const
  have hd (u : ℝ) (hu : u ∈ Ioo a b) :=
    ClockTree.hasDerivAt_finiteProfileJets hw φ ho v q K hp hr [] T P x hu
  have hbound (u : ℝ) (hu : u ∈ Ioo a b) :
      |ClockTree.disorderProfileJets w φ v (fun j i => q j i+u*K j i) x
        [ReplicaTree.coordinateProfile φ K] T P| ≤
        (ClockTree.jetVariation r 1*M)*T.disorderExpect w φ v (fun j i => q j i+u*K j i) P x := by
    have hb := ClockTree.disorderProfileJets_relative_abs_le hw φ ho
      [ReplicaTree.coordinateProfile φ K] T hT P hM
      (by intro L hL j σ τ; simpa only [List.mem_singleton.mp hL] using hK j σ τ)
      v (fun j i => q j i+u*K j i) x
    have habs : (fun σ => |P σ|) = P := funext fun σ => abs_of_nonneg (hP σ)
    simpa only [List.length_singleton,pow_one,habs,mul_assoc,mul_left_comm,mul_comm] using hb
  simpa only [neg_mul] using relative_derivative_exp_comparison hc.continuousOn hd hbound hs ht hst

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open scoped NNReal
variable {S ι : Type*}

 

def ClockTree.erase : {as : List PositiveMass} → {q : ℕ → ι → ℝ≥0} →
    ReplicaTree ι S (clockSteps as q) → ClockTree S as
  | [], _, .leaf => .leaf
  | a::as, q, .step _ T => .step a (ClockTree.erase (q := fun j => q (j+1)) T)
  | _, _, .fork T U => .fork (ClockTree.erase T) (ClockTree.erase U)

theorem ClockTree.erase_realize {as : List PositiveMass} {q : ℕ → ι → ℝ≥0}
    (T : ReplicaTree ι S (clockSteps as q)) : (ClockTree.erase T).realize q = T := by
  fun_induction ClockTree.erase T with
  | case1 => rfl
  | case2 a as q T ih => exact congrArg (ReplicaTree.step _) ih
  | case3 as q T U ihT ihU => exact congrArg₂ ReplicaTree.fork ihT ihU

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy.ClockTree
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 

theorem rootAbsProfileJets_triple_holder {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (x : Fin (n+1) → ℝ) {ι : Type*} (is : List ι)
    (K L M : ι → ℕ → S → S → ℝ)
    (T : ClockTree S as) (P Q R : T.Assignment → ℝ)
    {r s : ℝ} (hrs : r.HolderConjugate s) :
    rootAbsProfileJets w φ q₀ q x
      (is.map fun i j σ τ => (K i j σ τ*L i j σ τ)*M i j σ τ)
      T (fun σ => (P σ*Q σ)*R σ) ≤
      (rootAbsProfileJets w φ q₀ q x (is.map fun i j σ τ => |K i j σ τ|^(2*r))
        T (fun σ => |P σ|^(2*r)))^(1/(2*r))*
      (rootAbsProfileJets w φ q₀ q x (is.map fun i j σ τ => |L i j σ τ|^(2*r))
        T (fun σ => |Q σ|^(2*r)))^(1/(2*r))*
      (rootAbsProfileJets w φ q₀ q x (is.map fun i j σ τ => |M i j σ τ|^s)
        T (fun σ => |R σ|^s))^(1/s) := by
  let A := rootAbsProfileJets w φ q₀ q x (is.map fun i j σ τ => |K i j σ τ|^(2*r))
        T (fun σ => |P σ|^(2*r))
  let B := rootAbsProfileJets w φ q₀ q x (is.map fun i j σ τ => |L i j σ τ|^(2*r))
        T (fun σ => |Q σ|^(2*r))
  let D := rootAbsProfileJets w φ q₀ q x (is.map fun i j σ τ => |K i j σ τ*L i j σ τ|^r)
        T (fun σ => |P σ*Q σ|^r)
  have hA : 0 ≤ A := rootAbsProfileJets_nonneg hw φ ho q₀ q x _ T _
  have hB : 0 ≤ B := rootAbsProfileJets_nonneg hw φ ho q₀ q x _ T _
  have hD : 0 ≤ D := rootAbsProfileJets_nonneg hw φ ho q₀ q x _ T _
  have hi : D ≤ A^(1/(2:ℝ))*B^(1/(2:ℝ)) := by
    have hh := rootAbsProfileJets_holder hw φ ho q₀ q x is
      (fun i j σ τ => |K i j σ τ|^r) (fun i j σ τ => |L i j σ τ|^r)
      T (fun σ => |P σ|^r) (fun σ => |Q σ|^r) Real.HolderConjugate.two_two
    simpa only [D,A,B,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      ← Real.rpow_mul (abs_nonneg _),mul_comm r (2:ℝ),abs_mul,
      Real.mul_rpow (abs_nonneg _) (abs_nonneg _)] using hh
  have hpow := Real.rpow_le_rpow hD hi (div_nonneg zero_le_one hrs.nonneg)
  rw [Real.mul_rpow (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _),
    ← Real.rpow_mul hA,← Real.rpow_mul hB,
    show (1/(2:ℝ))*(1/r) = 1/(2*r) by ring] at hpow
  apply (rootAbsProfileJets_holder hw φ ho q₀ q x is
    (fun i j σ τ => K i j σ τ*L i j σ τ) M T (fun σ => P σ*Q σ) R hrs).trans
  exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg
    (rootAbsProfileJets_nonneg hw φ ho q₀ q x _ T _) _)

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

 

def pairSegmentKernel (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre mid tail : List (GaussianStep ι)) :=
  segmentKernel w φ (mid++tail) pre ⊗ₖ
    (segmentKernel w φ tail mid).comap
      (fun p : (ι → ℝ) × (Fin pre.length → (ι → ℝ)) =>
        forwardEnd pre.length (hierarchyIncrements pre) p.1 p.2)
      (measurable_forwardEnd _ (hierarchyIncrements_measurable pre))

def segmentPairField (pre mid : List (GaussianStep ι)) (x : ι → ℝ)
    (p : (Fin pre.length → (ι → ℝ)) × (Fin mid.length → (ι → ℝ))) :=
  let y := forwardEnd pre.length (hierarchyIncrements pre) x p.1
  (y,forwardEnd mid.length (hierarchyIncrements mid) y p.2)

omit [Fintype S] [Nonempty S] [MeasurableSpace S] [StandardBorelSpace S] in
theorem segmentPairField_measurable (pre mid : List (GaussianStep ι)) (x : ι → ℝ) :
    Measurable (segmentPairField pre mid x) := by
  have h : Measurable (fun p : (Fin pre.length → (ι → ℝ)) × (Fin mid.length → (ι → ℝ)) =>
      forwardEnd pre.length (hierarchyIncrements pre) x p.1) :=
    (measurable_forwardEnd _ (hierarchyIncrements_measurable pre)).comp
      (measurable_const.prodMk measurable_fst)
  exact h.prodMk ((measurable_forwardEnd _ (hierarchyIncrements_measurable mid)).comp
    (h.prodMk measurable_snd))

omit [MeasurableSpace S] [StandardBorelSpace S] in
theorem pairSegmentKernel_markov {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre mid tail : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++(mid++tail))) :
    IsMarkovKernel (pairSegmentKernel w φ pre mid tail) := by
  have := segmentKernel_markov hw φ (mid++tail) pre ha
  have := segmentKernel_markov hw φ tail mid (ha.suffix pre _)
  unfold pairSegmentKernel
  infer_instance

omit [MeasurableSpace S] [StandardBorelSpace S] in
theorem integral_segmentPairField_tensor {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre mid tail : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++(mid++tail))) {F G : (ι → ℝ) → ℝ}
    (hF : BddSmooth 0 F) (hG : BddSmooth 0 G) (x : ι → ℝ) :
    (∫ p, F (segmentPairField pre mid x p).1*G (segmentPairField pre mid x p).2
      ∂pairSegmentKernel w φ pre mid tail x) =
      prefixTest pre (gaussianHierarchy w φ (mid++tail))
        (fun y => F y*prefixTest mid (gaussianHierarchy w φ tail) G y) x := by
  have := segmentKernel_markov hw φ (mid++tail) pre ha
  have := segmentKernel_markov hw φ tail mid (ha.suffix pre _)
  have := pairSegmentKernel_markov hw φ pre mid tail ha
  have hf := (bddSmooth0_tensor hF hG).integrable_comp_measurable
    (μ := pairSegmentKernel w φ pre mid tail x) (segmentPairField_measurable pre mid x)
  unfold pairSegmentKernel at hf ⊢
  rw [ProbabilityTheory.integral_compProd hf]
  simp only [Kernel.comap_apply,segmentPairField]
  simp_rw [segmentKernel_apply hw φ tail mid (ha.suffix pre _), integral_const_mul,
    integral_segmentLaw_test hw φ hG tail mid (ha.suffix pre _)]
  obtain ⟨C,hL⟩ := gaussianHierarchy_lipschitz hw φ tail ((ha.suffix pre _).suffix mid _)
  have hm : ∀ st ∈ mid, 0 < st.1 := fun st hs =>
    (ha.suffix pre _).mem_pos st (List.mem_append_left tail hs)
  rw [segmentKernel_apply hw φ (mid++tail) pre ha,
    integral_segmentLaw_test hw φ (hF.mul (prefixTest_smooth0 hL hG mid hm)) (mid++tail) pre ha]

 

theorem actualPairCut_law {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre mid tail : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++(mid++tail))) (x : ι → ℝ) :
    (hierarchyPathKernel w φ (pre++(mid++tail)) x).map (actualPairCut (S := S) pre mid tail x) =
      (pairSegmentKernel w φ pre mid tail x).map (segmentPairField pre mid x) := by
  have := hierarchyPathKernel_markov hw φ (pre++(mid++tail)) ha
  have := pairSegmentKernel_markov hw φ pre mid tail ha
  apply Measure.ext_of_integral_mul_boundedContinuousFunction
  intro f g
  have hfg : Continuous (fun p : (ι → ℝ) × (ι → ℝ) => f p.1*g p.2) :=
    (f.continuous.comp continuous_fst).mul (g.continuous.comp continuous_snd)
  rw [integral_map (actualPairCut_measurable pre mid tail x).aemeasurable hfg.aestronglyMeasurable,
    integral_map (segmentPairField_measurable pre mid x).aemeasurable hfg.aestronglyMeasurable,
    integral_actualPairCut_tensor hw φ pre mid tail ha (boundedContinuous_bddSmooth0 f)
      (boundedContinuous_bddSmooth0 g) x,
    integral_segmentPairField_tensor hw φ pre mid tail ha (boundedContinuous_bddSmooth0 f)
      (boundedContinuous_bddSmooth0 g) x]

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

theorem map_compProd_eq_of_maps_eq {P A B C : Type*} [MeasurableSpace P]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure P) [SFinite μ] (κ : Kernel P A) (η : Kernel P B)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (f : P × A → C) (g : P × B → C)
    (hf : Measurable f) (hg : Measurable g)
    (he : ∀ p, (κ p).map (fun a => f (p,a)) = (η p).map (fun b => g (p,b))) :
    (μ ⊗ₘ κ).map f = (μ ⊗ₘ η).map g := by
  ext s hs
  rw [Measure.map_apply hf hs,Measure.compProd_apply (hf hs),
    Measure.map_apply hg hs,Measure.compProd_apply (hg hs)]
  apply lintegral_congr
  intro p
  have hp := congrArg (fun ν : Measure C => ν s) (he p)
  have hfp : Measurable (fun a : A => f (p,a)) := hf.comp (measurable_const.prodMk measurable_id)
  have hgp : Measurable (fun b : B => g (p,b)) := hg.comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hfp hs, Measure.map_apply hgp hs] at hp
  exact hp

variable {ι S P : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S] [MeasurableSpace P]

 
theorem actualPairCut_rooted_law {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre mid tail : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++(mid++tail)))
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x) :
    (μ ⊗ₘ (hierarchyPathKernel w φ (pre++(mid++tail))).comap x hx).map
      (fun p => (p.1,actualPairCut (S := S) pre mid tail (x p.1) p.2)) =
    (μ ⊗ₘ (pairSegmentKernel w φ pre mid tail).comap x hx).map
      (fun p => (p.1,segmentPairField pre mid (x p.1) p.2)) := by
  have := hierarchyPathKernel_markov hw φ (pre++(mid++tail)) ha
  have := pairSegmentKernel_markov hw φ pre mid tail ha
  have hf : Measurable (fun p : P × ForwardPath (ι → ℝ) S (pre++(mid++tail)).length =>
      (p.1,actualPairCut pre mid tail (x p.1) p.2)) :=
    measurable_fst.prodMk ((actualPairCut_measurable_joint pre mid tail).comp
      ((hx.comp measurable_fst).prodMk measurable_snd))
  have hs : Measurable (fun p : P × ((Fin pre.length → (ι → ℝ)) × (Fin mid.length → (ι → ℝ))) =>
      forwardEnd pre.length (hierarchyIncrements pre) (x p.1) p.2.1) :=
    (measurable_forwardEnd _ (hierarchyIncrements_measurable pre)).comp
      ((hx.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))
  have hg : Measurable (fun p : P × ((Fin pre.length → (ι → ℝ)) × (Fin mid.length → (ι → ℝ))) =>
      (p.1,segmentPairField pre mid (x p.1) p.2)) :=
    measurable_fst.prodMk (hs.prodMk
      ((measurable_forwardEnd _ (hierarchyIncrements_measurable mid)).comp
        (hs.prodMk (measurable_snd.comp measurable_snd))))
  apply map_compProd_eq_of_maps_eq μ _ _ _ _ hf hg
  intro p
  simp only [Kernel.comap_apply]
  have he := congrArg (Measure.map (Prod.mk p)) (actualPairCut_law hw φ pre mid tail ha (x p))
  rw [Measure.map_map measurable_prodMk_left (actualPairCut_measurable pre mid tail (x p)),
    Measure.map_map measurable_prodMk_left (segmentPairField_measurable pre mid (x p))] at he
  exact he

end SKFluctuations.Hierarchy
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal BigOperators

 
theorem actualTwoSegmentLaw_eq_pair {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (n : ℕ)
    (tail mid pre : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++(mid++tail))) (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    (μ ⊗ₘ (pairSegmentKernel (uniformWeight n) (finiteFeature n) pre mid tail).comap x hx).map
      MeasurableEquiv.prodAssoc.symm = actualTwoSegmentLaw μ n tail mid pre x hx := by
  have := segmentKernel_markov (uniformWeight_pos n) (finiteFeature n) (mid++tail) pre ha
  have := segmentKernel_markov (uniformWeight_pos n) (finiteFeature n) tail mid (ha.suffix pre _)
  unfold pairSegmentKernel actualTwoSegmentLaw
  rw [kernel_compProd_comap, Measure.compProd_assoc]
  congr 1

end SKFluctuations

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S : Type} [Fintype ι] [Fintype S]

 

theorem hierarchyMeanPath_at_pair_left (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A : S → ℝ) (pre mid tail : List (GaussianStep ι)) {P : Type} (x : P → ι → ℝ)
    (p : P × ForwardPath (ι → ℝ) S (pre++(mid++tail)).length) :
    hierarchyMeanPath w φ A (pre++(mid++tail)) x pre.length p =
      gaussianHierarchyMean w φ A (mid++tail) (actualPairCut pre mid tail (x p.1) p.2).1 := by
  induction pre generalizing P with
  | nil => exact hierarchyMeanPath_zero w φ A (mid++tail) x p
  | cons st pre ih =>
    exact ih (fun q : P × (ι → ℝ) => x q.1+q.2) ((p.1,p.2.1),p.2.2)

 
theorem hierarchyMeanPath_at_pair_right (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A : S → ℝ) (pre mid tail : List (GaussianStep ι)) {P : Type} (x : P → ι → ℝ)
    (p : P × ForwardPath (ι → ℝ) S (pre++(mid++tail)).length) :
    hierarchyMeanPath w φ A (pre++(mid++tail)) x (pre.length+mid.length) p =
      gaussianHierarchyMean w φ A tail (actualPairCut pre mid tail (x p.1) p.2).2 := by
  induction pre generalizing P with
  | nil => simpa only [List.length_nil,zero_add,List.nil_append,actualPairCut] using
      hierarchyMeanPath_at_cut w φ A mid tail x p
  | cons st pre ih =>
    simpa only [List.length_cons,Nat.succ_add,List.cons_append,hierarchyMeanPath,actualPairCut] using
      ih (fun q : P × (ι → ℝ) => x q.1+q.2) ((p.1,p.2.1),p.2.2)

end SKFluctuations.Hierarchy
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

abbrev PhysicalPathState (P : Type) (n : ℕ) (steps : List (GaussianStep (FeatureIndex n))) :=
  P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length

def physicalPathLaw {P : Type} [MeasurableSpace P] (μ : Measure P) (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :=
  μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx

def physicalPairIncrement {P : Type} (n : ℕ) (tail mid pre : List (GaussianStep (FeatureIndex n)))
    (x : P → FeatureIndex n → ℝ) (p : PhysicalPathState P n (pre++(mid++tail))) : Fin n → ℝ :=
  let z := actualPairCut pre mid tail (x p.1) p.2
  actualSpinMean n tail z.2-actualSpinMean n (mid++tail) z.1

 

theorem physicalPairIncrement_eq_spinPath {P : Type} (n : ℕ)
    (tail mid pre : List (GaussianStep (FeatureIndex n))) (x : P → FeatureIndex n → ℝ)
    (p : PhysicalPathState P n (pre++(mid++tail))) :
    WithLp.toLp 2 (physicalPairIncrement n tail mid pre x p) =
      actualSpinPath n (pre++(mid++tail)) x (pre.length+mid.length) p -
        actualSpinPath n (pre++(mid++tail)) x pre.length p := by
  ext i
  change actualSpinMean n tail (actualPairCut pre mid tail (x p.1) p.2).2 i -
    actualSpinMean n (mid++tail) (actualPairCut pre mid tail (x p.1) p.2).1 i = _
  simp only [actualSpinPath,PiLp.sub_apply,
    hierarchyMeanPath_at_pair_left,hierarchyMeanPath_at_pair_right,actualSpinMean]

theorem physicalPairIncrement_measurable {P : Type} [MeasurableSpace P] (n : ℕ)
    (tail mid pre : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++(mid++tail))) {x : P → FeatureIndex n → ℝ} (hx : Measurable x) :
    Measurable (physicalPairIncrement n tail mid pre x) := by
  have hm : Measurable (fun p : PhysicalPathState P n (pre++(mid++tail)) =>
      actualPairCut pre mid tail (x p.1) p.2) :=
    (actualPairCut_measurable_joint pre mid tail).comp ((hx.comp measurable_fst).prodMk measurable_snd)
  exact ((actualSpinMean_measurable n tail ((ha.suffix pre _).suffix mid tail)).comp hm.snd).sub
    ((actualSpinMean_measurable n (mid++tail) (ha.suffix pre _)).comp hm.fst)

end SKFluctuations

end

end OAI
