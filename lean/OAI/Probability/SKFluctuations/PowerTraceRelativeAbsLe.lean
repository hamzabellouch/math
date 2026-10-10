import Mathlib
import OAI.Probability.SKFluctuations.ScalarParisiValueDiracDyadic

namespace OAI

/-! Power Trace Relative Abs Le. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

 theorem powerTrace_relative_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    (P : T.Assignment → ℝ) (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i) (x : ι → ℝ) :
    |T.powerTrace w φ L a P x| ≤
      (4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*∑ i, (D i)^2)*T.expect w φ (fun σ => |P σ|) x := by
  have hi (i : Fin (n+1)) : |powerJet w φ a [L (Pi.single i 1),L (Pi.single i 1)] T P x| ≤
      4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*T.expect w φ (fun σ => |P σ|) x*(D i)^2 := by
    have hh := powerJet_relative_abs_le hw φ [L (Pi.single i 1),L (Pi.single i 1)] T ha
      (le_refl T.leaves) P (hD i) (fun u hu => by
        have huv : u = L (Pi.single i 1) := by simpa using hu
        simpa only [huv] using hB i) x
    convert hh using 1
    simp only [List.length_cons,List.length_nil,attachmentCount,Nat.cast_mul,Nat.cast_ofNat,
      Nat.cast_add,Nat.cast_one,mul_one]
    ring
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i, 4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*T.expect w φ (fun σ => |P σ|) x*(D i)^2 :=
      Finset.sum_le_sum fun i _ => hi i
    _ = _ := by rw [← Finset.mul_sum]; ring

 theorem clock_nonneg {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    {P : T.Assignment → ℝ} (hP : ∀ σ, 0 ≤ P σ) (t : ℝ) (x : ι → ℝ) :
    0 ≤ linearClockTest L a (gaussianHierarchy w φ steps) (T.expect w φ P) t x := by
  obtain ⟨K,hF⟩ := (gaussianHierarchy_regular hw φ steps ha 0).1
  exact shiftedMean_nonneg (fun y => T.expect_nonneg hw φ ha hP y)
    ((exponentialIncrement_linearGaussian L (Real.toNNReal t)).integrable_shift hF a x)

 theorem clock_powerTrace_relative_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    (P : T.Assignment → ℝ) (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i) (t : ℝ) (x : ι → ℝ) :
    |linearClockTest L a (gaussianHierarchy w φ steps) (T.powerTrace w φ L a P) t x| ≤
      (4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*∑ i, (D i)^2)*
        linearClockTest L a (gaussianHierarchy w φ steps) (T.expect w φ (fun σ => |P σ|)) t x := by
  obtain ⟨K,hF⟩ := (gaussianHierarchy_regular hw φ steps ha 0).1
  exact shiftedMean_abs_le_mul (T.powerTrace_smooth hw φ L ha P 0)
    (T.expect_smooth hw φ ha (fun σ => |P σ|) 0)
    (T.powerTrace_relative_abs_le hw φ L ha P D hD hB)
    ((exponentialIncrement_linearGaussian L (Real.toNNReal t)).integrable_shift hF a x)

 theorem clockResponse_relative_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    (P : T.Assignment → ℝ) (hP : ∀ σ, 0 ≤ P σ)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i) (t : ℝ) (x : ι → ℝ) :
    |T.clockResponse w φ L a P t x| ≤ (4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*∑ i, (D i)^2)*
      linearClockTest L a (gaussianHierarchy w φ steps) (T.expect w φ P) t x := by
  have hh := T.clock_powerTrace_relative_abs_le hw φ L ha P D hD hB t x
  simp_rw [abs_of_nonneg (hP _)] at hh
  have h1 := T.clock_powerTrace_abs_le hw φ L ha (P := fun _ => 1) (C := 1) D (by norm_num) hD
    (fun _ => by norm_num) hB t x
  have hp := T.clock_nonneg hw φ L ha hP t x
  dsimp only [clockResponse]
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  apply (mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num : (0:ℝ) ≤ 1/2)).trans
  rw [abs_mul,abs_of_nonneg hp]
  nlinarith [mul_le_mul_of_nonneg_left h1 hp]

 

 theorem clock_exp_comparison {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    (P : T.Assignment → ℝ) (hP : ∀ σ, 0 ≤ P σ) (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (x : ι → ℝ) :
    let c := 4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*∑ i, (D i)^2
    Real.exp (-c*|t-s|)*linearClockTest L a (gaussianHierarchy w φ steps) (T.expect w φ P) s x ≤
      linearClockTest L a (gaussianHierarchy w φ steps) (T.expect w φ P) t x ∧
    linearClockTest L a (gaussianHierarchy w φ steps) (T.expect w φ P) t x ≤
      Real.exp (c*|t-s|)*linearClockTest L a (gaussianHierarchy w φ steps) (T.expect w φ P) s x := by
  apply relative_derivative_exp_bound_on (convex_Ici (0:ℝ))
    (fun u hu => (T.hasDerivWithinAt_linearClockTest hw φ L ha P x hu).continuousWithinAt)
    (fun u hu => (T.hasDerivWithinAt_linearClockTest hw φ L ha P x (interior_subset hu)).mono interior_subset)
    (fun u _ => T.clockResponse_relative_abs_le hw φ L ha P hP D hD hB u x) hs ht

end SKFluctuations.Hierarchy.ReplicaTree

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

structure ExpClose (c p q : ℝ) : Prop where
  left_nonneg : 0 ≤ p
  right_nonneg : 0 ≤ q
  le_mul : p ≤ Real.exp c*q
  rev_le_mul : q ≤ Real.exp c*p

namespace ExpClose
 theorem refl {p : ℝ} (hp : 0 ≤ p) : ExpClose 0 p p :=
  ⟨hp,hp,by simp,by simp⟩
 theorem symm {c p q : ℝ} (h : ExpClose c p q) : ExpClose c q p :=
  ⟨h.right_nonneg,h.left_nonneg,h.rev_le_mul,h.le_mul⟩
 theorem mono {c d p q : ℝ} (h : ExpClose c p q) (hc : c ≤ d) : ExpClose d p q :=
  ⟨h.left_nonneg,h.right_nonneg,
    h.le_mul.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hc) h.right_nonneg),
    h.rev_le_mul.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hc) h.left_nonneg)⟩
 theorem trans {c d p q r : ℝ} (h : ExpClose c p q) (k : ExpClose d q r) : ExpClose (c+d) p r := by
  refine ⟨h.left_nonneg,k.right_nonneg,?_,?_⟩
  · calc
      p ≤ Real.exp c*q := h.le_mul
      _ ≤ Real.exp c*(Real.exp d*r) := mul_le_mul_of_nonneg_left k.le_mul (Real.exp_pos _).le
      _ = Real.exp (c+d)*r := by rw [Real.exp_add]; ring
  · calc
      r ≤ Real.exp d*q := k.rev_le_mul
      _ ≤ Real.exp d*(Real.exp c*p) := mul_le_mul_of_nonneg_left h.rev_le_mul (Real.exp_pos _).le
      _ = Real.exp (c+d)*p := by rw [Real.exp_add]; ring
 theorem mul {c d p q r s : ℝ} (h : ExpClose c p q) (k : ExpClose d r s) :
    ExpClose (c+d) (p*r) (q*s) := by
  refine ⟨mul_nonneg h.left_nonneg k.left_nonneg,mul_nonneg h.right_nonneg k.right_nonneg,?_,?_⟩
  · calc
      _ ≤ (Real.exp c*q)*(Real.exp d*s) :=
        mul_le_mul h.le_mul k.le_mul k.left_nonneg (mul_nonneg (Real.exp_pos _).le h.right_nonneg)
      _ = _ := by rw [Real.exp_add]; ring
  · calc
      _ ≤ (Real.exp c*p)*(Real.exp d*r) :=
        mul_le_mul h.rev_le_mul k.rev_le_mul k.right_nonneg (mul_nonneg (Real.exp_pos _).le h.left_nonneg)
      _ = _ := by rw [Real.exp_add]; ring
 theorem of_bounds {c p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h : Real.exp (-c)*q ≤ p ∧ p ≤ Real.exp c*q) : ExpClose c p q := by
  refine ⟨hp,hq,h.2,?_⟩
  have hh := mul_le_mul_of_nonneg_left h.1 (Real.exp_pos c).le
  simpa only [← mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul] using hh
 theorem finset_sum {α : Type*} (A : Finset α) {c : ℝ} {p q : α → ℝ}
    (h : ∀ i ∈ A, ExpClose c (p i) (q i)) : ExpClose c (∑ i ∈ A, p i) (∑ i ∈ A, q i) := by
  refine ⟨Finset.sum_nonneg fun i hi => (h i hi).left_nonneg,
    Finset.sum_nonneg fun i hi => (h i hi).right_nonneg,?_,?_⟩
  · simpa only [Finset.mul_sum] using Finset.sum_le_sum (fun i hi => (h i hi).le_mul)
  · simpa only [Finset.mul_sum] using Finset.sum_le_sum (fun i hi => (h i hi).rev_le_mul)
end ExpClose

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S β : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

 theorem ReplicaTree.clock_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    (P : T.Assignment → ℝ) (hP : ∀ σ, 0 ≤ P σ) (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (x : ι → ℝ) :
    ExpClose ((4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*∑ i, (D i)^2)*|t-s|)
      (linearClockTest L a (gaussianHierarchy w φ steps) (T.expect w φ P) t x)
      (linearClockTest L a (gaussianHierarchy w φ steps) (T.expect w φ P) s x) := by
  apply ExpClose.of_bounds (T.clock_nonneg hw φ L ha hP t x) (T.clock_nonneg hw φ L ha hP s x)
  simpa only [neg_mul] using T.clock_exp_comparison hw φ L ha P hP D hD hB ht hs x

omit [Fintype S] [Nonempty S] in
 theorem BoundaryTree.finite_close {κ : β → Type*} {F G : (ι → ℝ) → ℝ} {C₀ C₁ : ℝ≥0} {K m : ℝ}
    (hF : LipschitzWith C₀ F) (hG : LipschitzWith C₁ G) (hK : 0 ≤ K)
    (hFG : ∀ x, |G x-F x| ≤ K)
    {W V : ∀ b, κ b → (ι → ℝ) → ℝ} (hW : ∀ b σ, BddSmooth 0 (W b σ))
    (hV : ∀ b σ, BddSmooth 0 (V b σ))
    (E : β → ℝ) (hE : ∀ b σ x, ExpClose (E b) (V b σ x) (W b σ x))
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front) (hO : PrefixOrdered 0 m front)
    (σ : T.Assignment κ) (x : ι → ℝ) :
    ExpClose (T.budget (fun b => E b+2*m*K))
      (T.weight (fun _ => G) (fun b σ _ => V b σ) σ 0 x)
      (T.weight (fun _ => F) (fun b σ _ => W b σ) σ 0 x) := by
  refine ⟨T.weight_nonneg_static hG (fun b σ x => (hE b σ x).left_nonneg) hO.positive σ x,
    T.weight_nonneg_static hF (fun b σ x => (hE b σ x).right_nonneg) hO.positive σ x,?_,?_⟩
  · exact T.finite_relative hF hG hK hFG hW hV
      (fun b σ x => (hE b σ x).right_nonneg) (fun b σ x => (hE b σ x).left_nonneg)
      E (fun b σ x => (hE b σ x).le_mul) hO σ x
  · exact T.finite_relative hG hF hK (fun y => (abs_sub_comm (F y) (G y)) ▸ hFG y) hV hW
      (fun b σ x => (hE b σ x).left_nonneg) (fun b σ x => (hE b σ x).right_nonneg)
      E (fun b σ x => (hE b σ x).rev_le_mul) hO σ x

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 
def ClockTree.rootForks : {as : List PositiveMass} → ClockTree S as → ℕ
  | _,.leaf => 0
  | _,.step _ _ => 0
  | _,.fork T U => 1+T.rootForks+U.rootForks

noncomputable def ClockTree.atomicHead (w : S → ℝ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (q : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0) (a : ℝ)
    (σ : T.Assignment) (x : Fin (n+1) → ℝ) : ℝ :=
  shiftedMean (Measure.pi fun i => gaussianReal 0 (v i)) a
    (gaussianHierarchy w φ (clockSteps as q)) (T.weight w φ q σ) x

omit [Nonempty S] in
 theorem ClockTree.atomicHead_eq_clock (w : S → ℝ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (q : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0) (a : ℝ)
    (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    T.atomicHead w φ q v a σ x = (T.realize q).atomicClock w φ (diagonalDriver v) a
      (T.assignmentEquiv q σ) 1 x := by
  classical
  simp only [ReplicaTree.atomicClock,linearClockTest,Real.toNNReal_one,linearGaussian_diagonal]
  have he : (T.realize q).expect w φ
      (fun τ => if τ = T.assignmentEquiv q σ then 1 else 0) = T.weight w φ q σ :=
    funext fun y => (T.realize q).expect_indicator w φ _ y
  rw [he]
  rfl

 theorem ClockTree.atomicHead_variation {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0) (x : Fin (n+1) → ℝ) :
    ∑ σ, |T.atomicHead w φ q v a σ x-T.weight w φ q σ x| ≤
      4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*∑ i, (v i:ℝ)*(D i)^2 := by
  classical
  have hd (i : Fin (n+1)) (σ : S) : |φ σ (diagonalDriver v (Pi.single i 1))| ≤ Real.sqrt (v i)*D i := by
    rw [diagonalDriver_single,map_smul,smul_eq_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hB i σ) (Real.sqrt_nonneg _)
  have hh := (T.realize q).atomic_clock_variation hw φ (diagonalDriver v)
    (clockSteps_ordered ho q) (fun i => Real.sqrt (v i)*D i)
    (fun i => mul_nonneg (Real.sqrt_nonneg _) (hD i)) hd
    (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 0) x
  simp only [sub_zero,abs_one,mul_one,mul_pow,Real.sq_sqrt (v _).coe_nonneg,
    (T.realize q).atomicClock_zero hw φ (diagonalDriver v) (clockSteps_ordered ho q),
    ClockTree.realize_leaves] at hh
  have he : (∑ σ, |T.atomicHead w φ q v a σ x-T.weight w φ q σ x|) =
      ∑ τ, |(T.realize q).atomicClock w φ (diagonalDriver v) a τ 1 x-(T.realize q).weight w φ τ x| := by
    apply Fintype.sum_equiv (T.assignmentEquiv q)
    intro σ
    rw [T.atomicHead_eq_clock]
    rfl
  rw [he]
  exact hh

 

 theorem ClockTree.atomicHead_crossing {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {b : PositiveMass} {bs : List PositiveMass} (he : as = b::bs) (ho : MassOrdered b.val bs)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0) (x : Fin (n+1) → ℝ) :
    ∑ σ, |T.atomicHead w φ q v b.val σ x-T.weight w φ (addHeadClock q v) σ x| ≤
      8*(T.leaves:ℝ)*(T.leaves+1:ℝ)*T.rootForks*∑ i, (v i:ℝ)*(D i)^2 := by
  classical
  cases T with
  | leaf => cases he
  | @step a cs T =>
    cases he
    have hEq (σ : (T.step b).Assignment) := (T.step b).atomicHead_eq_clock w φ q v b.val σ x
    simp_rw [hEq,T.step_addHead_atomic hw φ ho q v]
    simp [ClockTree.rootForks]
  | @fork cs T U =>
    have hO : MassOrdered b.val as := he ▸ ⟨b.property.le,le_rfl,ho⟩
    have h₁ := (T.fork U).atomicHead_variation hw φ hO D hD hB q v x
    have h₂ := (T.fork U).addHead_variation hw φ he ho D hD hB q v x
    have ht : (∑ σ, |(T.fork U).atomicHead w φ q v b.val σ x-(T.fork U).weight w φ (addHeadClock q v) σ x|) ≤
        (∑ σ, |(T.fork U).atomicHead w φ q v b.val σ x-(T.fork U).weight w φ q σ x|)+
        ∑ σ, |(T.fork U).weight w φ (addHeadClock q v) σ x-(T.fork U).weight w φ q σ x| := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro σ _
      simpa only [abs_sub_comm] using abs_sub_le ((T.fork U).atomicHead w φ q v b.val σ x)
        ((T.fork U).weight w φ q σ x) ((T.fork U).weight w φ (addHeadClock q v) σ x)
    apply (ht.trans (add_le_add h₁ h₂)).trans
    have hr : (1:ℝ) ≤ (T.fork U).rootForks := by
      simp only [ClockTree.rootForks,Nat.cast_add,Nat.cast_one]
      linarith [Nat.cast_nonneg (α := ℝ) T.rootForks,Nat.cast_nonneg (α := ℝ) U.rootForks]
    have hv : 0 ≤ ∑ i, (v i:ℝ)*(D i)^2 := Finset.sum_nonneg fun i _ => mul_nonneg (v i).coe_nonneg (sq_nonneg _)
    calc
      _ = (8*((T.fork U).leaves:ℝ)*((T.fork U).leaves+1:ℝ)*∑ i, (v i:ℝ)*(D i)^2)*1 := by ring
      _ ≤ (8*((T.fork U).leaves:ℝ)*((T.fork U).leaves+1:ℝ)*∑ i, (v i:ℝ)*(D i)^2)*(T.fork U).rootForks :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S β : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 theorem massOrdered_bounds {a : ℝ} {as : List PositiveMass} (ho : MassOrdered a as) :
    0 ≤ a ∧ a ≤ 1 := by
  induction as generalizing a with
  | nil => exact ho
  | cons b bs ih => exact ⟨ho.1,ho.2.1.trans (ih ho.2.2).2⟩

 theorem ClockTree.atomicHead_mass_difference {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a b : ℝ} (ho : MassOrdered b as) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0) (x : Fin (n+1) → ℝ) :
    ∑ σ, |T.atomicHead w φ q v a σ x-T.atomicHead w φ q v b σ x| ≤
      |a-b| *(2*(T.leaves:ℝ)+3)*∑ i, (v i:ℝ)*(D i)^2 := by
  classical
  have hd (i : Fin (n+1)) (σ : S) : |φ σ (diagonalDriver v (Pi.single i 1))| ≤ Real.sqrt (v i)*D i := by
    rw [diagonalDriver_single,map_smul,smul_eq_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hB i σ) (Real.sqrt_nonneg _)
  have hh := (T.realize q).atomic_mass_difference hw φ (diagonalDriver v)
    (clockSteps_ordered ho q) (fun i => Real.sqrt (v i)*D i)
    (fun i => mul_nonneg (Real.sqrt_nonneg _) (hD i)) hd ha ha1 hb hb1
    (by norm_num : (0:ℝ) ≤ 1) x
  simp only [mul_one,mul_pow,Real.sq_sqrt (v _).coe_nonneg,ClockTree.realize_leaves] at hh
  have he : (∑ σ, |T.atomicHead w φ q v a σ x-T.atomicHead w φ q v b σ x|) =
      ∑ τ, |(T.realize q).atomicClock w φ (diagonalDriver v) a τ 1 x-
        (T.realize q).atomicClock w φ (diagonalDriver v) b τ 1 x| := by
    apply Fintype.sum_equiv (T.assignmentEquiv q)
    intro σ
    rw [T.atomicHead_eq_clock,T.atomicHead_eq_clock]
  rw [he]
  exact hh

 theorem ClockTree.atomicHead_transfer {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {b : PositiveMass} {bs : List PositiveMass}
    (T : ClockTree S (b::bs)) (ho : MassOrdered b.val bs)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0) (x : Fin (n+1) → ℝ) :
    ∑ σ, |T.atomicHead w φ q v a σ x-T.weight w φ (addHeadClock q v) σ x| ≤
      (|a-b.val| *(2*(T.leaves:ℝ)+3)+8*(T.leaves:ℝ)*(T.leaves+1:ℝ)*T.rootForks)*
        ∑ i, (v i:ℝ)*(D i)^2 := by
  classical
  have hb1 : b.val ≤ 1 := (massOrdered_bounds ho).2
  have hO : MassOrdered b.val (b::bs) := ⟨b.property.le,le_rfl,ho⟩
  have h₁ := T.atomicHead_mass_difference hw φ hO ha ha1 b.property hb1 D hD hB q v x
  have h₂ := T.atomicHead_crossing hw φ rfl ho D hD hB q v x
  calc
    _ ≤ (∑ σ, |T.atomicHead w φ q v a σ x-T.atomicHead w φ q v b.val σ x|)+
        ∑ σ, |T.atomicHead w φ q v b.val σ x-T.weight w φ (addHeadClock q v) σ x| := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun σ _ => abs_sub_le _ _ _
    _ ≤ _ := by convert add_le_add h₁ h₂ using 1; first | rfl | ring

 theorem ClockTree.atomicHead_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (ha : 0 < a)
    (q : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0) (σ : T.Assignment) (k : ℕ) :
    BddSmooth k (T.atomicHead w φ q v a σ) :=
  ((T.realize q).step (a,v)).weight_smooth hw φ
    (show OrderedSteps a ((a,v)::clockSteps as q) from ⟨ha.le,le_rfl,ha,clockSteps_ordered ho q⟩)
    k (T.assignmentEquiv q σ)

 theorem ClockTree.atomicHead_probability {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (ha : 0 < a)
    (q : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0) (x : Fin (n+1) → ℝ) :
    (∀ σ, 0 ≤ T.atomicHead w φ q v a σ x) ∧ ∑ σ, T.atomicHead w φ q v a σ x = 1 := by
  classical
  have hO : OrderedSteps a ((a,v)::clockSteps as q) := ⟨ha.le,le_rfl,ha,clockSteps_ordered ho q⟩
  refine ⟨fun σ => ((T.realize q).step (a,v)).weight_nonneg hw φ hO (T.assignmentEquiv q σ) x,?_⟩
  calc
    _ = ∑ τ, ((T.realize q).step (a,v)).weight w φ τ x :=
      Fintype.sum_equiv (T.assignmentEquiv q) _ _ (fun _ => rfl)
    _ = 1 := ((T.realize q).step (a,v)).weight_sum hw φ hO x

 

 theorem BoundaryTree.head_transfer {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {b : PositiveMass} {bs : List PositiveMass}
    (R : β → ClockTree S (b::bs)) (ho : MassOrdered b.val bs)
    {a c : ℝ} (ha : 0 < a) (hab : a ≤ b.val)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0)
    {front : List (GaussianStep (Fin (n+1)))} (T : BoundaryTree (Fin (n+1)) β front)
    (hO : PrefixOrdered 0 c front) (x : Fin (n+1) → ℝ) :
    ∑ σ, |T.weight
      (fun _ => shiftedContinuation (Measure.pi fun i => gaussianReal 0 (v i)) a
        (gaussianHierarchy w φ (clockSteps (b::bs) q)))
      (fun d τ _ => (R d).atomicHead w φ q v a τ) σ 0 x-
      T.weight (fun _ => gaussianHierarchy w φ (clockSteps (b::bs) (addHeadClock q v)))
        (fun d τ _ => (R d).weight w φ (addHeadClock q v) τ) σ 0 x| ≤
      T.budget (fun d => ((|a-b.val| *(2*((R d).leaves:ℝ)+3)+
        8*((R d).leaves:ℝ)*((R d).leaves+1:ℝ)*(R d).rootForks)+c*|a-b.val|)*
        ∑ i, (v i:ℝ)*(D i)^2) := by
  classical
  have hb1 : b.val ≤ 1 := (massOrdered_bounds ho).2
  have hA : MassOrdered a (b::bs) := ⟨ha.le,hab,ho⟩
  have hB₀ : MassOrdered b.val (b::bs) := ⟨b.property.le,le_rfl,ho⟩
  have hF := (gaussianHierarchy_regular hw φ _ (clockSteps_ordered hA q) 0).1.choose_spec
  have hG := (gaussianHierarchy_regular hw φ _ (clockSteps_ordered hB₀ (addHeadClock q v)) 0).1.choose_spec
  have hd (i : Fin (n+1)) (σ : S) : |φ σ (diagonalDriver v (Pi.single i 1))| ≤ Real.sqrt (v i)*D i := by
    rw [diagonalDriver_single,map_smul,smul_eq_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hB i σ) (Real.sqrt_nonneg _)
  have hP (y : Fin (n+1) → ℝ) :
      |shiftedContinuation (Measure.pi fun i => gaussianReal 0 (v i)) a
        (gaussianHierarchy w φ (clockSteps (b::bs) q)) y-
        gaussianHierarchy w φ (clockSteps (b::bs) (addHeadClock q v)) y| ≤
      |a-b.val|/2*∑ i, (v i:ℝ)*(D i)^2 := by
    rw [gaussianHierarchy_addHeadClock hw φ ho q v]
    have hh := (ReplicaTree.single (clockSteps (b::bs) q)).linearPotential_mass_difference hw φ
      (diagonalDriver v) (clockSteps_ordered hB₀ q) (fun i => Real.sqrt (v i)*D i) hd ha b.property
      (by norm_num : (0:ℝ) ≤ 1) y
    simpa only [linearClockContinuation,Real.toNNReal_one,linearGaussian_diagonal,
      mul_pow,Real.sq_sqrt (v _).coe_nonneg,mul_one] using hh
  have hh := T.finite_stability hG
    (lipschitzWith_shiftedContinuation hF ha ((exponentialIncrement_gaussian v).integrable_shift hF a))
    (by positivity : 0 ≤ |a-b.val|/2*∑ i, (v i:ℝ)*(D i)^2) hP
    (fun d σ => ((R d).weight_smooth hw φ hB₀ (addHeadClock q v) σ 0).continuous)
    (fun d σ => ((R d).atomicHead_smooth hw φ hA ha q v σ 0).continuous)
    (fun d y => (R d).weight_probability hw φ hB₀ (addHeadClock q v) y)
    (fun d y => (R d).atomicHead_probability hw φ hA ha q v y)
    (fun d => (|a-b.val| *(2*((R d).leaves:ℝ)+3)+
      8*((R d).leaves:ℝ)*((R d).leaves+1:ℝ)*(R d).rootForks)*∑ i, (v i:ℝ)*(D i)^2)
    (fun d y => (R d).atomicHead_transfer hw φ ho ha.le (hab.trans hb1) D hD hB q v y) hO x
  convert hh using 1
  congr 1
  funext d
  ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι β : Type*}

 theorem BoundaryTree.budget_add {front : List (GaussianStep ι)} (T : BoundaryTree ι β front)
    (f g : β → ℝ) : T.budget (fun b => f b+g b) = T.budget f+T.budget g := by
  induction T with
  | leaf => rfl
  | step _ _ ih => exact ih
  | fork T U ihT ihU => simp only [BoundaryTree.budget,ihT,ihU]; ring

 theorem BoundaryTree.budget_mul {front : List (GaussianStep ι)} (T : BoundaryTree ι β front)
    (f : β → ℝ) (c : ℝ) : T.budget (fun b => f b*c) = T.budget f*c := by
  induction T with
  | leaf => rfl
  | step _ _ ih => exact ih
  | fork T U ihT ihU => simp only [BoundaryTree.budget,ihT,ihU]; ring

 theorem BoundaryTree.budget_mono {front : List (GaussianStep ι)} (T : BoundaryTree ι β front)
    {f g : β → ℝ} (h : ∀ b, f b ≤ g b) : T.budget f ≤ T.budget g := by
  induction T with
  | leaf b => exact h b
  | step _ _ ih => exact ih
  | fork T U ihT ihU => exact add_le_add ihT ihU

 
def ClockTree.forksAt : {as : List PositiveMass} → ClockTree S as → ℕ → ℕ
  | _,.leaf,_ => 0
  | _,.step _ _,0 => 0
  | _,.step _ T,j+1 => T.forksAt j
  | _,.fork T U,j => (if j=0 then 1 else 0)+T.forksAt j+U.forksAt j

 theorem ClockTree.forksAt_zero {as : List PositiveMass} (T : ClockTree S as) :
    T.forksAt 0 = T.rootForks := by
  induction T with
  | leaf => rfl
  | step => rfl
  | fork T U ihT ihU => simp [ClockTree.forksAt,ClockTree.rootForks,ihT,ihU]

 theorem ClockTree.leaves_pos {as : List PositiveMass} (T : ClockTree S as) : 0 < T.leaves := by
  induction T with
  | leaf => exact Nat.zero_lt_one
  | step _ _ ih => exact ih
  | fork T U ihT ihU => exact Nat.add_pos_left ihT _

 theorem ClockTree.forks_total {as : List PositiveMass} (T : ClockTree S as) :
    (∑ j ∈ Finset.range (as.length+1), T.forksAt j)+1 = T.leaves := by
  classical
  induction T with
  | leaf => simp [ClockTree.forksAt,ClockTree.leaves]
  | @step a cs T ih =>
    rw [List.length_cons,Finset.sum_range_succ']
    simp only [ClockTree.forksAt,add_zero,ClockTree.leaves]
    exact ih
  | @fork cs T U ihT ihU =>
    simp only [ClockTree.forksAt,Finset.sum_add_distrib,ClockTree.leaves]
    have hz : 0 < cs.length+1 := Nat.succ_pos _
    simp only [Finset.sum_ite_eq',Finset.mem_range,hz,ite_eq_left]
    omega

 theorem ClockTree.cut_budget_leaves {as : List PositiveMass} (T : ClockTree S as)
    (j : ℕ) (q : ℕ → ι → ℝ≥0) (hj : j ≤ as.length) :
    (T.cut j q).budget (fun U => (U.leaves:ℝ)) = T.leaves := by
  induction T generalizing j q with
  | leaf =>
    have : j = 0 := by simpa using hj
    subst j
    rfl
  | @step a cs T ih =>
    cases j with
    | zero => rfl
    | succ j =>
      have hj' : j ≤ cs.length := by simpa using hj
      exact ih j (fun k => q (k+1)) hj'
  | @fork cs T U ihT ihU =>
    cases j with
    | zero => rfl
    | succ j =>
      change (T.cut (j+1) q).budget (fun U => (U.leaves:ℝ))+
        (U.cut (j+1) q).budget (fun V => (V.leaves:ℝ)) = _
      rw [ihT (j+1) q hj,ihU (j+1) q hj]
      exact (Nat.cast_add T.leaves U.leaves).symm

 theorem ClockTree.cut_budget_forks {as : List PositiveMass} (T : ClockTree S as)
    (j : ℕ) (q : ℕ → ι → ℝ≥0) (hj : j ≤ as.length) :
    (T.cut j q).budget (fun U => (U.rootForks:ℝ)) = T.forksAt j := by
  induction T generalizing j q with
  | leaf =>
    have : j = 0 := by simpa using hj
    subst j
    rfl
  | @step a cs T ih =>
    cases j with
    | zero => rfl
    | succ j =>
      have hj' : j ≤ cs.length := by simpa using hj
      exact ih j (fun k => q (k+1)) hj'
  | @fork cs T U ihT ihU =>
    cases j with
    | zero =>
      change ((T.fork U).rootForks:ℝ) = (T.fork U).forksAt 0
      exact_mod_cast (T.fork U).forksAt_zero.symm
    | succ j =>
      change (T.cut (j+1) q).budget (fun U => (U.rootForks:ℝ))+
        (U.cut (j+1) q).budget (fun V => (V.rootForks:ℝ)) = _
      rw [ihT (j+1) q hj,ihU (j+1) q hj]
      simp only [ClockTree.forksAt,Nat.succ_ne_zero,ite_false,zero_add,Nat.cast_add]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 theorem ClockTree.atomicHead_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0) (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    ExpClose (4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*∑ i, (v i:ℝ)*(D i)^2)
      (T.atomicHead w φ q v a σ x) (T.weight w φ q σ x) := by
  classical
  have hd (i : Fin (n+1)) (σ : S) : |φ σ (diagonalDriver v (Pi.single i 1))| ≤ Real.sqrt (v i)*D i := by
    rw [diagonalDriver_single,map_smul,smul_eq_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hB i σ) (Real.sqrt_nonneg _)
  have hh := (T.realize q).clock_close hw φ (diagonalDriver v) (clockSteps_ordered ho q)
    (fun τ => if τ = T.assignmentEquiv q σ then 1 else 0) (by intro τ; split_ifs <;> norm_num)
    (fun i => Real.sqrt (v i)*D i) (fun i => mul_nonneg (Real.sqrt_nonneg _) (hD i)) hd
    (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 0) x
  change ExpClose _ ((T.realize q).atomicClock w φ (diagonalDriver v) a (T.assignmentEquiv q σ) 1 x)
    ((T.realize q).atomicClock w φ (diagonalDriver v) a (T.assignmentEquiv q σ) 0 x) at hh
  simp only [sub_zero,abs_one,mul_one,mul_pow,Real.sq_sqrt (v _).coe_nonneg,
    (T.realize q).atomicClock_zero hw φ (diagonalDriver v) (clockSteps_ordered ho q),
    ClockTree.realize_leaves] at hh
  rw [T.atomicHead_eq_clock]
  exact hh

 theorem ClockTree.addHead_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {b : PositiveMass} {bs : List PositiveMass} (he : as = b::bs) (ho : MassOrdered b.val bs)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0) (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    ExpClose (4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*∑ i, (v i:ℝ)*(D i)^2)
      (T.weight w φ (addHeadClock q v) σ x) (T.weight w φ q σ x) := by
  classical
  induction T generalizing b bs with
  | leaf => cases he
  | @step a cs T ih =>
    cases he
    have hO : MassOrdered a.val (a::cs) := ⟨a.property.le,le_rfl,ho⟩
    have hh := (T.step a).atomicHead_close hw φ hO D hD hB q v σ x
    rw [(T.step a).atomicHead_eq_clock,T.step_addHead_atomic hw φ ho q v] at hh
    exact hh
  | @fork cs T U ihT ihU =>
    have hh := (ihT he ho σ.1).mul (ihU he ho σ.2)
    apply hh.mono
    simp only [ClockTree.leaves,Nat.cast_add]
    have hv : 0 ≤ ∑ i, (v i:ℝ)*(D i)^2 := Finset.sum_nonneg fun i _ => mul_nonneg (v i).coe_nonneg (sq_nonneg _)
    rw [← add_mul]
    apply mul_le_mul_of_nonneg_right _ hv
    nlinarith [Nat.cast_nonneg (α := ℝ) T.leaves,Nat.cast_nonneg (α := ℝ) U.leaves,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) T.leaves) (Nat.cast_nonneg (α := ℝ) U.leaves)]

 theorem ClockTree.atomicHead_crossing_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {b : PositiveMass} {bs : List PositiveMass} (he : as = b::bs) (ho : MassOrdered b.val bs)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0) (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    ExpClose (8*(T.leaves:ℝ)*(T.leaves+1:ℝ)*T.rootForks*∑ i, (v i:ℝ)*(D i)^2)
      (T.atomicHead w φ q v b.val σ x) (T.weight w φ (addHeadClock q v) σ x) := by
  classical
  cases T with
  | leaf => cases he
  | @step a cs T =>
    cases he
    rw [(T.step b).atomicHead_eq_clock,T.step_addHead_atomic hw φ ho q v]
    simp only [ClockTree.rootForks,Nat.cast_zero,mul_zero,zero_mul]
    exact ExpClose.refl (((T.step b).weight_probability hw φ ⟨b.property.le,le_rfl,ho⟩ (addHeadClock q v) x).1 σ)
  | @fork cs T U =>
    have hO : MassOrdered b.val as := he ▸ ⟨b.property.le,le_rfl,ho⟩
    have hh := ((T.fork U).atomicHead_close hw φ hO D hD hB q v σ x).trans
      ((T.fork U).addHead_close hw φ he ho D hD hB q v σ x).symm
    apply hh.mono
    have hr : (1:ℝ) ≤ (T.fork U).rootForks := by
      simp only [ClockTree.rootForks,Nat.cast_add,Nat.cast_one]
      linarith [Nat.cast_nonneg (α := ℝ) T.rootForks,Nat.cast_nonneg (α := ℝ) U.rootForks]
    have hv : 0 ≤ ∑ i, (v i:ℝ)*(D i)^2 := Finset.sum_nonneg fun i _ => mul_nonneg (v i).coe_nonneg (sq_nonneg _)
    calc
      _ = (8*((T.fork U).leaves:ℝ)*((T.fork U).leaves+1:ℝ)*∑ i, (v i:ℝ)*(D i)^2)*1 := by ring
      _ ≤ (8*((T.fork U).leaves:ℝ)*((T.fork U).leaves+1:ℝ)*∑ i, (v i:ℝ)*(D i)^2)*(T.fork U).rootForks :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by ring

end SKFluctuations.Hierarchy

end

end OAI
