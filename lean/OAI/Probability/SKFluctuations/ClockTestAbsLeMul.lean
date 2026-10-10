import Mathlib
import OAI.Probability.SKFluctuations.PowerTraceRelativeAbsLe

namespace OAI

/-! Clock Test Abs Le Mul. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem clockTest_abs_le_mul {ι : Type*} [Fintype ι] {F A B : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) (hB : BddSmooth 0 B)
    {c : ℝ} (hb : ∀ y, |A y| ≤ c*B y) (m t : ℝ) (x : ι → ℝ) :
    |clockTest m F A t x| ≤ c*clockTest m F B t x :=
  shiftedMean_abs_le_mul hA hB hb
    ((exponentialIncrement_gaussian (fun _ : ι => Real.toNNReal t)).integrable_shift hF m x)

 theorem clockTest_nonneg {ι : Type*} [Fintype ι] {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : ∀ y, 0 ≤ A y) (m t : ℝ) (x : ι → ℝ) :
    0 ≤ clockTest m F A t x :=
  shiftedMean_nonneg hA
    ((exponentialIncrement_gaussian (fun _ : ι => Real.toNNReal t)).integrable_shift hF m x)

 theorem clockGradient_relative_abs_le {ι : Type*} [Fintype ι] {F G A A₁ : (ι → ℝ) → ℝ}
    {C : ℝ≥0} (hF : LipschitzWith C F) (hG : BddSmooth 0 G) (hA : BddSmooth 0 A)
    (hA₁ : BddSmooth 0 A₁) {D E : ℝ} (hAp : ∀ y, 0 ≤ A y)
    (hbG : ∀ y, |G y| ≤ D) (hbA₁ : ∀ y, |A₁ y| ≤ E*A y)
    (m t : ℝ) (x : ι → ℝ) :
    |clockGradient m F G A A₁ t x| ≤ (E+2*|m| *D)*clockTest m F A t x := by
  have hp := clockTest_nonneg hF hAp m t x
  have hAG : ∀ y, |A y*G y| ≤ D*A y := by
    intro y
    rw [abs_mul,abs_of_nonneg (hAp y),mul_comm D]
    exact mul_le_mul_of_nonneg_left (hbG y) (hAp y)
  have h1 := clockTest_abs_le_mul hF hA₁ hA hbA₁ m t x
  have h2 := clockTest_abs_le_mul hF (hA.mul hG) hA hAG m t x
  have h4 := clockTest_abs_le hF hG hbG m t x
  have h34 : |clockTest m F A t x*clockTest m F G t x| ≤ D*clockTest m F A t x := by
    rw [abs_mul,abs_of_nonneg hp,mul_comm D]
    exact mul_le_mul_of_nonneg_left h4 hp
  have hcov := (abs_sub (clockTest m F (fun y => A y*G y) t x)
    (clockTest m F A t x*clockTest m F G t x)).trans (add_le_add h2 h34)
  unfold clockGradient
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hcov (abs_nonneg m)]

 theorem HeatJet.massSplitResponse_relative_abs_le {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    {k a b : ℝ} (hD : ∀ i, 0 ≤ D i)
    (hA : ∀ y, 0 ≤ J.A y) (hG : ∀ i y, |J.G i y| ≤ D i)
    (hA₁ : ∀ i y, |J.A₁ i y| ≤ k*D i*J.A y)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (T t : ℝ) (x : Fin (n+1) → ℝ) :
    |J.massSplitResponse a hb T t x| ≤ (|a-b| *(k+3)*∑ i, (D i)^2)*J.massSplit a hb T t x := by
  let K := J.evolve hb (T-t)
  let Q := ∑ i, (D i)^2
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hAK : ∀ y, 0 ≤ K.A y := clockTest_nonneg J.lipschitz hA b (T-t)
  have hGK : ∀ i y, |K.G i y| ≤ D i := fun i =>
    clockTest_abs_le J.lipschitz (J.smoothG i) (hG i) b (T-t)
  have hA₁K : ∀ i y, |K.A₁ i y| ≤ ((k+2)*D i)*K.A y := by
    intro i y
    have hh := clockGradient_relative_abs_le J.lipschitz (J.smoothG i) J.smoothA (J.smoothA₁ i)
      hA (hG i) (hA₁ i) b (T-t) y
    rw [abs_of_pos hb] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (hAK y)
    nlinarith [mul_le_mul_of_nonneg_right hb1 (hD i)]
  have hGP (y) : |K.gradientPair y| ≤ ((k+2)*Q)*K.A y := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i, D i*(((k+2)*D i)*K.A y) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul (hGK i y) (hA₁K i y) (abs_nonneg _) (hD i)
      _ = _ := by
        dsimp only [Q]
        rw [Finset.mul_sum,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hAP (y) : |K.A y*K.potentialEnergy y| ≤ Q*K.A y := by
    rw [abs_mul,abs_of_nonneg (hAK y),mul_comm Q]
    exact mul_le_mul_of_nonneg_left (K.potentialEnergy_abs_le D hD hGK y) (hAK y)
  have hp := clockTest_nonneg K.lipschitz hAK a t x
  have hg := clockTest_abs_le_mul K.lipschitz K.smoothGradientPair K.smoothA hGP a t x
  have he := clockTest_abs_le K.lipschitz K.smoothPotentialEnergy
    (K.potentialEnergy_abs_le D hD hGK) a t x
  have hae := clockTest_abs_le_mul K.lipschitz (K.smoothA.mul K.smoothPotentialEnergy) K.smoothA hAP a t x
  have hm : |clockTest a K.F K.A t x*clockTest a K.F K.potentialEnergy t x| ≤ Q*clockTest a K.F K.A t x := by
    rw [abs_mul,abs_of_nonneg hp,mul_comm Q]
    exact mul_le_mul_of_nonneg_left he hp
  have hc := (abs_sub (clockTest a K.F (fun y => K.A y*K.potentialEnergy y) t x)
    (clockTest a K.F K.A t x*clockTest a K.F K.potentialEnergy t x)).trans (add_le_add hae hm)
  change |(a-b)*clockTest a K.F K.gradientPair t x+
    (a*(a-b)/2)*(clockTest a K.F (fun y => K.A y*K.potentialEnergy y) t x-
      clockTest a K.F K.A t x*clockTest a K.F K.potentialEnergy t x)| ≤ _
  apply (abs_add_le _ _).trans
  simp only [abs_mul,abs_div,abs_of_nonneg ha,abs_of_pos (by norm_num : (0:ℝ)<2)]
  change _ ≤ (|a-b| *(k+3)*Q)*clockTest a K.F K.A t x
  have h1 := mul_le_mul_of_nonneg_left hg (abs_nonneg (a-b))
  have h2 := mul_le_mul_of_nonneg_left hc (show 0 ≤ a*|a-b|/2 by positivity)
  have h3 := mul_le_mul_of_nonneg_right ha1 (show 0 ≤ |a-b| *Q*clockTest a K.F K.A t x by positivity)
  nlinarith

 theorem HeatJet.massSplit_exp_comparison {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    {k a b : ℝ} (hD : ∀ i, 0 ≤ D i)
    (hA : ∀ y, 0 ≤ J.A y) (hG : ∀ i y, |J.G i y| ≤ D i)
    (hA₁ : ∀ i y, |J.A₁ i y| ≤ k*D i*J.A y)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    {T s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : Fin (n+1) → ℝ) :
    let c := |a-b| *(k+3)*∑ i, (D i)^2
    Real.exp (-c*|t-s|)*J.massSplit a hb T s x ≤ J.massSplit a hb T t x ∧
    J.massSplit a hb T t x ≤ Real.exp (c*|t-s|)*J.massSplit a hb T s x := by
  apply relative_derivative_exp_bound_on (convex_Icc 0 T) (J.continuous_massSplit a hb T x).continuousOn
    (fun u hu => (J.hasDerivAt_massSplit a hb (by simpa only [interior_Icc] using hu) x).hasDerivWithinAt)
    (fun u _ => J.massSplitResponse_relative_abs_le D hD hA hG hA₁ ha ha1 hb hb1 T u x) hs ht

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

 theorem replicaFeatureJet_A₁_relative_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ}
    (ha : OrderedSteps a steps) {P : T.Assignment → ℝ} (hp : ∀ σ, 0 ≤ P σ)
    (x : ι → ℝ) (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i) (i : Fin (n+1)) (y : Fin (n+1) → ℝ) :
    |(replicaFeatureJet hw φ L T ha P x).A₁ i y| ≤
      (2*(T.leaves:ℝ))*D i*(replicaFeatureJet hw φ L T ha P x).A y := by
  rw [replicaFeatureJet_A₁,replicaFeatureJet_A]
  have hh := T.sourceJet_relative_abs_le hw φ [L (Pi.single i 1)] ha le_rfl P (hD i)
    (by intro v hv σ; simpa only [List.mem_singleton.mp hv] using hB i σ) (x+L y)
  simp only [List.length_singleton,ReplicaTree.attachmentCount,Nat.cast_mul,Nat.cast_ofNat,
    mul_one,pow_one,abs_of_nonneg (hp _)] at hh
  nlinarith

 

 theorem ReplicaTree.linearTestSplit_exp_comparison {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : ReplicaTree ι S steps) {a b : ℝ}
    (ho : OrderedSteps b steps) {P : R.Assignment → ℝ} (hp : ∀ σ, 0 ≤ P σ)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    {T s t : ℝ} (hs : s ∈ Icc (0:ℝ) T) (ht : t ∈ Icc (0:ℝ) T) (x : ι → ℝ) :
    let c := |a-b| *(2*(R.leaves:ℝ)+3)*∑ i, (D i)^2
    let f := fun u => linearTestSplit L a b (gaussianHierarchy w φ steps) (R.expect w φ P) T u x
    Real.exp (-c*|t-s|)*f s ≤ f t ∧ f t ≤ Real.exp (c*|t-s|)*f s := by
  let J := replicaFeatureJet hw φ L R ho P x
  have hh := J.massSplit_exp_comparison D hD
    (fun y => R.expect_nonneg hw φ ho hp (x+L y))
    (replicaFeatureJet_G_abs_le hw φ L R ho P x D hB)
    (replicaFeatureJet_A₁_relative_abs_le hw φ L R ho hp x D hD hB) ha ha1 hb hb1 hs ht 0
  have hF := (gaussianHierarchy_regular hw φ steps ho 0).1.choose_spec
  have hA := R.expect_smooth hw φ ho P 0
  simpa only [J,HeatJet.massSplit,HeatJet.evolve,replicaFeatureJet_F,replicaFeatureJet_A,
    ← linearTestSplit_eq L hF hA a hb] using hh

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S β : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

 theorem ReplicaTree.linearClock_mass_relative {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : ReplicaTree ι S steps) {a b : ℝ}
    (ho : OrderedSteps b steps) {P : R.Assignment → ℝ} (hp : ∀ σ, 0 ≤ P σ)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) (x : ι → ℝ) :
    linearClockTest L a (gaussianHierarchy w φ steps) (R.expect w φ P) t x ≤
      Real.exp ((|a-b| *(2*(R.leaves:ℝ)+3)*∑ i, (D i)^2)*t)*
      linearClockTest L b (gaussianHierarchy w φ steps) (R.expect w φ P) t x := by
  let J := replicaFeatureJet hw φ L R ho P x
  have hh := (J.massSplit_exp_comparison D hD
    (fun y => R.expect_nonneg hw φ ho hp (x+L y))
    (replicaFeatureJet_G_abs_le hw φ L R ho P x D hB)
    (replicaFeatureJet_A₁_relative_abs_le hw φ L R ho hp x D hD hB) ha ha1 hb hb1
    (show (0:ℝ) ∈ Icc 0 t from ⟨le_rfl,ht⟩) (show t ∈ Icc 0 t from ⟨ht,le_rfl⟩) 0).2
  rw [J.massSplit_zero,J.massSplit_terminal,sub_zero,abs_of_nonneg ht] at hh
  have hF := (gaussianHierarchy_regular hw φ steps ho 0).1.choose_spec.continuous
  have hA := (R.expect_smooth hw φ ho P 0).continuous
  simpa only [J,replicaFeatureJet_F,replicaFeatureJet_A,← linearClockTest_eq L hF hA] using hh

 theorem BoundaryTree.actual_mass_relative {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : β → ReplicaTree ι S steps) {a b c : ℝ}
    (hoa : OrderedSteps a steps) (hob : OrderedSteps b steps)
    (ha : 0 < a) (hb : 0 < b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front) (hO : PrefixOrdered 0 c front)
    {t : ℝ} (ht : 0 ≤ t) (σ : T.Assignment (fun d => (R d).Assignment)) (x : ι → ℝ) :
    T.weight (fun _ => linearClockContinuation L a (gaussianHierarchy w φ steps) t)
      (fun d τ _ => (R d).atomicClock w φ L a τ t) σ 0 x ≤
      Real.exp (T.budget (fun d => (|a-b| *(2*((R d).leaves:ℝ)+3)*∑ i, (D i)^2)*t+
        2*c*((|a-b| /2*∑ i, (D i)^2)*t)))*
      T.weight (fun _ => linearClockContinuation L b (gaussianHierarchy w φ steps) t)
      (fun d τ _ => (R d).atomicClock w φ L b τ t) σ 0 x := by
  classical
  have hF := gaussianHierarchy_regular hw φ steps hob 0
  have hi (m : ℝ) := (exponentialIncrement_linearGaussian L (Real.toNNReal t)).integrable_shift hF.1.choose_spec m
  have hc (m : ℝ) (d : β) (σ : (R d).Assignment) : BddSmooth 0 ((R d).atomicClock w φ L m σ t) :=
    ((R d).expect_smooth hw φ hob _ 0).shiftedMean hF (hi m)
  exact T.finite_relative
    (lipschitzWith_shiftedContinuation hF.1.choose_spec hb (hi b))
    (lipschitzWith_shiftedContinuation hF.1.choose_spec ha (hi a)) (by positivity)
    (fun y => (ReplicaTree.single steps).linearPotential_mass_difference hw φ L hob D hB ha hb ht y)
    (hc b) (hc a)
    (fun d τ y => ((R d).atomic_clockTest_probability hw φ L hob t y).1 τ)
    (fun d τ y => ((R d).atomic_clockTest_probability hw φ L hoa t y).1 τ)
    (fun d => (|a-b| *(2*((R d).leaves:ℝ)+3)*∑ i, (D i)^2)*t)
    (fun d τ y => (R d).linearClock_mass_relative hw φ L hob
      (P := fun v => if v = τ then 1 else 0) (by intro v; split_ifs <;> norm_num)
      D hD hB ha.le ha1 hb hb1 ht y) hO σ x

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S β : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 theorem ClockTree.atomicHead_mass_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a b : ℝ} (hoa : MassOrdered a as) (hob : MassOrdered b as)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0) (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    ExpClose (|a-b| *(2*(T.leaves:ℝ)+3)*∑ i, (v i:ℝ)*(D i)^2)
      (T.atomicHead w φ q v a σ x) (T.atomicHead w φ q v b σ x) := by
  classical
  have hd (i : Fin (n+1)) (σ : S) : |φ σ (diagonalDriver v (Pi.single i 1))| ≤ Real.sqrt (v i)*D i := by
    rw [diagonalDriver_single,map_smul,smul_eq_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hB i σ) (Real.sqrt_nonneg _)
  have h₁ := (T.realize q).linearClock_mass_relative hw φ (diagonalDriver v)
    (clockSteps_ordered hob q) (P := fun τ => if τ = T.assignmentEquiv q σ then 1 else 0)
    (by intro τ; split_ifs <;> norm_num) (fun i => Real.sqrt (v i)*D i)
    (fun i => mul_nonneg (Real.sqrt_nonneg _) (hD i)) hd ha.le ha1 hb hb1
    (by norm_num : (0:ℝ) ≤ 1) x
  have h₂ := (T.realize q).linearClock_mass_relative hw φ (diagonalDriver v)
    (clockSteps_ordered hoa q) (P := fun τ => if τ = T.assignmentEquiv q σ then 1 else 0)
    (by intro τ; split_ifs <;> norm_num) (fun i => Real.sqrt (v i)*D i)
    (fun i => mul_nonneg (Real.sqrt_nonneg _) (hD i)) hd hb.le hb1 ha ha1
    (by norm_num : (0:ℝ) ≤ 1) x
  refine ⟨(T.atomicHead_probability hw φ hoa ha q v x).1 σ,
    (T.atomicHead_probability hw φ hob hb q v x).1 σ,?_,?_⟩
  · rw [T.atomicHead_eq_clock,T.atomicHead_eq_clock]
    simpa only [ReplicaTree.atomicClock,mul_one,mul_pow,Real.sq_sqrt (v _).coe_nonneg,ClockTree.realize_leaves] using h₁
  · rw [T.atomicHead_eq_clock,T.atomicHead_eq_clock]
    simpa only [ReplicaTree.atomicClock,mul_one,mul_pow,Real.sq_sqrt (v _).coe_nonneg,ClockTree.realize_leaves,abs_sub_comm b a] using h₂

 theorem ClockTree.atomicHead_transfer_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {b : PositiveMass} {bs : List PositiveMass}
    (T : ClockTree S (b::bs)) (ho : MassOrdered b.val bs) {a : ℝ} (ha : 0 < a) (hab : a ≤ b.val)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0) (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    ExpClose ((|a-b.val| *(2*(T.leaves:ℝ)+3)+8*(T.leaves:ℝ)*(T.leaves+1:ℝ)*T.rootForks)*
        ∑ i, (v i:ℝ)*(D i)^2)
      (T.atomicHead w φ q v a σ x) (T.weight w φ (addHeadClock q v) σ x) := by
  have hb1 : b.val ≤ 1 := (massOrdered_bounds ho).2
  have h₁ := T.atomicHead_mass_close hw φ ⟨ha.le,hab,ho⟩ ⟨b.property.le,le_rfl,ho⟩
    ha (hab.trans hb1) b.property hb1 D hD hB q v σ x
  have h₂ := T.atomicHead_crossing_close hw φ rfl ho D hD hB q v σ x
  convert h₁.trans h₂ using 1
  ring

 theorem BoundaryTree.head_transfer_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {b : PositiveMass} {bs : List PositiveMass}
    (R : β → ClockTree S (b::bs)) (ho : MassOrdered b.val bs)
    {a c : ℝ} (ha : 0 < a) (hab : a ≤ b.val)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0)
    {front : List (GaussianStep (Fin (n+1)))} (T : BoundaryTree (Fin (n+1)) β front)
    (hO : PrefixOrdered 0 c front) (σ : T.Assignment (fun d => (R d).Assignment)) (x : Fin (n+1) → ℝ) :
    ExpClose (T.budget (fun d => ((|a-b.val| *(2*((R d).leaves:ℝ)+3)+
        8*((R d).leaves:ℝ)*((R d).leaves+1:ℝ)*(R d).rootForks)+c*|a-b.val|)*
        ∑ i, (v i:ℝ)*(D i)^2))
      (T.weight
        (fun _ => shiftedContinuation (Measure.pi fun i => gaussianReal 0 (v i)) a
          (gaussianHierarchy w φ (clockSteps (b::bs) q)))
        (fun d τ _ => (R d).atomicHead w φ q v a τ) σ 0 x)
      (T.weight (fun _ => gaussianHierarchy w φ (clockSteps (b::bs) (addHeadClock q v)))
        (fun d τ _ => (R d).weight w φ (addHeadClock q v) τ) σ 0 x) := by
  classical
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
  have hh := T.finite_close hG
    (lipschitzWith_shiftedContinuation hF ha ((exponentialIncrement_gaussian v).integrable_shift hF a))
    (by positivity : 0 ≤ |a-b.val|/2*∑ i, (v i:ℝ)*(D i)^2) hP
    (fun d σ => (R d).weight_smooth hw φ hB₀ (addHeadClock q v) σ 0)
    (fun d σ => (R d).atomicHead_smooth hw φ hA ha q v σ 0)
    (fun d => (|a-b.val| *(2*((R d).leaves:ℝ)+3)+
      8*((R d).leaves:ℝ)*((R d).leaves+1:ℝ)*(R d).rootForks)*∑ i, (v i:ℝ)*(D i)^2)
    (fun d τ y => (R d).atomicHead_transfer_close hw φ ho ha hab D hD hB q v τ y) hO σ x
  convert hh using 1
  congr 1
  funext d
  ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

def prependClock {ι : Type*} (u : ι → ℝ≥0) (q : ℕ → ι → ℝ≥0) : ℕ → ι → ℝ≥0
  | 0 => u
  | j+1 => q j

 theorem ClockTree.step_head_transfer {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {a b : PositiveMass} {bs : List PositiveMass}
    (T : ClockTree S (b::bs)) (ho : MassOrdered a.val (b::bs))
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℕ → Fin (n+1) → ℝ≥0) (u v : Fin (n+1) → ℝ≥0) (x : Fin (n+1) → ℝ) :
    ∑ σ, |(T.step a).weight w φ (prependClock (fun i => u i+v i) q) σ x-
      (T.step a).weight w φ (prependClock u (addHeadClock q v)) σ x| ≤
      ((|a.val-b.val| *(2*(T.leaves:ℝ)+3)+8*(T.leaves:ℝ)*(T.leaves+1:ℝ)*T.rootForks)+
        a.val*|a.val-b.val|)*∑ i, (v i:ℝ)*(D i)^2 := by
  classical
  let P : BoundaryTree (Fin (n+1)) Unit [(a.val,u)] :=
    (BoundaryTree.leaf () : BoundaryTree (Fin (n+1)) Unit []).step (a.val,u)
  have hO : PrefixOrdered 0 a.val [(a.val,u)] := ⟨le_rfl,a.property.le,a.property,a.property.le,le_rfl⟩
  have hh := P.head_transfer hw φ (fun _ => T) ho.2.2 a.property ho.2.1 D hD hB q v hO x
  have hF := (gaussianHierarchy_regular hw φ _ (clockSteps_ordered ho q) 0).1.choose_spec
  have hl (σ : T.Assignment) : shiftedMean (Measure.pi fun i => gaussianReal 0 (u i)) a.val
      (shiftedContinuation (Measure.pi fun i => gaussianReal 0 (v i)) a.val
        (gaussianHierarchy w φ (clockSteps (b::bs) q)))
      (T.atomicHead w φ q v a.val σ) x =
      (T.step a).weight w φ (prependClock (fun i => u i+v i) q) σ x :=
    shiftedMean_productGaussian_add hF (T.weight_smooth hw φ ho q σ 0) a.property.ne' u v x
  dsimp only [P,BoundaryTree.weight,BoundaryTree.budget,prefixContinuation] at hh
  simp_rw [hl] at hh
  exact hh

 

 theorem ClockTree.local_boundary_transfer {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a b : PositiveMass} {bs : List PositiveMass} (he : as = a::b::bs)
    (ho : MassOrdered a.val (b::bs)) (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℕ → Fin (n+1) → ℝ≥0) (u v : Fin (n+1) → ℝ≥0) (x : Fin (n+1) → ℝ) :
    ∑ σ, |T.weight w φ (prependClock (fun i => u i+v i) q) σ x-
      T.weight w φ (prependClock u (addHeadClock q v)) σ x| ≤
      (6*(T.leaves:ℝ)*|a.val-b.val|+8*(T.leaves:ℝ)*(T.leaves+1:ℝ)*T.forksAt 1)*
        ∑ i, (v i:ℝ)*(D i)^2 := by
  classical
  have hv : 0 ≤ ∑ i, (v i:ℝ)*(D i)^2 := Finset.sum_nonneg fun i _ => mul_nonneg (v i).coe_nonneg (sq_nonneg _)
  induction T generalizing a b bs with
  | leaf => cases he
  | @step c cs T ih =>
    cases he
    have hh := T.step_head_transfer hw φ ho D hD hB q u v x
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ hv
    simp only [ClockTree.leaves,ClockTree.forksAt,ClockTree.forksAt_zero]
    have hr : (1:ℝ) ≤ T.leaves := by exact_mod_cast T.leaves_pos
    have ha1 : c.val ≤ 1 := (massOrdered_bounds ho).2
    have hgap : 0 ≤ |c.val-b.val| := abs_nonneg _
    nlinarith [mul_nonneg hgap (sub_nonneg.mpr ha1),mul_nonneg hgap (sub_nonneg.mpr hr)]
  | @fork cs T U ihT ihU =>
    have hO : MassOrdered a.val cs := he ▸ ⟨a.property.le,le_rfl,ho⟩
    have hpT := T.weight_probability hw φ hO (prependClock u (addHeadClock q v)) x
    have hpU := U.weight_probability hw φ hO (prependClock (fun i => u i+v i) q) x
    have hp := finite_probability_product_distance hpT.1 hpU.1 hpT.2 hpU.2
      (p := fun σ => T.weight w φ (prependClock (fun i => u i+v i) q) σ x)
      (s := fun σ => U.weight w φ (prependClock u (addHeadClock q v)) σ x)
    change (∑ σ : T.Assignment × U.Assignment,
      |T.weight w φ (prependClock (fun i => u i+v i) q) σ.1 x*
        U.weight w φ (prependClock (fun i => u i+v i) q) σ.2 x-
        T.weight w φ (prependClock u (addHeadClock q v)) σ.1 x*
        U.weight w φ (prependClock u (addHeadClock q v)) σ.2 x|) ≤ _
    apply (hp.trans (add_le_add (ihT he ho) (ihU he ho))).trans
    rw [← add_mul]
    apply mul_le_mul_of_nonneg_right _ hv
    simp only [ClockTree.leaves,ClockTree.forksAt,show (1:ℕ) ≠ 0 from by omega,ite_false,zero_add,Nat.cast_add]
    have hT : 0 ≤ (T.leaves:ℝ) := Nat.cast_nonneg _
    have hU : 0 ≤ (U.leaves:ℝ) := Nat.cast_nonneg _
    have hTpoly : (T.leaves:ℝ)*(T.leaves+1:ℝ) ≤ (T.leaves+U.leaves:ℝ)*(T.leaves+U.leaves+1:ℝ) := by nlinarith
    have hUpoly : (U.leaves:ℝ)*(U.leaves+1:ℝ) ≤ (T.leaves+U.leaves:ℝ)*(T.leaves+U.leaves+1:ℝ) := by nlinarith
    have hTf := mul_le_mul_of_nonneg_right hTpoly (show (0:ℝ) ≤ T.forksAt 1 from Nat.cast_nonneg _)
    have hUf := mul_le_mul_of_nonneg_right hUpoly (show (0:ℝ) ≤ U.forksAt 1 from Nat.cast_nonneg _)
    nlinarith

 theorem gaussianHierarchy_local_boundary_transfer {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {a b : PositiveMass} {bs : List PositiveMass}
    (ho : MassOrdered b.val bs) (D : Fin (n+1) → ℝ) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℕ → Fin (n+1) → ℝ≥0) (u v : Fin (n+1) → ℝ≥0) (x : Fin (n+1) → ℝ) :
    |gaussianHierarchy w φ (clockSteps (a::b::bs) (prependClock (fun i => u i+v i) q)) x-
      gaussianHierarchy w φ (clockSteps (a::b::bs) (prependClock u (addHeadClock q v))) x| ≤
      |a.val-b.val|/2*∑ i, (v i:ℝ)*(D i)^2 := by
  have hh := gaussianHierarchy_covariance_transfer hw φ
    (clockSteps_ordered ho (fun j => q (j+1))) D hB a.property b.property u v (q 0) x
  simpa only [clockSteps,prependClock,addHeadClock,add_comm] using hh

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 theorem ClockTree.step_head_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {a b : PositiveMass} {bs : List PositiveMass}
    (T : ClockTree S (b::bs)) (ho : MassOrdered a.val (b::bs))
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℕ → Fin (n+1) → ℝ≥0) (u v : Fin (n+1) → ℝ≥0) (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    ExpClose (((|a.val-b.val| *(2*(T.leaves:ℝ)+3)+8*(T.leaves:ℝ)*(T.leaves+1:ℝ)*T.rootForks)+
        a.val*|a.val-b.val|)*∑ i, (v i:ℝ)*(D i)^2)
      ((T.step a).weight w φ (prependClock (fun i => u i+v i) q) σ x)
      ((T.step a).weight w φ (prependClock u (addHeadClock q v)) σ x) := by
  classical
  let P : BoundaryTree (Fin (n+1)) Unit [(a.val,u)] :=
    (BoundaryTree.leaf () : BoundaryTree (Fin (n+1)) Unit []).step (a.val,u)
  have hO : PrefixOrdered 0 a.val [(a.val,u)] := ⟨le_rfl,a.property.le,a.property,a.property.le,le_rfl⟩
  have hh := P.head_transfer_close hw φ (fun _ => T) ho.2.2 a.property ho.2.1 D hD hB q v hO σ x
  have hF := (gaussianHierarchy_regular hw φ _ (clockSteps_ordered ho q) 0).1.choose_spec
  have hl (σ : T.Assignment) : shiftedMean (Measure.pi fun i => gaussianReal 0 (u i)) a.val
      (shiftedContinuation (Measure.pi fun i => gaussianReal 0 (v i)) a.val
        (gaussianHierarchy w φ (clockSteps (b::bs) q)))
      (T.atomicHead w φ q v a.val σ) x =
      (T.step a).weight w φ (prependClock (fun i => u i+v i) q) σ x :=
    shiftedMean_productGaussian_add hF (T.weight_smooth hw φ ho q σ 0) a.property.ne' u v x
  dsimp only [P,BoundaryTree.weight,BoundaryTree.budget,prefixContinuation] at hh
  simp_rw [hl] at hh
  exact hh

 

 theorem ClockTree.local_boundary_close {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a b : PositiveMass} {bs : List PositiveMass} (he : as = a::b::bs)
    (ho : MassOrdered a.val (b::bs)) (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℕ → Fin (n+1) → ℝ≥0) (u v : Fin (n+1) → ℝ≥0) (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    ExpClose ((6*(T.leaves:ℝ)*|a.val-b.val|+8*(T.leaves:ℝ)*(T.leaves+1:ℝ)*T.forksAt 1)*
        ∑ i, (v i:ℝ)*(D i)^2)
      (T.weight w φ (prependClock (fun i => u i+v i) q) σ x)
      (T.weight w φ (prependClock u (addHeadClock q v)) σ x) := by
  classical
  have hv : 0 ≤ ∑ i, (v i:ℝ)*(D i)^2 := Finset.sum_nonneg fun i _ => mul_nonneg (v i).coe_nonneg (sq_nonneg _)
  induction T generalizing a b bs with
  | leaf => cases he
  | @step c cs T ih =>
    cases he
    have hh := T.step_head_close hw φ ho D hD hB q u v σ x
    apply hh.mono
    apply mul_le_mul_of_nonneg_right _ hv
    simp only [ClockTree.leaves,ClockTree.forksAt,ClockTree.forksAt_zero]
    have hr : (1:ℝ) ≤ T.leaves := by exact_mod_cast T.leaves_pos
    have ha1 : c.val ≤ 1 := (massOrdered_bounds ho).2
    have hgap : 0 ≤ |c.val-b.val| := abs_nonneg _
    nlinarith [mul_nonneg hgap (sub_nonneg.mpr ha1),mul_nonneg hgap (sub_nonneg.mpr hr)]
  | @fork cs T U ihT ihU =>
    have hh := (ihT he ho σ.1).mul (ihU he ho σ.2)
    apply hh.mono
    rw [← add_mul]
    apply mul_le_mul_of_nonneg_right _ hv
    simp only [ClockTree.leaves,ClockTree.forksAt,show (1:ℕ) ≠ 0 from by omega,ite_false,zero_add,Nat.cast_add]
    have hT : 0 ≤ (T.leaves:ℝ) := Nat.cast_nonneg _
    have hU : 0 ≤ (U.leaves:ℝ) := Nat.cast_nonneg _
    have hTpoly : (T.leaves:ℝ)*(T.leaves+1:ℝ) ≤ (T.leaves+U.leaves:ℝ)*(T.leaves+U.leaves+1:ℝ) := by nlinarith
    have hUpoly : (U.leaves:ℝ)*(U.leaves+1:ℝ) ≤ (T.leaves+U.leaves:ℝ)*(T.leaves+U.leaves+1:ℝ) := by nlinarith
    have hTf := mul_le_mul_of_nonneg_right hTpoly (show (0:ℝ) ≤ T.forksAt 1 from Nat.cast_nonneg _)
    have hUf := mul_le_mul_of_nonneg_right hUpoly (show (0:ℝ) ≤ U.forksAt 1 from Nat.cast_nonneg _)
    nlinarith

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι β : Type*}

 theorem BoundaryTree.budget_nonneg {front : List (GaussianStep ι)} (T : BoundaryTree ι β front)
    {f : β → ℝ} (hf : ∀ b, 0 ≤ f b) : 0 ≤ T.budget f := by
  induction T with
  | leaf b => exact hf b
  | step _ _ ih => exact ih
  | fork _ _ ihT ihU => exact add_nonneg ihT ihU

 theorem BoundaryTree.budget_quadratic {front : List (GaussianStep ι)} (T : BoundaryTree ι β front)
    {f g : β → ℝ} (hf : ∀ b, 0 ≤ f b) (hg : ∀ b, 0 ≤ g b) :
    T.budget (fun b => f b*(f b+1)*g b) ≤ T.budget f*(T.budget f+1)*T.budget g := by
  induction T with
  | leaf => exact le_rfl
  | step _ _ ih => exact ih
  | fork T U ihT ihU =>
    have hT := T.budget_nonneg hf
    have hU := U.budget_nonneg hf
    have hTpoly : T.budget f*(T.budget f+1) ≤ (T.budget f+U.budget f)*(T.budget f+U.budget f+1) := by nlinarith
    have hUpoly : U.budget f*(U.budget f+1) ≤ (T.budget f+U.budget f)*(T.budget f+U.budget f+1) := by nlinarith
    have hTf := mul_le_mul_of_nonneg_right hTpoly (T.budget_nonneg hg)
    have hUf := mul_le_mul_of_nonneg_right hUpoly (U.budget_nonneg hg)
    simp only [BoundaryTree.budget]
    nlinarith

 theorem ClockTree.cut_budget_one {as : List PositiveMass} (T : ClockTree S as)
    (j : ℕ) (q : ℕ → ι → ℝ≥0) (hj : j ≤ as.length) :
    (T.cut j q).budget (fun _ => (1:ℝ)) ≤ T.leaves := by
  rw [← T.cut_budget_leaves j q hj]
  exact (T.cut j q).budget_mono (fun U => by exact_mod_cast U.leaves_pos)

 theorem ClockTree.cut_budget_forksAt {as : List PositiveMass} (T : ClockTree S as)
    (j k : ℕ) (q : ℕ → ι → ℝ≥0) (hj : j ≤ as.length) :
    (T.cut j q).budget (fun U => (U.forksAt k:ℝ)) = T.forksAt (j+k) := by
  induction T generalizing j q with
  | leaf =>
    have : j = 0 := by simpa using hj
    subst j
    rfl
  | @step a cs T ih =>
    cases j with
    | zero => simp only [Nat.zero_add,ClockTree.cut,BoundaryTree.budget]; rfl
    | succ j =>
      have hj' : j ≤ cs.length := by simpa using hj
      change (T.cut j (fun r => q (r+1))).budget (fun U => (U.forksAt k:ℝ)) =
        (T.step a).forksAt (j+1+k)
      rw [ih j (fun r => q (r+1)) hj',show j+1+k = (j+k)+1 by omega]
      rfl
  | @fork cs T U ihT ihU =>
    cases j with
    | zero => simp only [Nat.zero_add,ClockTree.cut,BoundaryTree.budget]; rfl
    | succ j =>
      change (T.cut (j+1) q).budget (fun U => (U.forksAt k:ℝ))+
        (U.cut (j+1) q).budget (fun V => (V.forksAt k:ℝ)) = _
      rw [ihT (j+1) q hj,ihU (j+1) q hj]
      have hz : j+1+k ≠ 0 := by omega
      simp only [ClockTree.forksAt,hz,ite_false,zero_add,Nat.cast_add]

 

 theorem ClockTree.cut_budget_quadratic_forks {as : List PositiveMass} (T : ClockTree S as)
    (j k : ℕ) (q : ℕ → ι → ℝ≥0) (hj : j ≤ as.length) :
    (T.cut j q).budget (fun U => (U.leaves:ℝ)*(U.leaves+1:ℝ)*U.forksAt k) ≤
      (T.leaves:ℝ)*(T.leaves+1:ℝ)*T.forksAt (j+k) := by
  have h := (T.cut j q).budget_quadratic
    (fun U => (Nat.cast_nonneg U.leaves : (0:ℝ) ≤ U.leaves))
    (fun U => (Nat.cast_nonneg (U.forksAt k) : (0:ℝ) ≤ U.forksAt k))
  rwa [T.cut_budget_leaves j q hj,T.cut_budget_forksAt j k q hj] at h

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 

 theorem ClockTree.cut_boundary_transfer {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (j : ℕ) {a b : PositiveMass} {bs : List PositiveMass} (he : as.drop j = a::b::bs)
    (ho : MassOrdered a.val (b::bs))
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (p q : ℕ → Fin (n+1) → ℝ≥0) (u v : Fin (n+1) → ℝ≥0)
    {c : ℝ} (hO : PrefixOrdered 0 c (clockSteps (as.take j) p)) (hc : c ≤ 1)
    (x : Fin (n+1) → ℝ) :
    ∑ σ, |T.weight w φ (mixClocks j p (prependClock (fun i => u i+v i) q)) σ x-
      T.weight w φ (mixClocks j p (prependClock u (addHeadClock q v))) σ x| ≤
      (7*(T.leaves:ℝ)*|a.val-b.val|+8*(T.leaves:ℝ)*(T.leaves+1:ℝ)*T.forksAt (j+1))*
        ∑ i, (v i:ℝ)*(D i)^2 := by
  classical
  have hj : j ≤ as.length := by
    have hl := congrArg List.length he
    simp only [List.length_drop,List.length_cons] at hl
    omega
  have hv : 0 ≤ ∑ i, (v i:ℝ)*(D i)^2 := Finset.sum_nonneg fun i _ => mul_nonneg (v i).coe_nonneg (sq_nonneg _)
  have hc0 : 0 ≤ c := (hO.bounds).2
  have ha : MassOrdered a.val (as.drop j) := he ▸ ⟨a.property.le,le_rfl,ho⟩
  have hP (y : Fin (n+1) → ℝ) :
      |gaussianHierarchy w φ (clockSteps (as.drop j) (prependClock (fun i => u i+v i) q)) y-
        gaussianHierarchy w φ (clockSteps (as.drop j) (prependClock u (addHeadClock q v))) y| ≤
      |a.val-b.val|/2*∑ i, (v i:ℝ)*(D i)^2 := by
    rw [he]
    exact gaussianHierarchy_local_boundary_transfer hw φ ho.2.2 D hB q u v y
  have hh := T.cut_mix_stability hw φ j p
    (prependClock (fun i => u i+v i) q) (prependClock u (addHeadClock q v)) hj ha
    (by positivity : 0 ≤ |a.val-b.val|/2*∑ i, (v i:ℝ)*(D i)^2) hP
    (fun U => (6*(U.leaves:ℝ)*|a.val-b.val|+8*(U.leaves:ℝ)*(U.leaves+1:ℝ)*U.forksAt 1)*
      ∑ i, (v i:ℝ)*(D i)^2)
    (fun U y => U.local_boundary_transfer hw φ he ho D hD hB q u v y) hO x
  apply hh.trans
  let V : ℝ := ∑ i, (v i:ℝ)*(D i)^2
  have heq : (T.cut j p).budget (fun U =>
      (6*(U.leaves:ℝ)*|a.val-b.val|+8*(U.leaves:ℝ)*(U.leaves+1:ℝ)*U.forksAt 1)*V+
        2*c*(|a.val-b.val|/2*V)) =
      (T.cut j p).budget (fun U => (U.leaves:ℝ))*(6*|a.val-b.val| *V)+
      (T.cut j p).budget (fun U => (U.leaves:ℝ)*(U.leaves+1:ℝ)*U.forksAt 1)*(8*V)+
      (T.cut j p).budget (fun _ => (1:ℝ))*(c*|a.val-b.val| *V) := by
    calc
      _ = (T.cut j p).budget (fun U =>
        (U.leaves:ℝ)*(6*|a.val-b.val| *V)+
        ((U.leaves:ℝ)*(U.leaves+1:ℝ)*U.forksAt 1)*(8*V)+(1:ℝ)*(c*|a.val-b.val| *V)) := by
          congr 1
          funext U
          ring
      _ = _ := by rw [BoundaryTree.budget_add,BoundaryTree.budget_add,
        BoundaryTree.budget_mul,BoundaryTree.budget_mul,BoundaryTree.budget_mul]
  change (T.cut j p).budget _ ≤ _
  rw [heq,T.cut_budget_leaves j p hj]
  have hfork := mul_le_mul_of_nonneg_right (T.cut_budget_quadratic_forks j 1 p hj)
    (show 0 ≤ 8*V by positivity)
  have hone := mul_le_mul_of_nonneg_right (T.cut_budget_one j p hj)
    (show 0 ≤ c*|a.val-b.val| *V by positivity)
  have hlast : (T.leaves:ℝ)*(c*|a.val-b.val| *V) ≤ (T.leaves:ℝ)*(|a.val-b.val| *V) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (mul_nonneg (abs_nonneg (a.val-b.val)) hv)]
  dsimp only [V] at hfork hone hlast ⊢
  nlinarith

end SKFluctuations.Hierarchy

end

end OAI
