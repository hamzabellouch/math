import Mathlib
import OAI.Probability.SKFluctuations.FilledSquare

namespace OAI

/-! Feature Clock Response. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

noncomputable def featureClockResponse (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) (steps : List (GaussianStep ι)) (m : ℝ) : ℝ → (ι → ℝ) → ℝ :=
  linearClockDerivative L m (gaussianHierarchy w φ steps)
    (fun i => gaussianHierarchyMean w φ (fun σ => φ σ (L (Pi.single i 1))) steps)
    (fun i => gaussianHierarchyResponse w φ (fun σ => φ σ (L (Pi.single i 1))) (L (Pi.single i 1)) steps)

 theorem featureClockResponse_bound {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) {Q m : ℝ}
    (hQ : ∀ σ, ∑ i, (φ σ (L (Pi.single i 1)))^2 = Q)
    (steps : List (GaussianStep ι)) (ha : OrderedSteps m steps) (t : ℝ) (x : ι → ℝ) :
    |featureClockResponse w φ L steps m t x| ≤ Q/2 := by
  obtain ⟨C,hF⟩ := (gaussianHierarchy_regular hw φ steps ha 0).1
  have hi := (exponentialIncrement_linearGaussian L (Real.toNNReal t)).integrable_shift hF m x
  have hP := linearFeaturePenalty_smooth hw φ L steps ha 0
  have hp : 0 ≤ linearClockTest L m (gaussianHierarchy w φ steps) (linearFeaturePenalty w φ L m steps) t x :=
    shiftedMean_nonneg (fun y => (linearFeaturePenalty_bounds hw φ L hQ steps ha y).1) hi
  have hb : linearClockTest L m (gaussianHierarchy w φ steps) (linearFeaturePenalty w φ L m steps) t x ≤ Q := by
    have hh := shiftedMean_mono hP (BddSmooth.const 0 Q)
      (fun y => (le_abs_self _).trans (linearFeaturePenalty_abs_le hw φ L hQ steps ha y)) hi
    rwa [shiftedMean_const Q hi] at hh
  unfold featureClockResponse
  rw [linearClockDerivative_feature_trace hw φ L hQ steps ha t x]
  rw [abs_of_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hb))]
  linarith

 theorem parametric_featureClock {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) {Q m : ℝ}
    (hQ : ∀ σ, ∑ i, (φ σ (L (Pi.single i 1)))^2 = Q)
    (steps : List (GaussianStep ι)) (ha : OrderedSteps m steps) (hm : 0 < m) (r : ℝ) :
    ParametricRegular 0 r (Q/2) (linearClockContinuation L m (gaussianHierarchy w φ steps))
      (featureClockResponse w φ L steps m) := by
  obtain ⟨C,hC⟩ := (gaussianHierarchy_regular hw φ steps ha 0).1
  obtain ⟨K,hK⟩ := parametric_linear_clock L hC
    (fun i => gaussianHierarchyMean_smooth hw φ _ steps ha 0)
    (fun i => gaussianHierarchyResponse_smooth hw φ _ _ steps ha 0)
    (fun y => (gaussianHierarchy_linear_feature_derivatives hw φ L steps ha y).1)
    (fun y => (gaussianHierarchy_linear_feature_derivatives hw φ L steps ha y).2) hm
  have hQ0 : 0 ≤ Q := by
    obtain ⟨σ⟩ := ‹Nonempty S›
    rw [← hQ σ]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  exact ⟨by positivity,(hK r).spatial,(hK r).continuous,
    fun t _ x => featureClockResponse_bound hw φ L hQ steps ha t x,(hK r).derivative⟩

namespace ReplicaTree

 theorem clockResponse_smooth0 {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {m : ℝ} (ha : OrderedSteps m steps)
    (P : T.Assignment → ℝ) (t : ℝ) : BddSmooth 0 (T.clockResponse w φ L m P t) := by
  have hF := gaussianHierarchy_regular hw φ steps ha 0
  have hi := (exponentialIncrement_linearGaussian L (Real.toNNReal t)).integrable_shift hF.1.choose_spec m
  exact (((T.powerTrace_smooth hw φ L ha P 0).shiftedMean hF hi).sub
    (((T.expect_smooth hw φ ha P 0).shiftedMean hF hi).mul
      ((T.powerTrace_smooth hw φ L ha (fun _ => 1) 0).shiftedMean hF hi))).const_mul (1/2)

 theorem parametric_clockTest {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {m : ℝ} (ha : OrderedSteps m steps)
    {P : T.Assignment → ℝ} {C : ℝ} (D : Fin (n+1) → ℝ)
    (hC : 0 ≤ C) (hD : ∀ i, 0 ≤ D i) (hP : ∀ σ, |P σ| ≤ C)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i) (r : ℝ) :
    ParametricTest 0 r (C+4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*C*∑ i, (D i)^2)
      (linearClockTest L m (gaussianHierarchy w φ steps) (T.expect w φ P))
      (T.clockResponse w φ L m P) := by
  have hK : 0 ≤ 4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*C*∑ i, (D i)^2 := by positivity
  refine ⟨by positivity,?_,fun t _ => (T.clockResponse_smooth0 hw φ L ha P t).continuous,?_,?_,?_⟩
  · intro t _
    have hF := gaussianHierarchy_regular hw φ steps ha 0
    exact ((T.expect_smooth hw φ ha P 0).shiftedMean hF
      ((exponentialIncrement_linearGaussian L (Real.toNNReal t)).integrable_shift hF.1.choose_spec m)).continuous
  · intro t _ x
    exact (T.clock_abs_le hw φ L ha hP t x).trans (le_add_of_nonneg_right hK)
  · intro t _ x
    exact (T.clockResponse_abs_le hw φ L ha D hC hD hP hB t x).trans (le_add_of_nonneg_left hC)
  · intro t ht x
    exact (T.hasDerivWithinAt_linearClockTest hw φ L ha P x ht.1.le).hasDerivAt (Ici_mem_nhds ht.1)

end ReplicaTree
end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem finite_law_variation_dual {κ : Type*} [Fintype κ] {R : κ → ℝ} {K : ℝ}
    (h : ∀ P : κ → ℝ, (∀ σ, |P σ| ≤ 1) → |∑ σ, P σ*R σ| ≤ K) :
    ∑ σ, |R σ| ≤ K := by
  classical
  let P : κ → ℝ := fun σ => if 0 ≤ R σ then 1 else -1
  have hP : ∀ σ, |P σ| ≤ 1 := by intro σ; dsimp [P]; split_ifs <;> norm_num
  have he : ∑ σ, P σ*R σ = ∑ σ, |R σ| := by
    apply Finset.sum_congr rfl
    intro σ _
    dsimp [P]
    split_ifs with hh
    · rw [one_mul,abs_of_nonneg hh]
    · rw [neg_one_mul,abs_of_neg (lt_of_not_ge hh)]
  have hh := h P hP
  rw [he,abs_of_nonneg (Finset.sum_nonneg fun σ _ => abs_nonneg _)] at hh
  exact hh

variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}
namespace ReplicaTree

 theorem clockTest_atomic {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {m : ℝ} (ha : OrderedSteps m steps)
    [DecidableEq T.Assignment] (P : T.Assignment → ℝ) (t : ℝ) (x : ι → ℝ) :
    linearClockTest L m (gaussianHierarchy w φ steps) (T.expect w φ P) t x =
      ∑ σ, P σ*linearClockTest L m (gaussianHierarchy w φ steps)
        (T.expect w φ (fun τ => if τ = σ then 1 else 0)) t x := by
  have hF := gaussianHierarchy_regular hw φ steps ha 0
  have hi := (exponentialIncrement_linearGaussian L (Real.toNNReal t)).integrable_shift hF.1.choose_spec m x
  have he : T.expect w φ P = fun y => ∑ σ, P σ*T.expect w φ (fun τ => if τ = σ then 1 else 0) y := by
    funext y
    simp_rw [T.expect_indicator]
    unfold expect
    apply Finset.sum_congr rfl
    intro σ _
    ring
  change shiftedMean _ _ _ _ _ = _
  rw [he,shiftedMean_finsetSum Finset.univ
    (fun σ _ => (T.expect_smooth hw φ ha (fun τ => if τ = σ then 1 else 0) 0).const_mul (P σ)) hi]
  simp only [shiftedMean_const_mul,linearClockTest]

 theorem clockResponse_atomic {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {m : ℝ} (ha : OrderedSteps m steps)
    [DecidableEq T.Assignment] (P : T.Assignment → ℝ) {t : ℝ} (ht : 0 < t) (x : ι → ℝ) :
    T.clockResponse w φ L m P t x =
      ∑ σ, P σ*T.clockResponse w φ L m (fun τ => if τ = σ then 1 else 0) t x := by
  have hd (P : T.Assignment → ℝ) :=
    (T.hasDerivWithinAt_linearClockTest hw φ L ha P x ht.le).hasDerivAt (Ici_mem_nhds ht)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ => (hd (fun τ => if τ = σ then 1 else 0)).const_mul (P σ))
  have hh : HasDerivAt (fun s => linearClockTest L m (gaussianHierarchy w φ steps) (T.expect w φ P) s x)
      (∑ σ, P σ*T.clockResponse w φ L m (fun τ => if τ = σ then 1 else 0) t x) t := by
    have he : (fun s => linearClockTest L m (gaussianHierarchy w φ steps) (T.expect w φ P) s x) =
        (fun s => ∑ σ, P σ*linearClockTest L m (gaussianHierarchy w φ steps)
          (T.expect w φ (fun τ => if τ = σ then 1 else 0)) s x) :=
      funext fun s => T.clockTest_atomic hw φ L ha P s x
    rw [he]
    exact hs
  exact (hd P).unique hh

 theorem atomic_clockResponse_variation {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {m : ℝ} (ha : OrderedSteps m steps)
    [DecidableEq T.Assignment] (D : Fin (n+1) → ℝ)
    (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    {t : ℝ} (ht : 0 < t) (x : ι → ℝ) :
    ∑ σ, |T.clockResponse w φ L m (fun τ => if τ = σ then 1 else 0) t x| ≤
      4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*∑ i, (D i)^2 := by
  apply finite_law_variation_dual
  intro P hP
  rw [← T.clockResponse_atomic hw φ L ha P ht x]
  simpa only [mul_one] using T.clockResponse_abs_le hw φ L ha D (by norm_num : (0:ℝ) ≤ 1) hD hP hB t x

 theorem atomic_clockTest_probability {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {m : ℝ} (ha : OrderedSteps m steps)
    [DecidableEq T.Assignment] (t : ℝ) (x : ι → ℝ) :
    (∀ σ, 0 ≤ linearClockTest L m (gaussianHierarchy w φ steps)
      (T.expect w φ (fun τ => if τ = σ then 1 else 0)) t x) ∧
    (∑ σ, linearClockTest L m (gaussianHierarchy w φ steps)
      (T.expect w φ (fun τ => if τ = σ then 1 else 0)) t x) = 1 := by
  have hF := gaussianHierarchy_regular hw φ steps ha 0
  have hi := (exponentialIncrement_linearGaussian L (Real.toNNReal t)).integrable_shift hF.1.choose_spec m x
  refine ⟨fun σ => ?_,?_⟩
  · apply shiftedMean_nonneg _ hi
    intro y
    rw [T.expect_indicator]
    exact T.weight_nonneg hw φ ha σ y
  · have hh := T.clockTest_atomic hw φ L ha (fun _ => 1) t x
    simp only [one_mul] at hh
    rw [← hh]
    have he : T.expect w φ (fun _ => 1) = fun _ => 1 := funext fun y => T.expect_const hw φ ha 1 y
    unfold linearClockTest
    rw [he,shiftedMean_const 1 hi]

end ReplicaTree
end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
universe uB vB wB

 

inductive BoundaryTree (ι : Type uB) (β : Type vB) : List (GaussianStep ι) → Type (max uB vB) where
  | leaf (b : β) : BoundaryTree ι β []
  | step (st : GaussianStep ι) {tail : List (GaussianStep ι)}
      (T : BoundaryTree ι β tail) : BoundaryTree ι β (st::tail)
  | fork {front : List (GaussianStep ι)} (T U : BoundaryTree ι β front) : BoundaryTree ι β front

variable {ι : Type uB} {β : Type vB} {κ : β → Type wB}

@[reducible] def BoundaryTree.Assignment (κ : β → Type wB) :
    {front : List (GaussianStep ι)} → BoundaryTree ι β front → Type wB
  | _, .leaf b => κ b
  | _, .step _ T => T.Assignment κ
  | _, .fork T U => T.Assignment κ × U.Assignment κ

@[instance_reducible] noncomputable def BoundaryTree.assignmentFintype [∀ b, Fintype (κ b)] :
    {front : List (GaussianStep ι)} → (T : BoundaryTree ι β front) → Fintype (T.Assignment κ)
  | _, .leaf b => inferInstanceAs (Fintype (κ b))
  | _, .step _ T => T.assignmentFintype
  | _, .fork T U => @instFintypeProd _ _ T.assignmentFintype U.assignmentFintype
attribute [instance] BoundaryTree.assignmentFintype

variable [Fintype ι]

noncomputable def BoundaryTree.weight (F : ℝ → (ι → ℝ) → ℝ)
    (W : ∀ b, κ b → ℝ → (ι → ℝ) → ℝ) :
    {front : List (GaussianStep ι)} → (T : BoundaryTree ι β front) → T.Assignment κ → ℝ → (ι → ℝ) → ℝ
  | _, .leaf b, σ => W b σ
  | _, @BoundaryTree.step _ _ (m,q) tail T, σ => fun t =>
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m
        (prefixContinuation tail (F t)) (fun x => T.weight F W σ t x)
  | _, .fork T U, σ => fun t x => T.weight F W σ.1 t x*U.weight F W σ.2 t x

noncomputable def BoundaryTree.response (F D : ℝ → (ι → ℝ) → ℝ)
    (W B : ∀ b, κ b → ℝ → (ι → ℝ) → ℝ) :
    {front : List (GaussianStep ι)} → (T : BoundaryTree ι β front) → T.Assignment κ → ℝ → (ι → ℝ) → ℝ
  | _, .leaf b, σ => B b σ
  | _, @BoundaryTree.step _ _ (m,q) tail T, σ => fun t =>
      tiltedResponse q m (prefixContinuation tail (F t)) (prefixTest tail (F t) (D t))
        (fun x => T.weight F W σ t x) (fun x => T.response F D W B σ t x)
  | _, .fork T U, σ => fun t x => T.response F D W B σ.1 t x*U.weight F W σ.2 t x+
      T.weight F W σ.1 t x*U.response F D W B σ.2 t x

 theorem BoundaryTree.parametric {l r J : ℝ} {F D : ℝ → (ι → ℝ) → ℝ}
    {W B : ∀ b, κ b → ℝ → (ι → ℝ) → ℝ}
    (hF : ParametricRegular l r J F D)
    (hW : ∀ b σ, ∃ K, ParametricTest l r K (W b σ) (B b σ))
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front)
    (hm : ∀ st ∈ front, 0 < st.1) (σ : T.Assignment κ) :
    ∃ K, ParametricTest l r K (T.weight F W σ) (T.response F D W B σ) := by
  induction T with
  | leaf b => exact hW b σ
  | @step st tail T ih =>
    rcases st with ⟨m,q⟩
    have ht := fun s hs => hm s (List.mem_cons_of_mem _ hs)
    obtain ⟨K,hK⟩ := ih ht σ
    exact ⟨_,hK.step (hF.prefix tail ht) q m⟩
  | fork T U ihT ihU =>
    obtain ⟨K,hK⟩ := ihT hm σ.1
    obtain ⟨J,hJ⟩ := ihU hm σ.2
    exact ⟨_,hK.mul hJ⟩

 theorem BoundaryTree.weight_smooth0 {l r J : ℝ} {F D : ℝ → (ι → ℝ) → ℝ}
    {W B : ∀ b, κ b → ℝ → (ι → ℝ) → ℝ}
    (hF : ParametricRegular l r J F D)
    (hW : ∀ b σ, ∃ K, ParametricTest l r K (W b σ) (B b σ))
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front)
    (hm : ∀ st ∈ front, 0 < st.1) (σ : T.Assignment κ) {t : ℝ} (ht : t ∈ Ioo l r) :
    BddSmooth 0 (fun x => T.weight F W σ t x) :=
  (T.parametric hF hW hm σ).choose_spec.smooth0 ht

 theorem BoundaryTree.response_smooth0 {l r J : ℝ} {F D : ℝ → (ι → ℝ) → ℝ}
    {W B : ∀ b, κ b → ℝ → (ι → ℝ) → ℝ}
    (hF : ParametricRegular l r J F D)
    (hW : ∀ b σ, ∃ K, ParametricTest l r K (W b σ) (B b σ))
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front)
    (hm : ∀ st ∈ front, 0 < st.1) (σ : T.Assignment κ) {t : ℝ} (ht : t ∈ Ioo l r) :
    BddSmooth 0 (fun x => T.response F D W B σ t x) :=
  (T.parametric hF hW hm σ).choose_spec.response_smooth0 ht

 theorem BoundaryTree.probability [∀ b, Fintype (κ b)]
    {l r J : ℝ} {F D : ℝ → (ι → ℝ) → ℝ} {W B : ∀ b, κ b → ℝ → (ι → ℝ) → ℝ}
    (hF : ParametricRegular l r J F D)
    (hW : ∀ b σ, ∃ K, ParametricTest l r K (W b σ) (B b σ))
    (hp : ∀ b, ∀ t ∈ Ioo l r, ∀ x, (∀ σ, 0 ≤ W b σ t x) ∧ ∑ σ, W b σ t x = 1)
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front)
    (hm : ∀ st ∈ front, 0 < st.1) {t : ℝ} (ht : t ∈ Ioo l r) (x : ι → ℝ) :
    (∀ σ : T.Assignment κ, 0 ≤ T.weight F W σ t x) ∧ ∑ σ, T.weight F W σ t x = 1 := by
  induction T generalizing x with
  | leaf b => exact hp b t ht x
  | @step st tail T ih =>
    rcases st with ⟨m,q⟩
    have htail := fun s hs => hm s (List.mem_cons_of_mem _ hs)
    have hi := (exponentialIncrement_gaussian q).integrable_shift
      ((hF.prefix tail htail).spatial t ht).choose_spec m x
    refine ⟨fun σ => shiftedMean_nonneg (fun y => (ih htail y).1 σ) hi,?_⟩
    change ∑ σ, shiftedMean _ _ _ (fun y => T.weight F W σ t y) x = _
    rw [← shiftedMean_finsetSum Finset.univ (fun σ _ => T.weight_smooth0 hF hW htail σ ht) hi]
    simp_rw [(ih htail _).2]
    exact shiftedMean_const 1 hi
  | @fork front T U ihT ihU =>
    obtain ⟨hT,sT⟩ := ihT hm x
    obtain ⟨hU,sU⟩ := ihU hm x
    refine ⟨fun σ => mul_nonneg (hT σ.1) (hU σ.2),?_⟩
    change ∑ σ : T.Assignment κ × U.Assignment κ, T.weight F W σ.1 t x*U.weight F W σ.2 t x = _
    simp only [Fintype.sum_prod_type,← Finset.mul_sum,sU,mul_one,sT]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem BddSmooth.abs_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → ℝ} (h : BddSmooth 0 A) : BddSmooth 0 (fun x => |A x|) := by
  obtain ⟨K,hK,hb⟩ := h.bound
  exact ⟨h.continuous.abs,K,hK,fun x => by simpa only [abs_abs] using hb x⟩

 theorem sum_abs_shiftedMean_le {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsProbabilityMeasure ν] [Fintype κ]
    {F : E → ℝ} {m K : ℝ} {A : κ → E → ℝ}
    (hA : ∀ i, BddSmooth 0 (A i)) (hb : ∀ x, ∑ i, |A i x| ≤ K) {x : E}
    (hi : Integrable (fun z => Real.exp (m*F (x+z))) ν) :
    ∑ i, |shiftedMean ν m F (A i) x| ≤ K := by
  calc
    _ ≤ ∑ i, shiftedMean ν m F (fun y => |A i y|) x :=
      Finset.sum_le_sum fun i _ => shiftedMean_abs_mono (hA i) (hA i).abs_zero (fun y => le_refl _) hi
    _ = shiftedMean ν m F (fun y => ∑ i, |A i y|) x :=
      (shiftedMean_finsetSum Finset.univ (fun i _ => (hA i).abs_zero) hi).symm
    _ ≤ shiftedMean ν m F (fun _ => K) x := shiftedMean_mono
      (BddSmooth.sum Finset.univ fun i _ => (hA i).abs_zero) (BddSmooth.const 0 K) hb hi
    _ = K := shiftedMean_const K hi

 theorem finite_law_score_fork {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    {W : κ → ℝ} {V : ρ → ℝ} {B : κ → ℝ} {C : ρ → ℝ} {a D K L M : ℝ}
    (hW : ∀ i, 0 ≤ W i) (hV : ∀ j, 0 ≤ V j)
    (sW : ∑ i, W i = 1) (sV : ∑ j, V j = 1)
    (hB : ∑ i, |B i+a*W i*D| ≤ K) (hC : ∑ j, |C j+a*V j*D| ≤ L)
    (ha : 0 ≤ a) (hD : |D| ≤ M) :
    ∑ z : κ × ρ, |B z.1*V z.2+W z.1*C z.2+a*(W z.1*V z.2)*D| ≤ K+L+a*M := by
  have he (i : κ) (j : ρ) :
      B i*V j+W i*C j+a*(W i*V j)*D =
        (B i+a*W i*D)*V j+W i*(C j+a*V j*D)-a*W i*V j*D := by ring
  calc
    _ ≤ ∑ z : κ × ρ, (|B z.1+a*W z.1*D| *V z.2+W z.1*|C z.2+a*V z.2*D|+a*W z.1*V z.2*M) := by
      apply Finset.sum_le_sum
      intro z _
      rw [he]
      apply (abs_sub _ _).trans
      have h := abs_add_le ((B z.1+a*W z.1*D)*V z.2) (W z.1*(C z.2+a*V z.2*D))
      simp only [abs_mul,abs_of_nonneg (hW z.1),abs_of_nonneg (hV z.2),abs_of_nonneg ha] at h ⊢
      have hh := mul_le_mul_of_nonneg_left hD (mul_nonneg (mul_nonneg ha (hW z.1)) (hV z.2))
      linarith
    _ = (∑ i, |B i+a*W i*D|)+(∑ j, |C j+a*V j*D|)+a*M := by
      simp only [Fintype.sum_prod_type,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum,sV,sW,mul_one,one_mul]
    _ ≤ K+L+a*M := by linarith

 theorem finite_law_subtraction_bound {κ : Type*} [Fintype κ]
    {W R : κ → ℝ} {c D K J : ℝ} (hW : ∀ i, 0 ≤ W i) (sW : ∑ i, W i = 1)
    (hR : ∑ i, |R i| ≤ K) (hc : 0 ≤ c) (hD : |D| ≤ J) :
    ∑ i, |R i-c*W i*D| ≤ K+c*J := by
  calc
    _ ≤ ∑ i, (|R i|+c*W i*J) := by
      apply Finset.sum_le_sum
      intro i _
      apply (abs_sub _ _).trans
      rw [abs_mul,abs_mul,abs_of_nonneg hc,abs_of_nonneg (hW i)]
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hD (mul_nonneg hc (hW i)))
    _ = (∑ i, |R i|)+c*J := by
      simp only [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum,sW,mul_one]
    _ ≤ K+c*J := add_le_add hR (le_refl _)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
universe uB vB wB
variable {ι : Type uB} {β : Type vB} {κ : β → Type wB}

def PrefixOrdered (a b : ℝ) : List (GaussianStep ι) → Prop
  | [] => 0 ≤ a ∧ a ≤ b
  | (m,_)::tail => 0 ≤ a ∧ a ≤ m ∧ 0 < m ∧ PrefixOrdered m b tail

 theorem PrefixOrdered.positive {a b : ℝ} {front : List (GaussianStep ι)}
    (h : PrefixOrdered a b front) : ∀ st ∈ front, 0 < st.1 := by
  induction front generalizing a with
  | nil => simp
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    intro s hs
    rcases List.mem_cons.mp hs with hs|hs
    · simpa only [hs] using h.2.2.1
    · exact ih h.2.2.2 s hs

 theorem PrefixOrdered.bounds {a b : ℝ} {front : List (GaussianStep ι)}
    (h : PrefixOrdered a b front) : 0 ≤ a ∧ a ≤ b := by
  induction front generalizing a with
  | nil => exact h
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    exact ⟨h.1,h.2.1.trans (ih h.2.2.2).2⟩

def BoundaryTree.budget (V : β → ℝ) : {front : List (GaussianStep ι)} → BoundaryTree ι β front → ℝ
  | _, .leaf b => V b
  | _, .step _ T => T.budget V
  | _, .fork T U => T.budget V+U.budget V

variable [Fintype ι] [∀ b, Fintype (κ b)]

noncomputable def BoundaryTree.score (F D : ℝ → (ι → ℝ) → ℝ)
    (W B : ∀ b, κ b → ℝ → (ι → ℝ) → ℝ) {front : List (GaussianStep ι)}
    (T : BoundaryTree ι β front) (a : ℝ) (σ : T.Assignment κ) (t : ℝ) (x : ι → ℝ) : ℝ :=
  T.response F D W B σ t x+a*T.weight F W σ t x*prefixTest front (F t) (D t) x

omit [∀ b, Fintype (κ b)] in
 theorem BoundaryTree.score_smooth0 {l r J : ℝ} {F D : ℝ → (ι → ℝ) → ℝ}
    {W B : ∀ b, κ b → ℝ → (ι → ℝ) → ℝ}
    (hF : ParametricRegular l r J F D)
    (hW : ∀ b σ, ∃ K, ParametricTest l r K (W b σ) (B b σ))
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front)
    (hm : ∀ st ∈ front, 0 < st.1) (a : ℝ) (σ : T.Assignment κ) {t : ℝ} (ht : t ∈ Ioo l r) :
    BddSmooth 0 (T.score F D W B a σ t) :=
  (T.response_smooth0 hF hW hm σ ht).add
    (((T.weight_smooth0 hF hW hm σ ht).const_mul a).mul ((hF.prefix front hm).response_smooth0 ht))

omit [∀ b, Fintype (κ b)] in
 theorem BoundaryTree.score_step {l r J : ℝ} {F D : ℝ → (ι → ℝ) → ℝ}
    {W B : ∀ b, κ b → ℝ → (ι → ℝ) → ℝ}
    (hF : ParametricRegular l r J F D)
    (hW : ∀ b σ, ∃ K, ParametricTest l r K (W b σ) (B b σ))
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front)
    (hm : ∀ st ∈ front, 0 < st.1) (a m : ℝ) (q : ι → ℝ≥0)
    (σ : T.Assignment κ) {t : ℝ} (ht : t ∈ Ioo l r) (x : ι → ℝ) :
    (T.step (m,q)).score F D W B a σ t x =
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m (prefixContinuation front (F t))
        (T.score F D W B m σ t) x-
      (m-a)*(T.step (m,q)).weight F W σ t x*prefixTest ((m,q)::front) (F t) (D t) x := by
  let ν := Measure.pi fun i => gaussianReal 0 (q i)
  have hi := (exponentialIncrement_gaussian q).integrable_shift
    ((hF.prefix front hm).spatial t ht).choose_spec m x
  have hB := T.response_smooth0 hF hW hm σ ht
  have hA := T.weight_smooth0 hF hW hm σ ht
  have hD := (hF.prefix front hm).response_smooth0 ht
  have he : (T.score F D W B m σ t) = fun y =>
      T.response F D W B σ t y+m*(T.weight F W σ t y*prefixTest front (F t) (D t) y) := by
    funext y
    unfold score
    ring
  rw [he,shiftedMean_add hB ((hA.mul hD).const_mul m) hi,shiftedMean_const_mul]
  simp only [score,response,weight,tiltedResponse,prefixTest]
  ring

 

 theorem BoundaryTree.score_variation {l r J m a : ℝ} {F D : ℝ → (ι → ℝ) → ℝ}
    {W B : ∀ b, κ b → ℝ → (ι → ℝ) → ℝ} {V : β → ℝ}
    (hF : ParametricRegular l r J F D)
    (hW : ∀ b σ, ∃ K, ParametricTest l r K (W b σ) (B b σ))
    (hp : ∀ b, ∀ t ∈ Ioo l r, ∀ x, (∀ σ, 0 ≤ W b σ t x) ∧ ∑ σ, W b σ t x = 1)
    (hv : ∀ b, ∀ t ∈ Ioo l r, ∀ x, ∑ σ, |B b σ t x+m*W b σ t x*D t x| ≤ V b)
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front)
    (ha : PrefixOrdered a m front) {t : ℝ} (ht : t ∈ Ioo l r) (x : ι → ℝ) :
    ∑ σ, |T.score F D W B a σ t x| ≤ T.budget (fun b => V b+m*J)-a*J := by
  induction T generalizing a x with
  | leaf b =>
    have hh := finite_law_subtraction_bound (hp b t ht x).1 (hp b t ht x).2 (hv b t ht x)
      (sub_nonneg.mpr ha.2) (hF.bounded t ht x)
    have he (σ : κ b) : (B b σ t x+m*W b σ t x*D t x)-(m-a)*W b σ t x*D t x =
        (BoundaryTree.leaf b : BoundaryTree ι β []).score F D W B a σ t x := by
      simp only [score,response,weight,prefixTest]
      ring
    simp_rw [he] at hh
    dsimp only [budget]
    linarith
  | @step st tail T ih =>
    rcases st with ⟨b,q⟩
    let ν := Measure.pi fun i => gaussianReal 0 (q i)
    have hm := ha.positive
    have hb := ha.2.2.2.positive
    have hi := (exponentialIncrement_gaussian q).integrable_shift
      ((hF.prefix tail hb).spatial t ht).choose_spec b x
    have hs := sum_abs_shiftedMean_le (fun σ => T.score_smooth0 hF hW hb b σ ht)
      (fun y => ih ha.2.2.2 y) hi
    have hp' := (T.step (b,q)).probability hF hW hp hm ht x
    have hd := (hF.prefix ((b,q)::tail) hm).bounded t ht x
    have hh := finite_law_subtraction_bound hp'.1 hp'.2 hs (sub_nonneg.mpr ha.2.1) hd
    simp_rw [← T.score_step hF hW hb a b q _ ht x] at hh
    dsimp only [budget]
    linarith
  | @fork front T U ihT ihU =>
    have hT := T.probability hF hW hp ha.positive ht x
    have hU := U.probability hF hW hp ha.positive ht x
    have hd := (hF.prefix front ha.positive).bounded t ht x
    have hh := finite_law_score_fork hT.1 hU.1 hT.2 hU.2 (ihT ha x) (ihU ha x) ha.bounds.1 hd
    change (∑ σ : T.Assignment κ × U.Assignment κ,
      |T.response F D W B σ.1 t x*U.weight F W σ.2 t x+
       T.weight F W σ.1 t x*U.response F D W B σ.2 t x+
       a*(T.weight F W σ.1 t x*U.weight F W σ.2 t x)*prefixTest front (F t) (D t) x|) ≤ _
    dsimp only [budget]
    exact hh.trans (by linarith)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
universe uB vB wB

 theorem finite_law_addition_bound {κ : Type*} [Fintype κ]
    {W R : κ → ℝ} {c D K J : ℝ} (hW : ∀ i, 0 ≤ W i) (sW : ∑ i, W i = 1)
    (hR : ∑ i, |R i| ≤ K) (hc : 0 ≤ c) (hD : |D| ≤ J) :
    ∑ i, |R i+c*W i*D| ≤ K+c*J := by
  have hh := finite_law_subtraction_bound hW sW hR hc (show |-D| ≤ J by simpa only [abs_neg] using hD)
  simpa only [mul_neg,sub_neg_eq_add] using hh

variable {ι : Type uB} {β : Type vB} {κ : β → Type wB} [Fintype ι] [∀ b, Fintype (κ b)]

noncomputable def BoundaryTree.expect (F : ℝ → (ι → ℝ) → ℝ)
    (W : ∀ b, κ b → ℝ → (ι → ℝ) → ℝ) {front : List (GaussianStep ι)}
    (T : BoundaryTree ι β front) (P : T.Assignment κ → ℝ) (t : ℝ) (x : ι → ℝ) : ℝ :=
  ∑ σ, P σ*T.weight F W σ t x

 theorem BoundaryTree.expect_hasDerivAt {l r J : ℝ} {F D : ℝ → (ι → ℝ) → ℝ}
    {W B : ∀ b, κ b → ℝ → (ι → ℝ) → ℝ}
    (hF : ParametricRegular l r J F D)
    (hW : ∀ b σ, ∃ K, ParametricTest l r K (W b σ) (B b σ))
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front)
    (hm : ∀ st ∈ front, 0 < st.1) (P : T.Assignment κ → ℝ) {t : ℝ} (ht : t ∈ Ioo l r) (x : ι → ℝ) :
    HasDerivAt (fun s => T.expect F W P s x) (∑ σ, P σ*T.response F D W B σ t x) t := by
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ =>
    ((T.parametric hF hW hm σ).choose_spec.derivative t ht x).const_mul (P σ))

 theorem BoundaryTree.tested_response_bound {F D : ℝ → (ι → ℝ) → ℝ}
    {W B : ∀ b, κ b → ℝ → (ι → ℝ) → ℝ} {front : List (GaussianStep ι)}
    (T : BoundaryTree ι β front) {P : T.Assignment κ → ℝ} {C K : ℝ} {t : ℝ} {x : ι → ℝ}
    (hC : 0 ≤ C) (hP : ∀ σ, |P σ| ≤ C)
    (hR : ∑ σ, |T.response F D W B σ t x| ≤ K) :
    |∑ σ, P σ*T.response F D W B σ t x| ≤ C*K := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ σ, C*|T.response F D W B σ t x| := Finset.sum_le_sum fun σ _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hP σ) (abs_nonneg _)
    _ = C*∑ σ, |T.response F D W B σ t x| := (Finset.mul_sum _ _ _).symm
    _ ≤ C*K := mul_le_mul_of_nonneg_left hR hC

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S β : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

noncomputable def ReplicaTree.atomicClock (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) (m : ℝ) (σ : T.Assignment) : ℝ → (ι → ℝ) → ℝ := by
  classical
  exact linearClockTest L m (gaussianHierarchy w φ steps) (T.expect w φ (fun τ => if τ = σ then 1 else 0))

noncomputable def ReplicaTree.atomicResponse (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) (m : ℝ) (σ : T.Assignment) : ℝ → (ι → ℝ) → ℝ := by
  classical
  exact T.clockResponse w φ L m (fun τ => if τ = σ then 1 else 0)

 

 theorem BoundaryTree.actual_inserted_response_variation {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : β → ReplicaTree ι S steps)
    {m Q : ℝ} (ha : OrderedSteps m steps) (hm : 0 < m)
    (hQ : ∀ σ, ∑ i, (φ σ (L (Pi.single i 1)))^2 = Q)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front) (hO : PrefixOrdered 0 m front)
    {t : ℝ} (ht : 0 < t) (x : ι → ℝ) :
    ∑ σ, |T.response (linearClockContinuation L m (gaussianHierarchy w φ steps))
      (featureClockResponse w φ L steps m)
      (fun b => (R b).atomicClock w φ L m) (fun b => (R b).atomicResponse w φ L m) σ t x| ≤
      T.budget (fun b => 4*((R b).leaves:ℝ)*((R b).leaves+1:ℝ)*(∑ i, (D i)^2)+m*Q) := by
  classical
  let F := linearClockContinuation L m (gaussianHierarchy w φ steps)
  let J := featureClockResponse w φ L steps m
  let W := fun b => (R b).atomicClock w φ L m
  let B := fun b => (R b).atomicResponse w φ L m
  have hF : ParametricRegular 0 (t+1) (Q/2) F J := parametric_featureClock hw φ L hQ steps ha hm (t+1)
  have hW : ∀ b σ, ∃ K, ParametricTest 0 (t+1) K (W b σ) (B b σ) := by
    intro b σ
    refine ⟨_,(R b).parametric_clockTest hw φ L ha D (by norm_num : (0:ℝ) ≤ 1) hD ?_ hB (t+1)⟩
    intro τ
    split_ifs <;> norm_num
  have hp : ∀ b, ∀ s ∈ Ioo 0 (t+1), ∀ y, (∀ σ, 0 ≤ W b σ s y) ∧ ∑ σ, W b σ s y = 1 := by
    intro b s _ y
    exact (R b).atomic_clockTest_probability hw φ L ha s y
  let V : β → ℝ := fun b => 4*((R b).leaves:ℝ)*((R b).leaves+1:ℝ)*(∑ i, (D i)^2)+m*(Q/2)
  have hv : ∀ b, ∀ s ∈ Ioo 0 (t+1), ∀ y, ∑ σ, |B b σ s y+m*W b σ s y*J s y| ≤ V b := by
    intro b s hs y
    exact finite_law_addition_bound (hp b s hs y).1 (hp b s hs y).2
      ((R b).atomic_clockResponse_variation hw φ L ha D hD hB hs.1 y) hm.le (hF.bounded s hs y)
  have hs := T.score_variation hF hW hp hv hO (show t ∈ Ioo 0 (t+1) by exact ⟨ht,by linarith⟩) x
  have he : (fun b => V b+m*(Q/2)) = (fun b => 4*((R b).leaves:ℝ)*((R b).leaves+1:ℝ)*(∑ i, (D i)^2)+m*Q) := by
    funext b
    dsimp [V]
    ring
  rw [he] at hs
  simpa only [BoundaryTree.score,zero_mul,add_zero,sub_zero] using hs

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

 def interpolate (F G : (ι → ℝ) → ℝ) (t : ℝ) (x : ι → ℝ) : ℝ :=
  (1-t)*F x+t*G x

 omit [Fintype ι] in
 theorem interpolate_derivative (F G : (ι → ℝ) → ℝ) (t : ℝ) (x : ι → ℝ) :
    HasDerivAt (fun s => interpolate F G s x) (G x-F x) t := by
  apply ((((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).mul_const (F x)).add
    ((hasDerivAt_id t).mul_const (G x))).congr_deriv
  ring

 theorem parametric_interpolate {F G : (ι → ℝ) → ℝ} {C₀ C₁ : ℝ≥0} {K l r : ℝ}
    (hF : LipschitzWith C₀ F) (hG : LipschitzWith C₁ G) (hK : 0 ≤ K)
    (hb : ∀ x, |G x-F x| ≤ K) :
    ParametricRegular l r K (interpolate F G) (fun _ x => G x-F x) := by
  refine ⟨hK,?_,fun _ _ => hG.continuous.sub hF.continuous,fun _ _ x => hb x,fun t _ x => interpolate_derivative F G t x⟩
  intro t _
  exact ⟨_,((lipschitzWith_smul (1-t)).comp hF).add ((lipschitzWith_smul t).comp hG)⟩

 omit [Fintype ι] in
 theorem parametricTest_interpolate {F G : (ι → ℝ) → ℝ} {K : ℝ}
    (hF : Continuous F) (hG : Continuous G) (hK : 0 ≤ K)
    (hbF : ∀ x, |F x| ≤ K) (hbG : ∀ x, |G x| ≤ K) :
    ParametricTest (-1) 2 (5*K) (interpolate F G) (fun _ x => G x-F x) := by
  refine ⟨by positivity,fun t _ => (hF.const_mul (1-t)).add (hG.const_mul t),
    fun _ _ => hG.sub hF,?_,?_,fun t _ x => interpolate_derivative F G t x⟩
  · intro t ht x
    have ht1 : |1-t| ≤ 3 := by rw [abs_le]; constructor <;> linarith [ht.1,ht.2]
    have ht2 : |t| ≤ 2 := by rw [abs_le]; constructor <;> linarith [ht.1,ht.2]
    unfold interpolate
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul]
    have h1 := mul_le_mul ht1 (hbF x) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 3)
    have h2 := mul_le_mul ht2 (hbG x) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
    linarith
  · intro t _ x
    exact (abs_sub _ _).trans (by linarith [hbF x,hbG x])

 theorem ParametricRegular.restrict {l r l' r' K : ℝ} {F D : ℝ → (ι → ℝ) → ℝ}
    (h : ParametricRegular l r K F D) (hs : Ioo l' r' ⊆ Ioo l r) : ParametricRegular l' r' K F D :=
  ⟨h.nonneg,fun t ht => h.spatial t (hs ht),fun t ht => h.continuous t (hs ht),
    fun t ht => h.bounded t (hs ht),fun t ht => h.derivative t (hs ht)⟩

 omit [Fintype ι] in
 theorem ParametricTest.restrict {l r l' r' K : ℝ} {A B : ℝ → (ι → ℝ) → ℝ}
    (h : ParametricTest l r K A B) (hs : Ioo l' r' ⊆ Ioo l r) : ParametricTest l' r' K A B :=
  ⟨h.nonneg,fun t ht => h.continuous t (hs ht),fun t ht => h.response_continuous t (hs ht),
    fun t ht => h.bounded t (hs ht),fun t ht => h.response_bounded t (hs ht),
    fun t ht => h.derivative t (hs ht)⟩

end SKFluctuations.Hierarchy

end

end OAI
