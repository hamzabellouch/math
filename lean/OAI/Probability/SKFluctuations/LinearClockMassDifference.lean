import Mathlib
import OAI.Probability.SKFluctuations.WeightCongrAt

namespace OAI

/-! Linear Clock Mass Difference. -/

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

 theorem ReplicaTree.linearClock_mass_difference {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : ReplicaTree ι S steps) {a b : ℝ}
    (ho : OrderedSteps b steps) {P : R.Assignment → ℝ} {C : ℝ}
    (D : Fin (n+1) → ℝ) (hC : 0 ≤ C) (hD : ∀ i, 0 ≤ D i) (hP : ∀ σ, |P σ| ≤ C)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) (x : ι → ℝ) :
    |linearClockTest L a (gaussianHierarchy w φ steps) (R.expect w φ P) t x-
      linearClockTest L b (gaussianHierarchy w φ steps) (R.expect w φ P) t x| ≤
      (|a-b| *(2*(R.leaves:ℝ)+3)*C*∑ i, (D i)^2)*t := by
  have h := R.mass_difference hw φ L ho x D hC hD hP hB ha ha1 hb hb1 ht 0
  have hF := (gaussianHierarchy_regular hw φ steps ho 0).1.choose_spec.continuous
  have hA := (R.expect_smooth hw φ ho P 0).continuous
  simpa only [replicaFeatureJet_F,replicaFeatureJet_A,← linearClockTest_eq L hF hA] using h

 theorem ReplicaTree.linearPotential_mass_difference {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : ReplicaTree ι S steps) {a b : ℝ}
    (ho : OrderedSteps b steps) (D : Fin (n+1) → ℝ)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 ≤ t) (x : ι → ℝ) :
    |linearClockContinuation L a (gaussianHierarchy w φ steps) t x-
      linearClockContinuation L b (gaussianHierarchy w φ steps) t x| ≤
      (|a-b| /2*∑ i, (D i)^2)*t := by
  let J := replicaFeatureJet hw φ L R ho (fun _ => 0) x
  have hh := J.potential_mass_difference D (replicaFeatureJet_G_abs_le hw φ L R ho (fun _ => 0) x D hB) ha hb ht 0
  have hF := (gaussianHierarchy_regular hw φ steps ho 0).1.choose_spec.continuous
  simpa only [J,replicaFeatureJet_F,← linearClockContinuation_eq L hF] using hh

 theorem ReplicaTree.clockTest_atomic_any_mass {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {c : ℝ} (ha : OrderedSteps c steps) (m : ℝ)
    [DecidableEq T.Assignment] (P : T.Assignment → ℝ) (t : ℝ) (x : ι → ℝ) :
    linearClockTest L m (gaussianHierarchy w φ steps) (T.expect w φ P) t x =
      ∑ σ, P σ*linearClockTest L m (gaussianHierarchy w φ steps)
        (T.expect w φ (fun τ => if τ = σ then 1 else 0)) t x := by
  have hF := gaussianHierarchy_regular hw φ steps ha 0
  have hi := (exponentialIncrement_linearGaussian L (Real.toNNReal t)).integrable_shift hF.1.choose_spec m x
  have he : T.expect w φ P = fun y => ∑ σ, P σ*T.expect w φ (fun τ => if τ = σ then 1 else 0) y := by
    funext y
    simp_rw [T.expect_indicator]
    unfold ReplicaTree.expect
    apply Finset.sum_congr rfl
    intro σ _
    ring
  change shiftedMean _ _ _ _ _ = _
  rw [he,shiftedMean_finsetSum Finset.univ
    (fun σ _ => (T.expect_smooth hw φ ha (fun τ => if τ = σ then 1 else 0) 0).const_mul (P σ)) hi]
  simp only [shiftedMean_const_mul,linearClockTest]

 theorem ReplicaTree.atomic_mass_difference {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : ReplicaTree ι S steps) {a b : ℝ}
    (ho : OrderedSteps b steps) (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) (x : ι → ℝ) :
    ∑ σ, |R.atomicClock w φ L a σ t x-R.atomicClock w φ L b σ t x| ≤
      (|a-b| *(2*(R.leaves:ℝ)+3)*∑ i, (D i)^2)*t := by
  classical
  apply finite_law_variation_dual
  intro P hP
  have h := R.linearClock_mass_difference hw φ L ho D (by norm_num : (0:ℝ) ≤ 1) hD hP hB ha ha1 hb hb1 ht x
  rw [R.clockTest_atomic_any_mass hw φ L ho a P t x] at h
  rw [R.clockTest_atomic_any_mass hw φ L ho b P t x] at h
  simpa only [ReplicaTree.atomicClock,mul_sub,Finset.sum_sub_distrib,mul_one] using h

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem abs_sub_le_of_bounded_derivative {f g : ℝ → ℝ} {l r C : ℝ}
    (hc : ContinuousOn f (Icc l r)) (hd : ∀ t ∈ Ioo l r, HasDerivAt f (g t) t)
    (hb : ∀ t ∈ Ioo l r, |g t| ≤ C) {s t : ℝ} (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) :
    |f s-f t| ≤ C*|s-t| := by
  wlog hst : s ≤ t generalizing s t
  · simpa only [abs_sub_comm] using this ht hs (le_of_not_ge hst)
  rcases hst.eq_or_lt with hst | hst
  · simp only [hst,sub_self,abs_zero,mul_zero,le_refl]
  have hsub : Icc s t ⊆ Icc l r := fun _ h => ⟨hs.1.trans h.1,h.2.trans ht.2⟩
  have hsub' : Ioo s t ⊆ Ioo l r := fun _ h => ⟨hs.1.trans_lt h.1,h.2.trans_le ht.2⟩
  obtain ⟨u,hu,he⟩ := exists_hasDerivAt_eq_slope f g hst (hc.mono hsub) (fun u hu => hd u (hsub' hu))
  have he' := (eq_div_iff (sub_pos.mpr hst).ne').mp he
  rw [abs_sub_comm (f s),← he',abs_mul,abs_sub_comm s]
  exact mul_le_mul_of_nonneg_right (hb u (hsub' hu)) (abs_nonneg _)

 theorem HeatJet.potentialSplit_stability {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hG : ∀ i y, |J.G i y| ≤ D i) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {T s t : ℝ} (hs : s ∈ Icc (0:ℝ) T) (ht : t ∈ Icc (0:ℝ) T) (x : Fin (n+1) → ℝ) :
    |J.potentialSplit a hb T s x-J.potentialSplit a hb T t x| ≤
      (|a-b| /2*∑ i, (D i)^2)*|s-t| := by
  exact abs_sub_le_of_bounded_derivative (J.continuous_potentialSplit a hb T x).continuousOn
    (fun z hz => J.hasDerivAt_potentialSplit ha hb hz x)
    (fun z _ => J.potentialSplitResponse_abs_le D hG a hb T z x) hs ht

 

 theorem HeatJet.massSplit_stability {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    {C k a b : ℝ} (hC : 0 ≤ C) (hk : 0 ≤ k) (hD : ∀ i, 0 ≤ D i)
    (hA : ∀ y, |J.A y| ≤ C) (hG : ∀ i y, |J.G i y| ≤ D i)
    (hA₁ : ∀ i y, |J.A₁ i y| ≤ k*C*D i)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    {T s t : ℝ} (hs : s ∈ Icc (0:ℝ) T) (ht : t ∈ Icc (0:ℝ) T) (x : Fin (n+1) → ℝ) :
    |J.massSplit a hb T s x-J.massSplit a hb T t x| ≤
      (|a-b| *(k+3)*C*∑ i, (D i)^2)*|s-t| := by
  exact abs_sub_le_of_bounded_derivative (J.continuous_massSplit a hb T x).continuousOn
    (fun z hz => J.hasDerivAt_massSplit a hb hz x)
    (fun z _ => J.massSplitResponse_abs_le D hC hk hD hA hG hA₁ ha ha1 hb hb1 T z x) hs ht

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}

 theorem linearClockContinuation_affine (L : (Fin (n+1) → ℝ) →L[ℝ] E) {F : E → ℝ}
    (hF : Continuous F) (m t : ℝ) (x : E) (y : Fin (n+1) → ℝ) :
    linearClockContinuation L m F t (x+L y) =
      clockContinuation m (fun z => F (x+L z)) t y := by
  rw [linearClockContinuation_eq L hF]
  simp only [clockContinuation,shiftedContinuation,zero_add,map_add,add_assoc]

 theorem linearClockTest_affine (L : (Fin (n+1) → ℝ) →L[ℝ] E) {F A : E → ℝ}
    (hF : Continuous F) (hA : Continuous A) (m t : ℝ) (x : E) (y : Fin (n+1) → ℝ) :
    linearClockTest L m F A t (x+L y) =
      clockTest m (fun z => F (x+L z)) (fun z => A (x+L z)) t y := by
  rw [linearClockTest_eq L hF hA]
  simp only [clockTest,shiftedMean,tiltedMean,zero_add,map_add,add_assoc]

 def linearPotentialSplit (L : (Fin (n+1) → ℝ) →L[ℝ] E) (a b : ℝ) (F : E → ℝ)
    (T t : ℝ) : E → ℝ :=
  linearClockContinuation L a (linearClockContinuation L b F (T-t)) t

 def linearTestSplit (L : (Fin (n+1) → ℝ) →L[ℝ] E) (a b : ℝ) (F A : E → ℝ)
    (T t : ℝ) : E → ℝ :=
  linearClockTest L a (linearClockContinuation L b F (T-t))
    (linearClockTest L b F A (T-t)) t

 theorem linearPotentialSplit_eq (L : (Fin (n+1) → ℝ) →L[ℝ] E) {F : E → ℝ} {K : ℝ≥0}
    (hF : LipschitzWith K F) (a : ℝ) {b : ℝ} (hb : 0 < b) (T t : ℝ) (x : E) :
    linearPotentialSplit L a b F T t x =
      clockContinuation a (clockContinuation b (fun z => F (x+L z)) (T-t)) t 0 := by
  have hi := (exponentialIncrement_linearGaussian L (Real.toNNReal (T-t))).integrable_shift hF b
  have he : (fun z => linearClockContinuation L b F (T-t) (x+L z)) =
      clockContinuation b (fun z => F (x+L z)) (T-t) := by
    funext z
    exact linearClockContinuation_affine L hF.continuous b (T-t) x z
  have hfc : Continuous (linearClockContinuation L b F (T-t)) :=
    (lipschitzWith_shiftedContinuation hF hb hi).continuous
  unfold linearPotentialSplit
  rw [linearClockContinuation_eq L hfc,he]

 theorem linearTestSplit_eq (L : (Fin (n+1) → ℝ) →L[ℝ] E) {F A : E → ℝ} {K : ℝ≥0}
    (hF : LipschitzWith K F) (hA : BddSmooth 0 A) (a : ℝ) {b : ℝ} (hb : 0 < b) (T t : ℝ) (x : E) :
    linearTestSplit L a b F A T t x =
      clockTest a (clockContinuation b (fun z => F (x+L z)) (T-t))
        (clockTest b (fun z => F (x+L z)) (fun z => A (x+L z)) (T-t)) t 0 := by
  have hi := (exponentialIncrement_linearGaussian L (Real.toNNReal (T-t))).integrable_shift hF b
  obtain ⟨B,hB,hAb⟩ := hA.bound
  have hct := continuous_shiftedMean hF hA.continuous hB hAb hi
  have hfe : (fun z => linearClockContinuation L b F (T-t) (x+L z)) =
      clockContinuation b (fun z => F (x+L z)) (T-t) := by
    funext z
    exact linearClockContinuation_affine L hF.continuous b (T-t) x z
  have hae : (fun z => linearClockTest L b F A (T-t) (x+L z)) =
      clockTest b (fun z => F (x+L z)) (fun z => A (x+L z)) (T-t) := by
    funext z
    exact linearClockTest_affine L hF.continuous hA.continuous b (T-t) x z
  have hfc : Continuous (linearClockContinuation L b F (T-t)) :=
    (lipschitzWith_shiftedContinuation hF hb hi).continuous
  have hac : Continuous (linearClockTest L b F A (T-t)) := hct
  unfold linearTestSplit
  rw [linearClockTest_eq L hfc hac,hfe,hae]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

 

 theorem ReplicaTree.linearTestSplit_stability {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : ReplicaTree ι S steps) {a b : ℝ}
    (ho : OrderedSteps b steps) {P : R.Assignment → ℝ} {C : ℝ}
    (D : Fin (n+1) → ℝ) (hC : 0 ≤ C) (hD : ∀ i, 0 ≤ D i) (hP : ∀ σ, |P σ| ≤ C)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    {T s t : ℝ} (hs : s ∈ Icc (0:ℝ) T) (ht : t ∈ Icc (0:ℝ) T) (x : ι → ℝ) :
    |linearTestSplit L a b (gaussianHierarchy w φ steps) (R.expect w φ P) T s x-
      linearTestSplit L a b (gaussianHierarchy w φ steps) (R.expect w φ P) T t x| ≤
      (|a-b| *(2*(R.leaves:ℝ)+3)*C*∑ i, (D i)^2)*|s-t| := by
  let J := replicaFeatureJet hw φ L R ho P x
  have hh := J.massSplit_stability D hC (by positivity) hD
    (fun y => R.expect_abs_le hw φ ho hP (x+L y))
    (replicaFeatureJet_G_abs_le hw φ L R ho P x D hB)
    (replicaFeatureJet_A₁_abs_le hw φ L R ho x D hC hD hP hB) ha ha1 hb hb1 hs ht 0
  have hF := (gaussianHierarchy_regular hw φ steps ho 0).1.choose_spec
  have hA := R.expect_smooth hw φ ho P 0
  simpa only [J,HeatJet.massSplit,HeatJet.evolve,replicaFeatureJet_F,replicaFeatureJet_A,
    ← linearTestSplit_eq L hF hA a hb] using hh

 theorem ReplicaTree.linearPotentialSplit_stability {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : ReplicaTree ι S steps) {a b : ℝ}
    (ho : OrderedSteps b steps) (D : Fin (n+1) → ℝ)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    (ha : 0 < a) (hb : 0 < b) {T s t : ℝ}
    (hs : s ∈ Icc (0:ℝ) T) (ht : t ∈ Icc (0:ℝ) T) (x : ι → ℝ) :
    |linearPotentialSplit L a b (gaussianHierarchy w φ steps) T s x-
      linearPotentialSplit L a b (gaussianHierarchy w φ steps) T t x| ≤
      (|a-b| /2*∑ i, (D i)^2)*|s-t| := by
  let J := replicaFeatureJet hw φ L R ho (fun _ => 0) x
  have hh := J.potentialSplit_stability D
    (replicaFeatureJet_G_abs_le hw φ L R ho (fun _ => 0) x D hB) ha hb hs ht 0
  have hF := (gaussianHierarchy_regular hw φ steps ho 0).1.choose_spec
  simpa only [J,HeatJet.potentialSplit,HeatJet.evolve,replicaFeatureJet_F,
    ← linearPotentialSplit_eq L hF a hb] using hh

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

 theorem ReplicaTree.linearTestSplit_smooth0 {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : ReplicaTree ι S steps) {a b : ℝ}
    (ho : OrderedSteps b steps) (hb : 0 < b) (P : R.Assignment → ℝ) (T t : ℝ) :
    BddSmooth 0 (linearTestSplit L a b (gaussianHierarchy w φ steps) (R.expect w φ P) T t) := by
  have hF := gaussianHierarchy_regular hw φ steps ho 0
  have hib := (exponentialIncrement_linearGaussian L (Real.toNNReal (T-t))).integrable_shift hF.1.choose_spec b
  have hFi := hF.shiftedContinuation hb hib
  have hAi := (R.expect_smooth hw φ ho P 0).shiftedMean hF hib
  exact hAi.shiftedMean hFi ((exponentialIncrement_linearGaussian L (Real.toNNReal t)).integrable_shift hFi.1.choose_spec a)

 theorem ReplicaTree.linearTestSplit_atomic {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : ReplicaTree ι S steps) {a b : ℝ}
    (ho : OrderedSteps b steps) (hb : 0 < b) [DecidableEq R.Assignment]
    (P : R.Assignment → ℝ) (T t : ℝ) (x : ι → ℝ) :
    linearTestSplit L a b (gaussianHierarchy w φ steps) (R.expect w φ P) T t x =
      ∑ σ, P σ*linearTestSplit L a b (gaussianHierarchy w φ steps)
        (R.expect w φ (fun τ => if τ = σ then 1 else 0)) T t x := by
  have hF := gaussianHierarchy_regular hw φ steps ho 0
  have hib := (exponentialIncrement_linearGaussian L (Real.toNNReal (T-t))).integrable_shift hF.1.choose_spec b
  have hFi := hF.shiftedContinuation hb hib
  have hia := (exponentialIncrement_linearGaussian L (Real.toNNReal t)).integrable_shift hFi.1.choose_spec a x
  have he : linearClockTest L b (gaussianHierarchy w φ steps) (R.expect w φ P) (T-t) =
      fun y => ∑ σ, P σ*linearClockTest L b (gaussianHierarchy w φ steps)
        (R.expect w φ (fun τ => if τ = σ then 1 else 0)) (T-t) y := by
    funext y
    exact R.clockTest_atomic hw φ L ho P (T-t) y
  unfold linearTestSplit
  rw [he]
  unfold linearClockTest linearClockContinuation
  rw [shiftedMean_finsetSum Finset.univ
    (fun σ _ => (((R.expect_smooth hw φ ho (fun τ => if τ = σ then 1 else 0) 0).shiftedMean hF hib).const_mul (P σ))) hia]
  simp only [shiftedMean_const_mul]

 theorem ReplicaTree.atomic_split_probability {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : ReplicaTree ι S steps) {a b : ℝ}
    (ho : OrderedSteps b steps) (hb : 0 < b) [DecidableEq R.Assignment] (T t : ℝ) (x : ι → ℝ) :
    (∀ σ, 0 ≤ linearTestSplit L a b (gaussianHierarchy w φ steps)
      (R.expect w φ (fun τ => if τ = σ then 1 else 0)) T t x) ∧
    (∑ σ, linearTestSplit L a b (gaussianHierarchy w φ steps)
      (R.expect w φ (fun τ => if τ = σ then 1 else 0)) T t x) = 1 := by
  have hF := gaussianHierarchy_regular hw φ steps ho 0
  have hib := (exponentialIncrement_linearGaussian L (Real.toNNReal (T-t))).integrable_shift hF.1.choose_spec b
  have hFi := hF.shiftedContinuation hb hib
  have hia := (exponentialIncrement_linearGaussian L (Real.toNNReal t)).integrable_shift hFi.1.choose_spec a x
  constructor
  · intro σ
    exact shiftedMean_nonneg (fun y => (R.atomic_clockTest_probability hw φ L ho (T-t) y).1 σ) hia
  · have hh := R.linearTestSplit_atomic hw φ L ho hb (a := a) (fun _ => 1) T t x
    simp only [one_mul] at hh
    rw [← hh]
    have he : R.expect w φ (fun _ => 1) = fun _ => 1 := funext fun y => R.expect_const hw φ ho 1 y
    have hinner : linearClockTest L b (gaussianHierarchy w φ steps) (R.expect w φ (fun _ => 1)) (T-t) = fun _ => 1 := by
      funext y
      unfold linearClockTest
      rw [he,shiftedMean_const 1 (hib y)]
    unfold linearTestSplit
    rw [hinner]
    exact shiftedMean_const 1 hia

 theorem ReplicaTree.atomic_split_stability {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : ReplicaTree ι S steps) [DecidableEq R.Assignment] {a b : ℝ}
    (ho : OrderedSteps b steps) (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    {T s t : ℝ} (hs : s ∈ Icc (0:ℝ) T) (ht : t ∈ Icc (0:ℝ) T) (x : ι → ℝ) :
    ∑ σ, |linearTestSplit L a b (gaussianHierarchy w φ steps)
      (R.expect w φ (fun τ => if τ = σ then 1 else 0)) T s x-
      linearTestSplit L a b (gaussianHierarchy w φ steps)
      (R.expect w φ (fun τ => if τ = σ then 1 else 0)) T t x| ≤
      (|a-b| *(2*(R.leaves:ℝ)+3)*∑ i, (D i)^2)*|s-t| := by
  classical
  apply finite_law_variation_dual
  intro P hP
  have hh := R.linearTestSplit_stability hw φ L ho D (by norm_num : (0:ℝ) ≤ 1) hD hP hB ha ha1 hb hb1 hs ht x
  rw [R.linearTestSplit_atomic hw φ L ho hb P T s x,
    R.linearTestSplit_atomic hw φ L ho hb P T t x] at hh
  simpa only [mul_sub,Finset.sum_sub_distrib,mul_one] using hh

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S β : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

 

theorem BoundaryTree.actual_mass_change {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : β → ReplicaTree ι S steps) {a b c : ℝ}
    (hoa : OrderedSteps a steps) (hob : OrderedSteps b steps)
    (ha : 0 < a) (hb : 0 < b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front) (hO : PrefixOrdered 0 c front)
    {t : ℝ} (ht : 0 ≤ t) (x : ι → ℝ) :
    ∑ σ, |T.weight (fun _ => linearClockContinuation L a (gaussianHierarchy w φ steps) t)
      (fun d τ _ => (R d).atomicClock w φ L a τ t) σ 0 x-
      T.weight (fun _ => linearClockContinuation L b (gaussianHierarchy w φ steps) t)
      (fun d τ _ => (R d).atomicClock w φ L b τ t) σ 0 x| ≤
      T.budget (fun d => (|a-b| *(2*((R d).leaves:ℝ)+3)*∑ i, (D i)^2)*t+
        2*c*((|a-b| /2*∑ i, (D i)^2)*t)) := by
  classical
  have hF := (gaussianHierarchy_regular hw φ steps hob 0).1.choose_spec
  have hi (m : ℝ) := (exponentialIncrement_linearGaussian L (Real.toNNReal t)).integrable_shift hF m
  have hc (m : ℝ) (d : β) (σ : (R d).Assignment) : Continuous ((R d).atomicClock w φ L m σ t) := by
    apply continuous_shiftedMean hF ((R d).expect_smooth hw φ hob _ 0).continuous (by norm_num : (0:ℝ) ≤ 1) _ (hi m)
    intro y
    apply (R d).expect_abs_le hw φ hob
    intro τ
    split_ifs <;> norm_num
  exact T.finite_stability
    (lipschitzWith_shiftedContinuation hF hb (hi b))
    (lipschitzWith_shiftedContinuation hF ha (hi a)) (by positivity)
    (fun y => (ReplicaTree.single steps).linearPotential_mass_difference hw φ L hob D hB ha hb ht y)
    (hc b) (hc a)
    (fun d y => (R d).atomic_clockTest_probability hw φ L hob t y)
    (fun d y => (R d).atomic_clockTest_probability hw φ L hoa t y)
    (fun d => (|a-b| *(2*((R d).leaves:ℝ)+3)*∑ i, (D i)^2)*t)
    (fun d y => (R d).atomic_mass_difference hw φ L hob D hD hB ha.le ha1 hb hb1 ht y) hO x

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S β : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

 

 theorem BoundaryTree.actual_boundary_move {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : β → ReplicaTree ι S steps) [∀ d, DecidableEq (R d).Assignment] {a b c : ℝ}
    (ho : OrderedSteps b steps) (ha : 0 < a) (hb : 0 < b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    {front : List (GaussianStep ι)} (U : BoundaryTree ι β front) (hO : PrefixOrdered 0 c front)
    {T s t : ℝ} (hs : s ∈ Icc (0:ℝ) T) (ht : t ∈ Icc (0:ℝ) T) (x : ι → ℝ) :
    ∑ σ, |U.weight (fun _ => linearPotentialSplit L a b (gaussianHierarchy w φ steps) T s)
      (fun d τ _ => linearTestSplit L a b (gaussianHierarchy w φ steps)
        ((R d).expect w φ (fun v => if v = τ then 1 else 0)) T s) σ 0 x-
      U.weight (fun _ => linearPotentialSplit L a b (gaussianHierarchy w φ steps) T t)
      (fun d τ _ => linearTestSplit L a b (gaussianHierarchy w φ steps)
        ((R d).expect w φ (fun v => if v = τ then 1 else 0)) T t) σ 0 x| ≤
      U.budget (fun d => (|a-b| *(2*((R d).leaves:ℝ)+3)*∑ i, (D i)^2)*|s-t|+
        2*c*((|a-b| /2*∑ i, (D i)^2)*|s-t|)) := by
  have hF := (gaussianHierarchy_regular hw φ steps ho 0).1.choose_spec
  have hi (v : ℝ) := (exponentialIncrement_linearGaussian L (Real.toNNReal (T-v))).integrable_shift hF b
  have hFi (v : ℝ) := lipschitzWith_shiftedContinuation hF hb (hi v)
  have hlo (v : ℝ) : LipschitzWith _ (linearPotentialSplit L a b (gaussianHierarchy w φ steps) T v) :=
    lipschitzWith_shiftedContinuation (hFi v) ha
      ((exponentialIncrement_linearGaussian L (Real.toNNReal v)).integrable_shift (hFi v) a)
  exact U.finite_stability (hlo t) (hlo s) (by positivity)
    (fun y => (ReplicaTree.single steps).linearPotentialSplit_stability hw φ L ho D hB ha hb hs ht y)
    (fun d τ => ((R d).linearTestSplit_smooth0 hw φ L ho hb (fun v => if v = τ then 1 else 0) T t).continuous)
    (fun d τ => ((R d).linearTestSplit_smooth0 hw φ L ho hb (fun v => if v = τ then 1 else 0) T s).continuous)
    (fun d y => (R d).atomic_split_probability hw φ L ho hb T t y)
    (fun d y => (R d).atomic_split_probability hw φ L ho hb T s y)
    (fun d => (|a-b| *(2*((R d).leaves:ℝ)+3)*∑ i, (D i)^2)*|s-t|)
    (fun d y => (R d).atomic_split_stability hw φ L ho D hD hB ha.le ha1 hb hb1 hs ht y) hO x

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

 
theorem shiftedContinuation_productGaussian_add {F : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) {m : ℝ} (hm : m ≠ 0)
    (q r : ι → ℝ≥0) (x : ι → ℝ) :
    shiftedContinuation (Measure.pi fun i => gaussianReal 0 (q i)) m
      (shiftedContinuation (Measure.pi fun i => gaussianReal 0 (r i)) m F) x =
      shiftedContinuation (Measure.pi fun i => gaussianReal 0 (q i+r i)) m F x := by
  have hi := (exponentialIncrement_gaussian (fun i => q i+r i)).integrable_shift hF m x
  rw [← productGaussian_conv q r] at hi
  have he := integral_conv hi
  rw [productGaussian_conv] at he
  simp only [shiftedContinuation]
  congr 1
  congr 1
  rw [he]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    simpa only [add_assoc,shiftedContinuation] using exp_mul_shiftedContinuation hm (x+y)
      ((exponentialIncrement_gaussian r).integrable_shift hF m (x+y))

 theorem shiftedContinuation_productGaussian_comm {F : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) {m : ℝ} (hm : m ≠ 0)
    (q r : ι → ℝ≥0) (x : ι → ℝ) :
    shiftedContinuation (Measure.pi fun i => gaussianReal 0 (q i)) m
      (shiftedContinuation (Measure.pi fun i => gaussianReal 0 (r i)) m F) x =
    shiftedContinuation (Measure.pi fun i => gaussianReal 0 (r i)) m
      (shiftedContinuation (Measure.pi fun i => gaussianReal 0 (q i)) m F) x := by
  rw [shiftedContinuation_productGaussian_add hF hm,shiftedContinuation_productGaussian_add hF hm]
  simp only [add_comm]

 
theorem shiftedMean_productGaussian_add {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) {m : ℝ} (hm : m ≠ 0)
    (q r : ι → ℝ≥0) (x : ι → ℝ) :
    shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m
      (shiftedContinuation (Measure.pi fun i => gaussianReal 0 (r i)) m F)
      (shiftedMean (Measure.pi fun i => gaussianReal 0 (r i)) m F A) x =
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q i+r i)) m F A x := by
  have hi := (exponentialIncrement_gaussian (fun i => q i+r i)).integrable_shift hF m x
  have hiA := hA.integrable_shifted_weighted hi
  rw [← productGaussian_conv q r] at hi hiA
  have hd := integral_conv hi
  have hn := integral_conv hiA
  rw [productGaussian_conv] at hd hn
  unfold shiftedMean tiltedMean
  congr 1
  · rw [hn]
    apply integral_congr_ae
    refine Eventually.of_forall fun y => ?_
    dsimp only
    have hi' := (exponentialIncrement_gaussian r).integrable_shift hF m (x+y)
    rw [exp_mul_shiftedContinuation hm _ hi',div_mul_cancel₀ _ (partition_pos m hi').ne']
    simp only [add_assoc]
  · rw [hd]
    apply integral_congr_ae
    refine Eventually.of_forall fun y => ?_
    dsimp only
    rw [exp_mul_shiftedContinuation hm _ ((exponentialIncrement_gaussian r).integrable_shift hF m (x+y))]
    simp only [add_assoc]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

 
noncomputable def diagonalDriver (q : ι → ℝ≥0) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i => Real.sqrt (q i) • ContinuousLinearMap.proj i

omit [Fintype ι] in
 theorem diagonalDriver_apply (q : ι → ℝ≥0) (z : ι → ℝ) (i : ι) :
    diagonalDriver q z i = Real.sqrt (q i)*z i := rfl

 theorem linearGaussian_diagonal (q : ι → ℝ≥0) :
    linearGaussian (diagonalDriver q) 1 = Measure.pi (fun i => gaussianReal 0 (q i)) := by
  unfold linearGaussian
  change (Measure.pi fun _ : ι => gaussianReal 0 1).map
    (fun z i => Real.sqrt (q i)*z i) = _
  rw [Measure.pi_map_pi (f := fun i z => Real.sqrt (q i)*z) (fun i => (measurable_const.mul measurable_id).aemeasurable)]
  congr 1
  funext i
  rw [gaussianReal_map_const_mul]
  congr 1
  · ring
  · apply NNReal.coe_injective
    simp only [NNReal.coe_mk,mul_one,Real.sq_sqrt (q i).coe_nonneg]

omit [Fintype ι] in
 theorem diagonalDriver_single [DecidableEq ι] (q : ι → ℝ≥0) (i : ι) :
    diagonalDriver q (Pi.single i 1) = Real.sqrt (q i) • Pi.single i 1 := by
  ext j
  by_cases h : j = i
  · subst j
    simp only [diagonalDriver_apply,Pi.single_eq_same,Pi.smul_apply,smul_eq_mul]
  · simp only [diagonalDriver_apply,Pi.single_eq_of_ne h,Pi.smul_apply,smul_eq_mul,mul_zero]

variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 
theorem gaussianHierarchy_diagonal_mass_difference {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep (Fin (n+1)))}
    {a b : ℝ} (ho : OrderedSteps b steps) (D : Fin (n+1) → ℝ)
    (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i) (ha : 0 < a) (hb : 0 < b)
    (q : Fin (n+1) → ℝ≥0) (x : Fin (n+1) → ℝ) :
    |shiftedContinuation (Measure.pi fun i => gaussianReal 0 (q i)) a (gaussianHierarchy w φ steps) x-
      shiftedContinuation (Measure.pi fun i => gaussianReal 0 (q i)) b (gaussianHierarchy w φ steps) x| ≤
       |a-b|/2*∑ i, (q i:ℝ)*(D i)^2 := by
  have hd (i : Fin (n+1)) (σ : S) :
      |φ σ (diagonalDriver q (Pi.single i 1))| ≤ Real.sqrt (q i)*D i := by
    rw [diagonalDriver_single,map_smul,smul_eq_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hB i σ) (Real.sqrt_nonneg _)
  have hh := (ReplicaTree.single steps).linearPotential_mass_difference hw φ (diagonalDriver q)
    ho (fun i => Real.sqrt (q i)*D i) hd ha hb (by norm_num : (0:ℝ) ≤ 1) x
  simpa only [linearClockContinuation,Real.toNNReal_one,linearGaussian_diagonal,mul_one,
    mul_pow,Real.sq_sqrt (q _).coe_nonneg] using hh

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] {ν : Measure E}

 theorem shiftedContinuation_mono [IsProbabilityMeasure ν] {F G : E → ℝ} {m : ℝ}
    (hm : 0 < m) (hF : ∀ x, Integrable (fun z => Real.exp (m*F (x+z))) ν)
    (hG : ∀ x, Integrable (fun z => Real.exp (m*G (x+z))) ν)
    (hFG : ∀ x, F x ≤ G x) (x : E) :
    shiftedContinuation ν m F x ≤ shiftedContinuation ν m G x := by
  apply div_le_div_of_nonneg_right _ hm.le
  apply Real.log_le_log (partition_pos m (hF x))
  exact integral_mono (hF x) (hG x) (fun z => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hFG (x+z)) hm.le))

 theorem shiftedContinuation_add_const [IsProbabilityMeasure ν] {F : E → ℝ} {m : ℝ}
    (hm : m ≠ 0) (hF : ∀ x, Integrable (fun z => Real.exp (m*F (x+z))) ν)
    (c : ℝ) (x : E) :
    shiftedContinuation ν m (fun y => F y+c) x = shiftedContinuation ν m F x+c := by
  unfold shiftedContinuation
  simp_rw [mul_add,Real.exp_add]
  rw [integral_mul_const,Real.log_mul (partition_pos m (hF x)).ne' (Real.exp_ne_zero _),Real.log_exp]
  rw [add_div,mul_div_cancel_left₀ _ hm]

 theorem shiftedContinuation_abs_sub_le [IsProbabilityMeasure ν] {F G : E → ℝ} {m K : ℝ}
    (hm : 0 < m) (hF : ∀ x, Integrable (fun z => Real.exp (m*F (x+z))) ν)
    (hG : ∀ x, Integrable (fun z => Real.exp (m*G (x+z))) ν)
    (hFG : ∀ x, |F x-G x| ≤ K) (x : E) :
    |shiftedContinuation ν m F x-shiftedContinuation ν m G x| ≤ K := by
  have hFc : ∀ x, Integrable (fun z => Real.exp (m*(F (x+z)+K))) ν := by
    intro x
    simpa only [mul_add,Real.exp_add] using (hF x).mul_const (Real.exp (m*K))
  have hGc : ∀ x, Integrable (fun z => Real.exp (m*(G (x+z)+K))) ν := by
    intro x
    simpa only [mul_add,Real.exp_add] using (hG x).mul_const (Real.exp (m*K))
  have h1 := shiftedContinuation_mono (F := F) (G := fun y => G y+K) hm hF hGc (fun y => by linarith [(abs_le.mp (hFG y)).2]) x
  have h2 := shiftedContinuation_mono (F := G) (G := fun y => F y+K) hm hG hFc (fun y => by linarith [(abs_le.mp (hFG y)).1]) x
  rw [shiftedContinuation_add_const hm.ne' hG] at h1
  rw [shiftedContinuation_add_const hm.ne' hF] at h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

 theorem clockContinuation_abs_sub_le {ι : Type*} [Fintype ι]
    {F G : (ι → ℝ) → ℝ} {C₀ C₁ : ℝ≥0} {m K : ℝ}
    (hF : LipschitzWith C₀ F) (hG : LipschitzWith C₁ G) (hm : 0 < m)
    (hFG : ∀ x, |F x-G x| ≤ K) (t : ℝ) (x : ι → ℝ) :
    |clockContinuation m F t x-clockContinuation m G t x| ≤ K :=
  shiftedContinuation_abs_sub_le hm
    ((exponentialIncrement_gaussian (fun _ => Real.toNNReal t)).integrable_shift hF m)
    ((exponentialIncrement_gaussian (fun _ => Real.toNNReal t)).integrable_shift hG m) hFG x

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 

theorem gaussianHierarchy_covariance_transfer {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep (Fin (n+1)))}
    {a b : ℝ} (ho : OrderedSteps b steps) (D : Fin (n+1) → ℝ)
    (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i) (ha : 0 < a) (hb : 0 < b)
    (u v z : Fin (n+1) → ℝ≥0) (x : Fin (n+1) → ℝ) :
    |gaussianHierarchy w φ ((a,fun i => u i+v i)::(b,z)::steps) x-
      gaussianHierarchy w φ ((a,u)::(b,fun i => v i+z i)::steps) x| ≤
       |a-b|/2*∑ i, (v i:ℝ)*(D i)^2 := by
  let F := gaussianHierarchy w φ steps
  let G := gaussianHierarchy w φ ((b,z)::steps)
  have hF := (gaussianHierarchy_regular hw φ steps ho 0).1.choose_spec
  have hg : OrderedSteps b ((b,z)::steps) := ⟨hb.le,le_rfl,hb,ho⟩
  have hG := (gaussianHierarchy_regular hw φ ((b,z)::steps) hg 0).1.choose_spec
  have he (y : Fin (n+1) → ℝ) :
      shiftedContinuation (Measure.pi fun i => gaussianReal 0 (v i+z i)) b F y =
      shiftedContinuation (Measure.pi fun i => gaussianReal 0 (v i)) b G y :=
    (shiftedContinuation_productGaussian_add hF hb.ne' v z y).symm
  have hiA := (exponentialIncrement_gaussian v).integrable_shift hG a
  have hiB := (exponentialIncrement_gaussian v).integrable_shift hG b
  have hA := lipschitzWith_shiftedContinuation hG ha hiA
  have hB' := lipschitzWith_shiftedContinuation hG hb hiB
  change |shiftedContinuation (Measure.pi fun i => gaussianReal 0 (u i+v i)) a G x-
    shiftedContinuation (Measure.pi fun i => gaussianReal 0 (u i)) a
      (shiftedContinuation (Measure.pi fun i => gaussianReal 0 (v i+z i)) b F) x| ≤ _
  rw [← shiftedContinuation_productGaussian_add hG ha.ne' u v x]
  rw [funext he]
  apply shiftedContinuation_abs_sub_le ha
    ((exponentialIncrement_gaussian u).integrable_shift hA a)
    ((exponentialIncrement_gaussian u).integrable_shift hB' a)
  intro y
  exact gaussianHierarchy_diagonal_mass_difference hw φ hg D hB ha hb v y

end SKFluctuations.Hierarchy

end

end OAI
