import Mathlib
import OAI.Probability.SKFluctuations.CavityActualEndpoint
import OAI.Probability.SKFluctuations.ActualPairCut
import OAI.Probability.SKFluctuations.WeightedClockPDE

namespace OAI

/-! Variance Jet. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

theorem varianceTest_bddSmooth {k : ℕ} {F A : (ι → ℝ) → ℝ}
    (hF : PotentialRegularity k F) (hA : BddSmooth k A) (m : ℝ) (q : ι → ℝ) :
    BddSmooth k (varianceTest m F A q) := by
  obtain ⟨C,hC⟩ := hF.1
  exact hA.shiftedMean hF (fun x =>
    (exponentialIncrement_gaussian (fun i => Real.toNNReal (q i))).integrable_shift hC m x)

def varianceGradient (m : ℝ) (F G A A₁ : (ι → ℝ) → ℝ) (q : ι → ℝ) (x : ι → ℝ) : ℝ :=
  varianceTest m F A₁ q x + m*(varianceTest m F (fun y => A y*G y) q x-
    varianceTest m F A q x*varianceTest m F G q x)

 theorem hasDerivAt_varianceTest_source {F G A A₁ : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : BddSmooth 0 G) (hA : BddSmooth 0 A)
    (hA₁ : BddSmooth 0 A₁) {v : ι → ℝ}
    (hdF : ∀ x q, HasDerivAt (fun s : ℝ => F (x+s • v)) (G (x+q • v)) q)
    (hdA : ∀ x q, HasDerivAt (fun s : ℝ => A (x+s • v)) (A₁ (x+q • v)) q)
    (m : ℝ) (q : ι → ℝ) (x : ι → ℝ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => varianceTest m F A q (x+r • v))
      (varianceGradient m F G A A₁ q (x+s • v)) s := by
  obtain ⟨K,hK,hbK⟩ := hG.bound
  obtain ⟨B,hB,hbB⟩ := hA.bound
  obtain ⟨B₁,hB₁,hbB₁⟩ := hA₁.bound
  exact hasDerivAt_shiftedMean hK (add_nonneg hB hB₁) hF.continuous hG.continuous
    hA.continuous hA₁.continuous hdF hdA hbK (fun y => (hbB y).trans (by linarith))
    (fun y => (hbB₁ y).trans (by linarith))
    (fun y => (exponentialIncrement_gaussian (fun i : ι => Real.toNNReal (q i))).integrable_shift hF m y) x s

 theorem varianceGradient_bddSmooth {k : ℕ} {F G A A₁ : (ι → ℝ) → ℝ}
    (hF : PotentialRegularity k F) (hG : BddSmooth k G) (hA : BddSmooth k A)
    (hA₁ : BddSmooth k A₁) (m : ℝ) (q : ι → ℝ) : BddSmooth k (varianceGradient m F G A A₁ q) := by
  obtain ⟨C,hC⟩ := hF.1
  have hi (y) := (exponentialIncrement_gaussian (fun i : ι => Real.toNNReal (q i))).integrable_shift hC m y
  exact (hA₁.shiftedMean hF hi).add (((hA.mul hG).shiftedMean hF hi).sub
    ((hA.shiftedMean hF hi).mul (hG.shiftedMean hF hi)) |>.const_mul m)

def varianceSecond (m : ℝ) (F G H A A₁ A₂ : (ι → ℝ) → ℝ) (q : ι → ℝ) (x : ι → ℝ) : ℝ :=
  varianceGradient m F G A₁ A₂ q x + m*(
    varianceGradient m F G (fun y => A y*G y) (fun y => A₁ y*G y+A y*H y) q x-
    (varianceGradient m F G A A₁ q x*varianceTest m F G q x+
      varianceTest m F A q x*varianceGradient m F G G H q x))

 theorem hasDerivAt_varianceGradient_source {F G H A A₁ A₂ : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : BddSmooth 0 G) (hH : BddSmooth 0 H)
    (hA : BddSmooth 0 A) (hA₁ : BddSmooth 0 A₁) (hA₂ : BddSmooth 0 A₂) {v : ι → ℝ}
    (hdF : ∀ x q, HasDerivAt (fun s : ℝ => F (x+s • v)) (G (x+q • v)) q)
    (hdG : ∀ x q, HasDerivAt (fun s : ℝ => G (x+s • v)) (H (x+q • v)) q)
    (hdA : ∀ x q, HasDerivAt (fun s : ℝ => A (x+s • v)) (A₁ (x+q • v)) q)
    (hdA₁ : ∀ x q, HasDerivAt (fun s : ℝ => A₁ (x+s • v)) (A₂ (x+q • v)) q)
    (m : ℝ) (q : ι → ℝ) (x : ι → ℝ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => varianceGradient m F G A A₁ q (x+r • v))
      (varianceSecond m F G H A A₁ A₂ q (x+s • v)) s := by
  have h1 := hasDerivAt_varianceTest_source hF hG hA₁ hA₂ hdF hdA₁ m q x s
  have h2 := hasDerivAt_varianceTest_source hF hG (hA.mul hG)
    ((hA₁.mul hG).add (hA.mul hH)) hdF (fun y r => (hdA y r).mul (hdG y r)) m q x s
  have h3 := hasDerivAt_varianceTest_source hF hG hA hA₁ hdF hdA m q x s
  have h4 := hasDerivAt_varianceTest_source hF hG hG hH hdF hdG m q x s
  exact h1.add ((h2.sub (h3.mul h4)).const_mul m)

 theorem varianceSecond_bddSmooth {k : ℕ} {F G H A A₁ A₂ : (ι → ℝ) → ℝ}
    (hF : PotentialRegularity k F) (hG : BddSmooth k G) (hH : BddSmooth k H)
    (hA : BddSmooth k A) (hA₁ : BddSmooth k A₁) (hA₂ : BddSmooth k A₂) (m : ℝ) (q : ι → ℝ) :
    BddSmooth k (varianceSecond m F G H A A₁ A₂ q) := by
  obtain ⟨C,hC⟩ := hF.1
  have hi (y) := (exponentialIncrement_gaussian (fun i : ι => Real.toNNReal (q i))).integrable_shift hC m y
  exact (varianceGradient_bddSmooth hF hG hA₁ hA₂ m q).add
    (((varianceGradient_bddSmooth hF hG (hA.mul hG) ((hA₁.mul hG).add (hA.mul hH)) m q).sub
      (((varianceGradient_bddSmooth hF hG hA hA₁ m q).mul (hG.shiftedMean hF hi)).add
        ((hA.shiftedMean hF hi).mul (varianceGradient_bddSmooth hF hG hG hH m q)))).const_mul m)

 theorem hasDerivAt_varianceContinuation_source {F G : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : BddSmooth 0 G) {v : ι → ℝ}
    (hdF : ∀ x q, HasDerivAt (fun s : ℝ => F (x+s • v)) (G (x+q • v)) q)
    {m : ℝ} (hm : m ≠ 0) (q : ι → ℝ) (x : ι → ℝ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => varianceContinuation m F q (x+r • v))
      (varianceTest m F G q (x+s • v)) s := by
  obtain ⟨B,hB,hb⟩ := hG.bound
  exact hasDerivAt_continuation
    (F := fun r z => F (x+r • v+z)) (F₁ := fun r z => G (x+r • v+z)) hB hm
    (fun _ => (hF.continuous.comp (continuous_const.add continuous_id)).measurable)
    (fun _ => (hG.continuous.comp (continuous_const.add continuous_id)).measurable)
    (fun r z => by simpa only [add_assoc,add_comm z] using hdF (x+z) r)
    (fun _ _ => hb _) s ((exponentialIncrement_gaussian (fun i : ι => Real.toNNReal (q i))).integrable_shift hF m _)

 theorem varianceTest_const_mul {F A : (ι → ℝ) → ℝ} (c m : ℝ) (q : ι → ℝ) (x : ι → ℝ) :
    varianceTest m F (fun y => c*A y) q x = c*varianceTest m F A q x := shiftedMean_const_mul c x

 theorem varianceTest_sum {κ : Type*} [Fintype κ] {F : (ι → ℝ) → ℝ} {A : κ → (ι → ℝ) → ℝ}
    {C : ℝ≥0} (hF : LipschitzWith C F) (hA : ∀ i, BddSmooth 0 (A i)) (m : ℝ) (q : ι → ℝ) (x : ι → ℝ) :
    varianceTest m F (fun y => ∑ i, A i y) q x = ∑ i, varianceTest m F (A i) q x :=
  shiftedMean_sum hA ((exponentialIncrement_gaussian (fun i : ι => Real.toNNReal (q i))).integrable_shift hF m x)

variable {κ : Type*} [Fintype κ]

 theorem varianceGradient_sum {F A : (ι → ℝ) → ℝ} {G A₁ : κ → (ι → ℝ) → ℝ}
    {C : ℝ≥0} (hF : LipschitzWith C F) (hA : BddSmooth 0 A)
    (hG : ∀ i, BddSmooth 0 (G i)) (hA₁ : ∀ i, BddSmooth 0 (A₁ i))
    (v : κ → ℝ) (m : ℝ) (q : ι → ℝ) (x : ι → ℝ) :
    varianceGradient m F (fun y => ∑ i, v i*G i y) A (fun y => ∑ i, v i*A₁ i y) q x =
      ∑ i, v i*varianceGradient m F (G i) A (A₁ i) q x := by
  have he : (fun y => A y*(∑ i, v i*G i y)) = fun y => ∑ i, v i*(A y*G i y) := by
    funext y
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [varianceGradient,he,varianceTest_sum hF (fun i => (hA₁ i).const_mul (v i)),
    varianceTest_sum hF (fun i => (hA.mul (hG i)).const_mul (v i)),
    varianceTest_sum hF (fun i => (hG i).const_mul (v i)),varianceTest_const_mul]
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

 theorem hasDerivAt_varianceTest_source_vector {n : ℕ}
    {F A : (Fin (n+1) → ℝ) → ℝ} {G A₁ : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ}
    {C : ℝ≥0} (hF : LipschitzWith C F) (hA : BddSmooth 0 A)
    (hG : ∀ i, BddSmooth 0 (G i)) (hA₁ : ∀ i, BddSmooth 0 (A₁ i))
    (hdF : ∀ x v q, HasDerivAt (fun s : ℝ => F (x+s • v))
      (∑ i, v i*G i (x+q • v)) q)
    (hdA : ∀ x v q, HasDerivAt (fun s : ℝ => A (x+s • v))
      (∑ i, v i*A₁ i (x+q • v)) q)
    (m : ℝ) (q : Fin (n+1) → ℝ) (x v : Fin (n+1) → ℝ) (s : ℝ) :
    HasDerivAt (fun r => varianceTest m F A q (x+r • v))
      (∑ i, v i*varianceGradient m F (G i) A (A₁ i) q (x+s • v)) s := by
  have hsumG : BddSmooth 0 (fun y => ∑ i, v i*G i y) :=
    BddSmooth.sum Finset.univ (fun i _ => (hG i).const_mul (v i))
  have hsumA : BddSmooth 0 (fun y => ∑ i, v i*A₁ i y) :=
    BddSmooth.sum Finset.univ (fun i _ => (hA₁ i).const_mul (v i))
  have h := hasDerivAt_varianceTest_source hF hsumG hA hsumA
    (fun y r => hdF y v r) (fun y r => hdA y v r) m q x s
  rw [varianceGradient_sum hF hA hG hA₁] at h
  exact h

 theorem hasDerivAt_varianceContinuation_source_vector {n : ℕ} (J : HeatJet n) {m : ℝ} (hm : m ≠ 0)
    (q : Fin (n+1) → ℝ) (x v : Fin (n+1) → ℝ) (s : ℝ) :
    HasDerivAt (fun r => varianceContinuation m J.F q (x+r • v))
      (∑ i, v i*varianceTest m J.F (J.G i) q (x+s • v)) s := by
  have hb : ∀ i, BddSmooth 0 (fun y => v i*J.G i y) := fun i => (J.smoothG i).const_mul (v i)
  have h := hasDerivAt_varianceContinuation_source J.lipschitz
    (BddSmooth.sum Finset.univ fun i _ => hb i) (fun y r => J.derivF y v r) hm q x s
  rw [varianceTest_sum J.lipschitz hb] at h
  simpa only [varianceTest_const_mul] using h

def HeatJet.varianceEvolve {n : ℕ} (J : HeatJet n) {m : ℝ} (hm : 0 < m) (q : Fin (n+1) → ℝ) : HeatJet n where
  F := varianceContinuation m J.F q
  A := varianceTest m J.F J.A q
  G i := varianceTest m J.F (J.G i) q
  H i := varianceGradient m J.F (J.G i) (J.G i) (J.H i) q
  A₁ i := varianceGradient m J.F (J.G i) J.A (J.A₁ i) q
  A₂ i := varianceSecond m J.F (J.G i) (J.H i) J.A (J.A₁ i) (J.A₂ i) q
  C := J.C
  lipschitz := lipschitzWith_shiftedContinuation J.lipschitz hm (fun x =>
    (exponentialIncrement_gaussian (fun i => Real.toNNReal (q i))).integrable_shift J.lipschitz m x)
  smoothA := varianceTest_bddSmooth J.regular J.smoothA m q
  smoothG i := varianceTest_bddSmooth J.regular (J.smoothG i) m q
  smoothH i := varianceGradient_bddSmooth J.regular (J.smoothG i) (J.smoothG i) (J.smoothH i) m q
  smoothA₁ i := varianceGradient_bddSmooth J.regular (J.smoothG i) J.smoothA (J.smoothA₁ i) m q
  smoothA₂ i := varianceSecond_bddSmooth J.regular (J.smoothG i) (J.smoothH i) J.smoothA (J.smoothA₁ i) (J.smoothA₂ i) m q
  derivF := hasDerivAt_varianceContinuation_source_vector J hm.ne' q
  derivG i := hasDerivAt_varianceTest_source J.lipschitz (J.smoothG i) (J.smoothG i) (J.smoothH i)
    (J.derivF_coord i) (J.derivG i) m q
  derivA := hasDerivAt_varianceTest_source_vector J.lipschitz J.smoothA J.smoothG J.smoothA₁
    J.derivF J.derivA m q
  derivA₁ i := hasDerivAt_varianceGradient_source J.lipschitz (J.smoothG i) (J.smoothH i) J.smoothA
    (J.smoothA₁ i) (J.smoothA₂ i) (J.derivF_coord i) (J.derivG i) (J.derivA_coord i) (J.derivA₁ i) m q

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι P : Type*} [Fintype ι] [TopologicalSpace P] [FirstCountableTopology P]

theorem dynamic_varianceGradient_joint_continuous
    {F G A A₁ : P → (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : ∀ p, LipschitzWith C (F p))
    (hcF : Continuous (fun p : P × (ι → ℝ) => F p.1 p.2))
    (hcG : Continuous (fun p : P × (ι → ℝ) => G p.1 p.2))
    (hcA : Continuous (fun p : P × (ι → ℝ) => A p.1 p.2))
    (hcA₁ : Continuous (fun p : P × (ι → ℝ) => A₁ p.1 p.2))
    (hbG : AbsBounded (fun p : P × (ι → ℝ) => G p.1 p.2))
    (hbA : AbsBounded (fun p : P × (ι → ℝ) => A p.1 p.2))
    (hbA₁ : AbsBounded (fun p : P × (ι → ℝ) => A₁ p.1 p.2))
    (m : ℝ) {q : P → ι → ℝ} (hq : Continuous q) :
    Continuous (fun p : P × (ι → ℝ) => varianceGradient m (F p.1) (G p.1) (A p.1) (A₁ p.1) (q p.1) p.2) := by
  exact (dynamic_varianceTest_joint_continuous hF hcF hcA₁ hbA₁ m hq).add
    (((dynamic_varianceTest_joint_continuous (A := fun p y => A p y*G p y) hF hcF (hcA.mul hcG) (hbA.mul hbG) m hq).sub
      ((dynamic_varianceTest_joint_continuous hF hcF hcA hbA m hq).mul
        (dynamic_varianceTest_joint_continuous hF hcF hcG hbG m hq))).const_mul m)

omit [FirstCountableTopology P] in
theorem dynamic_varianceGradient_absBounded
    {F G A A₁ : P → (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : ∀ p, LipschitzWith C (F p))
    (hcG : Continuous (fun p : P × (ι → ℝ) => G p.1 p.2))
    (hcA : Continuous (fun p : P × (ι → ℝ) => A p.1 p.2))
    (hcA₁ : Continuous (fun p : P × (ι → ℝ) => A₁ p.1 p.2))
    (hbG : AbsBounded (fun p : P × (ι → ℝ) => G p.1 p.2))
    (hbA : AbsBounded (fun p : P × (ι → ℝ) => A p.1 p.2))
    (hbA₁ : AbsBounded (fun p : P × (ι → ℝ) => A₁ p.1 p.2))
    (m : ℝ) (q : P → ι → ℝ) :
    AbsBounded (fun p : P × (ι → ℝ) => varianceGradient m (F p.1) (G p.1) (A p.1) (A₁ p.1) (q p.1) p.2) := by
  exact (dynamic_varianceTest_absBounded hF hcA₁ hbA₁ m q).add
    (((dynamic_varianceTest_absBounded (A := fun p y => A p y*G p y) hF (hcA.mul hcG) (hbA.mul hbG) m q).sub
      ((dynamic_varianceTest_absBounded hF hcA hbA m q).mul
        (dynamic_varianceTest_absBounded hF hcG hbG m q))).const_mul m)

theorem dynamic_varianceSecond_joint_continuous
    {F G H A A₁ A₂ : P → (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : ∀ p, LipschitzWith C (F p))
    (hcF : Continuous (fun p : P × (ι → ℝ) => F p.1 p.2))
    (hcG : Continuous (fun p : P × (ι → ℝ) => G p.1 p.2))
    (hcH : Continuous (fun p : P × (ι → ℝ) => H p.1 p.2))
    (hcA : Continuous (fun p : P × (ι → ℝ) => A p.1 p.2))
    (hcA₁ : Continuous (fun p : P × (ι → ℝ) => A₁ p.1 p.2))
    (hcA₂ : Continuous (fun p : P × (ι → ℝ) => A₂ p.1 p.2))
    (hbG : AbsBounded (fun p : P × (ι → ℝ) => G p.1 p.2))
    (hbH : AbsBounded (fun p : P × (ι → ℝ) => H p.1 p.2))
    (hbA : AbsBounded (fun p : P × (ι → ℝ) => A p.1 p.2))
    (hbA₁ : AbsBounded (fun p : P × (ι → ℝ) => A₁ p.1 p.2))
    (hbA₂ : AbsBounded (fun p : P × (ι → ℝ) => A₂ p.1 p.2))
    (m : ℝ) {q : P → ι → ℝ} (hq : Continuous q) :
    Continuous (fun p : P × (ι → ℝ) => varianceSecond m (F p.1) (G p.1) (H p.1)
      (A p.1) (A₁ p.1) (A₂ p.1) (q p.1) p.2) := by
  exact (dynamic_varianceGradient_joint_continuous hF hcF hcG hcA₁ hcA₂ hbG hbA₁ hbA₂ m hq).add
    (((dynamic_varianceGradient_joint_continuous (A := fun p y => A p y*G p y)
        (A₁ := fun p y => A₁ p y*G p y+A p y*H p y) hF hcF hcG (hcA.mul hcG)
        ((hcA₁.mul hcG).add (hcA.mul hcH)) hbG (hbA.mul hbG)
        ((hbA₁.mul hbG).add (hbA.mul hbH)) m hq).sub
      (((dynamic_varianceGradient_joint_continuous hF hcF hcG hcA hcA₁ hbG hbA hbA₁ m hq).mul
        (dynamic_varianceTest_joint_continuous hF hcF hcG hbG m hq)).add
        ((dynamic_varianceTest_joint_continuous hF hcF hcA hbA m hq).mul
          (dynamic_varianceGradient_joint_continuous hF hcF hcG hcG hcH hbG hbG hbH m hq)))).const_mul m)

omit [FirstCountableTopology P] in
theorem dynamic_varianceSecond_absBounded
    {F G H A A₁ A₂ : P → (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : ∀ p, LipschitzWith C (F p))
    (hcG : Continuous (fun p : P × (ι → ℝ) => G p.1 p.2))
    (hcH : Continuous (fun p : P × (ι → ℝ) => H p.1 p.2))
    (hcA : Continuous (fun p : P × (ι → ℝ) => A p.1 p.2))
    (hcA₁ : Continuous (fun p : P × (ι → ℝ) => A₁ p.1 p.2))
    (hcA₂ : Continuous (fun p : P × (ι → ℝ) => A₂ p.1 p.2))
    (hbG : AbsBounded (fun p : P × (ι → ℝ) => G p.1 p.2))
    (hbH : AbsBounded (fun p : P × (ι → ℝ) => H p.1 p.2))
    (hbA : AbsBounded (fun p : P × (ι → ℝ) => A p.1 p.2))
    (hbA₁ : AbsBounded (fun p : P × (ι → ℝ) => A₁ p.1 p.2))
    (hbA₂ : AbsBounded (fun p : P × (ι → ℝ) => A₂ p.1 p.2))
    (m : ℝ) (q : P → ι → ℝ) :
    AbsBounded (fun p : P × (ι → ℝ) => varianceSecond m (F p.1) (G p.1) (H p.1)
      (A p.1) (A₁ p.1) (A₂ p.1) (q p.1) p.2) := by
  exact (dynamic_varianceGradient_absBounded hF hcG hcA₁ hcA₂ hbG hbA₁ hbA₂ m q).add
    (((dynamic_varianceGradient_absBounded (A := fun p y => A p y*G p y)
        (A₁ := fun p y => A₁ p y*G p y+A p y*H p y) hF hcG (hcA.mul hcG)
        ((hcA₁.mul hcG).add (hcA.mul hcH)) hbG (hbA.mul hbG)
        ((hbA₁.mul hbG).add (hbA.mul hbH)) m q).sub
      (((dynamic_varianceGradient_absBounded hF hcG hcA hcA₁ hbG hbA hbA₁ m q).mul
        (dynamic_varianceTest_absBounded hF hcG hbG m q)).add
        ((dynamic_varianceTest_absBounded hF hcA hbA m q).mul
          (dynamic_varianceGradient_absBounded hF hcG hcG hcH hbG hbG hbH m q)))).const_mul m)

 

def HeatJetFamily.varianceEvolve {n : ℕ} (V : HeatJetFamily n)
    {m : ℝ} (hm : 0 < m) {q : ℝ → Fin (n+1) → ℝ} (hq : Continuous q) : HeatJetFamily n where
  J t := (V.J t).varianceEvolve hm (q t)
  C := V.C
  lipschitz t := lipschitzWith_shiftedContinuation (V.lipschitz t) hm (fun x =>
    (exponentialIncrement_gaussian _).integrable_shift (V.lipschitz t) m x)
  continuousF := dynamic_varianceContinuation_continuous (fun p : ℝ × (Fin (n+1) → ℝ) => V.lipschitz p.1)
    (V.continuousF.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
    m (hq.comp continuous_fst) continuous_snd
  continuousA := dynamic_varianceTest_joint_continuous (A := fun t => (V.J t).A) V.lipschitz V.continuousF V.continuousA V.boundedA m hq
  continuousG i := dynamic_varianceTest_joint_continuous (A := fun t => (V.J t).G i) V.lipschitz V.continuousF (V.continuousG i) (V.boundedG i) m hq
  continuousH i := dynamic_varianceGradient_joint_continuous
    (G := fun t => (V.J t).G i) (A := fun t => (V.J t).G i) (A₁ := fun t => (V.J t).H i) V.lipschitz V.continuousF
    (V.continuousG i) (V.continuousG i) (V.continuousH i) (V.boundedG i) (V.boundedG i) (V.boundedH i) m hq
  continuousA₁ i := dynamic_varianceGradient_joint_continuous
    (G := fun t => (V.J t).G i) (A := fun t => (V.J t).A) (A₁ := fun t => (V.J t).A₁ i) V.lipschitz V.continuousF
    (V.continuousG i) V.continuousA (V.continuousA₁ i) (V.boundedG i) V.boundedA (V.boundedA₁ i) m hq
  continuousA₂ i := dynamic_varianceSecond_joint_continuous
    (G := fun t => (V.J t).G i) (H := fun t => (V.J t).H i)
    (A := fun t => (V.J t).A) (A₁ := fun t => (V.J t).A₁ i) (A₂ := fun t => (V.J t).A₂ i) V.lipschitz V.continuousF
    (V.continuousG i) (V.continuousH i) V.continuousA (V.continuousA₁ i) (V.continuousA₂ i)
    (V.boundedG i) (V.boundedH i) V.boundedA (V.boundedA₁ i) (V.boundedA₂ i) m hq
  boundedA := dynamic_varianceTest_absBounded (A := fun t => (V.J t).A) V.lipschitz V.continuousA V.boundedA m q
  boundedG i := dynamic_varianceTest_absBounded (A := fun t => (V.J t).G i) V.lipschitz (V.continuousG i) (V.boundedG i) m q
  boundedH i := dynamic_varianceGradient_absBounded
    (G := fun t => (V.J t).G i) (A := fun t => (V.J t).G i) (A₁ := fun t => (V.J t).H i) V.lipschitz
    (V.continuousG i) (V.continuousG i) (V.continuousH i) (V.boundedG i) (V.boundedG i) (V.boundedH i) m q
  boundedA₁ i := dynamic_varianceGradient_absBounded
    (G := fun t => (V.J t).G i) (A := fun t => (V.J t).A) (A₁ := fun t => (V.J t).A₁ i) V.lipschitz
    (V.continuousG i) V.continuousA (V.continuousA₁ i) (V.boundedG i) V.boundedA (V.boundedA₁ i) m q
  boundedA₂ i := dynamic_varianceSecond_absBounded
    (G := fun t => (V.J t).G i) (H := fun t => (V.J t).H i)
    (A := fun t => (V.J t).A) (A₁ := fun t => (V.J t).A₁ i) (A₂ := fun t => (V.J t).A₂ i) V.lipschitz
    (V.continuousG i) (V.continuousH i) V.continuousA (V.continuousA₁ i) (V.continuousA₂ i)
    (V.boundedG i) (V.boundedH i) V.boundedA (V.boundedA₁ i) (V.boundedA₂ i) m q

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

variable {n : ℕ}

theorem HeatJetFamily.continuous_signedVarianceRate (V : HeatJetFamily n)
    (m : ℝ) (d : Fin (n+1) → ℝ) {q : ℝ → Fin (n+1) → ℝ} (hq : Continuous q) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => (V.J p.1).signedVarianceRate m d (q p.1) p.2) := by
  apply continuous_finsetSum
  intro i _
  exact ((dynamic_varianceTest_joint_continuous (A := fun t => (V.J t).testedInsertion m i)
    V.lipschitz V.continuousF (V.continuous_testedInsertion m i) (V.bounded_testedInsertion m i) m hq).sub
      ((dynamic_varianceTest_joint_continuous (A := fun t => (V.J t).A)
          V.lipschitz V.continuousF V.continuousA V.boundedA m hq).mul
        (dynamic_varianceTest_joint_continuous (A := fun t => (V.J t).potentialInsertion m i)
          V.lipschitz V.continuousF (V.continuous_potentialInsertion m i) (V.bounded_potentialInsertion m i) m hq))).const_mul _

theorem HeatJetFamily.bounded_signedVarianceRate (V : HeatJetFamily n)
    (m : ℝ) (d : Fin (n+1) → ℝ) (q : ℝ → Fin (n+1) → ℝ) :
    AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => (V.J p.1).signedVarianceRate m d (q p.1) p.2) := by
  apply AbsBounded.sum
  intro i
  exact ((dynamic_varianceTest_absBounded (A := fun t => (V.J t).testedInsertion m i)
    V.lipschitz (V.continuous_testedInsertion m i) (V.bounded_testedInsertion m i) m q).sub
      ((dynamic_varianceTest_absBounded (A := fun t => (V.J t).A)
          V.lipschitz V.continuousA V.boundedA m q).mul
        (dynamic_varianceTest_absBounded (A := fun t => (V.J t).potentialInsertion m i)
          V.lipschitz (V.continuous_potentialInsertion m i) (V.bounded_potentialInsertion m i) m q))).const_mul _

theorem HeatJetFamily.continuous_signedVarianceDerivative (V : HeatJetFamily n)
    (m : ℝ) (d : Fin (n+1) → ℝ) {q : ℝ → Fin (n+1) → ℝ} (hq : Continuous q) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => signedVarianceDerivative m
      (V.J p.1).F (V.J p.1).G (V.J p.1).H d (q p.1) p.2) := by
  apply continuous_finsetSum
  intro i _
  exact ((dynamic_varianceTest_joint_continuous (A := fun t => (V.J t).H i)
    V.lipschitz V.continuousF (V.continuousH i) (V.boundedH i) m hq).add
      ((dynamic_varianceTest_joint_continuous (A := fun t y => ((V.J t).G i y)^2)
        V.lipschitz V.continuousF ((V.continuousG i).pow 2) ((V.boundedG i).pow 2) m hq).const_mul m)).const_mul _

theorem HeatJetFamily.bounded_signedVarianceDerivative (V : HeatJetFamily n)
    (m : ℝ) (d : Fin (n+1) → ℝ) (q : ℝ → Fin (n+1) → ℝ) :
    AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => signedVarianceDerivative m
      (V.J p.1).F (V.J p.1).G (V.J p.1).H d (q p.1) p.2) := by
  apply AbsBounded.sum
  intro i
  exact ((dynamic_varianceTest_absBounded (A := fun t => (V.J t).H i)
    V.lipschitz (V.continuousH i) (V.boundedH i) m q).add
      ((dynamic_varianceTest_absBounded (A := fun t y => ((V.J t).G i y)^2)
        V.lipschitz ((V.continuousG i).pow 2) ((V.boundedG i).pow 2) m q).const_mul m)).const_mul _

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

 

def AffineVarianceRegular (q d : ι → ℝ) (t : ℝ) : Prop :=
  ∀ i, 0 < q i+t*d i ∨ (d i = 0 ∧ 0 ≤ q i)

omit [Fintype ι] in
theorem AffineVarianceRegular.nonneg {q d : ι → ℝ} {t : ℝ}
    (h : AffineVarianceRegular q d t) (i : ι) : 0 ≤ q i+t*d i := by
  rcases h i with h | ⟨hd,hq⟩
  · exact h.le
  · simpa only [hd,mul_zero,add_zero] using hq

theorem AffineVarianceRegular.eventually {q d : ι → ℝ} {t : ℝ}
    (h : AffineVarianceRegular q d t) : ∀ᶠ s in 𝓝 t, AffineVarianceRegular q d s := by
  rw [show (fun s => AffineVarianceRegular q d s) =
    (fun s => ∀ i, 0 < q i+s*d i ∨ (d i = 0 ∧ 0 ≤ q i)) from rfl,eventually_all]
  intro i
  rcases h i with hp | hz
  · exact ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).eventually
      (eventually_gt_nhds hp)).mono fun _ hh => Or.inl hh
  · exact Eventually.of_forall fun _ => Or.inr hz

omit [Fintype ι] in
theorem AffineVarianceRegular.sqrt_coefficient {q d : ι → ℝ} {t : ℝ}
    (h : AffineVarianceRegular q d t) (i : ι) :
    Real.sqrt (q i+t*d i)*(d i/(2*Real.sqrt (q i+t*d i))) = d i/2 := by
  rcases h i with hp | ⟨hd,_⟩
  · field_simp [Real.sqrt_ne_zero'.mpr hp]
  · simp [hd]

theorem AffineVarianceRegular.amplitude_regular {q d : ι → ℝ} {t : ℝ}
    (h : AffineVarianceRegular q d t) :
    ∃ l r, t ∈ Ioo l r ∧
      (∀ s ∈ Ioo l r, AffineVarianceRegular q d s) ∧
      (∀ s ∈ Ioo l r, HasDerivAt (fun s i => Real.sqrt (q i+s*d i))
        (fun i => d i/(2*Real.sqrt (q i+s*d i))) s) ∧
      (∀ s ∈ Ioo l r, ‖fun i => Real.sqrt (q i+s*d i)‖ ≤ ‖fun i => Real.sqrt (q i+t*d i)‖+1) ∧
      (∀ s ∈ Ioo l r, ‖fun i => d i/(2*Real.sqrt (q i+s*d i))‖ ≤
        ‖fun i => d i/(2*Real.sqrt (q i+t*d i))‖+1) := by
  let a := fun s i => Real.sqrt (q i+s*d i)
  let a' := fun s i => d i/(2*Real.sqrt (q i+s*d i))
  have ha : Continuous a := continuous_pi fun i => (continuous_const.add (continuous_id.mul continuous_const)).sqrt
  have ha' : ContinuousAt a' t := by
    apply continuousAt_pi.mpr
    intro i
    rcases h i with hp | ⟨hd,_⟩
    · exact continuousAt_const.div (continuousAt_const.mul
        (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).sqrt)
        (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr hp))
    · simpa only [a',hd,zero_div] using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0:ℝ)) t)
  have hA : ∀ᶠ s in 𝓝 t, ‖a s‖ ≤ ‖a t‖+1 :=
    (ha.continuousAt.norm.eventually (eventually_lt_nhds (lt_add_one _))).mono fun _ h => h.le
  have hB : ∀ᶠ s in 𝓝 t, ‖a' s‖ ≤ ‖a' t‖+1 :=
    (ha'.norm.eventually (eventually_lt_nhds (lt_add_one _))).mono fun _ h => h.le
  obtain ⟨l,r,ht,hlr⟩ := (h.eventually.and (hA.and hB)).exists_Ioo_subset
  refine ⟨l,r,ht,fun s hs => (hlr hs).1,?_,fun s hs => (hlr hs).2.1,fun s hs => (hlr hs).2.2⟩
  intro s hs
  apply hasDerivAt_pi.mpr
  intro i
  rcases (hlr hs).1 i with hp | ⟨hd,_⟩
  · simpa only [id_eq,one_mul] using
      (((hasDerivAt_id s).mul_const (d i)).const_add (q i)).sqrt hp.ne'
  · simpa only [hd,mul_zero,add_zero,zero_div] using hasDerivAt_const s (Real.sqrt (q i))

omit [Fintype ι] in
 

theorem affineVarianceRegular_of_nonneg {q d : ι → ℝ} {l r t : ℝ}
    (hp : ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q i+s*d i) (ht : t ∈ Ioo l r) :
    AffineVarianceRegular q d t := by
  intro i
  by_cases hz : q i+t*d i = 0
  · right
    have hl : (l+t)/2 ∈ Ioo l r := by constructor <;> linarith [ht.1,ht.2]
    have hr : (t+r)/2 ∈ Ioo l r := by constructor <;> linarith [ht.1,ht.2]
    have hleft := hp _ hl i
    have hright := hp _ hr i
    have hd : d i = 0 := by
      rcases lt_trichotomy (d i) 0 with hneg | hzero | hpos
      · have hh := mul_neg_of_pos_of_neg (show 0 < r-t by linarith [ht.2]) hneg
        nlinarith
      · exact hzero
      · have hh := mul_pos (show 0 < t-l by linarith [ht.1]) hpos
        nlinarith
    exact ⟨hd,by simpa only [hd,mul_zero,add_zero] using hp t ht i⟩
  · exact Or.inl (lt_of_le_of_ne (hp t ht i) (Ne.symm hz))

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 

def actualScalarClock {ι : Type*} [Fintype ι] (n : ℕ) (w : Spin n → ℝ)
    (φ : Spin n → (ι → ℝ) →L[ℝ] ℝ) (q : ι → ℝ≥0)
    (steps : List (GaussianStep ι)) (b h : ℕ → ℝ) (j : ℕ) : ℝ :=
  h j+b j*rootLevelPairMean w φ q (orderedOverlap n) steps j

theorem actualScalarClock_nonneg {ι : Type*} [Fintype ι] (n : ℕ) {w : Spin n → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : Spin n → (ι → ℝ) →L[ℝ] ℝ) (q : ι → ℝ≥0)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    {b h : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (j : ℕ) :
    0 ≤ actualScalarClock n w φ q steps b h j :=
  add_nonneg (hh j) (mul_nonneg (hb j) (rootLevelPairMean_SK_bounds n hw φ q steps ha j).1)

theorem actualScalarClock_monotone {ι : Type*} [Fintype ι] (n : ℕ) {w : Spin n → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : Spin n → (ι → ℝ) →L[ℝ] ℝ) (q : ι → ℝ≥0)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    {b h : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) (hbm : Monotone b) (hhm : Monotone h) :
    Monotone (actualScalarClock n w φ q steps b h) :=
  scalarClock_monotone hbm hhm (rootLevelPairMean_overlap_monotone n hw φ q steps ha)
    hb (fun j => (rootLevelPairMean_SK_bounds n hw φ q steps ha j).1)

theorem actualScalarClock_le {ι : Type*} [Fintype ι] (n : ℕ) {w : Spin n → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : Spin n → (ι → ℝ) →L[ℝ] ℝ) (q : ι → ℝ≥0)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    {b h : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) (j : ℕ) :
    actualScalarClock n w φ q steps b h j ≤ h j+b j := by
  have hh := mul_le_mul_of_nonneg_left (rootLevelPairMean_SK_bounds n hw φ q steps ha j).2.1 (hb j)
  dsimp [actualScalarClock]
  linarith

end SKFluctuations.Cavity

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {ι κ S T : Type*} [Fintype ι] [Fintype κ] [Fintype S] [Fintype T]

 
def ClockTree.cavityLeft : {as : List PositiveMass} → ClockTree (S × T) as → ClockTree S as
  | _, .leaf => .leaf
  | _, .step a R => .step a R.cavityLeft
  | _, .fork R U => .fork R.cavityLeft U.cavityLeft

 
def ClockTree.cavityRight : {as : List PositiveMass} → ClockTree (S × T) as → ClockTree T as
  | _, .leaf => .leaf
  | _, .step a R => .step a R.cavityRight
  | _, .fork R U => .fork R.cavityRight U.cavityRight

 
def ClockTree.cavityAssignment : {as : List PositiveMass} → (R : ClockTree (S × T) as) →
    R.Assignment ≃ R.cavityLeft.Assignment × R.cavityRight.Assignment
  | _, .leaf => Equiv.refl _
  | _, .step _ R => R.cavityAssignment
  | _, .fork R U => (R.cavityAssignment.prodCongr U.cavityAssignment).trans
      (Equiv.prodProdProdComm _ _ _ _)

omit [Fintype ι] [Fintype κ] in
 theorem leftSteps_clockSteps (as : List PositiveMass) (q : ℕ → ι ⊕ κ → ℝ≥0) :
    leftSteps (clockSteps as q) = clockSteps as (fun j i => q j (.inl i)) := by
  induction as generalizing q with
  | nil => rfl
  | cons a as ih => simp only [clockSteps,leftSteps,List.map_cons]; exact congrArg _ (ih _)

omit [Fintype ι] [Fintype κ] in
 theorem rightSteps_clockSteps (as : List PositiveMass) (q : ℕ → ι ⊕ κ → ℝ≥0) :
    rightSteps (clockSteps as q) = clockSteps as (fun j i => q j (.inr i)) := by
  induction as generalizing q with
  | nil => rfl
  | cons a as ih => simp only [clockSteps,rightSteps,List.map_cons]; exact congrArg _ (ih _)

variable [Nonempty S] [Nonempty T]

 

theorem ClockTree.weight_cavity_product {w : S → ℝ} {v : T → ℝ}
    (hw : ∀ s, 0 < w s) (hv : ∀ t, 0 < v t)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ψ : T → (κ → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (R : ClockTree (S × T) as)
    {a : ℝ} (ha : MassOrdered a as) (q : ℕ → ι ⊕ κ → ℝ≥0)
    (σ : R.Assignment) (x : ι ⊕ κ → ℝ) :
    R.weight (fun s => w s.1*v s.2) (productFeature φ ψ) q σ x =
      R.cavityLeft.weight w φ (fun j i => q j (.inl i)) (R.cavityAssignment σ).1 (fun i => x (.inl i))*
      R.cavityRight.weight v ψ (fun j i => q j (.inr i)) (R.cavityAssignment σ).2 (fun i => x (.inr i)) := by
  induction R generalizing a q x with
  | leaf => exact spinWeight_product w v φ ψ x σ
  | @step b bs R ih =>
    simp only [ClockTree.weight_step]
    have hP : gaussianHierarchy (fun s => w s.1*v s.2) (productFeature φ ψ)
        (clockSteps bs (fun j => q (j+1))) = _ := funext fun y =>
      gaussianHierarchy_product hw hv φ ψ
        (clockSteps bs (fun j => q (j+1))) (clockSteps_ordered ha.2.2 _) y
    simp only [leftSteps_clockSteps,rightSteps_clockSteps] at hP
    have hA : R.weight (fun s => w s.1*v s.2) (productFeature φ ψ)
        (fun j => q (j+1)) σ = _ := funext fun y => ih ha.2.2 (fun j => q (j+1)) σ y
    rw [hP,hA]
    exact shiftedMean_sum_mul (q 0) b.val _ _ _ _ x
  | fork R U ihR ihU =>
    rw [ClockTree.weight_fork,ihR ha,ihU ha]
    exact mul_mul_mul_comm _ _ _ _

 
theorem ClockTree.disorderWeight_cavity_product {w : S → ℝ} {v : T → ℝ}
    (hw : ∀ s, 0 < w s) (hv : ∀ t, 0 < v t)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ψ : T → (κ → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (R : ClockTree (S × T) as)
    (ha : MassOrdered 0 as) (l : ι ⊕ κ → ℝ) (q : ℕ → ι ⊕ κ → ℝ)
    (σ : R.Assignment) (x : ι ⊕ κ → ℝ) :
    R.disorderWeight (fun s => w s.1*v s.2) (productFeature φ ψ) l q σ x =
      R.cavityLeft.disorderWeight w φ (fun i => l (.inl i)) (fun j i => q j (.inl i))
        (R.cavityAssignment σ).1 (fun i => x (.inl i))*
      R.cavityRight.disorderWeight v ψ (fun i => l (.inr i)) (fun j i => q j (.inr i))
        (R.cavityAssignment σ).2 (fun i => x (.inr i)) := by
  unfold ClockTree.disorderWeight
  simp_rw [R.weight_cavity_product hw hv φ ψ ha]
  have he := integral_sumGaussian (fun i => Real.toNNReal (q 0 i-l i))
    (fun z : (ι → ℝ) × (κ → ℝ) => R.cavityLeft.weight w φ
      (fun j i => cumulativeIncrements (q 0) (fun j => q (j+1)) j (.inl i))
        (R.cavityAssignment σ).1 ((fun i => x (.inl i))+z.1)*
      R.cavityRight.weight v ψ
        (fun j i => cumulativeIncrements (q 0) (fun j => q (j+1)) j (.inr i))
        (R.cavityAssignment σ).2 ((fun i => x (.inr i))+z.2))
  simp only [Pi.add_def] at he ⊢
  rw [he,integral_prod_mul
    (fun z : ι → ℝ => R.cavityLeft.weight w φ
      (fun j i => cumulativeIncrements (q 0) (fun j => q (j+1)) j (.inl i))
        (R.cavityAssignment σ).1 (fun i => x (.inl i)+z i))
    (fun z : κ → ℝ => R.cavityRight.weight v ψ
      (fun j i => cumulativeIncrements (q 0) (fun j => q (j+1)) j (.inr i))
        (R.cavityAssignment σ).2 (fun i => x (.inr i)+z i))]
  have hl : (fun j i => cumulativeIncrements (q 0) (fun j => q (j+1)) j (.inl i)) =
      cumulativeIncrements (fun i => q 0 (.inl i)) (fun j i => q (j+1) (.inl i)) := by
    funext j i; cases j <;> rfl
  have hr : (fun j i => cumulativeIncrements (q 0) (fun j => q (j+1)) j (.inr i)) =
      cumulativeIncrements (fun i => q 0 (.inr i)) (fun j i => q (j+1) (.inr i)) := by
    funext j i; cases j <;> rfl
  rw [hl,hr]

 
theorem ClockTree.disorderExpect_cavity_product {w : S → ℝ} {v : T → ℝ}
    (hw : ∀ s, 0 < w s) (hv : ∀ t, 0 < v t)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ψ : T → (κ → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (R : ClockTree (S × T) as)
    (ha : MassOrdered 0 as) (l : ι ⊕ κ → ℝ) (q : ℕ → ι ⊕ κ → ℝ)
    (P : R.cavityLeft.Assignment → ℝ) (Q : R.cavityRight.Assignment → ℝ) (x : ι ⊕ κ → ℝ) :
    R.disorderExpect (fun s => w s.1*v s.2) (productFeature φ ψ) l q
      (fun σ => P (R.cavityAssignment σ).1*Q (R.cavityAssignment σ).2) x =
      R.cavityLeft.disorderExpect w φ (fun i => l (.inl i)) (fun j i => q j (.inl i)) P (fun i => x (.inl i))*
      R.cavityRight.disorderExpect v ψ (fun i => l (.inr i)) (fun j i => q j (.inr i)) Q (fun i => x (.inr i)) := by
  unfold ClockTree.disorderExpect
  simp_rw [R.disorderWeight_cavity_product hw hv φ ψ ha]
  let f := fun σ : R.cavityLeft.Assignment × R.cavityRight.Assignment =>
    (R.cavityLeft.disorderWeight w φ (fun i => l (.inl i)) (fun j i => q j (.inl i)) σ.1 (fun i => x (.inl i))*P σ.1)*
    (R.cavityRight.disorderWeight v ψ (fun i => l (.inr i)) (fun j i => q j (.inr i)) σ.2 (fun i => x (.inr i))*Q σ.2)
  calc
    _ = ∑ σ, f (R.cavityAssignment σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      dsimp [f]
      ring
    _ = ∑ σ, f σ := R.cavityAssignment.sum_comp f
    _ = _ := by
      simp only [f,Fintype.sum_prod_type]
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]

end SKFluctuations.Hierarchy

end

end OAI
