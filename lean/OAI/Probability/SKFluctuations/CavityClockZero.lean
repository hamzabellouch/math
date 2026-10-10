import Mathlib
import OAI.Probability.SKFluctuations.ActualPairCut
import OAI.Probability.SKFluctuations.VarianceJet

namespace OAI

/-! Cavity Clock Zero. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {ι κ S : Type*} [Fintype ι] [Fintype κ] [Fintype S]

omit [Fintype ι] [Fintype κ] in
 theorem clockSteps_zeroRow (as : List PositiveMass) (q : ℕ → ι → ℝ≥0) :
    clockSteps as (fun j => Sum.elim (q j) (fun _ : κ => 0)) = zeroRowSteps (clockSteps as q) := by
  induction as generalizing q with
  | nil => rfl
  | cons a as ih => simp only [clockSteps,zeroRowSteps,List.map_cons]; exact congrArg _ (ih _)

 

theorem ClockTree.weight_zeroRow (w : S → ℝ)
    (φ : S → (ι ⊕ κ → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (R : ClockTree S as)
    (q : ℕ → ι → ℝ≥0) (σ : R.Assignment) (x : ι → ℝ) :
    R.weight w φ (fun j => Sum.elim (q j) (fun _ => 0)) σ (cavityEmbed x) =
      R.weight w (fun s => (φ s).comp cavityEmbed) q σ x := by
  induction R generalizing q x with
  | leaf => rfl
  | @step a as R ih =>
    simp only [ClockTree.weight_step,clockSteps_zeroRow]
    rw [shiftedMean_zeroRow]
    have hP : (fun y => gaussianHierarchy w φ (zeroRowSteps (clockSteps as (fun j => q (j+1))))
        (cavityEmbed y)) = gaussianHierarchy w (fun s => (φ s).comp cavityEmbed)
          (clockSteps as (fun j => q (j+1))) :=
      funext fun y => gaussianHierarchy_zeroRow w φ _ y
    have hA : (fun y => R.weight w φ (fun j => Sum.elim (q (j+1)) (fun _ => 0)) σ
        (cavityEmbed y)) = R.weight w (fun s => (φ s).comp cavityEmbed) (fun j => q (j+1)) σ :=
      funext fun y => ih _ σ y
    rw [hP,hA]
  | fork R U ihR ihU => simp only [ClockTree.weight_fork,ihR,ihU]

omit [Fintype ι] [Fintype κ] in
 theorem cumulativeIncrements_zeroRow (l : ι → ℝ) (q : ℕ → ι → ℝ) :
    cumulativeIncrements (Sum.elim l (fun _ : κ => 0))
      (fun j => Sum.elim (q j) (fun _ => 0)) =
      fun j => Sum.elim (cumulativeIncrements l q j) (fun _ => 0) := by
  funext j i
  cases j <;> cases i <;> simp [cumulativeIncrements]

 
theorem ClockTree.disorderWeight_zeroRow (w : S → ℝ)
    (φ : S → (ι ⊕ κ → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (R : ClockTree S as)
    (l : ι → ℝ) (q : ℕ → ι → ℝ) (σ : R.Assignment) (x : ι → ℝ) :
    R.disorderWeight w φ (Sum.elim l (fun _ => 0))
        (fun j => Sum.elim (q j) (fun _ => 0)) σ (cavityEmbed x) =
      R.disorderWeight w (fun s => (φ s).comp cavityEmbed) l q σ x := by
  unfold ClockTree.disorderWeight
  rw [cumulativeIncrements_zeroRow]
  have he : (fun i : ι ⊕ κ => Real.toNNReal
      (Sum.elim (q 0) (fun _ => 0) i-Sum.elim l (fun _ => 0) i)) =
        Sum.elim (fun i => Real.toNNReal (q 0 i-l i)) (fun _ => 0) := by
    funext i; cases i <;> simp
  change (∫ z, R.weight w φ (fun j => Sum.elim
    (cumulativeIncrements (q 0) (fun j => q (j+1)) j) (fun _ => 0)) σ (cavityEmbed x+z)
    ∂Measure.pi (fun i => gaussianReal 0 ((fun j : ι ⊕ κ => Real.toNNReal
      (Sum.elim (q 0) (fun _ => 0) j-Sum.elim l (fun _ => 0) j)) i))) = _
  rw [he,integral_zeroRowGaussian]
  simp_rw [← map_add,R.weight_zeroRow]

 
theorem ClockTree.disorderExpect_zeroRow (w : S → ℝ)
    (φ : S → (ι ⊕ κ → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (R : ClockTree S as)
    (l : ι → ℝ) (q : ℕ → ι → ℝ) (P : R.Assignment → ℝ) (x : ι → ℝ) :
    R.disorderExpect w φ (Sum.elim l (fun _ => 0))
        (fun j => Sum.elim (q j) (fun _ => 0)) P (cavityEmbed x) =
      R.disorderExpect w (fun s => (φ s).comp cavityEmbed) l q P x := by
  unfold ClockTree.disorderExpect
  simp_rw [R.disorderWeight_zeroRow]

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 
def HeatJet.productTest {n : ℕ} (J K : HeatJet n) : HeatJet n :=
  { J with
    A := fun y => J.A y*K.A y
    A₁ := fun i y => J.A₁ i y*K.A y+J.A y*K.A₁ i y
    A₂ := fun i y => J.A₂ i y*K.A y+2*(J.A₁ i y*K.A₁ i y)+J.A y*K.A₂ i y
    smoothA := J.smoothA.mul K.smoothA
    smoothA₁ := fun i => ((J.smoothA₁ i).mul K.smoothA).add (J.smoothA.mul (K.smoothA₁ i))
    smoothA₂ := fun i => (((J.smoothA₂ i).mul K.smoothA).add
      (((J.smoothA₁ i).mul (K.smoothA₁ i)).const_mul 2)).add (J.smoothA.mul (K.smoothA₂ i))
    derivA := by
      intro x v s
      apply ((J.derivA x v s).mul (K.derivA x v s)).congr_deriv
      simp only [Finset.sum_mul,Finset.mul_sum,Finset.sum_add_distrib,mul_add]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    derivA₁ := by
      intro i x s
      apply (((J.derivA₁ i x s).mul (K.derivA_coord i x s)).add
        ((J.derivA_coord i x s).mul (K.derivA₁ i x s))).congr_deriv
      ring }

def HeatJetFamily.productTest {n : ℕ} (V W : HeatJetFamily n) : HeatJetFamily n :=
  { V with
    J := fun q => (V.J q).productTest (W.J q)
    continuousA := V.continuousA.mul W.continuousA
    continuousA₁ := fun i => ((V.continuousA₁ i).mul W.continuousA).add
      (V.continuousA.mul (W.continuousA₁ i))
    continuousA₂ := fun i => (((V.continuousA₂ i).mul W.continuousA).add
      (((V.continuousA₁ i).mul (W.continuousA₁ i)).const_mul 2)).add
        (V.continuousA.mul (W.continuousA₂ i))
    boundedA := V.boundedA.mul W.boundedA
    boundedA₁ := fun i => ((V.boundedA₁ i).mul W.boundedA).add
      (V.boundedA.mul (W.boundedA₁ i))
    boundedA₂ := fun i => (((V.boundedA₂ i).mul W.boundedA).add
      (((V.boundedA₁ i).mul (W.boundedA₁ i)).const_mul 2)).add
        (V.boundedA.mul (W.boundedA₂ i)) }

def HeatJet.constantFamily {n : ℕ} (J : HeatJet n) : HeatJetFamily n where
  J _ := J
  C := J.C
  lipschitz _ := J.lipschitz
  continuousF := J.lipschitz.continuous.comp continuous_snd
  continuousA := J.smoothA.continuous.comp continuous_snd
  continuousG i := (J.smoothG i).continuous.comp continuous_snd
  continuousH i := (J.smoothH i).continuous.comp continuous_snd
  continuousA₁ i := (J.smoothA₁ i).continuous.comp continuous_snd
  continuousA₂ i := (J.smoothA₂ i).continuous.comp continuous_snd
  boundedA := let ⟨C,hC,bC⟩ := J.smoothA.bound; ⟨C,hC,fun p => bC p.2⟩
  boundedG i := let ⟨C,hC,bC⟩ := (J.smoothG i).bound; ⟨C,hC,fun p => bC p.2⟩
  boundedH i := let ⟨C,hC,bC⟩ := (J.smoothH i).bound; ⟨C,hC,fun p => bC p.2⟩
  boundedA₁ i := let ⟨C,hC,bC⟩ := (J.smoothA₁ i).bound; ⟨C,hC,fun p => bC p.2⟩
  boundedA₂ i := let ⟨C,hC,bC⟩ := (J.smoothA₂ i).bound; ⟨C,hC,fun p => bC p.2⟩

variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

def spinWeightJet {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (σ : S) : HeatJet n :=
  let J := gaussianFeatureJet hw φ (fun _ => 0) (ContinuousLinearMap.id ℝ _) []
    (a := 0) ⟨le_rfl,zero_le_one⟩ 0
  HeatJet.ofTest J.F (fun x => spinWeight w φ x σ) J.G J.H J.lipschitz
    (bddSmooth_spinWeight hw φ 2 σ) J.smoothG J.smoothH J.derivF J.derivG

@[simp] theorem spinWeightJet_F {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (σ : S) :
    (spinWeightJet hw φ σ).F = spinLogPartition w φ := by
  funext x
  change gaussianHierarchy w φ [] (0+ContinuousLinearMap.id ℝ _ x) = _
  simp only [ContinuousLinearMap.id_apply,zero_add,gaussianHierarchy]

@[simp] theorem spinWeightJet_A {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (σ : S) :
    (spinWeightJet hw φ σ).A = fun x => spinWeight w φ x σ := rfl

 

def ClockTree.weightFamily {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) :
    {as : List PositiveMass} → (T : ClockTree S as) →
    (q : ℕ → ℝ → Fin (n+1) → ℝ) → (∀ j, Continuous (q j)) → T.Assignment → HeatJetFamily n
  | _, .leaf, _, _, σ => (spinWeightJet hw φ σ).constantFamily
  | _, .step a T, q, hq, σ =>
    (T.weightFamily hw φ (fun j => q (j+1)) (fun j => hq (j+1)) σ).varianceEvolve
      a.property (hq 0)
  | _, .fork T U, q, hq, σ =>
    (T.weightFamily hw φ q hq σ.1).productTest (U.weightFamily hw φ q hq σ.2)

theorem ClockTree.weightFamily_actual {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (q : ℕ → ℝ → Fin (n+1) → ℝ) (hq : ∀ j, Continuous (q j)) (σ : T.Assignment) (t : ℝ) :
    ((T.weightFamily hw φ q hq σ).J t).F =
      gaussianHierarchy w φ (clockSteps as (fun j i => Real.toNNReal (q j t i))) ∧
    ((T.weightFamily hw φ q hq σ).J t).A =
      T.weight w φ (fun j i => Real.toNNReal (q j t i)) σ := by
  induction T generalizing q with
  | leaf => exact ⟨spinWeightJet_F hw φ σ,rfl⟩
  | step a T ih =>
    obtain ⟨hF,hA⟩ := ih (fun j => q (j+1)) (fun j => hq (j+1)) σ
    constructor
    · change varianceContinuation (a:ℝ) _ (q 0 t) = _
      rw [hF]
      rfl
    · change varianceTest (a:ℝ) _ _ (q 0 t) = _
      rw [hF,hA]
      rfl
  | fork T U ihT ihU =>
    obtain ⟨hF,hA⟩ := ihT q hq σ.1
    obtain ⟨_,hB⟩ := ihU q hq σ.2
    exact ⟨hF,by
      change (fun x => ((T.weightFamily hw φ q hq σ.1).J t).A x *
        ((U.weightFamily hw φ q hq σ.2).J t).A x) = _
      rw [hA,hB]
      rfl⟩

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

structure JetVariation {n : ℕ} (V : HeatJetFamily n) (l r : ℝ) where
  D : ℝ → (Fin (n+1) → ℝ) → ℝ
  B : ℝ → (Fin (n+1) → ℝ) → ℝ
  continuousD : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => D p.1 p.2)
  continuousB : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => B p.1 p.2)
  boundedD : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => D p.1 p.2)
  boundedB : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => B p.1 p.2)
  derivF : ∀ t ∈ Ioo l r, ∀ x, HasDerivAt (fun s => (V.J s).F x) (D t x) t
  derivA : ∀ t ∈ Ioo l r, ∀ x, HasDerivAt (fun s => (V.J s).A x) (B t x) t

variable {n : ℕ} {l r : ℝ}

def HeatJet.constantVariation (J : HeatJet n) : JetVariation J.constantFamily l r where
  D _ _ := 0
  B _ _ := 0
  continuousD := continuous_const
  continuousB := continuous_const
  boundedD := ⟨0,le_rfl,fun _ => by simp⟩
  boundedB := ⟨0,le_rfl,fun _ => by simp⟩
  derivF t _ x := hasDerivAt_const t (J.F x)
  derivA t _ x := hasDerivAt_const t (J.A x)

def JetVariation.productTest {V W : HeatJetFamily n}
    (v : JetVariation V l r) (w : JetVariation W l r) : JetVariation (V.productTest W) l r where
  D := v.D
  B t x := v.B t x*(W.J t).A x+(V.J t).A x*w.B t x
  continuousD := v.continuousD
  continuousB := (v.continuousB.mul W.continuousA).add (V.continuousA.mul w.continuousB)
  boundedD := v.boundedD
  boundedB := (v.boundedB.mul W.boundedA).add (V.boundedA.mul w.boundedB)
  derivF := v.derivF
  derivA t ht x := (v.derivA t ht x).mul (w.derivA t ht x)

def JetVariation.pressureRate {V : HeatJetFamily n} (v : JetVariation V l r)
    (m : ℝ) (d : Fin (n+1) → ℝ) (q : ℝ → Fin (n+1) → ℝ) (t : ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  signedVarianceDerivative m (V.J t).F (V.J t).G (V.J t).H d (q t) x+
    varianceTest m (V.J t).F (v.D t) (q t) x

def JetVariation.testRate {V : HeatJetFamily n} (v : JetVariation V l r)
    (m : ℝ) (d : Fin (n+1) → ℝ) (q : ℝ → Fin (n+1) → ℝ) (t : ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  (V.J t).signedVarianceRate m d (q t) x + varianceTest m (V.J t).F (v.B t) (q t) x+
    m*(varianceTest m (V.J t).F (fun y => (V.J t).A y*v.D t y) (q t) x-
      varianceTest m (V.J t).F (V.J t).A (q t) x*varianceTest m (V.J t).F (v.D t) (q t) x)

theorem JetVariation.continuous_pressureRate {V : HeatJetFamily n} (v : JetVariation V l r)
    (m : ℝ) (d : Fin (n+1) → ℝ) {q : ℝ → Fin (n+1) → ℝ} (hq : Continuous q) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => v.pressureRate m d q p.1 p.2) := by
  exact (V.continuous_signedVarianceDerivative m d hq).add
    (dynamic_varianceTest_joint_continuous (A := v.D) V.lipschitz V.continuousF
      v.continuousD v.boundedD m hq)

theorem JetVariation.bounded_pressureRate {V : HeatJetFamily n} (v : JetVariation V l r)
    (m : ℝ) (d : Fin (n+1) → ℝ) (q : ℝ → Fin (n+1) → ℝ) :
    AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => v.pressureRate m d q p.1 p.2) := by
  exact (V.bounded_signedVarianceDerivative m d q).add
    (dynamic_varianceTest_absBounded (A := v.D) V.lipschitz v.continuousD v.boundedD m q)

theorem JetVariation.continuous_testRate {V : HeatJetFamily n} (v : JetVariation V l r)
    (m : ℝ) (d : Fin (n+1) → ℝ) {q : ℝ → Fin (n+1) → ℝ} (hq : Continuous q) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => v.testRate m d q p.1 p.2) := by
  have hA := dynamic_varianceTest_joint_continuous (A := fun t => (V.J t).A)
    V.lipschitz V.continuousF V.continuousA V.boundedA m hq
  have hB := dynamic_varianceTest_joint_continuous (A := v.B) V.lipschitz V.continuousF
    v.continuousB v.boundedB m hq
  have hD := dynamic_varianceTest_joint_continuous (A := v.D) V.lipschitz V.continuousF
    v.continuousD v.boundedD m hq
  have hAD := dynamic_varianceTest_joint_continuous (A := fun t y => (V.J t).A y*v.D t y)
    V.lipschitz V.continuousF (V.continuousA.mul v.continuousD) (V.boundedA.mul v.boundedD) m hq
  exact ((V.continuous_signedVarianceRate m d hq).add hB).add ((hAD.sub (hA.mul hD)).const_mul m)

theorem JetVariation.bounded_testRate {V : HeatJetFamily n} (v : JetVariation V l r)
    (m : ℝ) (d : Fin (n+1) → ℝ) (q : ℝ → Fin (n+1) → ℝ) :
    AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => v.testRate m d q p.1 p.2) := by
  have hA := dynamic_varianceTest_absBounded (A := fun t => (V.J t).A)
    V.lipschitz V.continuousA V.boundedA m q
  have hB := dynamic_varianceTest_absBounded (A := v.B) V.lipschitz v.continuousB v.boundedB m q
  have hD := dynamic_varianceTest_absBounded (A := v.D) V.lipschitz v.continuousD v.boundedD m q
  have hAD := dynamic_varianceTest_absBounded (A := fun t y => (V.J t).A y*v.D t y)
    V.lipschitz (V.continuousA.mul v.continuousD) (V.boundedA.mul v.boundedD) m q
  exact ((V.bounded_signedVarianceRate m d q).add hB).add ((hAD.sub (hA.mul hD)).const_mul m)

 
def JetVariation.varianceEvolve {V : HeatJetFamily n}
    (v : JetVariation V l r) {m : ℝ} (hm : 0 < m) (q d : Fin (n+1) → ℝ)
    (hpos : ∀ t ∈ Ioo l r, ∀ i, 0 < q i+t*d i) :
    JetVariation (V.varianceEvolve hm (q := fun t i => q i+t*d i)
      (continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const))) l r where
  D := v.pressureRate m d (fun t i => q i+t*d i)
  B := v.testRate m d (fun t i => q i+t*d i)
  continuousD := v.continuous_pressureRate m d
    (continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const))
  continuousB := v.continuous_testRate m d
    (continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const))
  boundedD := v.bounded_pressureRate m d _
  boundedB := v.bounded_testRate m d _
  derivF t ht x := hasDerivAt_dynamic_varianceContinuation
    V.lipschitz (fun t => (V.J t).smoothG) (fun t => (V.J t).smoothH)
    V.continuousF V.continuousG V.continuousH v.continuousD V.boundedG V.boundedH v.boundedD
    (fun s => (V.J s).derivF) (fun s => (V.J s).derivG) v.derivF q d hm ht (hpos t ht) x
  derivA t ht x := hasDerivAt_dynamic_varianceTest V v.continuousD v.continuousB
    v.boundedD v.boundedB v.derivF v.derivA q d ht (hpos t ht) x

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {n : ℕ}

theorem hasDerivAt_face_variance_test (J : HeatJet n)
    (q d : Fin (n+1) → ℝ) {t : ℝ} (ht : AffineVarianceRegular q d t)
    (m : ℝ) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => varianceTest m J.F J.A (fun i => q i+s*d i) x)
      (J.signedVarianceRate m d (fun i => q i+t*d i) x) t := by
  obtain ⟨l,r,htr,hface,haD,hA,hB⟩ := ht.amplitude_regular
  have hh := hasDerivAt_diagonal_heat_test J htr haD hA hB m x
  have he : (fun s => varianceTest m J.F J.A (fun i => q i+s*d i) x) =ᶠ[𝓝 t]
      (fun s => tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
        (fun z => J.F (x+(fun i => Real.sqrt (q i+s*d i))*z))
          (fun z => J.A (x+(fun i => Real.sqrt (q i+s*d i))*z))) := by
    filter_upwards [ht.eventually] with s hs
    exact varianceTest_eq J.lipschitz.continuous J.smoothA.continuous m hs.nonneg x
  apply (hh.congr_of_eventuallyEq he).congr_deriv
  unfold HeatJet.signedVarianceRate
  apply Finset.sum_congr rfl
  intro i _
  rw [varianceTest_eq J.lipschitz.continuous (J.smooth_testedInsertion m i).continuous m ht.nonneg,
    varianceTest_eq J.lipschitz.continuous J.smoothA.continuous m ht.nonneg,
    varianceTest_eq J.lipschitz.continuous (J.smooth_potentialInsertion m i).continuous m ht.nonneg]
  rw [ht.sqrt_coefficient i]
  rfl

theorem hasDerivAt_face_varianceContinuation (J : HeatJet n)
    (q d : Fin (n+1) → ℝ) {t : ℝ} (ht : AffineVarianceRegular q d t)
    {m : ℝ} (hm : m ≠ 0) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => varianceContinuation m J.F (fun i => q i+s*d i) x)
      (signedVarianceDerivative m J.F J.G J.H d (fun i => q i+t*d i) x) t := by
  obtain ⟨l,r,htr,hface,haD,hA,hB⟩ := ht.amplitude_regular
  have hh := hasDerivAt_diagonal_heat_continuation J.lipschitz J.smoothG J.smoothH
    J.derivF J.derivG htr haD hA hB hm x
  have he : (fun s => varianceContinuation m J.F (fun i => q i+s*d i) x) =ᶠ[𝓝 t]
      (fun s => Real.log (∫ z, Real.exp (m*J.F (x+(fun i => Real.sqrt (q i+s*d i))*z))
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))/m) := by
    filter_upwards [ht.eventually] with s hs
    exact varianceContinuation_eq J.lipschitz.continuous m hs.nonneg x
  apply (hh.congr_of_eventuallyEq he).congr_deriv
  unfold signedVarianceDerivative
  apply Finset.sum_congr rfl
  intro i _
  rw [ht.sqrt_coefficient i,
    varianceTest_eq J.lipschitz.continuous (J.smoothH i).continuous m ht.nonneg,
    varianceTest_eq J.lipschitz.continuous (show Continuous (fun y => J.G i y ^ 2) from (J.smoothG i).continuous.pow 2) m ht.nonneg]

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

theorem hasDerivAt_face_dynamic_varianceContinuation {n : ℕ} (V : HeatJetFamily n)
    {D : ℝ → (Fin (n+1) → ℝ) → ℝ}
    (hcD : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => D p.1 p.2))
    (hbD : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => D p.1 p.2))
    {l r : ℝ}
    (hdF : ∀ s ∈ Ioo l r, ∀ y, HasDerivAt (fun q => (V.J q).F y) (D s y) s)
    (q d : Fin (n+1) → ℝ) {m t : ℝ} (hm : 0 < m)
    (ht : t ∈ Ioo l r) (hqt : AffineVarianceRegular q d t) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => varianceContinuation m (V.J s).F (fun i => q i+s*d i) x)
      (signedVarianceDerivative m (V.J t).F (V.J t).G (V.J t).H d (fun i => q i+t*d i) x+
        varianceTest m (V.J t).F (D t) (fun i => q i+t*d i) x) t := by
  obtain ⟨KD,hKD,bD⟩ := hbD
  choose KG hKG bG using V.boundedG
  choose KH hKH bH using V.boundedH
  let Q : ℝ × ℝ → Fin (n+1) → ℝ := fun p i => q i+p.1*d i
  have hQ : Continuous Q := continuous_pi fun i => continuous_const.add (continuous_fst.mul continuous_const)
  have hF' : ∀ p : ℝ × ℝ, LipschitzWith V.C (V.J p.2).F := fun p => V.lipschitz p.2
  have hcF' : Continuous (fun p : (ℝ × ℝ) × (Fin (n+1) → ℝ) => (V.J p.1.2).F p.2) :=
    V.continuousF.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hc₁ : Continuous (fun p : ℝ × ℝ =>
      signedVarianceDerivative m (V.J p.2).F (V.J p.2).G (V.J p.2).H d (Q p) x) := by
    apply continuous_finsetSum
    intro i _
    apply Continuous.const_mul
    apply Continuous.add
    · exact dynamic_varianceTest_continuous hF' hcF'
        ((V.continuousH i).comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
        (fun p y => bH i (p.2,y)) m hQ continuous_const
    · apply Continuous.const_mul
      exact dynamic_varianceTest_continuous (K := (KG i)^2) hF' hcF'
        (((V.continuousG i).comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)).pow 2)
        (fun p y => by
          rw [abs_sq]
          exact (sq_abs ((V.J p.2).G i y)) ▸ sq_le_sq₀ (abs_nonneg _) (hKG i) |>.mpr (bG i (p.2,y))) m hQ continuous_const
  have hc₂ : Continuous (fun p : ℝ × ℝ => varianceTest m (V.J p.2).F (D p.2) (Q p) x) :=
    dynamic_varianceTest_continuous hF' hcF'
      (hcD.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
      (fun p y => bD (p.2,y)) m hQ continuous_const
  have hp := hqt.eventually
  have hc₃ : ∀ᶠ p : ℝ × ℝ in 𝓝 (t,t),
      HasDerivAt (fun s => varianceContinuation m (V.J p.2).F (fun i => q i+s*d i) x)
        (signedVarianceDerivative m (V.J p.2).F (V.J p.2).G (V.J p.2).H d (fun i => q i+p.1*d i) x) p.1 := by
    filter_upwards [continuous_fst.continuousAt.tendsto.eventually hp] with p hp
    exact hasDerivAt_face_varianceContinuation (V.J p.2) q d hp hm.ne' x
  have hc₄ : ∀ᶠ p : ℝ × ℝ in 𝓝 (t,t),
      HasDerivAt (fun s => varianceContinuation m (V.J s).F (fun i => q i+p.1*d i) x)
        (varianceTest m (V.J p.2).F (D p.2) (fun i => q i+p.1*d i) x) p.2 := by
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds ht)] with p hp
    exact hasDerivAt_continuation_local hp hKD hm.ne'
      (fun s _ => ((V.lipschitz s).continuous.comp (continuous_const.add continuous_id)).measurable)
      ((hcD.comp (continuous_const.prodMk (continuous_const.add continuous_id))).measurable)
      (fun s hs z => hdF s hs (x+z)) (fun s _ z => bD (s,x+z))
      ((exponentialIncrement_gaussian (fun i => Real.toNNReal (q i+p.1*d i))).integrable_shift (V.lipschitz p.2) m x)
  have hchain := hasDerivAt_bivariate_chain
    (f := fun a b => varianceContinuation m (V.J b).F (fun i => q i+a*d i) x)
    (f₁ := fun a b => signedVarianceDerivative m (V.J b).F (V.J b).G (V.J b).H d (fun i => q i+a*d i) x)
    (f₂ := fun a b => varianceTest m (V.J b).F (D b) (fun i => q i+a*d i) x)
    hc₃ hc₄ hc₁.continuousAt hc₂.continuousAt (hasDerivAt_id t) (hasDerivAt_id t)
  simpa only [id_eq,mul_one] using hchain

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

theorem hasDerivAt_face_dynamic_varianceTest {n : ℕ} (V : HeatJetFamily n)
    {D B : ℝ → (Fin (n+1) → ℝ) → ℝ}
    (hcD : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => D p.1 p.2))
    (hcB : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => B p.1 p.2))
    (hbD : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => D p.1 p.2))
    (hbB : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => B p.1 p.2))
    {l r : ℝ}
    (hdF : ∀ s ∈ Ioo l r, ∀ y, HasDerivAt (fun q => (V.J q).F y) (D s y) s)
    (hdA : ∀ s ∈ Ioo l r, ∀ y, HasDerivAt (fun q => (V.J q).A y) (B s y) s)
    (q d : Fin (n+1) → ℝ) {m t : ℝ} (ht : t ∈ Ioo l r)
    (hqt : AffineVarianceRegular q d t) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => varianceTest m (V.J s).F (V.J s).A (fun i => q i+s*d i) x)
      ((V.J t).signedVarianceRate m d (fun i => q i+t*d i) x +
        varianceTest m (V.J t).F (B t) (fun i => q i+t*d i) x +
        m*(varianceTest m (V.J t).F (fun y => (V.J t).A y*D t y) (fun i => q i+t*d i) x -
          varianceTest m (V.J t).F (V.J t).A (fun i => q i+t*d i) x *
            varianceTest m (V.J t).F (D t) (fun i => q i+t*d i) x)) t := by
  obtain ⟨KD,hKD,bD⟩ := hbD
  obtain ⟨KB,hKB,bB⟩ := hbB
  obtain ⟨KA,hKA,bA⟩ := V.boundedA
  let Q : ℝ × ℝ → Fin (n+1) → ℝ := fun p i => q i+p.1*d i
  have hQ : Continuous Q := continuous_pi fun i => continuous_const.add (continuous_fst.mul continuous_const)
  have hF' : ∀ p : ℝ × ℝ, LipschitzWith V.C (V.J p.2).F := fun p => V.lipschitz p.2
  have hcF' : Continuous (fun p : (ℝ × ℝ) × (Fin (n+1) → ℝ) => (V.J p.1.2).F p.2) :=
    V.continuousF.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hcont (A : ℝ → (Fin (n+1) → ℝ) → ℝ)
      (hcA : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
      (hbA : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2)) :
      Continuous (fun p : ℝ × ℝ => varianceTest m (V.J p.2).F (A p.2) (Q p) x) := by
    obtain ⟨K,_,hb⟩ := hbA
    exact dynamic_varianceTest_continuous hF' hcF'
      (hcA.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
      (fun p y => hb (p.2,y)) m hQ continuous_const
  have hc₁ : Continuous (fun p : ℝ × ℝ => (V.J p.2).signedVarianceRate m d (Q p) x) := by
    apply continuous_finsetSum
    intro i _
    exact ((hcont (fun t => (V.J t).testedInsertion m i) (V.continuous_testedInsertion m i) (V.bounded_testedInsertion m i)).sub
      ((hcont (fun t => (V.J t).A) V.continuousA V.boundedA).mul
        (hcont (fun t => (V.J t).potentialInsertion m i) (V.continuous_potentialInsertion m i) (V.bounded_potentialInsertion m i)))).const_mul _
  have hc₂ : Continuous (fun p : ℝ × ℝ =>
      varianceTest m (V.J p.2).F (B p.2) (Q p) x+
        m*(varianceTest m (V.J p.2).F (fun y => (V.J p.2).A y*D p.2 y) (Q p) x-
          varianceTest m (V.J p.2).F (V.J p.2).A (Q p) x *
            varianceTest m (V.J p.2).F (D p.2) (Q p) x)) := by
    exact (hcont B hcB ⟨KB,hKB,bB⟩).add
      (((hcont (fun t y => (V.J t).A y*D t y) (V.continuousA.mul hcD) (V.boundedA.mul ⟨KD,hKD,bD⟩)).sub
        ((hcont (fun t => (V.J t).A) V.continuousA V.boundedA).mul (hcont D hcD ⟨KD,hKD,bD⟩))).const_mul m)
  have hp := hqt.eventually
  have hc₃ : ∀ᶠ p : ℝ × ℝ in 𝓝 (t,t),
      HasDerivAt (fun s => varianceTest m (V.J p.2).F (V.J p.2).A (fun i => q i+s*d i) x)
        ((V.J p.2).signedVarianceRate m d (Q p) x) p.1 := by
    filter_upwards [continuous_fst.continuousAt.tendsto.eventually hp] with p hp
    exact hasDerivAt_face_variance_test (V.J p.2) q d hp m x
  have hc₄ : ∀ᶠ p : ℝ × ℝ in 𝓝 (t,t),
      HasDerivAt (fun s => varianceTest m (V.J s).F (V.J s).A (Q p) x)
        (varianceTest m (V.J p.2).F (B p.2) (Q p) x+
          m*(varianceTest m (V.J p.2).F (fun y => (V.J p.2).A y*D p.2 y) (Q p) x-
            varianceTest m (V.J p.2).F (V.J p.2).A (Q p) x *
              varianceTest m (V.J p.2).F (D p.2) (Q p) x)) p.2 := by
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds ht)] with p hp
    exact hasDerivAt_tiltedMean_local hp hKD (add_nonneg hKA hKB)
      (fun s _ => ((V.lipschitz s).continuous.comp (continuous_const.add continuous_id)).measurable)
      ((hcD.comp (continuous_const.prodMk (continuous_const.add continuous_id))).measurable)
      (fun s _ => ((V.J s).smoothA.continuous.comp (continuous_const.add continuous_id)).measurable)
      ((hcB.comp (continuous_const.prodMk (continuous_const.add continuous_id))).measurable)
      (fun s hs z => hdF s hs (x+z)) (fun s hs z => hdA s hs (x+z))
      (fun s _ z => bD (s,x+z))
      (fun s _ z => (bA (s,x+z)).trans (le_add_of_nonneg_right hKB))
      (fun s _ z => (bB (s,x+z)).trans (le_add_of_nonneg_left hKA)) m
      ((exponentialIncrement_gaussian (fun i => Real.toNNReal (Q p i))).integrable_shift (V.lipschitz p.2) m x)
  have hchain := hasDerivAt_bivariate_chain
    (f := fun a b => varianceTest m (V.J b).F (V.J b).A (fun i => q i+a*d i) x)
    (f₁ := fun a b => (V.J b).signedVarianceRate m d (fun i => q i+a*d i) x)
    (f₂ := fun a b => varianceTest m (V.J b).F (B b) (fun i => q i+a*d i) x+
      m*(varianceTest m (V.J b).F (fun y => (V.J b).A y*D b y) (fun i => q i+a*d i) x-
        varianceTest m (V.J b).F (V.J b).A (fun i => q i+a*d i) x *
          varianceTest m (V.J b).F (D b) (fun i => q i+a*d i) x))
    hc₃ hc₄ hc₁.continuousAt hc₂.continuousAt (hasDerivAt_id t) (hasDerivAt_id t)
  simpa only [id_eq,mul_one,add_assoc] using hchain

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {n : ℕ} {l r : ℝ}

 
def JetVariation.faceVarianceEvolve {V : HeatJetFamily n}
    (v : JetVariation V l r) {m : ℝ} (hm : 0 < m) (q d : Fin (n+1) → ℝ)
    (hpos : ∀ t ∈ Ioo l r, ∀ i, 0 ≤ q i+t*d i) :
    JetVariation (V.varianceEvolve hm (q := fun t i => q i+t*d i)
      (continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const))) l r where
  D := v.pressureRate m d (fun t i => q i+t*d i)
  B := v.testRate m d (fun t i => q i+t*d i)
  continuousD := v.continuous_pressureRate m d
    (continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const))
  continuousB := v.continuous_testRate m d
    (continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const))
  boundedD := v.bounded_pressureRate m d _
  boundedB := v.bounded_testRate m d _
  derivF _t ht x := hasDerivAt_face_dynamic_varianceContinuation V
    v.continuousD v.boundedD v.derivF q d hm ht
    (affineVarianceRegular_of_nonneg hpos ht) x
  derivA _t ht x := hasDerivAt_face_dynamic_varianceTest V v.continuousD v.continuousB
    v.boundedD v.boundedB v.derivF v.derivA q d ht
    (affineVarianceRegular_of_nonneg hpos ht) x

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 

def ClockTree.faceWeightVariation {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {l r : ℝ} :
    {as : List PositiveMass} → (T : ClockTree S as) →
    (q d : ℕ → Fin (n+1) → ℝ) →
    (hpos : ∀ j t, t ∈ Ioo l r → ∀ i, 0 ≤ q j i+t*d j i) → (σ : T.Assignment) →
    JetVariation (T.weightFamily hw φ (fun j t i => q j i+t*d j i)
      (fun _ => continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const)) σ) l r
  | _, .leaf, _, _, _, σ => (spinWeightJet hw φ σ).constantVariation
  | _, .step a T, q, d, hp, σ =>
    (T.faceWeightVariation hw φ (fun j => q (j+1)) (fun j => d (j+1)) (fun j => hp (j+1)) σ).faceVarianceEvolve
      a.property (q 0) (d 0) (hp 0)
  | _, .fork T U, q, d, hp, σ =>
    (T.faceWeightVariation hw φ q d hp σ.1).productTest (U.faceWeightVariation hw φ q d hp σ.2)

theorem ClockTree.hasDerivAt_weight_fullNonnegativePath {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (q d : ℕ → Fin (n+1) → ℝ) {l r : ℝ}
    (hp : ∀ j t, t ∈ Ioo l r → ∀ i, 0 ≤ q j i+t*d j i)
    (σ : T.Assignment) {t : ℝ} (ht : t ∈ Ioo l r) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => T.weight w φ (fun j i => Real.toNNReal (q j i+s*d j i)) σ x)
      ((T.faceWeightVariation hw φ q d hp σ).B t x) t := by
  have h := (T.faceWeightVariation hw φ q d hp σ).derivA t ht x
  have he (s : ℝ) := (T.weightFamily_actual hw φ (fun j s i => q j i+s*d j i)
    (fun _ => continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const)) σ s).2
  simpa only [he] using h

 

theorem ClockTree.hasDerivAt_expect_fullNonnegativePath {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (q d : ℕ → Fin (n+1) → ℝ) {l r : ℝ}
    (hp : ∀ j t, t ∈ Ioo l r → ∀ i, 0 ≤ q j i+t*d j i)
    (P : T.Assignment → ℝ) {t : ℝ} (ht : t ∈ Ioo l r) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => T.expect w φ (fun j i => Real.toNNReal (q j i+s*d j i)) P x)
      (∑ σ, (T.faceWeightVariation hw φ q d hp σ).B t x*P σ) t := by
  exact HasDerivAt.fun_sum (u := Finset.univ) fun σ _ => (T.hasDerivAt_weight_fullNonnegativePath hw φ q d hp σ ht x).mul_const (P σ)

end SKFluctuations.Hierarchy

end

end OAI
