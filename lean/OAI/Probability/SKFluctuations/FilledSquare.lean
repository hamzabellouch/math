import Mathlib
import OAI.Probability.SKFluctuations.ClockDerivativeContinuous

namespace OAI

/-! Filled Square. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

def HeatJet.filledSquare {n : ℕ} (J : HeatJet n) {m : ℝ} (hm : 0 < m)
    (T t : ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  clockTest m (J.evolve hm (T-t)).F (J.evolve hm (T-t)).square.A t x

def HeatJet.filledEnergy {n : ℕ} (J : HeatJet n) {m : ℝ} (hm : 0 < m)
    (T t : ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  clockTest m (J.evolve hm (T-t)).F (J.evolve hm (T-t)).energy t x

 
theorem HeatJet.hasDerivAt_filledSquare {n : ℕ} (J : HeatJet n) {m : ℝ} (hm : 0 < m)
    {T t : ℝ} (ht : t ∈ Ioo 0 T) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => J.filledSquare hm T s x) (J.filledEnergy hm T t x) t := by
  let V := J.family hm
  have hF : ∀ s ∈ Ioo (0:ℝ) (T+1), ∀ y,
      HasDerivAt (fun q => V.square.J q |>.F y) ((V.J s).potentialRate m y) s := by
    intro s hs y
    exact J.evolve_time_F hm hs.1 y
  have hA : ∀ s ∈ Ioo (0:ℝ) (T+1), ∀ y,
      HasDerivAt (fun q => (V.square.J q).A y) (2*((V.J s).A y*(V.J s).testRate m y)) s := by
    intro s hs y
    apply ((J.evolve_time_A hm hs.1 y).pow 2).congr_deriv
    simp only [pow_one,Nat.cast_ofNat,Nat.reduceSub]
    change 2*(V.J s).A y*(V.J s).testRate m y = _
    ring
  have hbt : T-t ∈ Ioo (0:ℝ) (T+1) := by constructor <;> linarith [ht.1,ht.2]
  have hh := hasDerivAt_dynamic_clockTest (V.square.J)
    (D := fun s => (V.J s).potentialRate m)
    (B := fun s y => 2*((V.J s).A y*(V.J s).testRate m y)) m
    V.square.lipschitz V.square.continuousF V.square.continuousA
    (V.continuousPotentialRate m) ((V.continuousA.mul (V.continuousTestRate m)).const_mul 2)
    V.square.boundedA (V.boundedPotentialRate m) ((V.boundedA.mul (V.boundedTestRate m)).const_mul 2)
    (V.square.continuousP m) (V.square.continuousW m) (V.square.boundedP m) (V.square.boundedW m)
    hF hA x (hasDerivAt_id t) ((hasDerivAt_const t T).sub (hasDerivAt_id t)) ht.1 hbt
  apply hh.congr_deriv
  simpa only [Pi.sub_apply,id_eq,sub_zero,zero_sub,mul_one,mul_neg_one,sub_eq_add_neg,zero_add,V,HeatJetFamily.square,HeatJet.family,HeatJet.filledEnergy,HeatJet.square] using
    (J.evolve hm (T-t)).square_cancellation m t x

 theorem HeatJetFamily.continuousEnergy {n : ℕ} (V : HeatJetFamily n) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => (V.J p.1).energy p.2) :=
  continuous_finsetSum _ fun i _ => (V.continuousA₁ i).pow 2
 theorem HeatJetFamily.boundedEnergy {n : ℕ} (V : HeatJetFamily n) :
    AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => (V.J p.1).energy p.2) := by
  apply AbsBounded.sum
  intro i
  simpa only [pow_two] using (V.boundedA₁ i).mul (V.boundedA₁ i)

 theorem HeatJet.continuous_filledSquare {n : ℕ} (J : HeatJet n) {m : ℝ} (hm : 0 < m)
    (T : ℝ) (x : Fin (n+1) → ℝ) : Continuous (fun t => J.filledSquare hm T t x) := by
  let V := (J.family hm).square
  obtain ⟨K,_,hK⟩ := V.boundedA
  exact (dynamic_clockTest_continuous (F := fun s => (V.J s).F) (A := fun s => (V.J s).A)
    V.lipschitz V.continuousF V.continuousA (fun s y => hK (s,y)) m x).comp
      (continuous_id.prodMk (continuous_const.sub continuous_id))

 theorem HeatJet.continuous_filledEnergy {n : ℕ} (J : HeatJet n) {m : ℝ} (hm : 0 < m)
    (T : ℝ) (x : Fin (n+1) → ℝ) : Continuous (fun t => J.filledEnergy hm T t x) := by
  let V := J.family hm
  obtain ⟨K,_,hK⟩ := V.boundedEnergy
  exact (dynamic_clockTest_continuous (F := fun s => (V.J s).F) (A := fun s => (V.J s).energy)
    V.lipschitz V.continuousF V.continuousEnergy (fun s y => hK (s,y)) m x).comp
      (continuous_id.prodMk (continuous_const.sub continuous_id))

 theorem HeatJet.filledEnergy_nonneg {n : ℕ} (J : HeatJet n) {m : ℝ} (hm : 0 < m)
    (T t : ℝ) (x : Fin (n+1) → ℝ) : 0 ≤ J.filledEnergy hm T t x :=
  shiftedMean_nonneg (J.evolve hm (T-t)).energy_nonneg
    ((exponentialIncrement_gaussian (fun _ => Real.toNNReal t)).integrable_shift
      (J.evolve hm (T-t)).lipschitz m x)

 theorem HeatJet.filledSquare_zero {n : ℕ} (J : HeatJet n) {m : ℝ} (hm : 0 < m)
    (T : ℝ) (x : Fin (n+1) → ℝ) : J.filledSquare hm T 0 x = (clockTest m J.F J.A T x)^2 := by
  unfold HeatJet.filledSquare
  rw [clockTest_zero]
  simp only [HeatJet.square,HeatJet.evolve,sub_zero]

 theorem HeatJet.filledSquare_terminal {n : ℕ} (J : HeatJet n) {m : ℝ} (hm : 0 < m)
    (T : ℝ) (x : Fin (n+1) → ℝ) : J.filledSquare hm T T x = clockTest m J.F (fun y => (J.A y)^2) T x := by
  unfold HeatJet.filledSquare
  simp only [HeatJet.square,HeatJet.evolve,sub_self,clockTest_zero]
  have h0 : clockContinuation m J.F 0 = J.F := funext (clockContinuation_zero hm.ne')
  rw [h0]

 

theorem HeatJet.variance_eq_integral_energy {n : ℕ} (J : HeatJet n) {m : ℝ} (hm : 0 < m)
    {T : ℝ} (hT : 0 ≤ T) (x : Fin (n+1) → ℝ) :
    clockTest m J.F (fun y => (J.A y)^2) T x-(clockTest m J.F J.A T x)^2 =
      ∫ t in 0..T, J.filledEnergy hm T t x := by
  rw [← J.filledSquare_terminal hm T x,← J.filledSquare_zero hm T x]
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    (J.continuous_filledSquare hm T x).continuousOn
    (fun t ht => J.hasDerivAt_filledSquare hm ht x)
    ((J.continuous_filledEnergy hm T x).intervalIntegrable 0 T)).symm

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

theorem clockTest_zero_potential {ι : Type*} [Fintype ι] (A : (ι → ℝ) → ℝ)
    (m t : ℝ) (x : ι → ℝ) : clockTest m (fun _ => 0) A t x = clockRoot A t x := by
  simp [clockTest,shiftedMean,tiltedMean,clockRoot,zeroContinuation]

theorem clockTest_zero_mass {ι : Type*} [Fintype ι] (F A : (ι → ℝ) → ℝ)
    (t : ℝ) (x : ι → ℝ) : clockTest 0 F A t x = clockRoot A t x :=
  shiftedMean_zero F A x

theorem clockContinuation_zero_potential {ι : Type*} [Fintype ι] (m t : ℝ) :
    clockContinuation m (fun _ : ι → ℝ => 0) t = fun _ => 0 := by
  funext x
  simp [clockContinuation,shiftedContinuation]

theorem clockRoot_zero {ι : Type*} [Fintype ι] (t : ℝ) (x : ι → ℝ) :
    clockRoot (fun _ => 0) t x = 0 := by simp [clockRoot,zeroContinuation]

 

def HeatJet.erasePotential {n : ℕ} (J : HeatJet n) : HeatJet n where
  F := fun _ => 0
  G := fun _ _ => 0
  H := fun _ _ => 0
  A := J.A
  A₁ := J.A₁
  A₂ := J.A₂
  C := 0
  lipschitz := LipschitzWith.const _
  smoothA := J.smoothA
  smoothG _ := BddSmooth.const 0 0
  smoothH _ := BddSmooth.const 0 0
  smoothA₁ := J.smoothA₁
  smoothA₂ := J.smoothA₂
  derivF _ _ t := by simpa using hasDerivAt_const t (0:ℝ)
  derivG _ _ t := hasDerivAt_const t 0
  derivA := J.derivA
  derivA₁ := J.derivA₁

 def HeatJet.rootFilledSquare {n : ℕ} (J : HeatJet n) (T t : ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  clockRoot (fun y => (clockRoot J.A (T-t) y)^2) t x
 def HeatJet.rootFilledEnergy {n : ℕ} (J : HeatJet n) (T t : ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  clockRoot (fun y => ∑ i, (clockRoot (J.A₁ i) (T-t) y)^2) t x

 theorem HeatJet.erased_filledSquare {n : ℕ} (J : HeatJet n)
    (T t : ℝ) (x : Fin (n+1) → ℝ) :
    J.erasePotential.filledSquare (m := 1) zero_lt_one T t x = J.rootFilledSquare T t x := by
  unfold HeatJet.filledSquare HeatJet.rootFilledSquare
  dsimp only [HeatJet.square,HeatJet.evolve,HeatJet.erasePotential]
  rw [clockContinuation_zero_potential,clockTest_zero_potential]
  simp_rw [clockTest_zero_potential]

 theorem HeatJet.erased_filledEnergy {n : ℕ} (J : HeatJet n)
    (T t : ℝ) (x : Fin (n+1) → ℝ) :
    J.erasePotential.filledEnergy (m := 1) zero_lt_one T t x = J.rootFilledEnergy T t x := by
  unfold HeatJet.filledEnergy HeatJet.rootFilledEnergy
  change clockTest 1 (clockContinuation 1 (fun _ => 0) (T-t))
    (fun y => ∑ i, (clockGradient 1 (fun _ => 0) (fun _ => 0) J.A (J.A₁ i) (T-t) y)^2) t x = _
  rw [clockContinuation_zero_potential,clockTest_zero_potential]
  unfold clockGradient
  simp only [clockTest_zero_potential,mul_zero,clockRoot_zero,sub_zero,add_zero]

 theorem HeatJet.hasDerivAt_rootFilledSquare {n : ℕ} (J : HeatJet n)
    {T t : ℝ} (ht : t ∈ Ioo 0 T) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => J.rootFilledSquare T s x) (J.rootFilledEnergy T t x) t := by
  have hh := J.erasePotential.hasDerivAt_filledSquare (m := 1) zero_lt_one ht x
  simpa only [J.erased_filledEnergy,J.erased_filledSquare] using hh

 

theorem HeatJet.root_variance_eq_integral_energy {n : ℕ} (J : HeatJet n)
    {T : ℝ} (hT : 0 ≤ T) (x : Fin (n+1) → ℝ) :
    clockRoot (fun y => (J.A y)^2) T x-(clockRoot J.A T x)^2 =
      ∫ t in 0..T, J.rootFilledEnergy T t x := by
  have hh := J.erasePotential.variance_eq_integral_energy (m := 1) zero_lt_one hT x
  simp only [J.erased_filledEnergy] at hh
  simpa only [HeatJet.erasePotential,clockTest_zero_potential] using hh

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem BddSmooth.affine {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D] {r : ℕ} {f : E → ℝ} (hf : BddSmooth r f)
    (L : D →L[ℝ] E) (x : E) : BddSmooth r (fun z => f (x+L z)) := by
  induction r generalizing f with
  | zero =>
    obtain ⟨B,hB,hb⟩ := hf.bound
    exact ⟨hf.continuous.comp (continuous_const.add L.continuous),B,hB,fun z => hb _⟩
  | succ r ih =>
    refine ⟨ih hf.1,fun v => ?_⟩
    obtain ⟨g,hg,hd⟩ := hf.2 (L v)
    refine ⟨fun z => g (x+L z),ih hg,fun z t => ?_⟩
    simpa only [map_add,map_smul,add_assoc] using hd (x+L z) t

 

noncomputable def HeatJet.ofTest {n : ℕ} (F A : (Fin (n+1) → ℝ) → ℝ)
    (G H : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ) {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 2 A)
    (hG : ∀ i, BddSmooth 0 (G i)) (hH : ∀ i, BddSmooth 0 (H i))
    (hdF : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v)) (∑ i, v i*G i (x+t • v)) t)
    (hdG : ∀ i x t, HasDerivAt (fun s : ℝ => G i (x+s • Pi.single i 1)) (H i (x+t • Pi.single i 1)) t) : HeatJet n where
  F := F
  A := A
  G := G
  H := H
  A₁ i y := lineDeriv ℝ A y (Pi.single i 1)
  A₂ i y := lineDeriv ℝ (fun z => lineDeriv ℝ A z (Pi.single i 1)) y (Pi.single i 1)
  C := C
  lipschitz := hF
  smoothA := hA.down.down
  smoothG := hG
  smoothH := hH
  smoothA₁ i := (hA.lineDeriv_smooth (Pi.single i 1)).down
  smoothA₂ i := (hA.lineDeriv_smooth (Pi.single i 1)).lineDeriv_smooth (Pi.single i 1)
  derivF := hdF
  derivG := hdG
  derivA x v t := by
    rw [← hA.down.lineDeriv_pi]
    exact hA.down.hasDerivAt_line x v t
  derivA₁ i x t := (hA.lineDeriv_smooth (Pi.single i 1)).hasDerivAt_line x (Pi.single i 1) t

variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

 

noncomputable def gaussianFeatureJet {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ)
    (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) : HeatJet n := by
  let C := (gaussianHierarchy_regular hw φ steps ha 0).1.choose
  have hC : LipschitzWith C (gaussianHierarchy w φ steps) := (gaussianHierarchy_regular hw φ steps ha 0).1.choose_spec
  let F := fun y => gaussianHierarchy w φ steps (x+L y)
  let M := fun y => gaussianHierarchyMean w φ A steps (x+L y)
  let G := fun i y => gaussianHierarchyMean w φ (fun σ => φ σ (L (Pi.single i 1))) steps (x+L y)
  let H := fun i y => gaussianHierarchyResponse w φ (fun σ => φ σ (L (Pi.single i 1)))
    (L (Pi.single i 1)) steps (x+L y)
  have hF : LipschitzWith (C*(1*‖L‖₊)) F :=
    hC.comp ((isometry_add_left x).lipschitzWith.comp L.lipschitzWith)
  have hA := (gaussianHierarchyMean_smooth hw φ A steps ha 2).affine L x
  have hG i := (gaussianHierarchyMean_smooth hw φ (fun σ => φ σ (L (Pi.single i 1))) steps ha 0).affine_zero L x
  have hH i := (gaussianHierarchyResponse_smooth hw φ (fun σ => φ σ (L (Pi.single i 1)))
    (L (Pi.single i 1)) steps ha 0).affine_zero L x
  have hd := gaussianHierarchy_linear_feature_derivatives hw φ L steps ha x
  exact HeatJet.ofTest F M G H hF hA hG hH hd.1 hd.2

 theorem gaussianFeatureJet_F {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ)
    (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    (gaussianFeatureJet hw φ A L steps ha x).F = fun y => gaussianHierarchy w φ steps (x+L y) := rfl
 theorem gaussianFeatureJet_A {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ)
    (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    (gaussianFeatureJet hw φ A L steps ha x).A = fun y => gaussianHierarchyMean w φ A steps (x+L y) := rfl

 

 theorem gaussianFeatureJet_A₁ {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ)
    (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) (i : Fin (n+1)) (y : Fin (n+1) → ℝ) :
    (gaussianFeatureJet hw φ A L steps ha x).A₁ i y =
      gaussianHierarchyResponse w φ A (L (Pi.single i 1)) steps (x+L y) := by
  change lineDeriv ℝ (fun z => gaussianHierarchyMean w φ A steps (x+L z)) y (Pi.single i 1) = _
  apply HasLineDerivAt.lineDeriv
  have hh := gaussianHierarchyMean_hasDerivAt hw φ A steps ha (x+L y) (L (Pi.single i 1)) 0
  simpa only [HasLineDerivAt,map_add,map_smul,add_assoc,zero_smul,add_zero] using hh

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

 
noncomputable def replicaFeatureJet {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ}
    (ha : OrderedSteps a steps) (P : T.Assignment → ℝ) (x : ι → ℝ) : HeatJet n := by
  let J := gaussianFeatureJet hw φ (fun _ => 0) L steps ha x
  exact HeatJet.ofTest J.F (fun y => T.expect w φ P (x+L y)) J.G J.H
    J.lipschitz ((T.expect_smooth hw φ ha P 2).affine L x) J.smoothG J.smoothH J.derivF J.derivG

 theorem replicaFeatureJet_F {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ}
    (ha : OrderedSteps a steps) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    (replicaFeatureJet hw φ L T ha P x).F = fun y => gaussianHierarchy w φ steps (x+L y) := rfl

 theorem replicaFeatureJet_A {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ}
    (ha : OrderedSteps a steps) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    (replicaFeatureJet hw φ L T ha P x).A = fun y => T.expect w φ P (x+L y) := rfl

 theorem replicaFeatureJet_A₁ {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ}
    (ha : OrderedSteps a steps) (P : T.Assignment → ℝ) (x : ι → ℝ)
    (i : Fin (n+1)) (y : Fin (n+1) → ℝ) :
    (replicaFeatureJet hw φ L T ha P x).A₁ i y =
      ReplicaTree.sourceJet w φ a [L (Pi.single i 1)] T P (x+L y) := by
  change lineDeriv ℝ (fun z => T.expect w φ P (x+L z)) y (Pi.single i 1) = _
  apply HasLineDerivAt.lineDeriv
  have hh := ReplicaTree.sourceJet_hasDerivAt hw φ [] T ha P (L (Pi.single i 1)) (x+L y) 0
  simpa only [HasLineDerivAt,ReplicaTree.sourceJet,map_add,map_smul,add_assoc,zero_smul,add_zero,List.nil_append] using hh

 theorem replicaFeatureJet_A₂ {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ}
    (ha : OrderedSteps a steps) (P : T.Assignment → ℝ) (x : ι → ℝ)
    (i : Fin (n+1)) (y : Fin (n+1) → ℝ) :
    (replicaFeatureJet hw φ L T ha P x).A₂ i y =
      ReplicaTree.sourceJet w φ a [L (Pi.single i 1),L (Pi.single i 1)] T P (x+L y) := by
  change lineDeriv ℝ (fun z => (replicaFeatureJet hw φ L T ha P x).A₁ i z) y (Pi.single i 1) = _
  simp_rw [replicaFeatureJet_A₁]
  apply HasLineDerivAt.lineDeriv
  have hh := ReplicaTree.sourceJet_hasDerivAt hw φ [L (Pi.single i 1)] T ha P
    (L (Pi.single i 1)) (x+L y) 0
  simpa only [HasLineDerivAt,map_add,map_smul,add_assoc,zero_smul,add_zero,List.cons_append,List.nil_append] using hh

namespace ReplicaTree

 
noncomputable def powerTrace (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) (a : ℝ) (P : T.Assignment → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, powerJet w φ a [L (Pi.single i 1),L (Pi.single i 1)] T P x

 theorem powerTrace_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ}
    (ha : OrderedSteps a steps) (P : T.Assignment → ℝ) (r : ℕ) :
    BddSmooth r (T.powerTrace w φ L a P) :=
  BddSmooth.sum Finset.univ (fun _ _ => powerJet_smooth hw φ _ T ha P r)

 theorem powerTrace_eq_testedHeatTrace {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ}
    (ha : OrderedSteps a steps) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    let J := replicaFeatureJet hw φ L T ha P x
    (fun y => T.powerTrace w φ L a P (x+L y)) = testedHeatTrace a J.G J.H J.A J.A₁ J.A₂ := by
  dsimp only
  funext y
  unfold powerTrace testedHeatTrace
  apply Finset.sum_congr rfl
  intro i _
  rw [replicaFeatureJet_A₁,replicaFeatureJet_A₂,powerJet_two_eq hw φ T ha]
  rfl

 theorem powerTrace_one_eq_potentialHeatTrace {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ}
    (ha : OrderedSteps a steps) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    let J := replicaFeatureJet hw φ L T ha P x
    (fun y => T.powerTrace w φ L a (fun _ => 1) (x+L y)) = potentialHeatTrace a J.G J.H := by
  dsimp only
  funext y
  unfold powerTrace potentialHeatTrace
  apply Finset.sum_congr rfl
  intro i _
  rw [powerJet_constant_two hw φ T ha]
  rfl

 

 theorem hasDerivWithinAt_linearClockTest {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ}
    (ha : OrderedSteps a steps) (P : T.Assignment → ℝ) (x : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => linearClockTest L a (gaussianHierarchy w φ steps) (T.expect w φ P) s x)
      ((1/2:ℝ)*(linearClockTest L a (gaussianHierarchy w φ steps) (T.powerTrace w φ L a P) t x-
        linearClockTest L a (gaussianHierarchy w φ steps) (T.expect w φ P) t x*
          linearClockTest L a (gaussianHierarchy w φ steps) (T.powerTrace w φ L a (fun _ => 1)) t x)) (Ici 0) t := by
  let J := replicaFeatureJet hw φ L T ha P x
  have h := hasDerivWithinAt_clockTest J.lipschitz J.smoothA J.smoothG J.smoothH J.smoothA₁ J.smoothA₂
    J.derivF J.derivG J.derivA J.derivA₁ a 0 ht
  have hF := (gaussianHierarchy_regular hw φ steps ha 0).1.choose_spec.continuous
  have hA := (T.expect_smooth hw φ ha P 0).continuous
  have hP := (T.powerTrace_smooth hw φ L ha P 0).continuous
  have h1 := (T.powerTrace_smooth hw φ L ha (fun _ => 1) 0).continuous
  rw [← T.powerTrace_eq_testedHeatTrace hw φ L ha P x,
    ← T.powerTrace_one_eq_potentialHeatTrace hw φ L ha P x] at h
  simp only [J,replicaFeatureJet_F,replicaFeatureJet_A] at h
  simpa only [linearClockTest_eq L hF hA,linearClockTest_eq L hF hP,linearClockTest_eq L hF h1] using h

end ReplicaTree
end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

 theorem powerJet_two_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) {P : T.Assignment → ℝ} {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hP : ∀ σ, |P σ| ≤ C) (v : ι → ℝ)
    (hB : ∀ σ, |φ σ v| ≤ D) (x : ι → ℝ) :
    |powerJet w φ a [v,v] T P x| ≤ 4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*C*D^2 := by
  have h := powerJet_abs_le hw φ [v,v] T ha (le_refl T.leaves) hC hD hP
    (fun u hu => by
      have huv : u = v := by simpa using hu
      simpa only [huv] using hB) x
  convert h using 1
  simp only [List.length_cons,List.length_nil,attachmentCount,
    Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,mul_one]
  ring

 theorem powerTrace_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    {P : T.Assignment → ℝ} {C : ℝ} (D : Fin (n+1) → ℝ)
    (hC : 0 ≤ C) (hD : ∀ i, 0 ≤ D i) (hP : ∀ σ, |P σ| ≤ C)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i) (x : ι → ℝ) :
    |T.powerTrace w φ L a P x| ≤ 4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*C*∑ i, (D i)^2 := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => powerJet_two_abs_le hw φ T ha hC (hD i) hP _ (hB i) x

 theorem clock_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    {P : T.Assignment → ℝ} {C : ℝ} (hP : ∀ σ, |P σ| ≤ C) (t : ℝ) (x : ι → ℝ) :
    |linearClockTest L a (gaussianHierarchy w φ steps) (T.expect w φ P) t x| ≤ C := by
  obtain ⟨K,hF⟩ := (gaussianHierarchy_regular hw φ steps ha 0).1
  exact abs_tiltedMean_le ((T.expect_smooth hw φ ha P 0).continuous.comp (continuous_const.add continuous_id)).measurable
    ((exponentialIncrement_linearGaussian L (Real.toNNReal t)).integrable_shift hF a x)
    (fun z => T.expect_abs_le hw φ ha hP (x+z))

 theorem clock_powerTrace_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    {P : T.Assignment → ℝ} {C : ℝ} (D : Fin (n+1) → ℝ)
    (hC : 0 ≤ C) (hD : ∀ i, 0 ≤ D i) (hP : ∀ σ, |P σ| ≤ C)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i) (t : ℝ) (x : ι → ℝ) :
    |linearClockTest L a (gaussianHierarchy w φ steps) (T.powerTrace w φ L a P) t x| ≤
      4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*C*∑ i, (D i)^2 := by
  obtain ⟨K,hF⟩ := (gaussianHierarchy_regular hw φ steps ha 0).1
  exact abs_tiltedMean_le ((T.powerTrace_smooth hw φ L ha P 0).continuous.comp (continuous_const.add continuous_id)).measurable
    ((exponentialIncrement_linearGaussian L (Real.toNNReal t)).integrable_shift hF a x)
    (fun z => T.powerTrace_abs_le hw φ L ha D hC hD hP hB (x+z))

noncomputable def clockResponse (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) (a : ℝ) (P : T.Assignment → ℝ) (t : ℝ) (x : ι → ℝ) : ℝ :=
  (1/2:ℝ)*(linearClockTest L a (gaussianHierarchy w φ steps) (T.powerTrace w φ L a P) t x-
        linearClockTest L a (gaussianHierarchy w φ steps) (T.expect w φ P) t x*
          linearClockTest L a (gaussianHierarchy w φ steps) (T.powerTrace w φ L a (fun _ => 1)) t x)

 theorem clockResponse_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    {P : T.Assignment → ℝ} {C : ℝ} (D : Fin (n+1) → ℝ)
    (hC : 0 ≤ C) (hD : ∀ i, 0 ≤ D i) (hP : ∀ σ, |P σ| ≤ C)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i) (t : ℝ) (x : ι → ℝ) :
    |T.clockResponse w φ L a P t x| ≤ 4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*C*∑ i, (D i)^2 := by
  have h1 := T.clock_powerTrace_abs_le hw φ L ha D hC hD hP hB t x
  have h2 := T.clock_abs_le hw φ L ha hP t x
  have h3 := T.clock_powerTrace_abs_le hw φ L ha (P := fun _ => 1) (C := 1) D (by norm_num) hD
    (fun _ => by norm_num) hB t x
  have hn : 0 ≤ 4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*1*∑ i, (D i)^2 := by positivity
  dsimp only [clockResponse]
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  apply (mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num : (0:ℝ) ≤ 1/2)).trans
  rw [abs_mul]
  have hh := mul_le_mul h2 h3 (abs_nonneg _) hC
  nlinarith

 

 theorem clock_lipschitz {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    {P : T.Assignment → ℝ} {C : ℝ} (D : Fin (n+1) → ℝ)
    (hC : 0 ≤ C) (hD : ∀ i, 0 ≤ D i) (hP : ∀ σ, |P σ| ≤ C)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (x : ι → ℝ) :
    |linearClockTest L a (gaussianHierarchy w φ steps) (T.expect w φ P) t x-
       linearClockTest L a (gaussianHierarchy w φ steps) (T.expect w φ P) s x| ≤
      (4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*C*∑ i, (D i)^2)*|t-s| := by
  exact (convex_Ici (0:ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => T.hasDerivWithinAt_linearClockTest hw φ L ha P x hz)
    (fun z _ => T.clockResponse_abs_le hw φ L ha D hC hD hP hB z x) hs ht

end SKFluctuations.Hierarchy.ReplicaTree

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

 
structure ParametricTest (l r K : ℝ) (A B : ℝ → (ι → ℝ) → ℝ) : Prop where
  nonneg : 0 ≤ K
  continuous : ∀ t ∈ Ioo l r, Continuous (A t)
  response_continuous : ∀ t ∈ Ioo l r, Continuous (B t)
  bounded : ∀ t ∈ Ioo l r, ∀ x, |A t x| ≤ K
  response_bounded : ∀ t ∈ Ioo l r, ∀ x, |B t x| ≤ K
  derivative : ∀ t ∈ Ioo l r, ∀ x, HasDerivAt (fun s => A s x) (B t x) t

 theorem ParametricTest.smooth0 {l r K : ℝ} {A B : ℝ → (ι → ℝ) → ℝ}
    (h : ParametricTest l r K A B) {t : ℝ} (ht : t ∈ Ioo l r) : BddSmooth 0 (A t) :=
  ⟨h.continuous t ht,K,h.nonneg,h.bounded t ht⟩

 theorem ParametricTest.response_smooth0 {l r K : ℝ} {A B : ℝ → (ι → ℝ) → ℝ}
    (h : ParametricTest l r K A B) {t : ℝ} (ht : t ∈ Ioo l r) : BddSmooth 0 (B t) :=
  ⟨h.response_continuous t ht,K,h.nonneg,h.response_bounded t ht⟩

 theorem ParametricRegular.response_smooth0 {l r K : ℝ} {F D : ℝ → (ι → ℝ) → ℝ}
    (h : ParametricRegular l r K F D) {t : ℝ} (ht : t ∈ Ioo l r) : BddSmooth 0 (D t) :=
  ⟨h.continuous t ht,K,h.nonneg,h.bounded t ht⟩

 omit [Fintype ι] in
 theorem ParametricTest.mul {l r K J : ℝ} {A B C D : ℝ → (ι → ℝ) → ℝ}
    (h : ParametricTest l r K A B) (g : ParametricTest l r J C D) :
    ParametricTest l r (2*K*J) (fun t x => A t x*C t x)
      (fun t x => B t x*C t x+A t x*D t x) := by
  have hK := h.nonneg
  have hJ := g.nonneg
  have hb {t : ℝ} (ht : t ∈ Ioo l r) (x : ι → ℝ) : |A t x*C t x| ≤ K*J := by
    rw [abs_mul]; exact mul_le_mul (h.bounded t ht x) (g.bounded t ht x) (abs_nonneg _) h.nonneg
  refine ⟨by positivity,fun t ht => (h.continuous t ht).mul (g.continuous t ht),
    fun t ht => ((h.response_continuous t ht).mul (g.continuous t ht)).add
      ((h.continuous t ht).mul (g.response_continuous t ht)),?_,?_,?_⟩
  · intro t ht x
    exact (hb ht x).trans (by nlinarith [mul_nonneg h.nonneg g.nonneg])
  · intro t ht x
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul]
    have h1 := mul_le_mul (h.response_bounded t ht x) (g.bounded t ht x) (abs_nonneg _) h.nonneg
    have h2 := mul_le_mul (h.bounded t ht x) (g.response_bounded t ht x) (abs_nonneg _) h.nonneg
    linarith
  · exact fun t ht x => (h.derivative t ht x).mul (g.derivative t ht x)

 
noncomputable def tiltedResponse (q : ι → ℝ≥0) (m : ℝ) (F D A B : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  let ν := Measure.pi fun i => gaussianReal 0 (q i)
  shiftedMean ν m F B x + m*(shiftedMean ν m F (fun y => A y*D y) x-
    shiftedMean ν m F A x*shiftedMean ν m F D x)

 theorem ParametricTest.step {l r K J : ℝ} {F D A B : ℝ → (ι → ℝ) → ℝ}
    (hF : ParametricRegular l r J F D) (h : ParametricTest l r K A B)
    (q : ι → ℝ≥0) (m : ℝ) :
    ParametricTest l r (K+2*|m| *K*J)
      (fun t => shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m (F t) (A t))
      (fun t => tiltedResponse q m (F t) (D t) (A t) (B t)) := by
  have hK := h.nonneg
  have hJ := hF.nonneg
  let ν := Measure.pi fun i => gaussianReal 0 (q i)
  have hi (t) (ht : t ∈ Ioo l r) (x : ι → ℝ) :=
    (exponentialIncrement_gaussian q).integrable_shift (hF.spatial t ht).choose_spec m x
  have hmean (t) (ht : t ∈ Ioo l r) {V : (ι → ℝ) → ℝ} {C : ℝ}
      (hc : Continuous V) (hb : ∀ x, |V x| ≤ C) (x : ι → ℝ) :
      |shiftedMean ν m (F t) V x| ≤ C :=
    abs_tiltedMean_le (hc.comp (continuous_const.add continuous_id)).measurable (hi t ht x)
      (fun z => hb (x+z))
  have hcont (t) (ht : t ∈ Ioo l r) {V : (ι → ℝ) → ℝ} (hV : BddSmooth 0 V) :
      Continuous (shiftedMean ν m (F t) V) := by
    obtain ⟨C,hC⟩ := hF.spatial t ht
    obtain ⟨B,hB,hb⟩ := hV.bound
    exact continuous_shiftedMean hC hV.continuous hB hb (hi t ht)
  refine ⟨by positivity,?_,?_,?_,?_,?_⟩
  · intro t ht
    exact hcont t ht (h.smooth0 ht)
  · intro t ht
    exact (hcont t ht (h.response_smooth0 ht)).add
      (((hcont t ht ((h.smooth0 ht).mul (hF.response_smooth0 ht))).sub
        ((hcont t ht (h.smooth0 ht)).mul (hcont t ht (hF.response_smooth0 ht)))).const_mul m)
  · intro t ht x
    exact (hmean t ht (h.continuous t ht) (h.bounded t ht) x).trans (le_add_of_nonneg_right (by positivity))
  · intro t ht x
    have hb := hmean t ht (h.response_continuous t ht) (h.response_bounded t ht) x
    have ha := hmean t ht (h.continuous t ht) (h.bounded t ht) x
    have hd := hmean t ht (hF.continuous t ht) (hF.bounded t ht) x
    have had := hmean t ht ((h.continuous t ht).mul (hF.continuous t ht))
      (fun y => show |A t y*D t y| ≤ K*J by
        rw [abs_mul]; exact mul_le_mul (h.bounded t ht y) (hF.bounded t ht y) (abs_nonneg _) h.nonneg) x
    change |shiftedMean ν m (F t) (fun y => A t y*D t y) x| ≤ K*J at had
    change |_+m*(_-_)| ≤ _
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    have hsub := abs_sub (shiftedMean ν m (F t) (fun y => A t y*D t y) x)
      (shiftedMean ν m (F t) (A t) x*shiftedMean ν m (F t) (D t) x)
    rw [abs_mul] at hsub
    have hh := mul_le_mul ha hd (abs_nonneg _) h.nonneg
    have hsub' : |shiftedMean ν m (F t) (fun y => A t y*D t y) x-
        shiftedMean ν m (F t) (A t) x*shiftedMean ν m (F t) (D t) x| ≤ 2*K*J := by linarith
    have hx := mul_le_mul_of_nonneg_left hsub' (abs_nonneg m)
    nlinarith
  · intro t ht x
    exact hasDerivAt_tiltedMean_local ht hF.nonneg h.nonneg
      (fun s hs => ((hF.spatial s hs).choose_spec.continuous.comp (continuous_const.add continuous_id)).measurable)
      ((hF.continuous t ht).comp (continuous_const.add continuous_id)).measurable
      (fun s hs => ((h.continuous s hs).comp (continuous_const.add continuous_id)).measurable)
      ((h.response_continuous t ht).comp (continuous_const.add continuous_id)).measurable
      (fun s hs z => hF.derivative s hs (x+z)) (fun s hs z => h.derivative s hs (x+z))
      (fun s hs z => hF.bounded s hs (x+z)) (fun s hs z => h.bounded s hs (x+z))
      (fun s hs z => h.response_bounded s hs (x+z)) m (hi t ht x)

end SKFluctuations.Hierarchy

end

end OAI
