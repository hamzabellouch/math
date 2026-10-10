import Mathlib
import OAI.Probability.SKFluctuations.CavityClockZero

namespace OAI

/-! Tree Root Variation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 
def covarianceDifference {ι : Type*} (q : ℕ → ι → ℝ) (j : ℕ) (i : ι) : ℝ :=
  q (j+1) i-q j i

theorem cumulativeIncrements_affine {ι : Type*} (q d : ℕ → ι → ℝ) (t : ℝ) :
    cumulativeIncrements (fun i => q 0 i+t*d 0 i)
      (fun j i => q (j+1) i+t*d (j+1) i) =
    fun j i => Real.toNNReal (covarianceDifference q j i+t*covarianceDifference d j i) := by
  funext j i
  cases j <;> simp only [cumulativeIncrements,covarianceDifference] <;> congr 1 <;> ring

def ClockTree.cumulativeFamily {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (q d : ℕ → Fin (n+1) → ℝ) (σ : T.Assignment) : HeatJetFamily n :=
  T.weightFamily hw φ
    (fun j t i => covarianceDifference q j i+t*covarianceDifference d j i)
    (fun _ => continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const)) σ

def ClockTree.cumulativeVariation {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (q d : ℕ → Fin (n+1) → ℝ) {l r : ℝ}
    (hp : ∀ t ∈ Ioo l r, ∀ i, Monotone (fun j => q j i+t*d j i)) (σ : T.Assignment) :
    JetVariation (T.cumulativeFamily hw φ q d σ) l r :=
  T.faceWeightVariation hw φ (covarianceDifference q) (covarianceDifference d)
    (fun j t ht i => by
      have hh := hp t ht i (Nat.le_succ j)
      dsimp [covarianceDifference]
      linarith) σ

theorem ClockTree.cumulativeFamily_actual {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (q d : ℕ → Fin (n+1) → ℝ) (σ : T.Assignment) (t : ℝ) :
    ((T.cumulativeFamily hw φ q d σ).J t).A =
      T.weight w φ (cumulativeIncrements (fun i => q 0 i+t*d 0 i)
        (fun j i => q (j+1) i+t*d (j+1) i)) σ := by
  rw [cumulativeIncrements_affine]
  exact (T.weightFamily_actual hw φ _ _ σ t).2

 

theorem ClockTree.hasDerivAt_disorderWeight_fullPath {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (v : Fin (n+1) → ℝ) (q d : ℕ → Fin (n+1) → ℝ) {l r : ℝ}
    (hp : ∀ t ∈ Ioo l r, ∀ i, Monotone (fun j => q j i+t*d j i))
    (hroot : ∀ t ∈ Ioo l r, ∀ i, v i ≤ q 0 i+t*d 0 i)
    (σ : T.Assignment) {t : ℝ} (ht : t ∈ Ioo l r) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => T.disorderWeight w φ v (fun j i => q j i+s*d j i) σ x)
      ((T.cumulativeVariation hw φ q d hp σ).testRate 0 (d 0)
        (fun s i => q 0 i-v i+s*d 0 i) t x) t := by
  let V := T.cumulativeFamily hw φ q d σ
  let W := T.cumulativeVariation hw φ q d hp σ
  have hface : AffineVarianceRegular (fun i => q 0 i-v i) (d 0) t :=
    affineVarianceRegular_of_nonneg (fun s hs i => by linarith [hroot s hs i]) ht
  have hd := hasDerivAt_face_dynamic_varianceTest (m := 0) V W.continuousD W.continuousB
    W.boundedD W.boundedB W.derivF W.derivA (fun i => q 0 i-v i) (d 0) ht hface x
  have he (s : ℝ) : varianceTest 0 (V.J s).F (V.J s).A (fun i => q 0 i-v i+s*d 0 i) x =
      T.disorderWeight w φ v (fun j i => q j i+s*d j i) σ x := by
    unfold varianceTest
    rw [shiftedMean_zero]
    change (∫ z, (V.J s).A (x+z) ∂Measure.pi (fun i => gaussianReal 0
      (Real.toNNReal (q 0 i-v i+s*d 0 i)))) = _
    change (∫ z, ((T.cumulativeFamily hw φ q d σ).J s).A (x+z) ∂_) = _
    rw [T.cumulativeFamily_actual hw φ q d σ s]
    unfold ClockTree.disorderWeight
    congr 2
    funext i
    congr 2
    ring
  simpa only [JetVariation.testRate, zero_mul, add_zero, he] using hd

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Nonempty ι] [Fintype S] [Nonempty S]

def finiteJetEquiv (ι : Type*) [Fintype ι] [Nonempty ι] :
    Fin (Fintype.card ι-1+1) ≃ ι :=
  (finCongr (Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ‹Nonempty ι›))).trans
    (Fintype.equivFin ι).symm

 

def ClockTree.finiteDisorderRate {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (v : ι → ℝ) (q d : ℕ → ι → ℝ) {l r : ℝ}
    (hp : ∀ t ∈ Ioo l r, ∀ i, Monotone (fun j => q j i+t*d j i))
    (σ : T.Assignment) (t : ℝ) (x : ι → ℝ) : ℝ :=
  let e := finiteJetEquiv ι
  (T.cumulativeVariation hw (reindexFeature e φ) (fun j i => q j (e i))
    (fun j i => d j (e i)) (fun t ht i => hp t ht (e i)) σ).testRate 0
    (fun i => d 0 (e i)) (fun s i => q 0 (e i)-v (e i)+s*d 0 (e i)) t
    ((coordinateEquiv e).symm x)

theorem ClockTree.hasDerivAt_finiteDisorderWeight {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (v : ι → ℝ) (q d : ℕ → ι → ℝ) {l r : ℝ}
    (hp : ∀ t ∈ Ioo l r, ∀ i, Monotone (fun j => q j i+t*d j i))
    (hroot : ∀ t ∈ Ioo l r, ∀ i, v i ≤ q 0 i+t*d 0 i)
    (σ : T.Assignment) {t : ℝ} (ht : t ∈ Ioo l r) (x : ι → ℝ) :
    HasDerivAt (fun s => T.disorderWeight w φ v (fun j i => q j i+s*d j i) σ x)
      (T.finiteDisorderRate hw φ v q d hp σ t x) t := by
  let e := finiteJetEquiv ι
  have hd := T.hasDerivAt_disorderWeight_fullPath hw (reindexFeature e φ)
    (fun i => v (e i)) (fun j i => q j (e i)) (fun j i => d j (e i))
    (fun t ht i => hp t ht (e i)) (fun t ht i => hroot t ht (e i)) σ ht
    ((coordinateEquiv e).symm x)
  have he (s : ℝ) : T.disorderWeight w (reindexFeature e φ) (fun i => v (e i))
      (fun j i => q j (e i)+s*d j (e i)) σ ((coordinateEquiv e).symm x) =
      T.disorderWeight w φ v (fun j i => q j i+s*d j i) σ x := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      T.disorderWeight_reindex e w φ v (fun j i => q j i+s*d j i) σ ((coordinateEquiv e).symm x)
  simp only [he] at hd
  simpa only [ClockTree.finiteDisorderRate, e] using hd

 

theorem ClockTree.hasDerivAt_finiteDisorderExpect {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (v : ι → ℝ) (q d : ℕ → ι → ℝ) {l r : ℝ}
    (hp : ∀ t ∈ Ioo l r, ∀ i, Monotone (fun j => q j i+t*d j i))
    (hroot : ∀ t ∈ Ioo l r, ∀ i, v i ≤ q 0 i+t*d 0 i)
    (P : T.Assignment → ℝ) {t : ℝ} (ht : t ∈ Ioo l r) (x : ι → ℝ) :
    HasDerivAt (fun s => T.disorderExpect w φ v (fun j i => q j i+s*d j i) P x)
      (∑ σ, T.finiteDisorderRate hw φ v q d hp σ t x*P σ) t := by
  exact HasDerivAt.fun_sum (u := Finset.univ) fun σ _ =>
    (T.hasDerivAt_finiteDisorderWeight hw φ v q d hp hroot σ ht x).mul_const (P σ)

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

inductive ClockExpr (S : Type*) : List PositiveMass → Type _ where
  | leaf (P : S → ℝ) : ClockExpr S []
  | step (a : PositiveMass) {as : List PositiveMass} (E : ClockExpr S as) : ClockExpr S (a::as)
  | add {as : List PositiveMass} (E F : ClockExpr S as) : ClockExpr S as
  | scale {as : List PositiveMass} (c : ℝ) (E : ClockExpr S as) : ClockExpr S as
  | mul {as : List PositiveMass} (E F : ClockExpr S as) : ClockExpr S as

variable {S ι : Type*}

def ClockExpr.sub {as : List PositiveMass} (E F : ClockExpr S as) : ClockExpr S as :=
  E.add (F.scale (-1))

def ClockExpr.mean (P : S → ℝ) : (as : List PositiveMass) → ClockExpr S as
  | [] => .leaf P
  | a::as => (mean P as).step a

def ClockExpr.listSum {as : List PositiveMass} (Es : List (ClockExpr S as)) : ClockExpr S as :=
  Es.foldr ClockExpr.add (ClockExpr.mean (fun _ => 0) as)

variable [Fintype ι] [Fintype S]
attribute [local instance] Classical.propDecidable

def ClockExpr.eval (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) :
    {as : List PositiveMass} → ClockExpr S as → (ℕ → ι → ℝ) → (ι → ℝ) → ℝ
  | _, .leaf P, _, x => gaussianHierarchyMean w φ P [] x
  | _, @ClockExpr.step _ a as E, q, x => varianceTest (a:ℝ)
      (gaussianHierarchy w φ (clockSteps as (fun j i => Real.toNNReal (q (j+1) i))))
      (E.eval w φ (fun j => q (j+1))) (q 0) x
  | _, .add E F, q, x => E.eval w φ q x+F.eval w φ q x
  | _, .scale c E, q, x => c*E.eval w φ q x
  | _, .mul E F, q, x => E.eval w φ q x*F.eval w φ q x

theorem ClockExpr.eval_sub (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (E F : ClockExpr S as) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    (E.sub F).eval w φ q x = E.eval w φ q x-F.eval w φ q x := by
  simp only [ClockExpr.sub,ClockExpr.eval,neg_one_mul,sub_eq_add_neg]

theorem ClockExpr.eval_mean (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (P : S → ℝ) (as : List PositiveMass) (q : ℕ → ι → ℝ) :
    (ClockExpr.mean P as).eval w φ q =
      gaussianHierarchyMean w φ P (clockSteps as (fun j i => Real.toNNReal (q j i))) := by
  induction as generalizing q with
  | nil => rfl
  | cons a as ih =>
    funext x
    change varianceTest (a:ℝ) _ _ _ x = _
    rw [ih]
    rfl

theorem MassOrdered.lower {a b : ℝ} {as : List PositiveMass}
    (ho : MassOrdered a as) (hb : 0 ≤ b) (hba : b ≤ a) : MassOrdered b as := by
  cases as with
  | nil => exact ⟨hb,hba.trans ho.2⟩
  | cons c cs => exact ⟨hb,hba.trans ho.2.1,ho.2.2⟩

variable [Nonempty S]

theorem ClockExpr.eval_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → ι → ℝ) (k : ℕ) :
    BddSmooth k (E.eval w φ q) := by
  induction E generalizing a q with
  | leaf P => exact gaussianHierarchyMean_smooth hw φ P [] (a := 0) ⟨le_rfl,zero_le_one⟩ k
  | @step b bs E ih =>
    exact varianceTest_bddSmooth
      (gaussianHierarchy_regular hw φ _ (clockSteps_ordered ho.2.2 _) k)
      (ih ho.2.2 _) b.val (q 0)
  | add E F ihE ihF => exact (ihE ho q).add (ihF ho q)
  | scale c E ih => exact (ih ho q).const_mul c
  | mul E F ihE ihF => exact (ihE ho q).mul (ihF ho q)

theorem ClockExpr.eval_mean_zero {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    (ClockExpr.mean (fun _ => 0) as).eval w φ q x = 0 := by
  rw [ClockExpr.eval_mean]
  exact gaussianHierarchyMean_const hw φ _ (clockSteps_ordered ho _) 0 x

theorem ClockExpr.eval_listSum {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    {a : ℝ} (ho : MassOrdered a as) (Es : List (ClockExpr S as))
    (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    (ClockExpr.listSum Es).eval w φ q x = (Es.map (fun E => E.eval w φ q x)).sum := by
  induction Es with
  | nil => exact ClockExpr.eval_mean_zero hw φ ho q x
  | cons E Es ih => exact congrArg (E.eval w φ q x+·) ih

 
def ClockTree.weightExpr : {as : List PositiveMass} → (T : ClockTree S as) →
    T.Assignment → ClockExpr S as
  | _, .leaf, σ => .leaf (fun τ => if τ = σ then 1 else 0)
  | _, .step a T, σ => (T.weightExpr σ).step a
  | _, .fork T U, σ => (T.weightExpr σ.1).mul (U.weightExpr σ.2)

def ClockTree.testExpr {as : List PositiveMass} (T : ClockTree S as)
    (P : T.Assignment → ℝ) : ClockExpr S as :=
  ClockExpr.listSum ((Finset.univ : Finset T.Assignment).toList.map fun σ =>
    (T.weightExpr σ).scale (P σ))

omit [Nonempty S] in
theorem ClockTree.eval_weightExpr (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (σ : T.Assignment) (q : ℕ → ι → ℝ) :
    (T.weightExpr σ).eval w φ q = T.weight w φ (fun j i => Real.toNNReal (q j i)) σ := by
  classical
  induction T generalizing q with
  | leaf => funext x; simp [ClockTree.weightExpr,ClockExpr.eval,gaussianHierarchyMean,ClockTree.weight_leaf]
  | step a T ih =>
    funext x
    change varianceTest (a:ℝ) _ _ _ x = _
    rw [ih]
    rfl
  | fork T U ihT ihU =>
    funext x
    change (T.weightExpr σ.1).eval w φ q x*(U.weightExpr σ.2).eval w φ q x = _
    rw [ihT,ihU]
    rfl

theorem ClockTree.eval_testExpr {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (P : T.Assignment → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    (T.testExpr P).eval w φ q x = T.expect w φ (fun j i => Real.toNNReal (q j i)) P x := by
  rw [ClockTree.testExpr,ClockExpr.eval_listSum hw φ ho]
  simp only [List.map_map,Function.comp_def,ClockExpr.eval,ClockTree.eval_weightExpr,
    Finset.sum_map_toList,ClockTree.expect]
  apply Finset.sum_congr rfl
  intro σ _
  exact mul_comm _ _

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 

def ClockExpr.source (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) :
    {as : List PositiveMass} → ClockExpr S as → ClockExpr S as
  | _, .leaf P => (ClockExpr.leaf (fun σ => P σ*φ σ v)).sub ((ClockExpr.leaf P).mul (ClockExpr.leaf (fun σ => φ σ v)))
  | _, @ClockExpr.step _ a as E =>
      ((E.source φ v).step a).add
        (ClockExpr.scale a.val (((E.mul (ClockExpr.mean (fun σ => φ σ v) as)).step a).sub
          ((E.step a).mul ((ClockExpr.mean (fun σ => φ σ v) as).step a))))
  | _, .add E F => (E.source φ v).add (F.source φ v)
  | _, .scale c E => (E.source φ v).scale c
  | _, .mul E F => ((E.source φ v).mul F).add (E.mul (F.source φ v))

theorem ClockExpr.hasDerivAt_source {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → ι → ℝ) (v x : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => E.eval w φ q (x+s • v))
      ((E.source φ v).eval w φ q (x+t • v)) t := by
  induction E generalizing a q x t with
  | leaf P =>
    have h := gaussianHierarchyMean_hasDerivAt hw φ P [] (a := 0) ⟨le_rfl,zero_le_one⟩ x v t
    simpa only [ClockExpr.eval,ClockExpr.source,ClockExpr.eval_sub,gaussianHierarchyResponse,
      gaussianHierarchyMean,mul_assoc] using h
  | @step b bs E ih =>
    let qs := fun j => q (j+1)
    let steps := clockSteps bs (fun j i => Real.toNNReal (qs j i))
    have hord := clockSteps_ordered ho.2.2 (fun j i => Real.toNNReal (qs j i))
    obtain ⟨C,hF⟩ := (gaussianHierarchy_regular hw φ steps hord 0).1
    have hG := gaussianHierarchyMean_smooth hw φ (fun σ => φ σ v) steps hord 0
    have hdF := gaussianHierarchy_hasDerivAt hw φ steps hord
    have h := hasDerivAt_varianceTest_source hF hG
      (E.eval_smooth hw φ ho.2.2 qs 0) ((E.source φ v).eval_smooth hw φ ho.2.2 qs 0)
      (fun y s => hdF y v s) (fun y s => ih ho.2.2 qs y s)
      b.val (q 0) x t
    change HasDerivAt (fun s => varianceTest b.val _ _ (q 0) (x+s • v)) _ t
    convert h using 1
    simp only [ClockExpr.source,ClockExpr.eval,ClockExpr.eval_sub,ClockExpr.eval_mean,
      varianceGradient,steps,qs]
  | add E F ihE ihF => exact (ihE ho q x t).add (ihF ho q x t)
  | scale c E ih => exact (ih ho q x t).const_mul c
  | mul E F ihE ihF => exact (ihE ho q x t).mul (ihF ho q x t)

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {n : ℕ} {l r : ℝ}

def HeatJet.addTest (J K : HeatJet n) : HeatJet n :=
  { J with
    A := fun y => J.A y+K.A y
    A₁ := fun i y => J.A₁ i y+K.A₁ i y
    A₂ := fun i y => J.A₂ i y+K.A₂ i y
    smoothA := J.smoothA.add K.smoothA
    smoothA₁ := fun i => (J.smoothA₁ i).add (K.smoothA₁ i)
    smoothA₂ := fun i => (J.smoothA₂ i).add (K.smoothA₂ i)
    derivA := by
      intro x v s
      apply ((J.derivA x v s).add (K.derivA x v s)).congr_deriv
      simp only [mul_add,Finset.sum_add_distrib]
    derivA₁ := fun i x s => (J.derivA₁ i x s).add (K.derivA₁ i x s) }

def HeatJet.scaleTest (c : ℝ) (J : HeatJet n) : HeatJet n :=
  { J with
    A := fun y => c*J.A y
    A₁ := fun i y => c*J.A₁ i y
    A₂ := fun i y => c*J.A₂ i y
    smoothA := J.smoothA.const_mul c
    smoothA₁ := fun i => (J.smoothA₁ i).const_mul c
    smoothA₂ := fun i => (J.smoothA₂ i).const_mul c
    derivA := by
      intro x v s
      apply ((J.derivA x v s).const_mul c).congr_deriv
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    derivA₁ := fun i x s => (J.derivA₁ i x s).const_mul c }

def HeatJetFamily.addTest (V W : HeatJetFamily n) : HeatJetFamily n :=
  { V with
    J := fun q => (V.J q).addTest (W.J q)
    continuousA := V.continuousA.add W.continuousA
    continuousA₁ := fun i => (V.continuousA₁ i).add (W.continuousA₁ i)
    continuousA₂ := fun i => (V.continuousA₂ i).add (W.continuousA₂ i)
    boundedA := V.boundedA.add W.boundedA
    boundedA₁ := fun i => (V.boundedA₁ i).add (W.boundedA₁ i)
    boundedA₂ := fun i => (V.boundedA₂ i).add (W.boundedA₂ i) }

def HeatJetFamily.scaleTest (c : ℝ) (V : HeatJetFamily n) : HeatJetFamily n :=
  { V with
    J := fun q => (V.J q).scaleTest c
    continuousA := V.continuousA.const_mul c
    continuousA₁ := fun i => (V.continuousA₁ i).const_mul c
    continuousA₂ := fun i => (V.continuousA₂ i).const_mul c
    boundedA := V.boundedA.const_mul c
    boundedA₁ := fun i => (V.boundedA₁ i).const_mul c
    boundedA₂ := fun i => (V.boundedA₂ i).const_mul c }

def JetVariation.addTest {V W : HeatJetFamily n}
    (v : JetVariation V l r) (w : JetVariation W l r) : JetVariation (V.addTest W) l r where
  D := v.D
  B t x := v.B t x+w.B t x
  continuousD := v.continuousD
  continuousB := v.continuousB.add w.continuousB
  boundedD := v.boundedD
  boundedB := v.boundedB.add w.boundedB
  derivF := v.derivF
  derivA t ht x := (v.derivA t ht x).add (w.derivA t ht x)

def JetVariation.scaleTest (c : ℝ) {V : HeatJetFamily n}
    (v : JetVariation V l r) : JetVariation (V.scaleTest c) l r where
  D := v.D
  B t x := c*v.B t x
  continuousD := v.continuousD
  continuousB := v.continuousB.const_mul c
  boundedD := v.boundedD
  boundedB := v.boundedB.const_mul c
  derivF := v.derivF
  derivA t ht x := (v.derivA t ht x).const_mul c

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

def spinTestJet {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (P : S → ℝ) : HeatJet n :=
  let J := gaussianFeatureJet hw φ (fun _ => 0) (ContinuousLinearMap.id ℝ _) []
    (a := 0) ⟨le_rfl,zero_le_one⟩ 0
  HeatJet.ofTest J.F (gaussianHierarchyMean w φ P []) J.G J.H J.lipschitz
    (gaussianHierarchyMean_smooth hw φ P [] (a := 0) ⟨le_rfl,zero_le_one⟩ 2)
    J.smoothG J.smoothH J.derivF J.derivG

@[simp] theorem spinTestJet_F {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (P : S → ℝ) :
    (spinTestJet hw φ P).F = spinLogPartition w φ := by
  funext x
  change gaussianHierarchy w φ [] (0+ContinuousLinearMap.id ℝ _ x) = _
  simp only [ContinuousLinearMap.id_apply,zero_add,gaussianHierarchy]

@[simp] theorem spinTestJet_A {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (P : S → ℝ) :
    (spinTestJet hw φ P).A = gaussianHierarchyMean w φ P [] := rfl

 

def ClockExpr.family {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) :
    {as : List PositiveMass} → ClockExpr S as →
    (q : ℕ → ℝ → Fin (n+1) → ℝ) → (∀ j, Continuous (q j)) → HeatJetFamily n
  | _, .leaf P, _, _ => (spinTestJet hw φ P).constantFamily
  | _, .step a E, q, hq =>
    (E.family hw φ (fun j => q (j+1)) (fun j => hq (j+1))).varianceEvolve a.property (hq 0)
  | _, .add E F, q, hq => (E.family hw φ q hq).addTest (F.family hw φ q hq)
  | _, .scale c E, q, hq => (E.family hw φ q hq).scaleTest c
  | _, .mul E F, q, hq => (E.family hw φ q hq).productTest (F.family hw φ q hq)

theorem ClockExpr.family_actual {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    (q : ℕ → ℝ → Fin (n+1) → ℝ) (hq : ∀ j, Continuous (q j)) (t : ℝ) :
    ((E.family hw φ q hq).J t).F =
      gaussianHierarchy w φ (clockSteps as (fun j i => Real.toNNReal (q j t i))) ∧
    ((E.family hw φ q hq).J t).A = E.eval w φ (fun j => q j t) := by
  induction E generalizing q with
  | leaf P => exact ⟨spinTestJet_F hw φ P,rfl⟩
  | step a E ih =>
    obtain ⟨hF,hA⟩ := ih (fun j => q (j+1)) (fun j => hq (j+1))
    constructor
    · change varianceContinuation (a:ℝ) _ (q 0 t) = _
      rw [hF]
      rfl
    · change varianceTest (a:ℝ) _ _ (q 0 t) = _
      rw [hF,hA]
      rfl
  | add E F ihE ihF =>
    obtain ⟨hF,hA⟩ := ihE q hq
    obtain ⟨_,hB⟩ := ihF q hq
    exact ⟨hF,by
      change (fun x => ((E.family hw φ q hq).J t).A x+((F.family hw φ q hq).J t).A x) = _
      rw [hA,hB]
      rfl⟩
  | scale c E ih =>
    obtain ⟨hF,hA⟩ := ih q hq
    exact ⟨hF,by
      change (fun x => c*((E.family hw φ q hq).J t).A x) = _
      rw [hA]
      rfl⟩
  | mul E F ihE ihF =>
    obtain ⟨hF,hA⟩ := ihE q hq
    obtain ⟨_,hB⟩ := ihF q hq
    exact ⟨hF,by
      change (fun x => ((E.family hw φ q hq).J t).A x*((F.family hw φ q hq).J t).A x) = _
      rw [hA,hB]
      rfl⟩

 

def ClockExpr.variation {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {l r : ℝ} :
    {as : List PositiveMass} → (E : ClockExpr S as) →
    (q d : ℕ → Fin (n+1) → ℝ) →
    (∀ j, ∀ t ∈ Ioo l r, ∀ i, 0 ≤ q j i+t*d j i) →
    JetVariation (E.family hw φ (fun j t i => q j i+t*d j i)
      (fun _ => continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const))) l r
  | _, .leaf P, _, _, _ => (spinTestJet hw φ P).constantVariation
  | _, .step a E, q, d, hp =>
    (E.variation hw φ (fun j => q (j+1)) (fun j => d (j+1)) (fun j => hp (j+1))).faceVarianceEvolve
      a.property (q 0) (d 0) (hp 0)
  | _, .add E F, q, d, hp => (E.variation hw φ q d hp).addTest (F.variation hw φ q d hp)
  | _, .scale c E, q, d, hp => (E.variation hw φ q d hp).scaleTest c
  | _, .mul E F, q, d, hp => (E.variation hw φ q d hp).productTest (F.variation hw φ q d hp)

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

def ClockExpr.grad (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (i : Fin (n+1)) (as : List PositiveMass) :
    ClockExpr S as := ClockExpr.mean (fun σ => φ σ (Pi.single i 1)) as

theorem ClockExpr.jet_G {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → Fin (n+1) → ℝ) (J : HeatJet n)
    (hF : J.F = gaussianHierarchy w φ (clockSteps as (fun j i => Real.toNNReal (q j i))))
    (i : Fin (n+1)) : J.G i = (ClockExpr.grad φ i as).eval w φ q := by
  funext x
  have hj := J.derivF_coord i x 0
  have hg := gaussianHierarchy_hasDerivAt hw φ _ (clockSteps_ordered ho (fun j i => Real.toNNReal (q j i))) x (Pi.single i 1) 0
  rw [hF] at hj
  have := hj.unique hg
  simpa only [zero_smul,add_zero,ClockExpr.grad,ClockExpr.eval_mean] using this

theorem ClockExpr.jet_H {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → Fin (n+1) → ℝ) (J : HeatJet n)
    (hF : J.F = gaussianHierarchy w φ (clockSteps as (fun j i => Real.toNNReal (q j i))))
    (i : Fin (n+1)) : J.H i = ((ClockExpr.grad φ i as).source φ (Pi.single i 1)).eval w φ q := by
  funext x
  have hj := J.derivG i x 0
  have hg := (ClockExpr.grad φ i as).hasDerivAt_source hw φ ho q (Pi.single i 1) x 0
  rw [ClockExpr.jet_G hw φ ho q J hF i] at hj
  simpa only [zero_smul,add_zero] using hj.unique hg

theorem ClockExpr.jet_A₁ {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → Fin (n+1) → ℝ) (J : HeatJet n)
    (hA : J.A = E.eval w φ q) (i : Fin (n+1)) :
    J.A₁ i = (E.source φ (Pi.single i 1)).eval w φ q := by
  funext x
  have hj := J.derivA_coord i x 0
  have hg := E.hasDerivAt_source hw φ ho q (Pi.single i 1) x 0
  rw [hA] at hj
  simpa only [zero_smul,add_zero] using hj.unique hg

theorem ClockExpr.jet_A₂ {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → Fin (n+1) → ℝ) (J : HeatJet n)
    (hA : J.A = E.eval w φ q) (i : Fin (n+1)) :
    J.A₂ i = ((E.source φ (Pi.single i 1)).source φ (Pi.single i 1)).eval w φ q := by
  funext x
  have hj := J.derivA₁ i x 0
  have hg := (E.source φ (Pi.single i 1)).hasDerivAt_source hw φ ho q (Pi.single i 1) x 0
  rw [E.jet_A₁ hw φ ho q J hA i] at hj
  simpa only [zero_smul,add_zero] using hj.unique hg

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}
attribute [local instance] Classical.propDecidable

def ClockExpr.coordSum {as : List PositiveMass} (E : Fin (n+1) → ClockExpr S as) : ClockExpr S as :=
  ClockExpr.listSum ((Finset.univ : Finset (Fin (n+1))).toList.map E)

theorem ClockExpr.eval_coordSum {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    {a : ℝ} (ho : MassOrdered a as) (E : Fin (n+1) → ClockExpr S as)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    (ClockExpr.coordSum E).eval w φ q x = ∑ i, (E i).eval w φ q x := by
  rw [ClockExpr.coordSum,ClockExpr.eval_listSum hw φ ho]
  simp only [List.map_map,Function.comp_def,Finset.sum_map_toList]

def ClockExpr.potentialInsert (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (m : ℝ) (i : Fin (n+1)) (as : List PositiveMass) : ClockExpr S as :=
  let G := ClockExpr.grad φ i as
  (G.source φ (Pi.single i 1)).scale m |>.add ((G.mul G).scale (m^2))

def ClockExpr.testedInsert (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (m : ℝ) (i : Fin (n+1)) {as : List PositiveMass} (E : ClockExpr S as) : ClockExpr S as :=
  let E₁ := E.source φ (Pi.single i 1)
  ((E₁.source φ (Pi.single i 1)).add ((E₁.mul (ClockExpr.grad φ i as)).scale (2*m))).add
    (E.mul (ClockExpr.potentialInsert φ m i as))

 

def ClockExpr.pressureCov (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) :
    (as : List PositiveMass) → (ℕ → Fin (n+1) → ℝ) → ClockExpr S as
  | [], _ => ClockExpr.leaf (fun _ => 0)
  | a::as, d =>
    (ClockExpr.coordSum fun i =>
      let G := ClockExpr.grad φ i as
      (((G.source φ (Pi.single i 1)).step a).add (((G.mul G).step a).scale a.val)).scale (d 0 i/2)).add
      ((ClockExpr.pressureCov φ as (fun j => d (j+1))).step a)

 

def ClockExpr.covariance (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) :
    {as : List PositiveMass} → ClockExpr S as → (ℕ → Fin (n+1) → ℝ) → ClockExpr S as
  | _, .leaf _, _ => ClockExpr.leaf (fun _ => 0)
  | _, @ClockExpr.step _ a as E, d =>
    let D := ClockExpr.pressureCov φ as (fun j => d (j+1))
    ((ClockExpr.coordSum fun i =>
      (((E.testedInsert φ a.val i).step a).sub
        ((E.step a).mul ((ClockExpr.potentialInsert φ a.val i as).step a))).scale (d 0 i/2)).add
      ((E.covariance φ (fun j => d (j+1))).step a)).add
      ((((E.mul D).step a).sub ((E.step a).mul (D.step a))).scale a.val)
  | _, .add E F, d => (E.covariance φ d).add (F.covariance φ d)
  | _, .scale c E, d => (E.covariance φ d).scale c
  | _, .mul E F, d => ((E.covariance φ d).mul F).add (E.mul (F.covariance φ d))

theorem ClockExpr.eval_potentialInsert {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → Fin (n+1) → ℝ) (J : HeatJet n)
    (hF : J.F = gaussianHierarchy w φ (clockSteps as (fun j i => Real.toNNReal (q j i))))
    (m : ℝ) (i : Fin (n+1)) :
    (ClockExpr.potentialInsert φ m i as).eval w φ q = J.potentialInsertion m i := by
  funext x
  simp only [ClockExpr.potentialInsert,ClockExpr.eval,HeatJet.potentialInsertion,
    ClockExpr.jet_G hw φ ho q J hF,ClockExpr.jet_H hw φ ho q J hF,pow_two]

theorem ClockExpr.eval_testedInsert {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → Fin (n+1) → ℝ) (J : HeatJet n)
    (hF : J.F = gaussianHierarchy w φ (clockSteps as (fun j i => Real.toNNReal (q j i))))
    (hA : J.A = E.eval w φ q) (m : ℝ) (i : Fin (n+1)) :
    (E.testedInsert φ m i).eval w φ q = J.testedInsertion m i := by
  funext x
  simp only [ClockExpr.testedInsert,ClockExpr.eval,
    ClockExpr.eval_potentialInsert hw φ ho q J hF,
    HeatJet.testedInsertion,HeatJet.potentialInsertion,
    E.jet_A₁ hw φ ho q J hA,E.jet_A₂ hw φ ho q J hA,
    ClockExpr.jet_G hw φ ho q J hF,ClockExpr.jet_H hw φ ho q J hF,hA,mul_assoc]

end SKFluctuations.Hierarchy

end

end OAI
