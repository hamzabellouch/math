import Mathlib
import OAI.Probability.SKFluctuations.TreeRootVariation

namespace OAI

/-! Replica Covariance Variation. -/

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

 

theorem ClockExpr.variation_actual {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (q d : ℕ → Fin (n+1) → ℝ) {l r : ℝ}
    (hp : ∀ j, ∀ t ∈ Ioo l r, ∀ i, 0 ≤ q j i+t*d j i) (t : ℝ) :
    (E.variation hw φ q d hp).D t =
      (ClockExpr.pressureCov φ as d).eval w φ (fun j i => q j i+t*d j i) ∧
    (E.variation hw φ q d hp).B t =
      (E.covariance φ d).eval w φ (fun j i => q j i+t*d j i) := by
  induction E generalizing a q d with
  | leaf P =>
    constructor <;> funext x <;> change 0=gaussianHierarchyMean w φ (fun _ => 0) [] x
    all_goals exact (gaussianHierarchyMean_const hw φ [] (a := 0) ⟨le_rfl,zero_le_one⟩ 0 x).symm
  | @step b bs E ih =>
    let qs := fun j => q (j+1)
    let ds := fun j => d (j+1)
    let qt := fun j i => qs j i+t*ds j i
    let V := E.family hw φ (fun j s i => qs j i+s*ds j i)
      (fun _ => continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const))
    let v := E.variation hw φ qs ds (fun j => hp (j+1))
    obtain ⟨ihD,ihB⟩ := ih ho.2.2 qs ds (fun j => hp (j+1))
    obtain ⟨hF,hA⟩ := E.family_actual hw φ
      (fun j s i => qs j i+s*ds j i)
      (fun _ => continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const)) t
    change (V.J t).F = _ at hF
    change (V.J t).A = E.eval w φ qt at hA
    change v.D t = (ClockExpr.pressureCov φ bs ds).eval w φ qt at ihD
    change v.B t = (E.covariance φ ds).eval w φ qt at ihB
    have hG := ClockExpr.jet_G hw φ ho.2.2 qt (V.J t) hF
    have hH := ClockExpr.jet_H hw φ ho.2.2 qt (V.J t) hF
    have hPI := ClockExpr.eval_potentialInsert hw φ ho.2.2 qt (V.J t) hF
    have hTI := E.eval_testedInsert hw φ ho.2.2 qt (V.J t) hF hA
    dsimp only [V,qs,ds,qt] at hF hA hG hH hPI hTI
    constructor
    · funext x
      change v.pressureRate b.val (d 0) (fun s i => q 0 i+s*d 0 i) t x = _
      simp only [JetVariation.pressureRate,signedVarianceDerivative,
        ClockExpr.pressureCov,ClockExpr.eval,ClockExpr.eval_coordSum hw φ ho,ihD,qs,ds,qt,pow_two]
      simp only [hF,hG,hH]
    · funext x
      change v.testRate b.val (d 0) (fun s i => q 0 i+s*d 0 i) t x = _
      simp only [JetVariation.testRate,HeatJet.signedVarianceRate,
        ClockExpr.covariance,ClockExpr.eval,ClockExpr.eval_sub,ClockExpr.eval_coordSum hw φ ho,
        ihB,ihD,qs,ds,qt]
      simp only [hF,hA,← hTI,← hPI]
  | add E F ihE ihF =>
    obtain ⟨hd,hb⟩ := ihE ho q d hp
    obtain ⟨_,hc⟩ := ihF ho q d hp
    exact ⟨hd,by
      change (fun x => (E.variation hw φ q d hp).B t x+(F.variation hw φ q d hp).B t x)=_
      rw [hb,hc]
      rfl⟩
  | scale c E ih =>
    obtain ⟨hd,hb⟩ := ih ho q d hp
    exact ⟨hd,by
      change (fun x => c*(E.variation hw φ q d hp).B t x)=_
      rw [hb]
      rfl⟩
  | mul E F ihE ihF =>
    obtain ⟨hd,hb⟩ := ihE ho q d hp
    obtain ⟨_,hc⟩ := ihF ho q d hp
    have hE := (E.family_actual hw φ
      (fun j s i => q j i+s*d j i)
      (fun _ => continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const)) t).2
    have hF := (F.family_actual hw φ
      (fun j s i => q j i+s*d j i)
      (fun _ => continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const)) t).2
    exact ⟨hd,by
      change (fun x => (E.variation hw φ q d hp).B t x*
        ((F.family hw φ (fun j s i => q j i+s*d j i) _).J t).A x+
        ((E.family hw φ (fun j s i => q j i+s*d j i) _).J t).A x*
        (F.variation hw φ q d hp).B t x)=_
      rw [hb,hc,hE,hF]
      rfl⟩

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 

theorem ClockExpr.hasDerivAt_covariance {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (q d : ℕ → Fin (n+1) → ℝ) {l r t : ℝ}
    (hp : ∀ j, ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q j i+s*d j i) (ht : t ∈ Ioo l r)
    (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => E.eval w φ (fun j i => q j i+s*d j i) x)
      ((E.covariance φ d).eval w φ (fun j i => q j i+t*d j i) x) t := by
  have hd := (E.variation hw φ q d hp).derivA t ht x
  have hA (s : ℝ) := (E.family_actual hw φ
    (fun j s i => q j i+s*d j i)
    (fun _ => continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const)) s).2
  have hB := (E.variation_actual hw φ ho q d hp t).2
  simpa only [hA,hB] using hd

def ClockExpr.iterCov (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (E : ClockExpr S as) (d : ℕ → Fin (n+1) → ℝ) : ℕ → ClockExpr S as
  | 0 => E
  | k+1 => (E.iterCov φ d k).covariance φ d

theorem ClockExpr.iteratedDeriv_eval {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (q d : ℕ → Fin (n+1) → ℝ) {l r : ℝ}
    (hp : ∀ j, ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q j i+s*d j i)
    (x : Fin (n+1) → ℝ) (k : ℕ) {t : ℝ} (ht : t ∈ Ioo l r) :
    iteratedDeriv k (fun s => E.eval w φ (fun j i => q j i+s*d j i) x) t =
      (E.iterCov φ d k).eval w φ (fun j i => q j i+t*d j i) x := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (fun s => E.eval w φ (fun j i => q j i+s*d j i) x) =ᶠ[𝓝 t]
        (fun s => (E.iterCov φ d k).eval w φ (fun j i => q j i+s*d j i) x) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact ih hs
    rw [he.deriv_eq]
    exact ((E.iterCov φ d k).hasDerivAt_covariance hw φ ho q d hp ht x).deriv

theorem ClockExpr.iteratedDeriv_hasDerivAt {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (q d : ℕ → Fin (n+1) → ℝ) {l r : ℝ}
    (hp : ∀ j, ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q j i+s*d j i)
    (x : Fin (n+1) → ℝ) (k : ℕ) {t : ℝ} (ht : t ∈ Ioo l r) :
    HasDerivAt (iteratedDeriv k (fun s => E.eval w φ (fun j i => q j i+s*d j i) x))
      ((E.iterCov φ d (k+1)).eval w φ (fun j i => q j i+t*d j i) x) t := by
  apply ((E.iterCov φ d k).hasDerivAt_covariance hw φ ho q d hp ht x).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact E.iteratedDeriv_eval hw φ ho q d hp x k hs

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 
def ClockExpr.rootEval (w : S → ℝ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (E : ClockExpr S as) (q₀ : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  varianceTest 0 (fun _ => 0) (E.eval w φ q) q₀ x

def ClockExpr.rootCov (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (E : ClockExpr S as) (d₀ : Fin (n+1) → ℝ)
    (d : ℕ → Fin (n+1) → ℝ) : ClockExpr S as :=
  (ClockExpr.coordSum fun i =>
    ((E.source φ (Pi.single i 1)).source φ (Pi.single i 1)).scale (d₀ i/2)).add
    (E.covariance φ d)

theorem varianceTest_add' {ι : Type*} [Fintype ι]
    {F A B : (ι → ℝ) → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F)
    (hA : BddSmooth 0 A) (hB : BddSmooth 0 B) (m : ℝ) (q x : ι → ℝ) :
    varianceTest m F (fun y => A y+B y) q x = varianceTest m F A q x+varianceTest m F B q x :=
  shiftedMean_add hA hB
    ((exponentialIncrement_gaussian (fun i => Real.toNNReal (q i))).integrable_shift hF m x)

theorem ClockExpr.rootEval_add {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E F : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (x : Fin (n+1) → ℝ) :
    (E.add F).rootEval w φ q₀ q x = E.rootEval w φ q₀ q x+F.rootEval w φ q₀ q x :=
  varianceTest_add' (LipschitzWith.const 0) (E.eval_smooth hw φ ho q 0)
    (F.eval_smooth hw φ ho q 0) 0 q₀ x

omit [Nonempty S] in
theorem ClockExpr.rootEval_scale (w : S → ℝ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    (c : ℝ) (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    (E.scale c).rootEval w φ q₀ q x = c*E.rootEval w φ q₀ q x := varianceTest_const_mul c 0 q₀ x

theorem ClockExpr.rootEval_coordSum {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    {a : ℝ} (ho : MassOrdered a as) (E : Fin (n+1) → ClockExpr S as)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    (ClockExpr.coordSum E).rootEval w φ q₀ q x = ∑ i, (E i).rootEval w φ q₀ q x := by
  unfold ClockExpr.rootEval
  have he : (ClockExpr.coordSum E).eval w φ q = fun y => ∑ i, (E i).eval w φ q y := by
    funext y
    exact ClockExpr.eval_coordSum hw φ ho E q y
  rw [he]
  exact varianceTest_sum (LipschitzWith.const 0) (fun i => (E i).eval_smooth hw φ ho q 0) 0 q₀ x

theorem ClockExpr.hasDerivAt_rootCov {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (q₀ d₀ : Fin (n+1) → ℝ)
    (q d : ℕ → Fin (n+1) → ℝ) {l r t : ℝ}
    (hp : ∀ j, ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q j i+s*d j i)
    (hr : ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q₀ i+s*d₀ i) (ht : t ∈ Ioo l r)
    (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => E.rootEval w φ (fun i => q₀ i+s*d₀ i) (fun j i => q j i+s*d j i) x)
      ((E.rootCov φ d₀ d).rootEval w φ (fun i => q₀ i+t*d₀ i) (fun j i => q j i+t*d j i) x) t := by
  let V := E.family hw φ (fun j s i => q j i+s*d j i)
    (fun _ => continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const))
  let v : JetVariation V l r := E.variation hw φ q d hp
  have hd := hasDerivAt_face_dynamic_varianceTest (m := 0) V v.continuousD v.continuousB
    v.boundedD v.boundedB v.derivF v.derivA q₀ d₀ ht (affineVarianceRegular_of_nonneg hr ht) x
  have hA (s : ℝ) : (V.J s).A = E.eval w φ (fun j i => q j i+s*d j i) :=
    (E.family_actual hw φ _ _ s).2
  have hB : v.B t = (E.covariance φ d).eval w φ (fun j i => q j i+t*d j i) :=
    (E.variation_actual hw φ ho q d hp t).2
  have hA₂ := E.jet_A₂ hw φ ho (fun j i => q j i+t*d j i) (V.J t) (hA t)
  have he (s : ℝ) : varianceTest 0 (V.J s).F (V.J s).A (fun i => q₀ i+s*d₀ i) x =
      E.rootEval w φ (fun i => q₀ i+s*d₀ i) (fun j i => q j i+s*d j i) x := by
    simp only [ClockExpr.rootEval,varianceTest_zero_root,hA]
  have hT (i : Fin (n+1)) : (V.J t).testedInsertion 0 i = (V.J t).A₂ i := by
    funext y
    simp [HeatJet.testedInsertion]
  have hP (i : Fin (n+1)) : (V.J t).potentialInsertion 0 i = fun _ => 0 := by
    funext y
    simp [HeatJet.potentialInsertion]
  have hZ (Q : Fin (n+1) → ℝ) : varianceTest 0 (V.J t).F (fun _ => 0) Q x = 0 := by
    simp [varianceTest_zero_root,zeroContinuation]
  simp only [HeatJet.signedVarianceRate,hT,hP,hZ,mul_zero,sub_zero,zero_mul,add_zero,
    he,hB,hA₂] at hd
  convert hd using 1
  rw [ClockExpr.rootCov,ClockExpr.rootEval_add hw φ _ _ ho,
    ClockExpr.rootEval_coordSum hw φ ho]
  simp only [ClockExpr.rootEval_scale]
  simp only [ClockExpr.rootEval,varianceTest_zero_root]

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 theorem ClockExpr.eval_step_add {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (a : PositiveMass) (ho : MassOrdered a.val as) (E F : ClockExpr S as)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    ((E.add F).step a).eval w φ q x =
      (E.step a).eval w φ q x+(F.step a).eval w φ q x := by
  obtain ⟨C,hC⟩ := (gaussianHierarchy_regular hw φ
    (clockSteps as (fun j i => Real.toNNReal (q (j+1) i))) (clockSteps_ordered ho _) 0).1
  exact varianceTest_add' hC
    (E.eval_smooth hw φ ho _ 0) (F.eval_smooth hw φ ho _ 0) a.val (q 0) x

omit [Nonempty S] in
 theorem ClockExpr.eval_step_scale (w : S → ℝ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (a : PositiveMass) (c : ℝ) (E : ClockExpr S as)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    ((E.scale c).step a).eval w φ q x = c*(E.step a).eval w φ q x :=
  varianceTest_const_mul c a.val (q 0) x

 theorem ClockExpr.rootCov_eval_add {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    {a : ℝ} (ho : MassOrdered a as) (E F : ClockExpr S as)
    (d₀ : Fin (n+1) → ℝ) (d q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    ((E.add F).rootCov φ d₀ d).eval w φ q x =
      (E.rootCov φ d₀ d).eval w φ q x+(F.rootCov φ d₀ d).eval w φ q x := by
  simp only [ClockExpr.rootCov,ClockExpr.eval,ClockExpr.eval_coordSum hw φ ho,
    ClockExpr.source,ClockExpr.covariance]
  simp only [mul_add,Finset.sum_add_distrib]
  ring

 theorem ClockExpr.rootCov_eval_scale {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    {a : ℝ} (ho : MassOrdered a as) (c : ℝ) (E : ClockExpr S as)
    (d₀ : Fin (n+1) → ℝ) (d q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    ((E.scale c).rootCov φ d₀ d).eval w φ q x = c*(E.rootCov φ d₀ d).eval w φ q x := by
  simp only [ClockExpr.rootCov,ClockExpr.eval,ClockExpr.eval_coordSum hw φ ho,
    ClockExpr.source,ClockExpr.covariance]
  simp only [mul_left_comm (d₀ _/2) c,← Finset.mul_sum,mul_add]

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 theorem ClockExpr.eval_step_linear {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (a : PositiveMass) (ho : MassOrdered a.val as) (E F G : ClockExpr S as) (c : ℝ)
    (q : ℕ → Fin (n+1) → ℝ)
    (he : ∀ y, E.eval w φ (fun j => q (j+1)) y =
      F.eval w φ (fun j => q (j+1)) y+c*G.eval w φ (fun j => q (j+1)) y)
    (x : Fin (n+1) → ℝ) :
    (E.step a).eval w φ q x = (F.step a).eval w φ q x+c*(G.step a).eval w φ q x := by
  have hfun : E.eval w φ (fun j => q (j+1)) =
      (F.add (G.scale c)).eval w φ (fun j => q (j+1)) := funext he
  change varianceTest _ _ _ _ _ = _
  rw [hfun]
  change ((F.add (G.scale c)).step a).eval w φ q x = _
  rw [ClockExpr.eval_step_add hw φ a ho,ClockExpr.eval_step_scale]

 theorem ClockExpr.pressureCov_direction_linear {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    {a : ℝ} (ho : MassOrdered a as) (d e q : ℕ → Fin (n+1) → ℝ) (c : ℝ)
    (x : Fin (n+1) → ℝ) :
    (ClockExpr.pressureCov φ as (fun j i => d j i+c*e j i)).eval w φ q x =
      (ClockExpr.pressureCov φ as d).eval w φ q x+c*(ClockExpr.pressureCov φ as e).eval w φ q x := by
  induction as generalizing a d e q x c with
  | nil =>
    have hz : (ClockExpr.leaf (fun _ : S => (0:ℝ))).eval w φ q x = 0 :=
      ClockExpr.eval_mean_zero hw φ ho q x
    simp only [ClockExpr.pressureCov,hz,mul_zero,add_zero]
  | cons b bs ih =>
    have hs := ClockExpr.eval_step_linear hw φ b ho.2.2
      (ClockExpr.pressureCov φ bs (fun j i => d (j+1) i+c*e (j+1) i))
      (ClockExpr.pressureCov φ bs (fun j => d (j+1)))
      (ClockExpr.pressureCov φ bs (fun j => e (j+1))) c q
      (fun y => ih ho.2.2 _ _ _ c y) x
    simp only [ClockExpr.pressureCov,ClockExpr.eval,ClockExpr.eval_coordSum hw φ ho]
    change _+((ClockExpr.pressureCov φ bs (fun j i => d (j+1) i+c*e (j+1) i)).step b).eval w φ q x = _
    rw [hs]
    simp only [ClockExpr.eval,add_div,add_mul,mul_div_assoc,mul_assoc,
      Finset.sum_add_distrib,← Finset.mul_sum]
    ring

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 theorem ClockExpr.covariance_direction_linear {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (d e q : ℕ → Fin (n+1) → ℝ) (c : ℝ)
    (x : Fin (n+1) → ℝ) :
    (E.covariance φ (fun j i => d j i+c*e j i)).eval w φ q x =
      (E.covariance φ d).eval w φ q x+c*(E.covariance φ e).eval w φ q x := by
  induction E generalizing a d e q x with
  | leaf P =>
    have hz : (ClockExpr.leaf (fun _ : S => (0:ℝ))).eval w φ q x = 0 :=
      ClockExpr.eval_mean_zero hw φ ho q x
    simp only [ClockExpr.covariance,hz,mul_zero,add_zero]
  | @step b bs E ih =>
    let D := ClockExpr.pressureCov φ bs (fun j i => d (j+1) i+c*e (j+1) i)
    let D₁ := ClockExpr.pressureCov φ bs (fun j => d (j+1))
    let D₂ := ClockExpr.pressureCov φ bs (fun j => e (j+1))
    have hD (y) : D.eval w φ (fun j => q (j+1)) y =
        D₁.eval w φ (fun j => q (j+1)) y+c*D₂.eval w φ (fun j => q (j+1)) y :=
      ClockExpr.pressureCov_direction_linear hw φ ho.2.2 _ _ _ c y
    have hsD := ClockExpr.eval_step_linear hw φ b ho.2.2 D D₁ D₂ c q hD x
    have hsM := ClockExpr.eval_step_linear hw φ b ho.2.2
      (E.mul D) (E.mul D₁) (E.mul D₂) c q (fun y => by
        simp only [ClockExpr.eval,hD]
        ring) x
    have hsE := ClockExpr.eval_step_linear hw φ b ho.2.2
      (E.covariance φ (fun j i => d (j+1) i+c*e (j+1) i))
      (E.covariance φ (fun j => d (j+1)))
      (E.covariance φ (fun j => e (j+1))) c q (fun y => ih ho.2.2 _ _ _ y) x
    simp only [ClockExpr.covariance,ClockExpr.eval,ClockExpr.eval_coordSum hw φ ho,
      ClockExpr.eval_sub]
    change (_+((E.covariance φ (fun j i => d (j+1) i+c*e (j+1) i)).step b).eval w φ q x)+
      b.val*(((E.mul D).step b).eval w φ q x-(E.step b).eval w φ q x*(D.step b).eval w φ q x) = _
    rw [hsE,hsM,hsD]
    simp only [ClockExpr.eval,add_div,add_mul,mul_div_assoc,mul_assoc,
      Finset.sum_add_distrib,← Finset.mul_sum]
    ring
  | add E F ihE ihF =>
    simp only [ClockExpr.covariance,ClockExpr.eval,ihE ho d e q x,ihF ho d e q x]
    ring
  | scale z E ih =>
    simp only [ClockExpr.covariance,ClockExpr.eval,ih ho d e q x]
    ring
  | mul E F ihE ihF =>
    simp only [ClockExpr.covariance,ClockExpr.eval,ihE ho d e q x,ihF ho d e q x]
    ring

 theorem ClockExpr.rootCov_direction_linear {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (d₀ e₀ : Fin (n+1) → ℝ)
    (d e q : ℕ → Fin (n+1) → ℝ) (c : ℝ) (x : Fin (n+1) → ℝ) :
    (E.rootCov φ (fun i => d₀ i+c*e₀ i) (fun j i => d j i+c*e j i)).eval w φ q x =
      (E.rootCov φ d₀ d).eval w φ q x+c*(E.rootCov φ e₀ e).eval w φ q x := by
  simp only [ClockExpr.rootCov,ClockExpr.eval,ClockExpr.eval_coordSum hw φ ho,
    E.covariance_direction_linear hw φ ho d e q c x]
  simp only [add_div,add_mul,mul_div_assoc,mul_assoc,
      Finset.sum_add_distrib,← Finset.mul_sum]
  ring

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

def ClockExpr.iterRootCov (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (E : ClockExpr S as) (d₀ : Fin (n+1) → ℝ) (d : ℕ → Fin (n+1) → ℝ) : ℕ → ClockExpr S as
  | 0 => E
  | k+1 => (E.iterRootCov φ d₀ d k).rootCov φ d₀ d

theorem ClockExpr.iteratedDeriv_rootEval {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (q₀ d₀ : Fin (n+1) → ℝ) (q d : ℕ → Fin (n+1) → ℝ) {l r : ℝ}
    (hp : ∀ j, ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q j i+s*d j i)
    (hr : ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q₀ i+s*d₀ i)
    (x : Fin (n+1) → ℝ) (k : ℕ) {t : ℝ} (ht : t ∈ Ioo l r) :
    iteratedDeriv k (fun s => E.rootEval w φ (fun i => q₀ i+s*d₀ i) (fun j i => q j i+s*d j i) x) t =
      (E.iterRootCov φ d₀ d k).rootEval w φ (fun i => q₀ i+t*d₀ i) (fun j i => q j i+t*d j i) x := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (fun s => E.rootEval w φ (fun i => q₀ i+s*d₀ i) (fun j i => q j i+s*d j i) x) =ᶠ[𝓝 t]
        (fun s => (E.iterRootCov φ d₀ d k).rootEval w φ (fun i => q₀ i+s*d₀ i) (fun j i => q j i+s*d j i) x) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact ih hs
    rw [he.deriv_eq]
    exact ((E.iterRootCov φ d₀ d k).hasDerivAt_rootCov hw φ ho q₀ d₀ q d hp hr ht x).deriv

theorem ClockExpr.iteratedDeriv_root_hasDerivAt {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (q₀ d₀ : Fin (n+1) → ℝ) (q d : ℕ → Fin (n+1) → ℝ) {l r : ℝ}
    (hp : ∀ j, ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q j i+s*d j i)
    (hr : ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q₀ i+s*d₀ i)
    (x : Fin (n+1) → ℝ) (k : ℕ) {t : ℝ} (ht : t ∈ Ioo l r) :
    HasDerivAt (iteratedDeriv k (fun s => E.rootEval w φ (fun i => q₀ i+s*d₀ i) (fun j i => q j i+s*d j i) x))
      ((E.iterRootCov φ d₀ d (k+1)).rootEval w φ (fun i => q₀ i+t*d₀ i) (fun j i => q j i+t*d j i) x) t := by
  apply ((E.iterRootCov φ d₀ d k).hasDerivAt_rootCov hw φ ho q₀ d₀ q d hp hr ht x).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact E.iteratedDeriv_rootEval hw φ ho q₀ d₀ q d hp hr x k hs

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 theorem ClockExpr.rootEval_mean_zero {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    {a : ℝ} (ho : MassOrdered a as) (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (x : Fin (n+1) → ℝ) :
    (ClockExpr.mean (fun _ => 0) as).rootEval w φ q₀ q x = 0 := by
  have he : (ClockExpr.mean (fun _ => 0) as).eval w φ q = fun _ => 0 := by
    funext y
    exact ClockExpr.eval_mean_zero hw φ ho q y
  simp [ClockExpr.rootEval,he,varianceTest_zero_root,zeroContinuation]

 theorem ClockExpr.rootEval_listSum {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    {a : ℝ} (ho : MassOrdered a as) (Es : List (ClockExpr S as))
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    (ClockExpr.listSum Es).rootEval w φ q₀ q x = (Es.map fun E => E.rootEval w φ q₀ q x).sum := by
  induction Es with
  | nil => exact ClockExpr.rootEval_mean_zero hw φ ho q₀ q x
  | cons E Es ih =>
    change (E.add (ClockExpr.listSum Es)).rootEval w φ q₀ q x = _
    rw [ClockExpr.rootEval_add hw φ _ _ ho,ih]
    rfl

omit [Nonempty S] in
 

 theorem ClockTree.rootEval_weightExpr (w : S → ℝ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (v : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (σ : T.Assignment)
    (x : Fin (n+1) → ℝ) :
    (T.weightExpr σ).rootEval w φ (fun i => q 0 i-v i) (fun j i => q (j+1) i-q j i) x =
      T.disorderWeight w φ v q σ x := by
  have he : (fun j i => Real.toNNReal (q (j+1) i-q j i)) =
      cumulativeIncrements (q 0) (fun j => q (j+1)) := by
    funext j i
    cases j <;> rfl
  simp only [ClockExpr.rootEval,ClockTree.eval_weightExpr,he,varianceTest_zero_root,
    zeroContinuation,ClockTree.disorderWeight]

 theorem ClockTree.rootEval_testExpr {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (v : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (P : T.Assignment → ℝ) (x : Fin (n+1) → ℝ) :
    (T.testExpr P).rootEval w φ (fun i => q 0 i-v i) (fun j i => q (j+1) i-q j i) x =
      T.disorderExpect w φ v q P x := by
  rw [ClockTree.testExpr,ClockExpr.rootEval_listSum hw φ ho]
  simp only [List.map_map,Function.comp_def,ClockExpr.rootEval_scale,
    ClockTree.rootEval_weightExpr,Finset.sum_map_toList,ClockTree.disorderExpect]
  apply Finset.sum_congr rfl
  intro σ _
  exact mul_comm _ _

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 theorem ClockExpr.rootCov_rootEval_direction_linear {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (d₀ e₀ q₀ : Fin (n+1) → ℝ)
    (d e q : ℕ → Fin (n+1) → ℝ) (c : ℝ) (x : Fin (n+1) → ℝ) :
    (E.rootCov φ (fun i => d₀ i+c*e₀ i) (fun j i => d j i+c*e j i)).rootEval w φ q₀ q x =
      (E.rootCov φ d₀ d).rootEval w φ q₀ q x+c*(E.rootCov φ e₀ e).rootEval w φ q₀ q x := by
  rw [← ClockExpr.rootEval_scale,← ClockExpr.rootEval_add hw φ _ _ ho]
  unfold ClockExpr.rootEval
  congr 1
  funext y
  exact E.rootCov_direction_linear hw φ ho d₀ e₀ d e q c y

 

abbrev ClockPolynomial (S : Type*) (as : List PositiveMass) :=
  List (Polynomial ℝ × ClockExpr S as)

namespace ClockPolynomial
variable {as : List PositiveMass}

def rootEval (P : ClockPolynomial S as) (w : S → ℝ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (t : ℝ) (q₀ : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  (P.map fun p => p.1.eval t*p.2.rootEval w φ q₀ q x).sum

def insert (P : ClockPolynomial S as) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (d₀ : Fin (n+1) → ℝ) (d : ℕ → Fin (n+1) → ℝ) : ClockPolynomial S as :=
  P.map fun p => (p.1,p.2.rootCov φ d₀ d)

def coeffDeriv (P : ClockPolynomial S as) : ClockPolynomial S as :=
  P.map fun p => (p.1.derivative,p.2)

def multiplyX (P : ClockPolynomial S as) : ClockPolynomial S as :=
  P.map fun p => (Polynomial.X*p.1,p.2)

def affineInsert (P : ClockPolynomial S as)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (d₀ e₀ : Fin (n+1) → ℝ) (d e : ℕ → Fin (n+1) → ℝ) : ClockPolynomial S as :=
  P.insert φ d₀ d ++ (P.insert φ e₀ e).multiplyX

omit [Nonempty S] in
 theorem rootEval_append (P Q : ClockPolynomial S as) (w : S → ℝ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (t : ℝ) (q₀ : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    (P++Q).rootEval w φ t q₀ q x = P.rootEval w φ t q₀ q x+Q.rootEval w φ t q₀ q x := by
  simp only [rootEval,List.map_append,List.sum_append]

omit [Nonempty S] in
 theorem rootEval_multiplyX (P : ClockPolynomial S as) (w : S → ℝ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (t : ℝ) (q₀ : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    P.multiplyX.rootEval w φ t q₀ q x = t*P.rootEval w φ t q₀ q x := by
  induction P with
  | nil => simp [rootEval,multiplyX]
  | cons p P ih =>
    simpa only [rootEval,multiplyX,List.map_cons,List.sum_cons,Polynomial.eval_mul,
      Polynomial.eval_X,mul_add,mul_assoc] using congrArg (t*(p.1.eval t*p.2.rootEval w φ q₀ q x)+·) ih

 theorem rootEval_affineInsert {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (P : ClockPolynomial S as)
    {a : ℝ} (ho : MassOrdered a as) (d₀ e₀ q₀ : Fin (n+1) → ℝ)
    (d e q : ℕ → Fin (n+1) → ℝ) (t : ℝ) (x : Fin (n+1) → ℝ) :
    (P.affineInsert φ d₀ e₀ d e).rootEval w φ t q₀ q x =
      (P.insert φ (fun i => d₀ i+t*e₀ i) (fun j i => d j i+t*e j i)).rootEval w φ t q₀ q x := by
  rw [affineInsert,rootEval_append,rootEval_multiplyX]
  induction P with
  | nil => simp [rootEval,insert]
  | cons p P ih =>
    simp only [insert,rootEval,List.map_cons,List.sum_cons] at ih ⊢
    rw [p.2.rootCov_rootEval_direction_linear hw φ ho]
    nlinarith

 theorem hasDerivAt_frozen {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (P : ClockPolynomial S as)
    {a : ℝ} (ho : MassOrdered a as) (q₀ d₀ : Fin (n+1) → ℝ)
    (q d : ℕ → Fin (n+1) → ℝ) {l r t : ℝ}
    (hp : ∀ j, ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q j i+s*d j i)
    (hr : ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q₀ i+s*d₀ i) (ht : t ∈ Ioo l r)
    (u : ℝ) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => P.rootEval w φ u (fun i => q₀ i+s*d₀ i) (fun j i => q j i+s*d j i) x)
      ((P.insert φ d₀ d).rootEval w φ u (fun i => q₀ i+t*d₀ i) (fun j i => q j i+t*d j i) x) t := by
  induction P with
  | nil => exact hasDerivAt_const t 0
  | cons p P ih =>
    exact ((p.2.hasDerivAt_rootCov hw φ ho q₀ d₀ q d hp hr ht x).const_mul (p.1.eval u)).add ih

 theorem hasDerivAt_diagonal {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (P : ClockPolynomial S as)
    {a : ℝ} (ho : MassOrdered a as) (q₀ d₀ : Fin (n+1) → ℝ)
    (q d : ℕ → Fin (n+1) → ℝ) {l r t : ℝ}
    (hp : ∀ j, ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q j i+s*d j i)
    (hr : ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q₀ i+s*d₀ i) (ht : t ∈ Ioo l r)
    (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => P.rootEval w φ s (fun i => q₀ i+s*d₀ i) (fun j i => q j i+s*d j i) x)
      ((P.coeffDeriv++P.insert φ d₀ d).rootEval w φ t
        (fun i => q₀ i+t*d₀ i) (fun j i => q j i+t*d j i) x) t := by
  rw [rootEval_append]
  induction P with
  | nil => simpa [rootEval,coeffDeriv,insert] using hasDerivAt_const t (0:ℝ)
  | cons p P ih =>
    have h := ((p.1.hasDerivAt t).mul
      (p.2.hasDerivAt_rootCov hw φ ho q₀ d₀ q d hp hr ht x)).add ih
    convert h using 1 <;> try rfl
    simp only [rootEval,coeffDeriv,insert,List.map_cons,List.sum_cons]
    ring

end ClockPolynomial
end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 

 theorem ClockExpr.rootEval_continuous {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    (q₀ : ℝ → Fin (n+1) → ℝ) (q : ℕ → ℝ → Fin (n+1) → ℝ)
    (hq₀ : Continuous q₀) (hq : ∀ j, Continuous (q j))
    (x : ℝ → Fin (n+1) → ℝ) (hx : Continuous x) :
    Continuous (fun t => E.rootEval w φ (q₀ t) (fun j => q j t) (x t)) := by
  let V := E.family hw φ q hq
  obtain ⟨K,_,hK⟩ := V.boundedA
  have hc := dynamic_zeroContinuation_continuous V.continuousA
    (fun t y => hK (t,y)) hq₀ hx
  have he (t : ℝ) : (V.J t).A = E.eval w φ (fun j => q j t) :=
    (E.family_actual hw φ q hq t).2
  simpa only [ClockExpr.rootEval,varianceTest_zero_root,he] using hc

end SKFluctuations.Hierarchy

end

end OAI
