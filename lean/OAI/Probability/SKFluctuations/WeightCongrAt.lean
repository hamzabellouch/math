import Mathlib
import OAI.Probability.SKFluctuations.FeatureClockResponse

namespace OAI

/-! Weight Congr At. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
universe uB vB wB
variable {ι : Type uB} {β : Type vB} {κ : β → Type wB}
variable [Fintype ι] [∀ b, Fintype (κ b)]

 omit [∀ b, Fintype (κ b)] in
 theorem BoundaryTree.weight_congr_at {F G : ℝ → (ι → ℝ) → ℝ}
    {W V : ∀ b, κ b → ℝ → (ι → ℝ) → ℝ} {t s : ℝ}
    (hF : F t = G s) (hW : ∀ b σ, W b σ t = V b σ s)
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front) (σ : T.Assignment κ) :
    T.weight F W σ t = T.weight G V σ s := by
  induction T with
  | leaf b => exact hW b σ
  | @step st tail T ih =>
    rcases st with ⟨m,q⟩
    change shiftedMean _ m (prefixContinuation tail (F t)) (T.weight F W σ t) = _
    rw [hF,ih]
    rfl
  | fork T U ihT ihU =>
    funext x
    change T.weight F W σ.1 t x*U.weight F W σ.2 t x = _
    rw [congrFun (ihT σ.1) x,congrFun (ihU σ.2) x]
    rfl

 

theorem BoundaryTree.finite_stability {F G : (ι → ℝ) → ℝ} {C₀ C₁ : ℝ≥0} {K m : ℝ}
    (hF : LipschitzWith C₀ F) (hG : LipschitzWith C₁ G) (hK : 0 ≤ K)
    (hFG : ∀ x, |G x-F x| ≤ K)
    {W V : ∀ b, κ b → (ι → ℝ) → ℝ} (hcW : ∀ b σ, Continuous (W b σ))
    (hcV : ∀ b σ, Continuous (V b σ))
    (hpW : ∀ b x, (∀ σ, 0 ≤ W b σ x) ∧ ∑ σ, W b σ x = 1)
    (hpV : ∀ b x, (∀ σ, 0 ≤ V b σ x) ∧ ∑ σ, V b σ x = 1)
    (E : β → ℝ) (hE : ∀ b x, ∑ σ, |V b σ x-W b σ x| ≤ E b)
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front) (hO : PrefixOrdered 0 m front)
    (x : ι → ℝ) :
    ∑ σ, |T.weight (fun _ => G) (fun b σ _ => V b σ) σ 0 x-
      T.weight (fun _ => F) (fun b σ _ => W b σ) σ 0 x| ≤ T.budget (fun b => E b+2*m*K) := by
  let A := interpolate F G
  let D := fun (_ : ℝ) y => G y-F y
  let Z := fun b σ => interpolate (W b σ) (V b σ)
  let B := fun b σ (_ : ℝ) y => V b σ y-W b σ y
  have hP : ParametricRegular (-1) 2 K A D := parametric_interpolate hF hG hK hFG
  have hbound (U : ∀ b, κ b → (ι → ℝ) → ℝ)
      (hp : ∀ b x, (∀ σ, 0 ≤ U b σ x) ∧ ∑ σ, U b σ x = 1) (b) (σ : κ b) (y) : |U b σ y| ≤ 1 := by
    rw [abs_of_nonneg ((hp b y).1 σ),← (hp b y).2]
    exact Finset.single_le_sum (fun τ _ => (hp b y).1 τ) (Finset.mem_univ σ)
  have hZ : ∀ b σ, ∃ L, ParametricTest (-1) 2 L (Z b σ) (B b σ) := by
    intro b σ
    exact ⟨_,parametricTest_interpolate (hcW b σ) (hcV b σ) (by norm_num : (0:ℝ) ≤ 1)
      (hbound W hpW b σ) (hbound V hpV b σ)⟩
  have hsub : Ioo (0:ℝ) 1 ⊆ Ioo (-1:ℝ) 2 := by intro t ht; constructor <;> linarith [ht.1,ht.2]
  have hP' := hP.restrict hsub
  have hZ' : ∀ b σ, ∃ L, ParametricTest 0 1 L (Z b σ) (B b σ) :=
    fun b σ => ⟨_,(hZ b σ).choose_spec.restrict hsub⟩
  have hpZ : ∀ b, ∀ t ∈ Ioo (0:ℝ) 1, ∀ y,
      (∀ σ, 0 ≤ Z b σ t y) ∧ ∑ σ, Z b σ t y = 1 := by
    intro b t ht y
    have ht0 := ht.1.le
    have ht1 : 0 ≤ 1-t := by linarith [ht.2]
    constructor
    · intro σ
      exact add_nonneg (mul_nonneg ht1 ((hpW b y).1 σ)) (mul_nonneg ht0 ((hpV b y).1 σ))
    · simp only [Z,interpolate,Finset.sum_add_distrib,← Finset.mul_sum,(hpW b y).2,(hpV b y).2,mul_one]
      ring
  have hv : ∀ b, ∀ t ∈ Ioo (0:ℝ) 1, ∀ y,
      ∑ σ, |B b σ t y+m*Z b σ t y*D t y| ≤ E b+m*K := by
    intro b t ht y
    exact finite_law_addition_bound (hpZ b t ht y).1 (hpZ b t ht y).2 (hE b y)
      hO.bounds.2 (hFG y)
  have hr (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      ∑ σ, |T.response A D Z B σ t x| ≤ T.budget (fun b => E b+2*m*K) := by
    have hh := T.score_variation hP' hZ' hpZ hv hO ht x
    have he : (fun b => (E b+m*K)+m*K) = (fun b => E b+2*m*K) := by funext b; ring
    rw [he] at hh
    simpa only [BoundaryTree.score,zero_mul,add_zero,sub_zero] using hh
  have hd (P : T.Assignment κ → ℝ) (t : ℝ) (ht : t ∈ Ioo (-1:ℝ) 2) :
      HasDerivAt (fun s => ∑ σ, P σ*T.weight A Z σ s x)
        (∑ σ, P σ*T.response A D Z B σ t x) t :=
    HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ =>
      (((T.parametric hP hZ hO.positive σ).choose_spec.derivative t ht x).const_mul (P σ)))
  have he0 (σ : T.Assignment κ) : T.weight A Z σ 0 = T.weight (fun _ => F) (fun b σ _ => W b σ) σ 0 := by
    apply T.weight_congr_at
    · funext y; simp [A,interpolate]
    · intro b τ; funext y; simp [Z,interpolate]
  have he1 (σ : T.Assignment κ) : T.weight A Z σ 1 = T.weight (fun _ => G) (fun b σ _ => V b σ) σ 0 := by
    apply T.weight_congr_at
    · funext y; simp [A,interpolate]
    · intro b τ; funext y; simp [Z,interpolate]
  apply finite_law_variation_dual
  intro P htest
  have hc : ContinuousOn (fun s => ∑ σ, P σ*T.weight A Z σ s x) (Icc (0:ℝ) 1) := by
    intro t ht
    exact (hd P t (by constructor <;> linarith [ht.1,ht.2])).continuousAt.continuousWithinAt
  obtain ⟨t,ht,hh⟩ := exists_hasDerivAt_eq_slope
    (fun s => ∑ σ, P σ*T.weight A Z σ s x) (fun s => ∑ σ, P σ*T.response A D Z B σ s x)
    (by norm_num : (0:ℝ)<1) hc (fun s hs => hd P s (hsub hs))
  simp only [sub_zero,div_one] at hh
  have hb := T.tested_response_bound (P := P) (by norm_num : (0:ℝ) ≤ 1) htest (hr t ht)
  simp only [one_mul] at hb
  rw [hh] at hb
  simp_rw [he0,he1] at hb
  simpa only [mul_sub,Finset.sum_sub_distrib] using hb

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

noncomputable def HeatJet.gradientPair {n : ℕ} (J : HeatJet n) : (Fin (n+1) → ℝ) → ℝ :=
  fun y => ∑ i, J.G i y*J.A₁ i y
noncomputable def HeatJet.potentialEnergy {n : ℕ} (J : HeatJet n) : (Fin (n+1) → ℝ) → ℝ :=
  fun y => ∑ i, (J.G i y)^2

 theorem HeatJet.smoothGradientPair {n : ℕ} (J : HeatJet n) : BddSmooth 0 J.gradientPair :=
  BddSmooth.sum Finset.univ fun i _ => (J.smoothG i).mul (J.smoothA₁ i)
 theorem HeatJet.smoothPotentialEnergy {n : ℕ} (J : HeatJet n) : BddSmooth 0 J.potentialEnergy := by
  apply BddSmooth.sum Finset.univ
  intro i _
  simpa only [pow_two] using (J.smoothG i).mul (J.smoothG i)

 theorem HeatJet.testRate_sub {n : ℕ} (J : HeatJet n) (a b : ℝ) :
    J.testRate a = fun y => J.testRate b y+(a-b)*J.gradientPair y := by
  funext y
  unfold testRate gradientPair
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

 theorem HeatJet.potentialRate_sub {n : ℕ} (J : HeatJet n) (a b : ℝ) :
    J.potentialRate a = fun y => J.potentialRate b y+((a-b)/2)*J.potentialEnergy y := by
  funext y
  unfold potentialRate potentialEnergy
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

 theorem HeatJet.testedTrace_eq_rate {n : ℕ} (J : HeatJet n) (a : ℝ) :
    testedHeatTrace a J.G J.H J.A J.A₁ J.A₂ =
      fun y => 2*J.testRate a y+(2*a)*(J.A y*J.potentialRate a y) := by
  funext y
  unfold testedHeatTrace testRate potentialRate
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

 theorem HeatJet.clockDerivative_eq_rate {n : ℕ} (J : HeatJet n) (a t : ℝ) (x : Fin (n+1) → ℝ) :
    clockTestDerivative a J.F J.G J.H J.A J.A₁ J.A₂ t x =
      clockTest a J.F (J.testRate a) t x+
        a*(clockTest a J.F (fun y => J.A y*J.potentialRate a y) t x-
          clockTest a J.F J.A t x*clockTest a J.F (J.potentialRate a) t x) := by
  unfold clockTestDerivative
  rw [J.testedTrace_eq_rate,J.trace_eq_rate,
    clockTest_add_test J.lipschitz ((J.smoothTestRate a).const_mul 2)
      ((J.smoothA.mul (J.smoothPotentialRate a)).const_mul (2*a))]
  simp only [clockTest_const_mul]
  ring

 

 theorem HeatJet.mass_transfer_cancellation {n : ℕ} (J : HeatJet n) (a b t : ℝ) (x : Fin (n+1) → ℝ) :
    clockTestDerivative a J.F J.G J.H J.A J.A₁ J.A₂ t x-
      clockGradient a J.F (J.potentialRate b) J.A (J.testRate b) t x =
        (a-b)*clockTest a J.F J.gradientPair t x+
        (a*(a-b)/2)*(clockTest a J.F (fun y => J.A y*J.potentialEnergy y) t x-
          clockTest a J.F J.A t x*clockTest a J.F J.potentialEnergy t x) := by
  rw [J.clockDerivative_eq_rate]
  unfold clockGradient
  rw [J.testRate_sub a b,J.potentialRate_sub a b]
  have he : (fun y => J.A y*(J.potentialRate b y+(a-b)/2*J.potentialEnergy y)) =
      (fun y => J.A y*J.potentialRate b y+(a-b)/2*(J.A y*J.potentialEnergy y)) := by
    funext y
    ring
  rw [he,clockTest_add_test J.lipschitz (J.smoothTestRate b) (J.smoothGradientPair.const_mul (a-b)),
    clockTest_add_test J.lipschitz (J.smoothPotentialRate b) (J.smoothPotentialEnergy.const_mul ((a-b)/2)),
    clockTest_add_test J.lipschitz (J.smoothA.mul (J.smoothPotentialRate b))
      ((J.smoothA.mul J.smoothPotentialEnergy).const_mul ((a-b)/2))]
  simp only [clockTest_const_mul]
  ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 
def HeatJet.massSplit {n : ℕ} (J : HeatJet n) (a : ℝ) {b : ℝ} (hb : 0 < b)
    (T t : ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  clockTest a (J.evolve hb (T-t)).F (J.evolve hb (T-t)).A t x

 
def HeatJet.massSplitResponse {n : ℕ} (J : HeatJet n) (a : ℝ) {b : ℝ} (hb : 0 < b)
    (T t : ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  let K := J.evolve hb (T-t)
  (a-b)*clockTest a K.F K.gradientPair t x+
    (a*(a-b)/2)*(clockTest a K.F (fun y => K.A y*K.potentialEnergy y) t x-
      clockTest a K.F K.A t x*clockTest a K.F K.potentialEnergy t x)

 

theorem HeatJet.hasDerivAt_massSplit {n : ℕ} (J : HeatJet n) (a : ℝ) {b : ℝ} (hb : 0 < b)
    {T t : ℝ} (ht : t ∈ Ioo 0 T) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => J.massSplit a hb T s x) (J.massSplitResponse a hb T t x) t := by
  let V := J.family hb
  have hF : ∀ s ∈ Ioo (0:ℝ) (T+1), ∀ y,
      HasDerivAt (fun q => (V.J q).F y) ((V.J s).potentialRate b y) s := by
    intro s hs y
    exact J.evolve_time_F hb hs.1 y
  have hA : ∀ s ∈ Ioo (0:ℝ) (T+1), ∀ y,
      HasDerivAt (fun q => (V.J q).A y) ((V.J s).testRate b y) s := by
    intro s hs y
    exact J.evolve_time_A hb hs.1 y
  have hbt : T-t ∈ Ioo (0:ℝ) (T+1) := by constructor <;> linarith [ht.1,ht.2]
  have hh := hasDerivAt_dynamic_clockTest V.J
    (D := fun s => (V.J s).potentialRate b) (B := fun s => (V.J s).testRate b) a
    V.lipschitz V.continuousF V.continuousA
    (V.continuousPotentialRate b) (V.continuousTestRate b)
    V.boundedA (V.boundedPotentialRate b) (V.boundedTestRate b)
    (V.continuousP a) (V.continuousW a) (V.boundedP a) (V.boundedW a)
    hF hA x (hasDerivAt_id t) ((hasDerivAt_const t T).sub (hasDerivAt_id t)) ht.1 hbt
  apply hh.congr_deriv
  simpa only [Pi.sub_apply,id_eq,sub_zero,zero_sub,mul_one,mul_neg_one,sub_eq_add_neg,zero_add,
    HeatJet.massSplitResponse,V,HeatJet.family] using
    (J.evolve hb (T-t)).mass_transfer_cancellation a b t x

 theorem HeatJet.continuous_massSplit {n : ℕ} (J : HeatJet n) (a : ℝ) {b : ℝ} (hb : 0 < b)
    (T : ℝ) (x : Fin (n+1) → ℝ) : Continuous (fun t => J.massSplit a hb T t x) := by
  let V := J.family hb
  obtain ⟨K,_,hK⟩ := V.boundedA
  exact (dynamic_clockTest_continuous (F := fun s => (V.J s).F) (A := fun s => (V.J s).A)
    V.lipschitz V.continuousF V.continuousA (fun s y => hK (s,y)) a x).comp
      (continuous_id.prodMk (continuous_const.sub continuous_id))

 theorem HeatJet.massSplit_zero {n : ℕ} (J : HeatJet n) (a : ℝ) {b : ℝ} (hb : 0 < b)
    (T : ℝ) (x : Fin (n+1) → ℝ) : J.massSplit a hb T 0 x = clockTest b J.F J.A T x := by
  unfold HeatJet.massSplit
  simp only [clockTest_zero,HeatJet.evolve,sub_zero]

 theorem HeatJet.massSplit_terminal {n : ℕ} (J : HeatJet n) (a : ℝ) {b : ℝ} (hb : 0 < b)
    (T : ℝ) (x : Fin (n+1) → ℝ) : J.massSplit a hb T T x = clockTest a J.F J.A T x := by
  unfold HeatJet.massSplit
  simp only [HeatJet.evolve,sub_self]
  have h0 : clockContinuation b J.F 0 = J.F := funext (clockContinuation_zero hb.ne')
  have hA0 : clockTest b J.F J.A 0 = J.A := funext (clockTest_zero b)
  rw [h0,hA0]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem HeatJet.clockPotentialDerivative_eq_rate {n : ℕ} (J : HeatJet n) (m t : ℝ)
    (x : Fin (n+1) → ℝ) :
    clockDerivative m J.F J.G J.H t x = clockTest m J.F (J.potentialRate m) t x := by
  unfold clockDerivative HeatJet.potentialRate
  rw [clockTest_const_mul]
  rw [clockTest_sum J.lipschitz]
  · congr 1
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [clockTest_add_test J.lipschitz (J.smoothH i)
      (by simpa only [pow_two] using ((J.smoothG i).mul (J.smoothG i)).const_mul m)]
    rw [clockTest_const_mul]
  · intro i
    exact (J.smoothH i).add (by simpa only [pow_two] using
      ((J.smoothG i).mul (J.smoothG i)).const_mul m)

 

theorem hasDerivAt_dynamic_clockContinuation {n : ℕ} (V : HeatJetFamily n)
    {D : ℝ → (Fin (n+1) → ℝ) → ℝ} {l r : ℝ} {m : ℝ} (hm : 0 < m)
    (hcD : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => D p.1 p.2))
    (hbD : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => D p.1 p.2))
    (hdF : ∀ s ∈ Ioo l r, ∀ y, HasDerivAt (fun q => (V.J q).F y) (D s y) s)
    (x : Fin (n+1) → ℝ) {a b : ℝ → ℝ} {a' b' t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) (ha₀ : 0 < a t) (hbt : b t ∈ Ioo l r) :
    HasDerivAt (fun s => clockContinuation m (V.J (b s)).F (a s) x)
      (clockTest m (V.J (b t)).F ((V.J (b t)).potentialRate m) (a t) x*a'+
        clockTest m (V.J (b t)).F (D (b t)) (a t) x*b') t := by
  obtain ⟨KD,hKD,bD⟩ := hbD
  obtain ⟨KP,_,bP⟩ := V.boundedPotentialRate m
  have hc₁ : Continuous (fun p : ℝ × ℝ => clockTest m (V.J p.2).F
      ((V.J p.2).potentialRate m) p.1 x) :=
    dynamic_clockTest_continuous V.lipschitz V.continuousF (V.continuousPotentialRate m)
      (fun s y => bP (s,y)) m x
  have hc₂ : Continuous (fun p : ℝ × ℝ => clockTest m (V.J p.2).F (D p.2) p.1 x) :=
    dynamic_clockTest_continuous V.lipschitz V.continuousF hcD (fun s y => bD (s,y)) m x
  apply hasDerivAt_bivariate_chain
    (f := fun q s => clockContinuation m (V.J s).F q x)
    (f₁ := fun q s => clockTest m (V.J s).F ((V.J s).potentialRate m) q x)
    (f₂ := fun q s => clockTest m (V.J s).F (D s) q x)
    ?_ ?_ hc₁.continuousAt hc₂.continuousAt ha hb
  · filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds ha₀)] with p hp
    rw [← (V.J p.2).clockPotentialDerivative_eq_rate]
    exact hasDerivAt_clockContinuation (V.J p.2).lipschitz (V.J p.2).smoothG
      (V.J p.2).smoothH (V.J p.2).derivF (V.J p.2).derivG hm hp x
  · filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hbt)] with p hp
    exact hasDerivAt_continuation_local hp hKD hm.ne'
      (fun s _ => ((V.J s).lipschitz.continuous.comp (continuous_const.add continuous_id)).measurable)
      ((hcD.comp (continuous_const.prodMk (continuous_const.add continuous_id))).measurable)
      (fun s hs z => hdF s hs (x+z)) (fun s _ z => bD (s,x+z))
      ((exponentialIncrement_gaussian (fun _ : Fin (n+1) => Real.toNNReal p.1)).integrable_shift (V.J p.2).lipschitz m x)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem clockTest_abs_le {ι : Type*} [Fintype ι] {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) {K : ℝ} (hb : ∀ y, |A y| ≤ K)
    (m t : ℝ) (x : ι → ℝ) : |clockTest m F A t x| ≤ K :=
  abs_tiltedMean_le (hA.continuous.comp (continuous_const.add continuous_id)).measurable
    ((exponentialIncrement_gaussian (fun _ : ι => Real.toNNReal t)).integrable_shift hF m x)
    (fun z => hb (x+z))

 theorem clockGradient_abs_le {ι : Type*} [Fintype ι] {F G A A₁ : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : BddSmooth 0 G) (hA : BddSmooth 0 A)
    (hA₁ : BddSmooth 0 A₁) {D K E : ℝ} (_hD : 0 ≤ D) (hK : 0 ≤ K)
    (hbG : ∀ y, |G y| ≤ D) (hbA : ∀ y, |A y| ≤ K) (hbA₁ : ∀ y, |A₁ y| ≤ E)
    (m t : ℝ) (x : ι → ℝ) : |clockGradient m F G A A₁ t x| ≤ E+2*|m| *K*D := by
  have hAG : ∀ y, |A y*G y| ≤ K*D := by
    intro y
    rw [abs_mul]
    exact mul_le_mul (hbA y) (hbG y) (abs_nonneg _) hK
  have h1 := clockTest_abs_le hF hA₁ hbA₁ m t x
  have h2 := clockTest_abs_le hF (hA.mul hG) hAG m t x
  have h3 := clockTest_abs_le hF hA hbA m t x
  have h4 := clockTest_abs_le hF hG hbG m t x
  have h34 : |clockTest m F A t x*clockTest m F G t x| ≤ K*D := by
    rw [abs_mul]
    exact mul_le_mul h3 h4 (abs_nonneg _) hK
  have hcov := (abs_sub (clockTest m F (fun y => A y*G y) t x)
    (clockTest m F A t x*clockTest m F G t x)).trans (add_le_add h2 h34)
  unfold clockGradient
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hcov (abs_nonneg m)]

 theorem HeatJet.gradientPair_abs_le {n : ℕ} (J : HeatJet n) (D E : Fin (n+1) → ℝ)
    (hD : ∀ i, 0 ≤ D i) (hG : ∀ i y, |J.G i y| ≤ D i) (hA₁ : ∀ i y, |J.A₁ i y| ≤ E i)
    (y : Fin (n+1) → ℝ) : |J.gradientPair y| ≤ ∑ i, D i*E i := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul (hG i y) (hA₁ i y) (abs_nonneg _) (hD i)

 theorem HeatJet.potentialEnergy_abs_le {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i, 0 ≤ D i) (hG : ∀ i y, |J.G i y| ≤ D i) (y : Fin (n+1) → ℝ) :
    |J.potentialEnergy y| ≤ ∑ i, (D i)^2 := by
  rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  apply Finset.sum_le_sum
  intro i _
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (hD i)).2 (hG i y)

 theorem HeatJet.mass_transfer_abs_le {n : ℕ} (J : HeatJet n) (D E : Fin (n+1) → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hD : ∀ i, 0 ≤ D i)
    (hA : ∀ y, |J.A y| ≤ C) (hG : ∀ i y, |J.G i y| ≤ D i) (hA₁ : ∀ i y, |J.A₁ i y| ≤ E i)
    (a b t : ℝ) (x : Fin (n+1) → ℝ) :
    |clockTestDerivative a J.F J.G J.H J.A J.A₁ J.A₂ t x-
      clockGradient a J.F (J.potentialRate b) J.A (J.testRate b) t x| ≤
        |a-b| *((∑ i, D i*E i)+|a| *C*∑ i, (D i)^2) := by
  have hGP := clockTest_abs_le J.lipschitz J.smoothGradientPair (J.gradientPair_abs_le D E hD hG hA₁) a t x
  have hPE := clockTest_abs_le J.lipschitz J.smoothPotentialEnergy (J.potentialEnergy_abs_le D hD hG) a t x
  have hAP (y) : |J.A y*J.potentialEnergy y| ≤ C*∑ i, (D i)^2 := by
    rw [abs_mul]
    exact mul_le_mul (hA y) (J.potentialEnergy_abs_le D hD hG y) (abs_nonneg _) hC
  have hAPE := clockTest_abs_le J.lipschitz (J.smoothA.mul J.smoothPotentialEnergy) hAP a t x
  have hAC := clockTest_abs_le J.lipschitz J.smoothA hA a t x
  have hmul : |clockTest a J.F J.A t x*clockTest a J.F J.potentialEnergy t x| ≤ C*∑ i, (D i)^2 := by
    rw [abs_mul]
    exact mul_le_mul hAC hPE (abs_nonneg _) hC
  have hcov := (abs_sub (clockTest a J.F (fun y => J.A y*J.potentialEnergy y) t x)
    (clockTest a J.F J.A t x*clockTest a J.F J.potentialEnergy t x)).trans (add_le_add hAPE hmul)
  rw [J.mass_transfer_cancellation]
  apply (abs_add_le _ _).trans
  simp only [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hg := mul_le_mul_of_nonneg_left hGP (abs_nonneg (a-b))
  have hc := mul_le_mul_of_nonneg_left hcov (show 0 ≤ |a| *|a-b|/2 by positivity)
  nlinarith

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem dynamic_clockContinuation_continuous {ι : Type*} [Fintype ι]
    {F : ℝ → (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : ∀ r, LipschitzWith C (F r))
    (hcF : Continuous (fun p : ℝ × (ι → ℝ) => F p.1 p.2)) (m : ℝ) (x : ι → ℝ) :
    Continuous (fun p : ℝ × ℝ => clockContinuation m (F p.2) p.1 x) := by
  have hd := dynamic_testedPartition_continuous (A := fun _ _ => 1) hF hcF continuous_const
    (fun _ _ => le_refl |(1:ℝ)|) m x
  simp only [one_mul] at hd
  have hh := (hd.log (fun p => (partition_pos m
    ((ExpNormBounded.exp_lipschitz (hF p.2) m).affine_integrable
      (exponentialIncrement_gaussian (fun _ : ι => 1)) x _)).ne')).div_const m
  exact hh.congr fun p => (clockContinuation_eq_all (hF p.2).continuous m p.1 x).symm

 def HeatJet.potentialSplit {n : ℕ} (J : HeatJet n) (a : ℝ) {b : ℝ} (hb : 0 < b)
    (T t : ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  clockContinuation a (J.evolve hb (T-t)).F t x

 def HeatJet.potentialSplitResponse {n : ℕ} (J : HeatJet n) (a : ℝ) {b : ℝ} (hb : 0 < b)
    (T t : ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  let K := J.evolve hb (T-t)
  ((a-b)/2)*clockTest a K.F K.potentialEnergy t x

 theorem HeatJet.hasDerivAt_potentialSplit {n : ℕ} (J : HeatJet n) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {T t : ℝ} (ht : t ∈ Ioo 0 T) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => J.potentialSplit a hb T s x) (J.potentialSplitResponse a hb T t x) t := by
  let V := J.family hb
  have hF : ∀ s ∈ Ioo (0:ℝ) (T+1), ∀ y,
      HasDerivAt (fun q => (V.J q).F y) ((V.J s).potentialRate b y) s := by
    intro s hs y
    exact J.evolve_time_F hb hs.1 y
  have hbt : T-t ∈ Ioo (0:ℝ) (T+1) := by constructor <;> linarith [ht.1,ht.2]
  have hh := hasDerivAt_dynamic_clockContinuation V ha
    (V.continuousPotentialRate b) (V.boundedPotentialRate b) hF x
    (hasDerivAt_id t) ((hasDerivAt_const t T).sub (hasDerivAt_id t)) ht.1 hbt
  apply hh.congr_deriv
  simp only [Pi.sub_apply,id_eq,zero_sub,mul_one,mul_neg_one,
    HeatJet.potentialSplitResponse,V,HeatJet.family]
  rw [(J.evolve hb (T-t)).potentialRate_sub a b,
    clockTest_add_test (J.evolve hb (T-t)).lipschitz
      ((J.evolve hb (T-t)).smoothPotentialRate b)
      ((J.evolve hb (T-t)).smoothPotentialEnergy.const_mul ((a-b)/2)),clockTest_const_mul]
  ring

 theorem HeatJet.continuous_potentialSplit {n : ℕ} (J : HeatJet n) (a : ℝ) {b : ℝ} (hb : 0 < b)
    (T : ℝ) (x : Fin (n+1) → ℝ) : Continuous (fun t => J.potentialSplit a hb T t x) :=
  (dynamic_clockContinuation_continuous (J.family hb).lipschitz (J.family hb).continuousF a x).comp
    (continuous_id.prodMk (continuous_const.sub continuous_id))

 theorem HeatJet.potentialSplit_zero {n : ℕ} (J : HeatJet n) {a b : ℝ} (ha : a ≠ 0) (hb : 0 < b)
    (T : ℝ) (x : Fin (n+1) → ℝ) :
    J.potentialSplit a hb T 0 x = clockContinuation b J.F T x := by
  simp only [HeatJet.potentialSplit,clockContinuation_zero ha,HeatJet.evolve,sub_zero]

 theorem HeatJet.potentialSplit_terminal {n : ℕ} (J : HeatJet n) (a : ℝ) {b : ℝ} (hb : 0 < b)
    (T : ℝ) (x : Fin (n+1) → ℝ) :
    J.potentialSplit a hb T T x = clockContinuation a J.F T x := by
  unfold HeatJet.potentialSplit
  simp only [HeatJet.evolve,sub_self]
  have h0 : clockContinuation b J.F 0 = J.F := funext (clockContinuation_zero hb.ne')
  rw [h0]

 theorem HeatJet.potentialSplitResponse_abs_le {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hG : ∀ i y, |J.G i y| ≤ D i) (a : ℝ) {b : ℝ} (hb : 0 < b)
    (T t : ℝ) (x : Fin (n+1) → ℝ) :
    |J.potentialSplitResponse a hb T t x| ≤ |a-b| /2*∑ i, (D i)^2 := by
  let K := J.evolve hb (T-t)
  have hGK : ∀ i y, |K.G i y| ≤ D i := fun i =>
    clockTest_abs_le J.lipschitz (J.smoothG i) (hG i) b (T-t)
  have henergy := clockTest_abs_le K.lipschitz K.smoothPotentialEnergy
    (K.potentialEnergy_abs_le D (fun i => (abs_nonneg (J.G i 0)).trans (hG i 0)) hGK) a t x
  dsimp only [HeatJet.potentialSplitResponse]
  rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left henergy (by positivity)

 

 theorem HeatJet.potential_mass_difference {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hG : ∀ i y, |J.G i y| ≤ D i) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {T : ℝ} (hT : 0 ≤ T) (x : Fin (n+1) → ℝ) :
    |clockContinuation a J.F T x-clockContinuation b J.F T x| ≤
      (|a-b| /2*∑ i, (D i)^2)*T := by
  rcases hT.eq_or_lt with hT | hT
  · rw [← hT,clockContinuation_zero ha.ne',clockContinuation_zero hb.ne',sub_self,abs_zero,mul_zero]
  obtain ⟨t,_,he⟩ := exists_hasDerivAt_eq_slope
    (fun s => J.potentialSplit a hb T s x) (fun s => J.potentialSplitResponse a hb T s x) hT
    (J.continuous_potentialSplit a hb T x).continuousOn
    (fun s hs => J.hasDerivAt_potentialSplit ha hb hs x)
  rw [J.potentialSplit_zero ha.ne',J.potentialSplit_terminal,sub_zero] at he
  have he' := (eq_div_iff hT.ne').mp he
  rw [← he',abs_mul,abs_of_pos hT]
  exact mul_le_mul_of_nonneg_right (J.potentialSplitResponse_abs_le D hG a hb T t x) hT.le

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem HeatJet.massSplitResponse_abs_le {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    {C k a b : ℝ} (hC : 0 ≤ C) (_hk : 0 ≤ k) (hD : ∀ i, 0 ≤ D i)
    (hA : ∀ y, |J.A y| ≤ C) (hG : ∀ i y, |J.G i y| ≤ D i)
    (hA₁ : ∀ i y, |J.A₁ i y| ≤ k*C*D i)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (T t : ℝ) (x : Fin (n+1) → ℝ) :
    |J.massSplitResponse a hb T t x| ≤ |a-b| *(k+3)*C*∑ i, (D i)^2 := by
  let K := J.evolve hb (T-t)
  have hAK : ∀ y, |K.A y| ≤ C := clockTest_abs_le J.lipschitz J.smoothA hA b (T-t)
  have hGK : ∀ i y, |K.G i y| ≤ D i := fun i =>
    clockTest_abs_le J.lipschitz (J.smoothG i) (hG i) b (T-t)
  have hA₁K : ∀ i y, |K.A₁ i y| ≤ (k+2)*C*D i := by
    intro i y
    have hh := clockGradient_abs_le J.lipschitz (J.smoothG i) J.smoothA (J.smoothA₁ i)
      (hD i) hC (hG i) hA (hA₁ i) b (T-t) y
    rw [abs_of_pos hb] at hh
    exact hh.trans (by nlinarith [mul_nonneg hC (hD i),mul_le_mul_of_nonneg_right hb1 (mul_nonneg hC (hD i))])
  have hh := K.mass_transfer_abs_le D (fun i => (k+2)*C*D i) hC hD hAK hGK hA₁K a b t x
  rw [K.mass_transfer_cancellation] at hh
  change |J.massSplitResponse a hb T t x| ≤ |a-b| *((∑ i, D i*((k+2)*C*D i))+|a| *C*∑ i, (D i)^2) at hh
  have he : (∑ i, D i*((k+2)*C*D i)) = (k+2)*C*∑ i, (D i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,abs_of_nonneg ha] at hh
  exact hh.trans (by
    have hq : 0 ≤ C*∑ i, (D i)^2 := by positivity
    have h := mul_le_mul_of_nonneg_right ha1 hq
    nlinarith [mul_nonneg (abs_nonneg (a-b)) (sub_nonneg.mpr h)])

 

theorem HeatJet.clock_mass_difference {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    {C k a b : ℝ} (hC : 0 ≤ C) (hk : 0 ≤ k) (hD : ∀ i, 0 ≤ D i)
    (hA : ∀ y, |J.A y| ≤ C) (hG : ∀ i y, |J.G i y| ≤ D i)
    (hA₁ : ∀ i y, |J.A₁ i y| ≤ k*C*D i)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (x : Fin (n+1) → ℝ) :
    |clockTest a J.F J.A T x-clockTest b J.F J.A T x| ≤
      (|a-b| *(k+3)*C*∑ i, (D i)^2)*T := by
  rcases hT.eq_or_lt with hT | hT
  · rw [← hT,clockTest_zero,clockTest_zero,sub_self,abs_zero,mul_zero]
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope
    (fun s => J.massSplit a hb T s x) (fun s => J.massSplitResponse a hb T s x) hT
    (J.continuous_massSplit a hb T x).continuousOn
    (fun s hs => J.hasDerivAt_massSplit a hb hs x)
  rw [J.massSplit_zero,J.massSplit_terminal,sub_zero] at he
  have he' := (eq_div_iff hT.ne').mp he
  rw [← he',abs_mul,abs_of_pos hT]
  exact mul_le_mul_of_nonneg_right
    (J.massSplitResponse_abs_le D hC hk hD hA hG hA₁ ha ha1 hb hb1 T t x) hT.le

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

 theorem replicaFeatureJet_G_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ}
    (ha : OrderedSteps a steps) (P : T.Assignment → ℝ) (x : ι → ℝ)
    (D : Fin (n+1) → ℝ) (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    (i : Fin (n+1)) (y : Fin (n+1) → ℝ) :
    |(replicaFeatureJet hw φ L T ha P x).G i y| ≤ D i :=
  gaussianHierarchyMean_abs_le hw φ (hB i) steps ha (x+L y)

 theorem replicaFeatureJet_A₁_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {a : ℝ}
    (ha : OrderedSteps a steps) {P : T.Assignment → ℝ} {C : ℝ} (x : ι → ℝ)
    (D : Fin (n+1) → ℝ) (hC : 0 ≤ C) (hD : ∀ i, 0 ≤ D i) (hP : ∀ σ, |P σ| ≤ C)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i) (i : Fin (n+1)) (y : Fin (n+1) → ℝ) :
    |(replicaFeatureJet hw φ L T ha P x).A₁ i y| ≤ 2*(T.leaves:ℝ)*C*D i := by
  rw [replicaFeatureJet_A₁]
  have hh := ReplicaTree.sourceJet_abs_le hw φ [L (Pi.single i 1)] T ha
    (le_refl T.leaves) hC (hD i) hP
    (fun v hv => by simpa only [List.mem_singleton.mp hv] using hB i) (x+L y)
  simpa only [List.length_cons,List.length_nil,ReplicaTree.attachmentCount,
    Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,mul_one,Nat.zero_add,pow_one] using hh

 

 theorem ReplicaTree.massSplitResponse_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : ReplicaTree ι S steps) {a b : ℝ}
    (ho : OrderedSteps b steps) {P : R.Assignment → ℝ} {C : ℝ} (x : ι → ℝ)
    (D : Fin (n+1) → ℝ) (hC : 0 ≤ C) (hD : ∀ i, 0 ≤ D i) (hP : ∀ σ, |P σ| ≤ C)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (T t : ℝ) (y : Fin (n+1) → ℝ) :
    |(replicaFeatureJet hw φ L R ho P x).massSplitResponse a hb T t y| ≤
      |a-b| *(2*(R.leaves:ℝ)+3)*C*∑ i, (D i)^2 := by
  exact HeatJet.massSplitResponse_abs_le _ D hC (by positivity) hD
    (fun z => R.expect_abs_le hw φ ho hP (x+L z))
    (replicaFeatureJet_G_abs_le hw φ L R ho P x D hB)
    (replicaFeatureJet_A₁_abs_le hw φ L R ho x D hC hD hP hB) ha ha1 hb hb1 T t y

 theorem ReplicaTree.mass_difference {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : ReplicaTree ι S steps) {a b : ℝ}
    (ho : OrderedSteps b steps) {P : R.Assignment → ℝ} {C : ℝ} (x : ι → ℝ)
    (D : Fin (n+1) → ℝ) (hC : 0 ≤ C) (hD : ∀ i, 0 ≤ D i) (hP : ∀ σ, |P σ| ≤ C)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (y : Fin (n+1) → ℝ) :
    let J := replicaFeatureJet hw φ L R ho P x
    |clockTest a J.F J.A T y-clockTest b J.F J.A T y| ≤
      (|a-b| *(2*(R.leaves:ℝ)+3)*C*∑ i, (D i)^2)*T := by
  exact HeatJet.clock_mass_difference _ D hC (by positivity) hD
    (fun z => R.expect_abs_le hw φ ho hP (x+L z))
    (replicaFeatureJet_G_abs_le hw φ L R ho P x D hB)
    (replicaFeatureJet_A₁_abs_le hw φ L R ho x D hC hD hP hB) ha ha1 hb hb1 hT y

end SKFluctuations.Hierarchy

end

end OAI
