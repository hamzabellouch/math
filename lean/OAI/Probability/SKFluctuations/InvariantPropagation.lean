import Mathlib
import OAI.Probability.SKFluctuations.ScalarGeneralHeadBalance

namespace OAI

/-! Invariant Propagation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Scalar
open Set Filter
open scoped Topology ContDiff

structure PolynomialSigns (a : ℝ) (j : ℕ → ℝ → ℝ) : Prop where
  third : ∀ x, 0 ≤ x → j 3 x ≤ 0
  P : ∀ x, 0 ≤ invariantP a (j 2 x) (j 3 x) (j 4 x)
  Q : ∀ x, 0 ≤ x → 0 ≤ invariantQ (j 2 x) (j 3 x) (j 4 x) (j 5 x)
  R : ∀ x, 0 ≤ x → invariantR a (j 2 x) (j 3 x) (j 4 x) (j 5 x) ≤ 0

theorem PolynomialSigns.decrease {a b : ℝ} {j : ℕ → ℝ → ℝ}
    (hj : PolynomialSigns a j) (hb : b ≤ a) (hh : ∀ x, 0 ≤ j 2 x) : PolynomialSigns b j := by
  refine ⟨hj.third,?_,hj.Q,?_⟩
  · intro x
    have he : invariantP b (j 2 x) (j 3 x) (j 4 x) =
        invariantP a (j 2 x) (j 3 x) (j 4 x)+(a-b)*(j 2 x)^3 := by
      dsimp only [invariantP]; ring
    rw [he]
    exact add_nonneg (hj.P x) (mul_nonneg (sub_nonneg.mpr hb) (pow_nonneg (hh x) _))
  · intro x hx
    have he : invariantR b (j 2 x) (j 3 x) (j 4 x) (j 5 x) =
        invariantR a (j 2 x) (j 3 x) (j 4 x) (j 5 x)+3*(j 3 x)*(a-b)*(j 2 x)^3/2 := by
      dsimp only [invariantR,invariantP]; ring
    rw [he]
    exact add_nonpos (hj.R x hx) (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (hj.third x hx)) (sub_nonneg.mpr hb))
        (pow_nonneg (hh x) _)) (by norm_num))

theorem weightedP_tail {u : ℝ × ℝ → ℝ} {R : ℝ}
    (hj : ∀ k, UniformSpatialTail R (realSpatialJet u (k+2))) (a : ℝ) :
    UniformSpatialTail R (weightedP u a) :=
  (((hj 0).pow_succ 2).const_mul (-a) |>.sub (((hj 0).mul (hj 2)).div_const 2)).add
    (((hj 1).pow_succ 1).div_const 2)

theorem weightedQ_tail {u : ℝ × ℝ → ℝ} {R : ℝ}
    (hj : ∀ k, UniformSpatialTail R (realSpatialJet u (k+2))) :
    UniformSpatialTail R (weightedQ u) :=
  (((((hj 0).pow_succ 1).neg.mul (hj 3)).div_const 2).add
    ((((hj 0).const_mul 2).mul (hj 1)).mul (hj 2))).sub
    ((((hj 1).pow_succ 2).const_mul 3).div_const 2)

theorem weightedR_tail {u : ℝ × ℝ → ℝ} {R : ℝ}
    (hj : ∀ k, UniformSpatialTail R (realSpatialJet u (k+2))) (a : ℝ) :
    UniformSpatialTail R (weightedR u a) :=
  (weightedQ_tail hj).add ((((hj 1).const_mul 3).mul (weightedP_tail hj a)).div_const 2)

 

theorem polynomialSigns_evolve {u : ℝ × ℝ → ℝ} {a R K : ℝ}
    (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hs : ∀ k, SpatialRegular k u)
    (hu : ∀ k : ℕ, ContDiffOn ℝ k u {p : ℝ × ℝ | 0 < p.1})
    (hPDE : ∀ t x, 0 < t → HasDerivAt (fun s => u (s,x))
      ((1/2:ℝ)*(spatialJet u 2 (t,x)+a*(spatialJet u 1 (t,x))^2)) t)
    (hh : ∀ t ∈ Ioc 0 R, ∀ x, 0 < realSpatialJet u 2 (t,x))
    (hb : ∀ t ∈ Ioc 0 R, ∀ x,
      |realSpatialJet u 2 (t,x)| ≤ K ∧
      |realSpatialJet u 3 (t,x)/realSpatialJet u 2 (t,x)| ≤ K ∧
      |realSpatialJet u 4 (t,x)/realSpatialJet u 2 (t,x)| ≤ K)
    (htail : ∀ k, UniformSpatialTail R (realSpatialJet u (k+2)))
    (hodd : ∀ t ∈ Icc 0 R, realSpatialJet u 3 (t,0) = 0 ∧ realSpatialJet u 5 (t,0) = 0)
    (hinit : PolynomialSigns a (fun k x => realSpatialJet u k (0,x))) :
    ∀ t ∈ Icc 0 R, PolynomialSigns a (fun k x => realSpatialJet u k (t,x)) := by
  let j := realSpatialJet u
  have hp : ∀ t ∈ Icc 0 R, ∀ x, 0 ≤ x → j 3 (t,x) ≤ 0 := by
    have hv := parabolic_nonneg_halfline (v := fun t x => -j 3 (t,x))
      (d := fun _ _ => 1/2) (b := fun t x => a*j 1 (t,x))
      (c := fun t x => 3*a*j 2 (t,x)) (F := fun _ _ => 0) (M := 3*a*K)
      ((realSpatialJet_continuous hs 3).neg.continuousOn) (by
        intro t ht x _
        have hd := (realJet_three_time hu hPDE (x := x) ht.1).neg
        simp only [deriv.fun_neg',deriv.fun_neg]
        change HasDerivAt (fun s => -j 3 (s,x))
          ((1/2:ℝ)*(-j 5 (t,x))+a*j 1 (t,x)*(-j 4 (t,x))+3*a*j 2 (t,x)*(-j 3 (t,x))+0) t
        convert hd using 1
        first | rfl | ring)
      (by intros; norm_num) (by
        intro t ht x _
        exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb t ht x).1) (by positivity))
      (by intros; exact le_rfl) (by intro x hx; exact neg_nonneg.mpr (hinit.third x hx))
      (by intro t ht; change 0 ≤ -realSpatialJet u 3 (t,0); rw [(hodd t ht).1]; simp)
      (htail 1 |>.neg.lower_half)
    exact fun t ht x hx => neg_nonneg.mp (hv t ht x hx)
  have hP : ∀ t ∈ Icc 0 R, ∀ x, 0 ≤ weightedP u a (t,x) := by
    apply parabolic_nonneg_real (d := fun _ _ => 1/2)
      (b := fun t x => a*j 1 (t,x)-j 3 (t,x)/j 2 (t,x))
      (c := fun t x => j 4 (t,x)/j 2 (t,x)+3*a*j 2 (t,x)) (F := fun _ _ => 0)
      (M := K+3*a*K) (weightedP_continuous hs a).continuousOn
    · intro t ht x
      convert weightedP_time hu hPDE ht.1 hs (hh t ht x).ne' using 1; ring
    · intros; norm_num
    · intro t ht x
      have h1 := (le_abs_self _).trans (hb t ht x).2.2
      have h2 := mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb t ht x).1)
        (show 0 ≤ 3*a by positivity)
      exact add_le_add h1 h2
    · intros; exact le_rfl
    · exact hinit.P
    · exact (weightedP_tail htail a).lower
  have hQ : ∀ t ∈ Icc 0 R, ∀ x, 0 ≤ x → 0 ≤ weightedQ u (t,x) := by
    apply parabolic_nonneg_halfline (d := fun _ _ => 1/2)
      (b := fun t x => a*j 1 (t,x)-2*j 3 (t,x)/j 2 (t,x))
      (c := fun t x => 4*j 4 (t,x)/j 2 (t,x)-(j 3 (t,x)/j 2 (t,x))^2+7*a*j 2 (t,x))
      (F := fun t x => -3*j 3 (t,x)*((j 3 (t,x))^2-j 2 (t,x)*j 4 (t,x))*weightedP u a (t,x)/(j 2 (t,x))^2)
      (M := 4*K+7*a*K) (weightedQ_continuous hs).continuousOn
    · intro t ht x _
      convert weightedQ_time hu hPDE ht.1 hs (hh t ht x).ne' using 1; ring
    · intros; norm_num
    · intro t ht x _
      have h1 := (le_abs_self _).trans (hb t ht x).2.2
      have h2 := mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb t ht x).1)
        (show 0 ≤ 7*a by positivity)
      have he : 4*j 4 (t,x)/j 2 (t,x) = 4*(j 4 (t,x)/j 2 (t,x)) := by ring
      rw [he]; nlinarith [sq_nonneg (j 3 (t,x)/j 2 (t,x))]
    · intro t ht x hx
      have hPtx := hP t ⟨ht.1.le,ht.2⟩ x
      have hdiff : 0 ≤ (j 3 (t,x))^2-j 2 (t,x)*j 4 (t,x) := by
        change 0 ≤ invariantP a (j 2 (t,x)) (j 3 (t,x)) (j 4 (t,x)) at hPtx
        dsimp only [invariantP] at hPtx
        nlinarith [mul_nonneg ha (pow_nonneg (hh t ht x).le 3)]
      exact div_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg_of_nonpos_of_nonpos (by norm_num) (hp t ⟨ht.1.le,ht.2⟩ x hx.le)) hdiff) hPtx)
        (sq_nonneg _)
    · exact hinit.Q
    · intro t ht
      simp only [weightedQ,invariantQ,(hodd t ht).1,(hodd t ht).2,mul_zero,zero_mul,zero_div,zero_pow (by decide : (3:ℕ) ≠ 0),add_zero,sub_zero,le_refl]
    · exact (weightedQ_tail htail).lower_half
  have hR : ∀ t ∈ Icc 0 R, ∀ x, 0 ≤ x → weightedR u a (t,x) ≤ 0 := by
    have hv := parabolic_nonneg_halfline (v := fun t x => -weightedR u a (t,x))
      (d := fun _ _ => 1/2) (b := fun t x => a*j 1 (t,x)-2*j 3 (t,x)/j 2 (t,x))
      (c := fun t x => 3*(j 3 (t,x)/j 2 (t,x))^2/4+9*j 4 (t,x)/(4*j 2 (t,x))+13*a*j 2 (t,x)/2)
      (F := fun t x => weightedP u a (t,x)*weightedQ u (t,x)/(2*(j 2 (t,x))^2)-
        3*j 3 (t,x)*(weightedP u a (t,x))^2/(4*(j 2 (t,x))^2))
      (M := 3*K^2/4+9*K/4+13*a*K/2)
      ((weightedR_continuous hs a).neg.continuousOn) (by
        intro t ht x _
        have hd := (weightedR_time hu hPDE ht.1 hs (hh t ht x).ne').neg
        simp only [deriv.fun_neg',deriv.fun_neg]
        convert hd using 1
        first | rfl | ring)
      (by intros; norm_num) (by
        intro t ht x _
        have h1 := sq_le_sq₀ (abs_nonneg _) hK |>.mpr (hb t ht x).2.1
        rw [sq_abs] at h1
        have h2 := (le_abs_self _).trans (hb t ht x).2.2
        have h3 := mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb t ht x).1)
          (show 0 ≤ 13*a by positivity)
        have he : 9*j 4 (t,x)/(4*j 2 (t,x)) = 9*(j 4 (t,x)/j 2 (t,x))/4 := by ring
        rw [he]; nlinarith) (by
        intro t ht x hx
        apply sub_nonneg.mpr
        exact (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (hp t ⟨ht.1.le,ht.2⟩ x hx.le)) (sq_nonneg _)) (by positivity)).trans
          (div_nonneg (mul_nonneg (hP t ⟨ht.1.le,ht.2⟩ x) (hQ t ⟨ht.1.le,ht.2⟩ x hx.le)) (by positivity)))
      (fun x hx => neg_nonneg.mpr (hinit.R x hx)) (by
        intro t ht
        simp only [weightedR,invariantR,invariantQ,(hodd t ht).1,(hodd t ht).2,mul_zero,zero_mul,zero_div,
          zero_pow (by decide : (3:ℕ) ≠ 0),add_zero,sub_zero,neg_zero,le_refl])
      (weightedR_tail htail a |>.neg.lower_half)
    exact fun t ht x hx => neg_nonneg.mp (hv t ht x hx)
  intro t ht
  exact ⟨hp t ht,hP t ht,hQ t ht,hR t ht⟩

end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

omit [Nonempty S] in
theorem sourceJet_sub (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (vs : List (ι → ℝ)) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (P Q : T.Assignment → ℝ) (x : ι → ℝ) :
    sourceJet w φ a vs T (fun σ => P σ-Q σ) x =
      sourceJet w φ a vs T P x-sourceJet w φ a vs T Q x := by
  induction vs generalizing T with
  | nil => simp only [sourceJet,expect,mul_sub,Finset.sum_sub_distrib]
  | cons v vs ih =>
    simp only [sourceJet,sub_mul,ih,mul_sub]
    generalize T.normalizedAttach a = ps
    induction ps with
    | nil => simp
    | cons p ps ihp => simp only [List.map_cons,List.sum_cons,ihp]; ring

theorem sourceJet_constant_replicate {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (c : ℝ) (v x : ι → ℝ) (k : ℕ) :
    sourceJet w φ a (List.replicate (k+1) v) T (fun _ => c) x = 0 := by
  induction k generalizing x with
  | zero => exact sourceJet_constant_one hw φ T ha c v x
  | succ k ih =>
    have hh := sourceJet_hasDerivAt hw φ (List.replicate (k+1) v) T ha (fun _ => c) v x 0
    have he (y : ι → ℝ) : sourceJet w φ a (List.replicate (k+1) v) T (fun _ => c) y = 0 := by
      exact ih y
    simp_rw [he] at hh
    simpa only [← List.replicate_succ',zero_smul,add_zero] using hh.unique (hasDerivAt_const 0 0)

end SKFluctuations.Hierarchy.ReplicaTree

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

theorem scalarSourceJet_relative_spin {steps : List (GaussianStep (Fin 1))}
    (ho : OrderedSteps 0 steps) (k : ℕ) (x : ℝ) :
    |scalarSourceJet steps (k+2) x| ≤
      (ReplicaTree.attachmentCount 1 (k+1):ℝ)*(1-|scalarSourceJet steps 1 x|) := by
  let T := ReplicaTree.single (S := Bool) steps
  let P : T.Assignment → ℝ := fun σ => scalarFeature (ReplicaTree.singleEquiv (S := Bool) steps σ) (fun _ => 1)
  let w : Bool → ℝ := fun _ => (1/2:ℝ)
  have hw : ∀ σ, 0 < w σ := fun _ => by norm_num [w]
  have hp (σ : T.Assignment) : |P σ| ≤ 1 := (scalarFeature_one_abs _).le
  have hminus := ReplicaTree.sourceJet_relative_abs_le hw scalarFeature
    (List.replicate (k+1) (fun _ : Fin 1 => (1:ℝ))) T ho (r := 1) (by simp [T,ReplicaTree.single_leaves])
    (fun σ => P σ-1) (D := 1) (by norm_num) (fun _ hv σ => by
      have hv := List.eq_of_mem_replicate hv
      subst hv
      exact (scalarFeature_one_abs σ).le) (fun _ => x)
  have hplus := ReplicaTree.sourceJet_relative_abs_le hw scalarFeature
    (List.replicate (k+1) (fun _ : Fin 1 => (1:ℝ))) T ho (r := 1) (by simp [T,ReplicaTree.single_leaves])
    (fun σ => P σ-(-1)) (D := 1) (by norm_num) (fun _ hv σ => by
      have hv := List.eq_of_mem_replicate hv
      subst hv
      exact (scalarFeature_one_abs σ).le) (fun _ => x)
  have hc := ReplicaTree.sourceJet_constant_replicate hw scalarFeature T ho
  rw [ReplicaTree.sourceJet_sub,hc 1 (fun _ => 1) (fun _ => x) k,sub_zero] at hminus
  rw [ReplicaTree.sourceJet_sub,hc (-1) (fun _ => 1) (fun _ => x) k,sub_zero] at hplus
  have hem : (fun σ => |P σ-1|) = fun σ => 1-P σ := by
    funext σ
    exact abs_sub_comm _ _ |>.trans (abs_of_nonneg (sub_nonneg.mpr (abs_le.mp (hp σ)).2))
  have hep : (fun σ => |P σ-(-1)|) = fun σ => P σ+1 := by
    funext σ
    rw [abs_of_nonneg (by linarith [(abs_le.mp (hp σ)).1])]
    ring
  have heg : T.expect w scalarFeature P (fun _ => x) = scalarSourceJet steps 1 x := rfl
  have he1 : T.expect w scalarFeature (fun σ => 1-P σ) (fun _ => x) = 1-scalarSourceJet steps 1 x := by
    simp only [ReplicaTree.expect,mul_sub,Finset.sum_sub_distrib,mul_one] at heg ⊢
    rw [T.weight_sum hw scalarFeature ho,heg]
  have he2 : T.expect w scalarFeature (fun σ => P σ+1) (fun _ => x) = scalarSourceJet steps 1 x+1 := by
    simp only [ReplicaTree.expect,mul_add,Finset.sum_add_distrib,mul_one] at heg ⊢
    rw [T.weight_sum hw scalarFeature ho,heg]
  simp only [hem,hep,he1,he2,List.length_replicate,one_pow,mul_one] at hminus hplus
  change |scalarSourceJet steps (k+2) x| ≤ _ at hminus hplus
  rcases le_total 0 (scalarSourceJet steps 1 x) with hg|hg
  · simpa only [abs_of_nonneg hg] using hminus
  · simpa only [abs_of_nonpos hg,sub_neg_eq_add,add_comm] using hplus

theorem clockTest_sub_test_via_shiftedMean {ι : Type*} [Fintype ι] {F A B : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) (hB : BddSmooth 0 B) (m t : ℝ) (x : ι → ℝ) :
    clockTest m F (fun y => A y-B y) t x = clockTest m F A t x-clockTest m F B t x :=
  shiftedMean_sub hA hB ((exponentialIncrement_gaussian (fun _ : ι => Real.toNNReal t)).integrable_shift hF m x)

 

def HeatJet.ScalarStrong (J : HeatJet 0) (a : ℝ) : Prop :=
  ∀ x, a*(1-(J.G 0 x)^2) ≤ J.H 0 x

theorem HeatJet.ScalarStrong.evolve {J : HeatJet 0} {a m : ℝ}
    (hJ : J.ScalarStrong a) (ham : a ≤ m) (hm : 0 < m) (t : ℝ) :
    (J.evolve hm t).ScalarStrong a := by
  intro x
  have hsq : BddSmooth 0 (fun y => (J.G 0 y)^2) := by
    simpa only [pow_two] using (J.smoothG 0).mul (J.smoothG 0)
  have hA : BddSmooth 0 (fun y => a*(1-(J.G 0 y)^2)) :=
    ((BddSmooth.const 0 1).sub hsq).const_mul a
  have hh := clockTest_mono J.lipschitz hA (J.smoothH 0) hJ m t x
  rw [clockTest_const_mul,clockTest_sub_test_via_shiftedMean J.lipschitz (BddSmooth.const 0 1) hsq,
    clockTest_const J.lipschitz] at hh
  have hv := clockTest_variance_nonneg J.lipschitz (J.smoothG 0) m t x
  change a*(1-(clockTest m J.F (J.G 0) t x)^2) ≤ clockGradient m J.F (J.G 0) (J.G 0) (J.H 0) t x
  unfold clockGradient
  simp only [← pow_two]
  nlinarith [mul_nonneg (sub_nonneg.mpr ham) hv]

theorem scalar_schedule_strong (cs : List HeatClock) {a : ℝ} (ha : a ≤ 1)
    (hc : ∀ c ∈ cs, a ≤ c.mass) : (scalarTerminal.schedule cs).ScalarStrong a := by
  induction cs with
  | nil =>
    intro x
    change a*(1-(scalarTerminal.G 0 x)^2) ≤ scalarTerminal.H 0 x
    rw [scalarTerminal_G,scalarTerminal_H]
    change a*Scalar.curvature (x 0) ≤ Scalar.curvature (x 0)
    exact mul_le_of_le_one_left (Scalar.curvature_bounds _).1 ha
  | cons c cs ih =>
    exact (ih (fun d hd => hc d (List.mem_cons_of_mem c hd))).evolve
      (hc c (List.mem_cons_self ..)) c.positive c.time

theorem scalarSourceJet_relative_curvature (cs : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) cs))
    (hc : ∀ c ∈ cs, c.mass ≤ 1) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hal : ∀ c ∈ cs, a ≤ c.mass) (k : ℕ) (x : ℝ) :
    |scalarSourceJet (heatSteps cs) (k+2) x| ≤
      ((ReplicaTree.attachmentCount 1 (k+1):ℝ)/a)*scalarSourceJet (heatSteps cs) 2 x := by
  have hg := (scalarTerminal_admissible.schedule cs hc).gradient (fun _ => x)
  rw [← scalarSourceJet_one_schedule cs ho] at hg
  have hh := scalar_schedule_strong cs ha1 hal (fun _ => x)
  rw [← scalarSourceJet_one_schedule cs ho,← scalarSourceJet_two_schedule cs ho] at hh
  have hv : 1-|scalarSourceJet (heatSteps cs) 1 x| ≤ 1-(scalarSourceJet (heatSteps cs) 1 x)^2 := by
    nlinarith [sq_abs (scalarSourceJet (heatSteps cs) 1 x),abs_nonneg (scalarSourceJet (heatSteps cs) 1 x)]
  have hl : a*(1-|scalarSourceJet (heatSteps cs) 1 x|) ≤ scalarSourceJet (heatSteps cs) 2 x :=
    (mul_le_mul_of_nonneg_left hv ha.le).trans hh
  apply (scalarSourceJet_relative_spin ho k x).trans
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ ha).mpr (by
    nlinarith [mul_le_mul_of_nonneg_left hl (show (0:ℝ) ≤ ReplicaTree.attachmentCount 1 (k+1) by positivity)])

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem scalarSourceJet_bddSmooth_all {steps : List (GaussianStep (Fin 1))}
    (ho : OrderedSteps 0 steps) (r k : ℕ) :
    BddSmooth r (fun x : Fin 1 → ℝ => scalarSourceJet steps (k+1) (x 0)) := by
  induction r generalizing k with
  | zero =>
    refine ⟨?_,(ReplicaTree.attachmentCount 1 k:ℝ),by positivity,?_⟩
    · exact (continuous_iff_continuousAt.mpr (fun x =>
        (scalarSourceJet_hasDerivAt ho (k+1) x).continuousAt)).comp (continuous_apply 0)
    · exact fun x => scalarSourceJet_bound ho k (x 0)
  | succ r ih =>
    refine ⟨ih k,fun v => ⟨fun y => v 0*scalarSourceJet steps (k+2) (y 0),
      (ih (k+1)).const_mul (v 0),?_⟩⟩
    intro x s
    have hh := (scalarSourceJet_hasDerivAt ho (k+1) (x 0+s*v 0)).comp s
      (((hasDerivAt_id s).mul_const (v 0)).const_add (x 0))
    convert hh using 1 <;> first | rfl | (simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring)

theorem scalar_schedule_smoothG (cs : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) cs)) (r : ℕ) (i : Fin 1) :
    BddSmooth r ((scalarTerminal.schedule cs).G i) := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have he : (scalarTerminal.schedule cs).G 0 =
      fun x => scalarSourceJet (heatSteps cs) 1 (x 0) := by
    funext x
    have hx : (fun _ : Fin 1 => x 0) = x := by ext j; rw [Fin.eq_zero j]
    rw [scalarSourceJet_one_schedule, hx]
    exact ho
  rw [he]
  exact scalarSourceJet_bddSmooth_all ho r 0

theorem scalar_schedule_smoothH (cs : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) cs)) (r : ℕ) (i : Fin 1) :
    BddSmooth r ((scalarTerminal.schedule cs).H i) := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have he : (scalarTerminal.schedule cs).H 0 =
      fun x => scalarSourceJet (heatSteps cs) 2 (x 0) := by
    funext x
    have hx : (fun _ : Fin 1 => x 0) = x := by ext j; rw [Fin.eq_zero j]
    rw [scalarSourceJet_two_schedule, hx]
    exact ho
  rw [he]
  exact scalarSourceJet_bddSmooth_all ho r 1

theorem scalar_schedule_ordered_masses {cs : List HeatClock} {a : ℝ}
    (ho : OrderedSteps a (heatSteps (ι := Fin 1) cs)) :
    ∀ c ∈ cs, a ≤ c.mass ∧ c.mass ≤ 1 := by
  induction cs generalizing a with
  | nil => simp
  | cons c cs ih =>
    change 0 ≤ a ∧ a ≤ c.mass ∧ 0 < c.mass ∧ OrderedSteps c.mass (heatSteps cs) at ho
    intro d hd
    rcases List.mem_cons.mp hd with rfl|hd
    · exact ⟨ho.2.1,ho.2.2.2.bounds.2⟩
    · have hh := ih ho.2.2.2 d hd
      exact ⟨ho.2.1.trans hh.1,hh.2⟩

def clockPrepend (cs : List HeatClock) (m : ℝ) (hm : 0 < m) (t : ℝ≥0) : List HeatClock :=
  ⟨m,hm,t⟩::cs

theorem clockPrepend_ordered (cs : List HeatClock) {m : ℝ} (hm : 0 < m)
    (ho : OrderedSteps m (heatSteps (ι := Fin 1) cs)) (t : ℝ≥0) :
    OrderedSteps 0 (heatSteps (ι := Fin 1) (clockPrepend cs m hm t)) :=
  ⟨le_refl 0,hm.le,hm,ho⟩

theorem scalarClock_realJet_eq_sourceJet (cs : List HeatClock) {m : ℝ} (hm : 0 < m)
    (ho : OrderedSteps m (heatSteps (ι := Fin 1) cs)) (t : ℝ≥0) (k : ℕ) (x : ℝ) :
    Scalar.realSpatialJet ((scalarTerminal.schedule cs).scalarClockPlane m) k (t,x) =
      scalarSourceJet (heatSteps (clockPrepend cs m hm t)) k x := by
  have ht := (scalarTerminal.schedule cs).scalarClockPlane_spatialRegular
    (scalar_schedule_smoothG cs (ho.lower (le_refl 0) hm.le)) hm
  induction k generalizing x with
  | zero =>
    change (scalarTerminal.schedule (clockPrepend cs m hm t)).F (fun _ => x) = _
    exact scalar_schedule_eq_hierarchy _ _
  | succ k ih =>
    have hd := Scalar.realSpatialJet_hasDerivAt ht k t x
    have he : (fun y => Scalar.realSpatialJet ((scalarTerminal.schedule cs).scalarClockPlane m) k (t,y)) =
        scalarSourceJet (heatSteps (clockPrepend cs m hm t)) k := funext ih
    rw [he] at hd
    exact hd.unique (scalarSourceJet_hasDerivAt (clockPrepend_ordered cs hm ho t) k x)

theorem scalarSourceJet_schedule_parity (cs : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) cs)) (k : ℕ) (x : ℝ) :
    scalarSourceJet (heatSteps cs) k (-x) = (-1:ℝ)^k*scalarSourceJet (heatSteps cs) k x := by
  induction k generalizing x with
  | zero =>
    simp only [pow_zero,one_mul]
    exact ((scalar_schedule_eq_hierarchy cs (fun _ => -x)).symm.trans
      (scalar_schedule_even cs (fun _ => x))).trans (scalar_schedule_eq_hierarchy cs _)
  | succ k ih =>
    have he : (fun y => scalarSourceJet (heatSteps cs) k (-y)) =
        (fun y => (-1:ℝ)^k*scalarSourceJet (heatSteps cs) k y) := funext ih
    have hd := (scalarSourceJet_hasDerivAt ho k (-x)).comp x (hasDerivAt_neg x)
    have hr := (scalarSourceJet_hasDerivAt ho k x).const_mul ((-1:ℝ)^k)
    change HasDerivAt (fun y => scalarSourceJet (heatSteps cs) k (-y)) _ x at hd
    rw [he] at hd
    have hh := hd.unique hr
    simp only [mul_neg_one] at hh
    rw [pow_succ]
    nlinarith

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Scalar
open Set

theorem tangent_bound_of_monotone_derivative {F G : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt F (G x) x) (hm : Monotone G) (x : ℝ) :
    F x-F 0 ≤ x*G x := by
  have hc : Continuous F := continuous_iff_continuousAt.mpr (fun y => (hd y).continuousAt)
  rcases lt_trichotomy 0 x with hx|hx|hx
  · obtain ⟨y,hy,he⟩ := exists_hasDerivAt_eq_slope F G hx hc.continuousOn (fun y _ => hd y)
    rw [sub_zero] at he
    have hh := mul_le_mul_of_nonneg_left (hm hy.2.le) hx.le
    rw [he, mul_div_cancel₀ _ hx.ne'] at hh
    exact hh
  · subst x; simp
  · obtain ⟨y,hy,he⟩ := exists_hasDerivAt_eq_slope F G hx hc.continuousOn (fun y _ => hd y)
    have hh := mul_le_mul_of_nonneg_left (hm hy.1.le) (sub_nonneg.mpr hx.le)
    rw [he, mul_div_cancel₀ _ (sub_ne_zero.mpr hx.ne')] at hh
    nlinarith

theorem spin_residual_tail {F G : ℝ → ℝ} {T : ℝ}
    (hd : ∀ x, HasDerivAt F (G x) x) (hm : Monotone G)
    (hb : ∀ x, |F x-logCosh x| ≤ T/2) (x : ℝ) :
    |x| *(1-|G x|) ≤ Real.log 2+T := by
  have hx := (abs_le.mp (hb x)).1
  have hz := (abs_le.mp (hb 0)).2
  have hl := logCosh_lower x
  have ht := tangent_bound_of_monotone_derivative hd hm x
  have ha : x*G x ≤ |x| *|G x| := by rw [← abs_mul]; exact le_abs_self _
  simp only [logCosh,Real.cosh_zero,Real.log_one,sub_zero] at hz
  nlinarith

end SKFluctuations.Scalar

namespace SKFluctuations.Hierarchy
open Set GaussianCalculus
open scoped NNReal

theorem scalarSourceJet_schedule_gradient_monotone (cs : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) cs)) :
    Monotone (scalarSourceJet (heatSteps cs) 1) := by
  apply monotone_of_deriv_nonneg (fun x => (scalarSourceJet_hasDerivAt ho 1 x).differentiableAt)
  intro x
  rw [(scalarSourceJet_hasDerivAt ho 1 x).deriv,scalarSourceJet_two_schedule cs ho]
  exact (scalarTerminal_admissible.schedule cs (fun c hc => (scalar_schedule_ordered_masses ho c hc).2) _).1

theorem scalarSourceJet_schedule_spin_tail (cs : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) cs)) (x : ℝ) :
    |x| *(1-|scalarSourceJet (heatSteps cs) 1 x|) ≤
      Real.log 2+(cs.map (fun c => (c.time:ℝ))).sum := by
  apply Scalar.spin_residual_tail (scalarSourceJet_hasDerivAt ho 0)
    (scalarSourceJet_schedule_gradient_monotone cs ho)
  intro y
  have hh := scalar_schedule_potential_bound cs (fun c hc => (scalar_schedule_ordered_masses ho c hc).2) (fun _ => y)
  rw [scalar_schedule_eq_hierarchy] at hh
  exact hh

theorem scalarSourceJet_schedule_jet_tail (cs : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) cs)) (k : ℕ) (x : ℝ) :
    |x| *|scalarSourceJet (heatSteps cs) (k+2) x| ≤
      (ReplicaTree.attachmentCount 1 (k+1):ℝ)*(Real.log 2+(cs.map (fun c => (c.time:ℝ))).sum) := by
  have hh := mul_le_mul_of_nonneg_left (scalarSourceJet_relative_spin ho k x) (abs_nonneg x)
  have ht := mul_le_mul_of_nonneg_left (scalarSourceJet_schedule_spin_tail cs ho x)
    (show (0:ℝ) ≤ ReplicaTree.attachmentCount 1 (k+1) by positivity)
  nlinarith

 
theorem scalarClock_realJet_uniform_tail (cs : List HeatClock) {m : ℝ} (hm : 0 < m)
    (ho : OrderedSteps m (heatSteps (ι := Fin 1) cs)) (R : ℝ) (k : ℕ) :
    ∀ ε > 0, ∃ L : ℝ, ∀ t ∈ Icc 0 R, ∀ x, L ≤ |x| →
      |Scalar.realSpatialJet ((scalarTerminal.schedule cs).scalarClockPlane m) (k+2) (t,x)| ≤ ε := by
  intro ε hε
  let C : ℝ := (ReplicaTree.attachmentCount 1 (k+1):ℝ)*
    (Real.log 2+max R 0+(cs.map (fun c => (c.time:ℝ))).sum)
  have hs : 0 ≤ (cs.map (fun c => (c.time:ℝ))).sum :=
    List.sum_nonneg (fun y hy => by obtain ⟨c,_,rfl⟩ := List.mem_map.mp hy; exact c.time.coe_nonneg)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C/ε+1,fun t ht x hx => ?_⟩
  have hh := scalarSourceJet_schedule_jet_tail (clockPrepend cs m hm ⟨t,ht.1⟩)
    (clockPrepend_ordered cs hm ho _) k x
  rw [← scalarClock_realJet_eq_sourceJet cs hm ho ⟨t,ht.1⟩ (k+2) x] at hh
  simp only [clockPrepend,List.map_cons,List.sum_cons] at hh
  have hb : |x| *|Scalar.realSpatialJet ((scalarTerminal.schedule cs).scalarClockPlane m) (k+2) (t,x)| ≤ C := by
    exact hh.trans (mul_le_mul_of_nonneg_left (by change Real.log 2+(t+_) ≤ _; linarith [ht.2,le_max_left R 0])
      (show (0:ℝ) ≤ ReplicaTree.attachmentCount 1 (k+1) by positivity))
  have hxp : 0 < |x| := by linarith [div_nonneg hC hε.le]
  have hc : C ≤ |x| *ε := by
    have h := (div_le_iff₀ hε).mp (show C/ε ≤ |x| by linarith)
    simpa only [mul_comm] using h
  exact (mul_le_mul_iff_right₀ hxp).mp (hb.trans hc)

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Scalar

noncomputable def fifth (x : ℝ) : ℝ := 16*Real.tanh x-40*(Real.tanh x)^3+24*(Real.tanh x)^5

theorem fourth_derivative (x : ℝ) : HasDerivAt fourth (fifth x) x := by
  have hh := ((hasDerivAt_const x (-2:ℝ)).add (((tanh_derivative x).pow 2).const_mul 8)).sub
    (((tanh_derivative x).pow 4).const_mul 6)
  apply hh.congr_deriv
  dsimp only [fifth,curvature]
  ring

theorem terminal_invariantP (x : ℝ) : invariantP 1 (curvature x) (third x) (fourth x) = 0 := by
  dsimp only [invariantP,curvature,third,fourth]; ring

theorem terminal_invariantQ (x : ℝ) : invariantQ (curvature x) (third x) (fourth x) (fifth x) = 0 := by
  dsimp only [invariantQ,curvature,third,fourth,fifth]; ring

theorem terminal_invariantR (x : ℝ) : invariantR 1 (curvature x) (third x) (fourth x) (fifth x) = 0 := by
  simp only [invariantR,terminal_invariantP,terminal_invariantQ,mul_zero,zero_div,add_zero]

theorem third_nonpos {x : ℝ} (hx : 0 ≤ x) : third x ≤ 0 := by
  have ht : 0 ≤ Real.tanh x := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.cosh_pos x).le
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) ht)
    (curvature_bounds x).1

end SKFluctuations.Scalar

namespace SKFluctuations.Hierarchy
open Scalar

theorem scalar_nil_jet_two (x : ℝ) : scalarSourceJet [] 2 x = curvature x := by
  have hh := scalarSourceJet_two_schedule [] (by constructor <;> norm_num) x
  simpa only [heatSteps,List.map_nil,HeatJet.schedule,scalarTerminal_H] using hh

theorem scalar_nil_jet_three (x : ℝ) : scalarSourceJet [] 3 x = third x := by
  have hd := scalarSourceJet_hasDerivAt (steps := []) (by constructor <;> norm_num) 2 x
  have he : scalarSourceJet [] 2 = curvature := funext scalar_nil_jet_two
  rw [he] at hd
  exact hd.unique (curvature_derivative x)

theorem scalar_nil_jet_four (x : ℝ) : scalarSourceJet [] 4 x = fourth x := by
  have hd := scalarSourceJet_hasDerivAt (steps := []) (by constructor <;> norm_num) 3 x
  have he : scalarSourceJet [] 3 = third := funext scalar_nil_jet_three
  rw [he] at hd
  exact hd.unique (third_derivative x)

theorem scalar_nil_jet_five (x : ℝ) : scalarSourceJet [] 5 x = fifth x := by
  have hd := scalarSourceJet_hasDerivAt (steps := []) (by constructor <;> norm_num) 4 x
  have he : scalarSourceJet [] 4 = fourth := funext scalar_nil_jet_four
  rw [he] at hd
  exact hd.unique (fourth_derivative x)

theorem scalar_nil_polynomialSigns {a : ℝ} (ha : a ≤ 1) : PolynomialSigns a (scalarSourceJet []) := by
  have h1 : PolynomialSigns 1 (scalarSourceJet []) := by
    refine ⟨?_,?_,?_,?_⟩
    · intro x hx; rw [scalar_nil_jet_three]; exact third_nonpos hx
    · intro x; rw [scalar_nil_jet_two,scalar_nil_jet_three,scalar_nil_jet_four,terminal_invariantP]
    · intro x _; rw [scalar_nil_jet_two,scalar_nil_jet_three,scalar_nil_jet_four,scalar_nil_jet_five,terminal_invariantQ]
    · intro x _; rw [scalar_nil_jet_two,scalar_nil_jet_three,scalar_nil_jet_four,scalar_nil_jet_five,terminal_invariantR]
  exact h1.decrease ha (fun x => by rw [scalar_nil_jet_two]; exact (curvature_bounds x).1)

end SKFluctuations.Hierarchy

end

end OAI
