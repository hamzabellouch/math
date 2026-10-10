import OAI.MeasureTheory.CompactFactors.RelativeProducts

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal
open scoped RealInnerProductSpace BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.Amenable.Mean
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable (M : EuclideanFiveColor.Amenable.Mean G)
lemma vector_real (f : G →ᵇ ℝ) : M.vector f = M.map f := by
  have h := M.vector_pair f 1
  have he : pairing f 1 = f := by ext g; simp [pairing_apply]
  simpa only [Real.inner_apply, mul_one, he] using h

lemma norm_mean_zero_of_square {H : Type*} [NormedAddCommGroup H]
    (V : G →ᵇ H) (h : M.map (squareNorm V) = 0) : M.map (normFn V) = 0 := by
  have he : squareNorm (normFn V) = squareNorm V := by
    ext g
    simp only [squareNorm_apply, normFn_apply, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hj := M.jensen (normFn V)
  rw [M.vector_real, he, h] at hj
  rw [Real.norm_eq_abs, sq_abs] at hj
  have : (M.map (normFn V))^2 = 0 := le_antisymm hj (sq_nonneg _)
  exact sq_eq_zero_iff.mp this
end EuclideanFiveColor.Amenable.Mean

namespace EuclideanFiveColor.BoundedMeasurable
variable {G X : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [AddAction G X] [MeasurableConstVAdd G X]
variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]

lemma l2_inner (f h : Func X) : inner ℝ (l2 μ f) (l2 μ h) =
    (∫ x, (bmConj f * h) x ∂μ).re := by
  rw [inner_l2]
  simp only [Complex.inner, starRingEnd_apply, mul_comm (h _)]
  change (∫ x, RCLike.re ((bmConj f * h) x) ∂μ) = _
  exact integral_re (integrable μ (bmConj f * h))

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma inner_act (g : G) (f h : Func X) :
    inner ℝ (l2 μ (act g f)) (l2 μ (act g h)) = inner ℝ (l2 μ f) (l2 μ h) := by
  rw [l2_act, l2_act]
  exact (Amenable.Koopman.action (E := ℂ) μ g).inner_map_map _ _

omit [TopologicalSpace G] [DiscreteTopology G] [IsProbabilityMeasure μ] in
lemma integral_act (g : G) (f : Func X) : ∫ x, act g f x ∂μ = ∫ x, f x ∂μ :=
  (measurePreserving_vadd g μ).integral_comp (MeasurableEquiv.vadd g).measurableEmbedding (f : X → ℂ)

lemma l2_mul_norm_le (f h : Func X) {C : ℝ} (hC : ∀ x, ‖h x‖ ≤ C) :
    ‖l2 μ (f*h)‖ ≤ C * ‖l2 μ f‖ := by
  have hC0 : 0 ≤ C := by
    have : Nonempty X := MeasureTheory.nonempty_of_isProbabilityMeasure μ
    exact (norm_nonneg (h (Classical.choice this))).trans (hC _)
  have hi : ‖l2 μ (f*h)‖^2 ≤ C^2 * ‖l2 μ f‖^2 := by
    rw [norm_l2_sq, norm_l2_sq, ← integral_const_mul]
    apply integral_mono (integrable_norm_sq μ (f*h)) ((integrable_norm_sq μ f).const_mul _)
    intro x
    change ‖f x * h x‖^2 ≤ C^2 * ‖f x‖^2
    rw [norm_mul, mul_pow]
    have hh : ‖h x‖^2 ≤ C^2 := pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hh (sq_nonneg ‖f x‖)
  have hn := norm_nonneg (l2 μ (f*h))
  have hm := norm_nonneg (l2 μ f)
  nlinarith [mul_nonneg hC0 hm]

end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable

section
variable {ι G X : Type*} [DecidableEq ι] [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X]

@[simp] lemma func_prod_apply (s : Finset ι) (f : ι → Func X) (x : X) :
    (∏ i ∈ s, f i) x = ∏ i ∈ s, f i x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

@[simp] lemma conj_conj (f : Func X) : bmConj (bmConj f) = f := by ext x; simp
lemma conj_mul (f h : Func X) : bmConj (f*h) = bmConj f * bmConj h := by ext x; simp
lemma conj_prod (s : Finset ι) (f : ι → Func X) : bmConj (∏ i ∈ s, f i) = ∏ i ∈ s, bmConj (f i) := by
  ext x
  simp
lemma comp_prod {Y : Type*} [MeasurableSpace Y] (s : Finset ι) (f : ι → Func Y)
    (q : X → Y) (hq : Measurable q) : comp (∏ i ∈ s, f i) q hq = ∏ i ∈ s, comp (f i) q hq := by
  ext x
  simp
lemma act_prod (g : G) (s : Finset ι) (f : ι → Func X) :
    act g (∏ i ∈ s, f i) = ∏ i ∈ s, act g (f i) := by ext x; simp
lemma act_zero (f : Func X) : act (0 : G) f = f := by ext x; simp

lemma prod_orbit_correlation (s : Finset ι) (φ : ι → G →+ G) (f : ι → Func X) (u h : G) :
    (∏ i ∈ s, act (φ i (u+h)) (f i)) * bmConj (∏ i ∈ s, act (φ i u) (f i)) =
    ∏ i ∈ s, act (φ i u) (act (φ i h) (f i) * bmConj (f i)) := by
  rw [conj_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_add, act_add, act_mul, act_conj]

lemma prod_shift_erase (s : Finset ι) (j : ι) (hj : j∈s)
    (φ : ι → G →+ G) (f : ι → Func X) (u : G) :
    (∏ i ∈ s, act (φ i u) (f i)) =
    act (φ j u) (f j * ∏ i ∈ s.erase j, act ((φ i - φ j) u) (f i)) := by
  rw [act_mul, act_prod]
  rw [← Finset.mul_prod_erase s (fun i => act (φ i u) (f i)) hj]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [← act_add]
  congr 1
  simp only [AddMonoidHom.sub_apply]
  abel

variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
omit [DecidableEq ι] in
lemma l2_inner_mul (f h : Func X) : inner ℝ (l2 μ f) (l2 μ (bmConj h)) =
    (∫ x, (f*h) x ∂μ).re := by
  rw [real_inner_comm, l2_inner, conj_conj]
  congr 1
  rw [mul_comm h f]

variable [TopologicalSpace G] [DiscreteTopology G]
lemma correlation_product (M : Amenable.Mean G) (s : Finset ι) (j : ι) (hj : j∈s)
    (φ : ι → G →+ G) (f : ι → Func X) (h : G) :
    M.correlation (Family.toL2 μ (∏ i ∈ s, Family.orbit (φ i) (f i)))
      (Family.toL2 μ (∏ i ∈ s, Family.orbit (φ i) (f i))) h =
    inner ℝ (Family.avg μ M (∏ i ∈ s.erase j,
      Family.orbit (φ i - φ j) (act (φ i h) (f i) * bmConj (f i))))
      (l2 μ (bmConj (act (φ j h) (f j) * bmConj (f j)))) := by
  rw [Family.avg_pair, Amenable.Mean.correlation_apply]
  congr 1
  apply BoundedContinuousFunction.ext
  intro u
  simp only [Amenable.Mean.cross_apply, Amenable.shift_apply, Family.toL2_apply,
    Family.prod_apply, Family.orbit_apply, Amenable.Mean.pairing_apply]
  rw [← conj_conj (∏ i ∈ s, act (φ i u) (f i)), l2_inner_mul]
  rw [prod_orbit_correlation, prod_shift_erase s j hj, integral_act, l2_inner_mul]
  congr 1
  rw [mul_comm]

end

section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

omit [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] in
lemma norm_l2_conj (f : Func X) : ‖l2 μ (bmConj f)‖ = ‖l2 μ f‖ := by
  have he : ‖l2 μ (bmConj f)‖^2 = ‖l2 μ f‖^2 := by simp only [norm_l2_sq, conj_apply, norm_star]
  nlinarith [norm_nonneg (l2 μ (bmConj f)), norm_nonneg (l2 μ f)]

lemma inner_replace_project (w h : Func X) (b : Func Y) (hw : w =ᵐ[μ] comp b q hq) :
    inner ℝ (l2 μ w) (l2 μ (bmConj h)) =
    inner ℝ (l2 μ w) (l2 μ (bmConj (project μ q hq h))) := by
  rw [l2_inner_mul, l2_inner_mul]
  congr 1
  calc
    (∫ x, (w*h) x ∂μ) = ∫ x, (h*comp b q hq) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hw] with x hx
      simp only [mul_apply, hx, mul_comm]
    _ = ∫ x, (project μ q hq h * comp b q hq) x ∂μ := integral_mul_lift μ q hq h b
    _ = ∫ x, (w * project μ q hq h) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hw] with x hx
      simp only [mul_apply, hx, mul_comm]

lemma inner_project_bound (w h : Func X) (b : Func Y) (hw : w =ᵐ[μ] comp b q hq)
    {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    |inner ℝ (l2 μ w) (l2 μ (bmConj h))| ≤ C * ‖l2 μ (project μ q hq h)‖ := by
  rw [inner_replace_project μ q hq w h b hw]
  calc
    |inner ℝ (l2 μ w) (l2 μ (bmConj (project μ q hq h)))| ≤
        ‖l2 μ w‖ * ‖l2 μ (bmConj (project μ q hq h))‖ := abs_real_inner_le_norm _ _
    _ ≤ C * ‖l2 μ (project μ q hq h)‖ := by
      rw [norm_l2_conj]
      exact mul_le_mul_of_nonneg_right (l2_norm_le μ w hC) (norm_nonneg _)

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
lemma avg_project_bound (M : Amenable.Mean G) (W : Family G X) (h : Func X) (b : G → Func Y)
    (hw : ∀ g, W g =ᵐ[μ] comp (b g) q hq) {C : ℝ} (hC : ∀ g x, ‖W g x‖ ≤ C) :
    |inner ℝ (Family.avg μ M W) (l2 μ (bmConj h))| ≤ C * ‖l2 μ (project μ q hq h)‖ := by
  rw [Family.avg_pair, ← M.map_const (C * ‖l2 μ (project μ q hq h)‖)]
  apply M.abs_le
  intro g
  exact inner_project_bound μ q hq (W g) h (b g) (hw g) (hC g)

variable [AddAction G X] [MeasurableConstVAdd G X] [VAddInvariantMeasure G X μ]
  [AddAction G Y] [MeasurableConstVAdd G Y]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
variable {ι : Type*} [DecidableEq ι]
omit [StandardBorelSpace Y] [Nonempty Y] [TopologicalSpace G] [DiscreteTopology G]
  [VAddInvariantMeasure G X μ] in
include hqcov in
lemma prod_act_project_lift (s : Finset ι) (ψ : ι → G →+ G) (f : ι → Func X) (u : G) :
    (∏ i ∈ s, act (ψ i u) (project μ q hq (f i))) =ᵐ[μ]
    comp (∏ i ∈ s, act (ψ i u) (conditional μ q (f i))) q hq := by
  rw [comp_prod]
  induction s using Finset.induction_on with
  | empty => exact .of_forall (fun _ => by simp)
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    filter_upwards [act_lift μ q hq hqcov (ψ i u) (conditional μ q (f i)), ih] with x hx hy
    exact congrArg₂ (·*·) hx hy

end

variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y] [AddAction G X] [MeasurableConstVAdd G X]
variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (q : X → Y) (hq : Measurable q)

def PairVanishing (M : Amenable.Mean G) : Prop :=
  ∀ (φ : G →+ G), Function.Surjective φ → ∀ v w : Func X,
    l2 μ (project μ q hq w) = 0 →
    M.map (Amenable.Mean.normFn (pairSequence μ q hq φ v w)) = 0

omit [VAddInvariantMeasure G X μ] in
lemma pairVanishing_of_ergodic [ErgodicVAdd G (X×X) (RelativeProduct.law μ q hq)]
    (M : Amenable.Mean G) : PairVanishing μ q hq M := by
  intro φ hs v w hw
  apply M.norm_mean_zero_of_square
  apply pair_mean_sq_zero μ q hq M φ hs v w
  apply norm_eq_zero.mp
  rw [← norm_project_l2 μ q hq w, hw, norm_zero]

variable {ι : Type*} [DecidableEq ι]
def Admissible (s : Finset ι) (φ : ι → G →+ G) : Prop :=
  (∀ i∈s, Function.Surjective (φ i)) ∧
  ∀ i∈s, ∀ j∈s, i≠j → Function.Surjective (φ i - φ j)

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma Admissible.erase_diff {s : Finset ι} {φ : ι → G →+ G}
    (ha : Admissible s φ) {j : ι} (hj : j∈s) :
    Admissible (s.erase j) (fun i => φ i - φ j) := by
  constructor
  · intro i hi
    exact ha.2 i (Finset.mem_of_mem_erase hi) j hj (Finset.ne_of_mem_erase hi)
  · intro i hi k hk hik
    have he : (φ i - φ j) - (φ k - φ j) = φ i - φ k := by abel
    rw [he]
    exact ha.2 i (Finset.mem_of_mem_erase hi) k (Finset.mem_of_mem_erase hk) hik

variable [AddAction G Y] [MeasurableConstVAdd G Y]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
include hqcov in
/-- Centered multiple vector averages for every invariant mean. The proof only
uses the actual conditional pair criterion, never exchanges iterated means. -/
theorem avg_product_zero_of_pair (M : Amenable.Mean G) (hpair : PairVanishing μ q hq M)
    (s : Finset ι) (φ : ι → G →+ G) (f : ι → Func X) (ha : Admissible s φ)
    (hc : ∃ j∈s, l2 μ (project μ q hq (f j)) = 0) :
    Family.avg μ M (∏ i∈s, Family.orbit (φ i) (f i)) = 0 := by
  have main : ∀ n : ℕ, ∀ (s : Finset ι), s.card ≤ n → ∀ (φ : ι → G →+ G)
      (f : ι → Func X), Admissible s φ →
      (∃ j∈s, l2 μ (project μ q hq (f j)) = 0) →
      Family.avg μ M (∏ i∈s, Family.orbit (φ i) (f i)) = 0 := by
    intro n
    induction n with
    | zero =>
      intro s hn φ f ha hc
      have hs : s = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hn)
      obtain ⟨j,hj,_⟩ := hc
      simp [hs] at hj
    | succ n ih =>
      intro s hn φ f ha hc
      obtain ⟨j,hj,hfj⟩ := hc
      let e := s.erase j
      let ψ := fun i => φ i - φ j
      have he : e.card ≤ n := by
        have := Finset.card_erase_of_mem hj
        dsimp [e]
        omega
      have had : Admissible e ψ := ha.erase_diff hj
      let F : G → ι → Func X := fun h i => act (φ i h) (f i) * bmConj (f i)
      have replace (h : G) :
          Family.avg μ M (∏ i∈e, Family.orbit (ψ i) (F h i)) =
          Family.avg μ M (∏ i∈e, Family.orbit (ψ i) (project μ q hq (F h i))) := by
        apply EuclideanFiveColor.AlgebraReplacement.add_prod_replace
          (A := Family G X) (H := Lp ℂ 2 μ) (Family.avg μ M).toAddMonoidHom e
          (fun i => Family.orbit (ψ i) (F h i))
          (fun i => Family.orbit (ψ i) (project μ q hq (F h i)))
        intro t ht htn
        have hte := Finset.mem_powerset.mp ht
        rw [EuclideanFiveColor.AlgebraReplacement.mixed_prod e t hte]
        have heq : (∏ i∈e, if i∈t then
            Family.orbit (ψ i) (F h i) - Family.orbit (ψ i) (project μ q hq (F h i))
            else Family.orbit (ψ i) (project μ q hq (F h i))) =
            ∏ i∈e, Family.orbit (ψ i)
              (if i∈t then F h i - project μ q hq (F h i) else project μ q hq (F h i)) := by
          apply Finset.prod_congr rfl
          intro i _
          split_ifs <;> simp only [Family.orbit_sub]
        rw [heq]
        apply ih e he ψ _ had
        obtain ⟨i,hit⟩ := Finset.nonempty_iff_ne_empty.mpr htn
        refine ⟨i,hte hit, ?_⟩
        rw [ite_eq_left hit]
        exact center_project_l2 μ q hq (F h i)
      let C : ℝ := ∏ i∈e, (bound (f i) : ℝ)^2
      have hCb (h u : G) (x : X) :
          ‖(∏ i∈e, Family.orbit (ψ i) (project μ q hq (F h i))) u x‖ ≤ C := by
        simp only [Family.prod_apply, Family.orbit_apply, func_prod_apply]
        rw [norm_prod]
        apply Finset.prod_le_prod₀ (fun index _ => norm_nonneg _)
        intro i _
        apply project_bound μ q hq
        intro z
        dsimp only [F, mul_apply, act_apply, conj_apply]
        rw [norm_mul, norm_star, pow_two]
        exact mul_le_mul (norm_le_bound (f i) _) (norm_le_bound (f i) _) (norm_nonneg _) (bound (f i)).coe_nonneg
      let V := Family.toL2 μ (∏ i∈s, Family.orbit (φ i) (f i))
      let a := Amenable.Mean.normFn (pairSequence μ q hq (φ j) (bmConj (f j)) (f j))
      have hcorr (h : G) : M.correlation V V h ≤ C * a h := by
        dsimp only [V]
        rw [correlation_product μ M s j hj]
        change inner ℝ (Family.avg μ M (∏ i∈e, Family.orbit (ψ i) (F h i)))
          (l2 μ (bmConj (F h j))) ≤ _
        rw [replace]
        have hb := avg_project_bound μ q hq M
          (∏ i∈e, Family.orbit (ψ i) (project μ q hq (F h i))) (F h j)
          (fun u => ∏ i∈e, act (ψ i u) (conditional μ q (F h i)))
          (fun u => by
            filter_upwards [prod_act_project_lift μ q hq hqcov e ψ (F h) u] with x hx
            simpa only [Family.prod_apply, Family.orbit_apply, func_prod_apply, Finset.prod_apply] using hx) (hCb h)
        apply (le_abs_self _).trans (hb.trans_eq ?_)
        congr 1
        rw [norm_project_l2]
        change ‖l2 (μ.map q) (conditional μ q (F h j))‖ =
          ‖l2 (μ.map q) (conditional μ q (bmConj (f j) * act (φ j h) (f j)))‖
        dsimp only [F]
        rw [mul_comm]
      change M.vector V = 0
      apply M.vector_eq_zero_of_correlation_nonpos
      have hm := M.mono (M.correlation V V) (C • a) hcorr
      rw [map_smul, show M.map a = 0 from hpair (φ j) (ha.1 j hj) (bmConj (f j)) (f j) hfj,
        smul_zero] at hm
      exact hm
  exact main s.card s le_rfl φ f ha hc

end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable.Family
variable {G X : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ] (M : Amenable.Mean G)
def meanNorm (F : Family G X) : ℝ := M.map (Amenable.Mean.normFn (toL2 μ F))
lemma meanNorm_nonneg (F : Family G X) : 0 ≤ meanNorm μ M F :=
  M.positive _ (fun g => by
    change 0 ≤ ‖l2 μ (F g)‖
    exact norm_nonneg _)
lemma meanNorm_mono {F H : Family G X} (h : ∀ g, ‖l2 μ (F g)‖ ≤ ‖l2 μ (H g)‖) :
    meanNorm μ M F ≤ meanNorm μ M H := M.mono _ _ h
lemma meanNorm_congr {F H : Family G X} (h : ∀ g, F g =ᵐ[μ] H g) :
    meanNorm μ M F = meanNorm μ M H := by
  apply congrArg M.map
  apply BoundedContinuousFunction.ext
  intro g
  exact congrArg norm ((l2_eq_iff μ _ _).mpr (h g))
lemma meanNorm_le {F : Family G X} {C : ℝ} (h : ∀ g, ‖l2 μ (F g)‖ ≤ C) :
    meanNorm μ M F ≤ C := by
  rw [meanNorm, ← M.map_const C]
  exact M.mono _ _ h
@[simp] lemma meanNorm_zero : meanNorm μ M (0 : Family G X) = 0 := by
  apply le_antisymm _ (meanNorm_nonneg μ M 0)
  apply meanNorm_le
  intro g
  change ‖l2 μ (0 : Func X)‖ ≤ 0
  rw [map_zero, norm_zero]
lemma meanNorm_add_le (F H : Family G X) :
    meanNorm μ M (F+H) ≤ meanNorm μ M F + meanNorm μ M H := by
  unfold meanNorm
  rw [← map_add]
  apply M.mono
  intro g
  simpa only [Amenable.Mean.normFn_apply, BoundedContinuousFunction.add_apply,
    toL2_apply, add_apply, map_add] using norm_add_le (l2 μ (F g)) (l2 μ (H g))
lemma meanNorm_neg (F : Family G X) : meanNorm μ M (-F) = meanNorm μ M F := by
  apply congrArg M.map
  apply BoundedContinuousFunction.ext
  intro g
  change ‖l2 μ (-(F g))‖ = ‖l2 μ (F g)‖
  rw [map_neg, norm_neg]
lemma meanNorm_sub_le (F H : Family G X) :
    meanNorm μ M (F-H) ≤ meanNorm μ M F + meanNorm μ M H := by
  have h := meanNorm_add_le μ M F (-H)
  rw [meanNorm_neg] at h
  change meanNorm μ M (F + -H) ≤ _
  exact h
lemma meanNorm_mul_le (F H : Family G X) {C : ℝ} (hC : ∀ g x, ‖H g x‖ ≤ C) :
    meanNorm μ M (F*H) ≤ C * meanNorm μ M F := by
  unfold meanNorm
  calc
    _ ≤ M.map (C • Amenable.Mean.normFn (toL2 μ F)) := by
      apply M.mono
      intro g
      exact l2_mul_norm_le μ (F g) (H g) (hC g)
    _ = _ := by rw [map_smul]; rfl
lemma meanNorm_const (f : Func X) : meanNorm μ M (const f : Family G X) = ‖l2 μ f‖ := by
  have he : Amenable.Mean.normFn (toL2 μ (const f : Family G X)) =
      BoundedContinuousFunction.const G ‖l2 μ f‖ := by
    ext g
    rfl
  unfold meanNorm
  rw [he, M.map_const]
lemma meanNorm_add_zero {F H : Family G X} (hF : meanNorm μ M F = 0) (hH : meanNorm μ M H = 0) :
    meanNorm μ M (F+H) = 0 := by
  have h := meanNorm_add_le μ M F H
  rw [hF, hH, add_zero] at h
  exact le_antisymm h (meanNorm_nonneg μ M _)
lemma meanNorm_mul_zero {F H : Family G X} (hF : meanNorm μ M F = 0) :
    meanNorm μ M (F*H) = 0 := by
  have h := meanNorm_mul_le μ M F H H.norm_le_bound
  rw [hF, mul_zero] at h
  exact le_antisymm h (meanNorm_nonneg μ M _)
lemma meanNorm_sum_zero {ι : Type*} (s : Finset ι) (F : ι → Family G X)
    (hF : ∀ i∈s, meanNorm μ M (F i) = 0) : meanNorm μ M (∑ i∈s, F i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact meanNorm_add_zero μ M (hF i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))
lemma meanNorm_eq_zero_of_approx {F : Family G X}
    (h : ∀ ε : ℝ, 0 < ε → ∃ H : Family G X, meanNorm μ M H = 0 ∧
      ∀ g, ‖l2 μ (F g - H g)‖ ≤ ε) : meanNorm μ M F = 0 := by
  apply le_antisymm _ (meanNorm_nonneg μ M F)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨H,hH,hd⟩ := h ε hε
  have hb := meanNorm_add_le μ M (F-H) H
  rw [hH, add_zero] at hb
  have ht : (F-H)+H = F := sub_add_cancel F H
  rw [ht] at hb
  have hd' : meanNorm μ M (F-H) ≤ ε := meanNorm_le μ M hd
  simpa only [zero_add] using hb.trans hd'
end EuclideanFiveColor.BoundedMeasurable.Family

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)
namespace Family
omit [AddCommGroup G] [StandardBorelSpace Y] [Nonempty Y] in
def conditional (F : Family G X) : Family G Y :=
  ⟨fun g => BoundedMeasurable.conditional μ q (F g), F.bound,
    fun g y => expect_bound _ _ (F.norm_le_bound g) y⟩
omit [AddCommGroup G] [StandardBorelSpace Y] [Nonempty Y] in
@[simp] lemma conditional_apply (F : Family G X) (g : G) :
    conditional μ q F g = BoundedMeasurable.conditional μ q (F g) := rfl
omit [AddCommGroup G] [StandardBorelSpace Y] [Nonempty Y] in
lemma conditional_add (F H : Family G X) : conditional μ q (F+H) = conditional μ q F + conditional μ q H := by
  ext g y
  exact integral_add (integrable _ (F g)) (integrable _ (H g))
omit [AddCommGroup G] [StandardBorelSpace Y] [Nonempty Y] in
lemma conditional_sub (F H : Family G X) : conditional μ q (F-H) = conditional μ q F - conditional μ q H := by
  ext g y
  exact integral_sub (integrable _ (F g)) (integrable _ (H g))
end Family
variable [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]

def covariance (φ : G →+ G) (v w : Func X) : Family G Y :=
  Family.conditional μ q (Family.const v * Family.orbit φ w) -
    Family.const (conditional μ q v) * Family.orbit φ (conditional μ q w)
omit [StandardBorelSpace Y] [Nonempty Y] in
@[simp] lemma covariance_apply (φ : G →+ G) (v w : Func X) (g : G) :
    covariance μ q φ v w g = conditional μ q (v*act (φ g) w) -
      conditional μ q v * act (φ g) (conditional μ q w) := rfl

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma covariance_add_left (φ : G →+ G) (v v' w : Func X) :
    covariance μ q φ (v+v') w = covariance μ q φ v w + covariance μ q φ v' w := by
  apply Family.ext
  intro g
  change conditional μ q ((v+v')*act (φ g) w) - conditional μ q (v+v') *
    act (φ g) (conditional μ q w) =
    (conditional μ q (v*act (φ g) w) - conditional μ q v * act (φ g) (conditional μ q w)) +
    (conditional μ q (v'*act (φ g) w) - conditional μ q v' * act (φ g) (conditional μ q w))
  unfold conditional
  rw [add_mul, expect_add, expect_add, add_mul]
  abel

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma covariance_add_right (φ : G →+ G) (v w w' : Func X) :
    covariance μ q φ v (w+w') = covariance μ q φ v w + covariance μ q φ v w' := by
  have ha (g : G) (a b : Func X) : act g (a+b) = act g a + act g b := rfl
  have hb (g : G) (a b : Func Y) : act g (a+b) = act g a + act g b := rfl
  apply Family.ext
  intro g
  change conditional μ q (v*act (φ g) (w+w')) - conditional μ q v *
    act (φ g) (conditional μ q (w+w')) =
    (conditional μ q (v*act (φ g) w) - conditional μ q v * act (φ g) (conditional μ q w)) +
    (conditional μ q (v*act (φ g) w') - conditional μ q v * act (φ g) (conditional μ q w'))
  unfold conditional
  rw [ha, mul_add, expect_add, expect_add, hb, mul_add]
  abel
variable [VAddInvariantMeasure G X μ]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
omit [VAddInvariantMeasure G X μ] in
include hqcov in
lemma conditional_mul_project_act (g : G) (v w : Func X) :
    conditional μ q (v*act g (project μ q hq w)) =ᵐ[μ.map q]
      conditional μ q v * act g (conditional μ q w) := by
  have h := act_lift μ q hq hqcov g (conditional μ q w)
  have hc : v*act g (project μ q hq w) =ᵐ[μ] v*comp (act g (conditional μ q w)) q hq := by
    filter_upwards [h] with x hx
    exact congrArg (fun t => v x*t) hx
  exact (conditional_congr μ q hq hc).trans (conditional_pullout μ q hq v _)

omit [VAddInvariantMeasure G X μ] in
include hqcov in
lemma covariance_center (φ : G →+ G) (v w : Func X) (g : G) :
    covariance μ q φ v w g =ᵐ[μ.map q]
      conditional μ q (v*act (φ g) (w-project μ q hq w)) := by
  have he : conditional μ q (v*act (φ g) (w-project μ q hq w)) =
      conditional μ q (v*act (φ g) w) - conditional μ q (v*act (φ g) (project μ q hq w)) := by
    rw [act_sub, mul_sub]
    exact (expectLinear (condDistrib id q μ)).map_sub _ _
  rw [he]
  filter_upwards [conditional_mul_project_act μ q hq hqcov (φ g) v w] with y hy
  simp only [covariance_apply, sub_apply]
  rw [hy]
  rfl

variable [TopologicalSpace G] [DiscreteTopology G]

omit [VAddInvariantMeasure G X μ] in
include hqcov in
lemma covariance_mean_zero (M : Amenable.Mean G) (hp : PairVanishing μ q hq M)
    (φ : G →+ G) (hs : Function.Surjective φ) (v w : Func X) :
    Family.meanNorm (μ.map q) M (covariance μ q φ v w) = 0 := by
  rw [Family.meanNorm_congr (μ.map q) M (F := covariance μ q φ v w)
    (H := Family.conditional μ q (Family.const v * Family.orbit φ (w-project μ q hq w)))
    (fun g => by
      simpa only [Family.conditional_apply, Family.mul_apply, Family.const_apply, Family.orbit_apply]
        using covariance_center μ q hq hqcov φ v w g)]
  have he : Family.toL2 (μ.map q) (Family.conditional μ q
      (Family.const v * Family.orbit φ (w-project μ q hq w))) =
      pairSequence μ q hq φ v (w-project μ q hq w) := by
    ext g
    rfl
  unfold Family.meanNorm
  rw [he]
  exact hp φ hs v _ (center_project_l2 μ q hq w)
end EuclideanFiveColor.BoundedMeasurable

end

end OAI
