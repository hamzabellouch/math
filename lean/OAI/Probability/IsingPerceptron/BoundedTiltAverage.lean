import Mathlib
import OAI.Probability.IsingPerceptron.VariationalDefs

namespace OAI

/-! Bounded Tilt Average. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma exp_mul_integrable_of_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {U : Ω → ℝ} (hU : Measurable U)
    {K : ℝ} (hK : ∀ x, |U x| ≤ K) (d : ℝ) :
    Integrable (fun x => Real.exp (d*U x)) P := by
  apply Integrable.of_bound ((measurable_const.mul hU).exp).aestronglyMeasurable (Real.exp (|d| * K))
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by
    change |d * U x| ≤ |d| * K
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK x) (abs_nonneg _)))

lemma integral_pos_exp_of_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {U : Ω → ℝ} (hU : Measurable U)
    {K : ℝ} (hK : ∀ x, |U x| ≤ K) (d : ℝ) :
    0 < ∫ x, Real.exp (d*U x) ∂P := by
  exact integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le)
    (exp_mul_integrable_of_bound P hU hK d) |>.mpr (by simp [Function.support,Real.exp_ne_zero])

lemma bounded_tilted_integral_abs {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {U A : Ω → ℝ} (hU : Measurable U)
    {K C : ℝ} (hK : ∀ x, |U x| ≤ K) (hA : Measurable A) (hC : ∀ x, |A x| ≤ C) (d : ℝ) :
    |∫ x, A x ∂P.tilted (fun x => d*U x)| ≤ C := by
  let := isProbabilityMeasure_tilted (exp_mul_integrable_of_bound P hU hK d)
  exact abs_integral_le_integral_abs.trans (by
    calc
      (∫ x, |A x| ∂P.tilted (fun x => d*U x)) ≤ ∫ _ : Ω, C ∂P.tilted (fun x => d*U x) :=
        integral_mono (Integrable.of_bound hA.abs.aestronglyMeasurable C
          (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs,abs_abs] using hC x)))
          (integrable_const _) hC
      _ = C := by simp)

lemma integral_tilted_eq_div {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U A : Ω → ℝ) :
    (∫ x, A x ∂P.tilted U) = (∫ x, Real.exp (U x)*A x ∂P) / (∫ x, Real.exp (U x) ∂P) := by
  rw [integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div]

 

def gaussianTiltAverage (s d : ℝ) (U A : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, A (x+Real.sqrt s*z) ∂(gaussianReal 0 1).tilted (fun z => d*U (x+Real.sqrt s*z))

lemma gaussianTiltAverage_abs_le (s d : ℝ) {U A : ℝ → ℝ}
    (hU : Measurable U) {K C : ℝ} (hK : ∀ x, |U x| ≤ K)
    (hA : Measurable A) (hC : ∀ x, |A x| ≤ C) (x : ℝ) :
    |gaussianTiltAverage s d U A x| ≤ C :=
  bounded_tilted_integral_abs _ (hU.comp (by fun_prop)) (fun z => hK _) (hA.comp (by fun_prop))
    (fun z => hC _) d

lemma gaussianTiltAverage_zero (s : ℝ) (U A : ℝ → ℝ) (x : ℝ) :
    gaussianTiltAverage s 0 U A x = ∫ z, A (x+Real.sqrt s*z) ∂gaussianReal 0 1 := by
  simp [gaussianTiltAverage]

lemma gaussianTiltAverage_eq_div (s d : ℝ) (U A : ℝ → ℝ) (x : ℝ) :
    gaussianTiltAverage s d U A x =
      (∫ z, Real.exp (d*U (x+Real.sqrt s*z))*A (x+Real.sqrt s*z) ∂gaussianReal 0 1) /
        (∫ z, Real.exp (d*U (x+Real.sqrt s*z)) ∂gaussianReal 0 1) :=
  integral_tilted_eq_div _ _ _

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma bounded_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {U : Ω → ℝ} (hU : Measurable U)
    {K : ℝ} (hK : ∀ x, |U x| ≤ K) : Integrable U P :=
  Integrable.of_bound hU.aestronglyMeasurable K (ae_of_all _ (fun x => by simpa using hK x))

lemma bounded_integral_hasDerivAt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {U D : ℝ → Ω → ℝ} {S : Set ℝ} {x : ℝ}
    (hS : S ∈ 𝓝 x) (hU : ∀ y, Measurable (U y)) (hD : Measurable (D x))
    {K C : ℝ} (hK : ∀ z, |U x z| ≤ K) (hC : ∀ y ∈ S, ∀ z, |D y z| ≤ C)
    (hd : ∀ y ∈ S, ∀ z, HasDerivAt (fun t => U t z) (D y z) y) :
    HasDerivAt (fun t => ∫ z, U t z ∂P) (∫ z, D x z ∂P) x := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hS
    (Eventually.of_forall (fun y => (hU y).aestronglyMeasurable))
    (bounded_integrable P (hU x) hK) hD.aestronglyMeasurable
    (ae_of_all _ (fun z y hy => by simpa using hC y hy z)) (integrable_const C)
    (ae_of_all _ (fun z y hy => hd y hy z))).2

lemma bounded_exp_integral_hasDerivAt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {U D : ℝ → Ω → ℝ} {S : Set ℝ} {x : ℝ}
    (hS : S ∈ 𝓝 x) (hU : ∀ y, Measurable (U y)) (hD : Measurable (D x))
    {K C : ℝ} (hK : ∀ y ∈ S, ∀ z, |U y z| ≤ K)
    (hC : ∀ y ∈ S, ∀ z, |D y z| ≤ C)
    (hd : ∀ y ∈ S, ∀ z, HasDerivAt (fun t => U t z) (D y z) y) :
    HasDerivAt (fun t => ∫ z, Real.exp (U t z) ∂P)
      (∫ z, Real.exp (U x z) * D x z ∂P) x := by
  apply bounded_integral_hasDerivAt P hS (fun y => (hU y).exp) ((hU x).exp.mul hD)
    (K := Real.exp K) (C := Real.exp K * C)
  · intro z
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hK x (mem_of_mem_nhds hS) z))
  · intro y hy z
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (Real.exp_le_exp.mpr ((le_abs_self _).trans (hK y hy z)))
      (hC y hy z) (abs_nonneg _) (Real.exp_pos _).le
  · exact fun y hy z => (hd y hy z).exp

lemma gaussianTransform_hasDerivAt {U D : ℝ → ℝ}
    (hU : Measurable U) (hD : Measurable D) {K C : ℝ}
    (hK : ∀ y, |U y| ≤ K) (hC : ∀ y, |D y| ≤ C)
    (hd : ∀ y, HasDerivAt U (D y) y) (s d x : ℝ) :
    HasDerivAt (gaussianTransform s d U) (gaussianTiltAverage s d U D x) x := by
  have hd0 : ∀ y ∈ (Set.univ : Set ℝ), ∀ z,
      HasDerivAt (fun t => U (t + Real.sqrt s*z)) (D (y+Real.sqrt s*z)) y := by
    intro y _ z
    convert (hd (y+Real.sqrt s*z)).comp y ((hasDerivAt_id y).add_const _) using 1 <;>
      first | rfl | simp only [mul_one]
  by_cases hdv : d = 0
  · subst d
    rw [show gaussianTransform s 0 U = (fun t => ∫ z, U (t+Real.sqrt s*z) ∂gaussianReal 0 1) from
      funext (fun t => by simp only [gaussianTransform,ite_true]), gaussianTiltAverage_zero]
    exact
      bounded_integral_hasDerivAt (gaussianReal 0 1) (Filter.univ_mem : Set.univ ∈ 𝓝 x)
        (fun y => hU.comp (by fun_prop)) (hD.comp (by fun_prop))
          (fun z => hK _) (fun y _ z => hC _) hd0
  · have hh := bounded_exp_integral_hasDerivAt (gaussianReal 0 1)
      (U := fun t z => d*U (t+Real.sqrt s*z)) (D := fun t z => d*D (t+Real.sqrt s*z))
      (Filter.univ_mem : Set.univ ∈ 𝓝 x)
      (fun y => measurable_const.mul (hU.comp (by fun_prop)))
      (measurable_const.mul (hD.comp (by fun_prop)))
      (K := |d| * K) (C := |d| * C)
      (fun y _ z => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK _) (abs_nonneg _))
      (fun y _ z => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _))
      (fun y hy z => (hd0 y hy z).const_mul d)
    have hp := integral_pos_exp_of_bound (gaussianReal 0 1)
      (hU.comp (by fun_prop : Measurable (fun z => x+Real.sqrt s*z))) (fun z => hK _) d
    convert (hh.log hp.ne').div_const d using 1 <;> try rfl
    · ext y
      simp only [gaussianTransform,hdv,ite_false]
    · rw [gaussianTiltAverage_eq_div]
      have he : (∫ z, Real.exp (d*U (x+Real.sqrt s*z))*(d*D (x+Real.sqrt s*z)) ∂gaussianReal 0 1) =
          d*(∫ z, Real.exp (d*U (x+Real.sqrt s*z))*D (x+Real.sqrt s*z) ∂gaussianReal 0 1) := by
        rw [← integral_const_mul]
        congr 1; ext z; ring
      rw [he]
      field_simp [hdv]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma bounded_exp_mul_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {U A : Ω → ℝ}
    (hU : Measurable U) (hA : Measurable A) {K C : ℝ}
    (hK : ∀ z, |U z| ≤ K) (hC : ∀ z, |A z| ≤ C) (d : ℝ) :
    Integrable (fun z => Real.exp (d*U z)*A z) P := by
  apply bounded_integrable P ((measurable_const.mul hU).exp.mul hA)
    (K := Real.exp (|d| * K) * C)
  intro z
  change |Real.exp (d*U z)*A z| ≤ _
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul ?_ (hC z) (abs_nonneg _) (Real.exp_pos _).le
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK z) (abs_nonneg _)))

lemma bounded_tilt_hasDerivAt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {U A DU DA : ℝ → Ω → ℝ}
    {S : Set ℝ} {x : ℝ} (hS : S ∈ 𝓝 x)
    (hU : ∀ t, Measurable (U t)) (hA : ∀ t, Measurable (A t))
    (hDU : Measurable (DU x)) (hDA : Measurable (DA x))
    {K M C L : ℝ} (hK : ∀ t ∈ S, ∀ z, |U t z| ≤ K)
    (hM : ∀ t ∈ S, ∀ z, |A t z| ≤ M)
    (hC : ∀ t ∈ S, ∀ z, |DU t z| ≤ C)
    (hL : ∀ t ∈ S, ∀ z, |DA t z| ≤ L)
    (dU : ∀ t ∈ S, ∀ z, HasDerivAt (fun a => U a z) (DU t z) t)
    (dA : ∀ t ∈ S, ∀ z, HasDerivAt (fun a => A a z) (DA t z) t) (d : ℝ) :
    HasDerivAt (fun t => ∫ z, A t z ∂P.tilted (fun z => d*U t z))
      ((∫ z, DA x z ∂P.tilted (fun z => d*U x z)) +
        d*((∫ z, A x z*DU x z ∂P.tilted (fun z => d*U x z)) -
          (∫ z, A x z ∂P.tilted (fun z => d*U x z))*
            (∫ z, DU x z ∂P.tilted (fun z => d*U x z)))) x := by
  have hx := mem_of_mem_nhds hS
  have hE : ∀ t ∈ S, ∀ z, Real.exp (d*U t z) ≤ Real.exp (|d| * K) := by
    intro t ht z
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK t ht z) (abs_nonneg _))
  have hAD : ∀ t ∈ S, ∀ z, |A t z*DU t z| ≤ M*C := by
    intro t ht z; rw [abs_mul]
    exact mul_le_mul (hM t ht z) (hC t ht z) (abs_nonneg _) ((abs_nonneg _).trans (hM t ht z))
  have hden := bounded_exp_integral_hasDerivAt P hS
    (U := fun t z => d*U t z) (D := fun t z => d*DU t z)
    (fun t => measurable_const.mul (hU t)) (measurable_const.mul hDU)
    (K := |d| * K) (C := |d| * C)
    (fun t ht z => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK t ht z) (abs_nonneg _))
    (fun t ht z => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC t ht z) (abs_nonneg _))
    (fun t ht z => (dU t ht z).const_mul d)
  have hnum := bounded_integral_hasDerivAt P hS
    (U := fun t z => Real.exp (d*U t z)*A t z)
    (D := fun t z => Real.exp (d*U t z)*DA t z + d*(Real.exp (d*U t z)*(A t z*DU t z)))
    (fun t => (measurable_const.mul (hU t)).exp.mul (hA t))
    (((measurable_const.mul (hU x)).exp.mul hDA).add
      (measurable_const.mul ((measurable_const.mul (hU x)).exp.mul ((hA x).mul hDU))))
    (K := Real.exp (|d| * K)*M) (C := Real.exp (|d| * K)*L + |d| * (Real.exp (|d| * K)*(M*C)))
    (fun z => by
      rw [abs_mul,abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (hE x hx z) (hM x hx z) (abs_nonneg _) (Real.exp_pos _).le)
    (fun t ht z => by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul,abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul (hE t ht z) (hL t ht z) (abs_nonneg _) (Real.exp_pos _).le
      · rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (hE t ht z) (hAD t ht z) (abs_nonneg _) (Real.exp_pos _).le) (abs_nonneg _))
    (fun t ht z => by
      convert (((dU t ht z).const_mul d).exp).mul (dA t ht z) using 1; first | rfl | ring)
  have hp := integral_pos_exp_of_bound P (hU x) (hK x hx) d
  have h1 := bounded_exp_mul_integrable P (hU x) hDA (hK x hx) (hL x hx) d
  have h2 := bounded_exp_mul_integrable P (hU x) ((hA x).mul hDU) (hK x hx) (hAD x hx) d
  change Integrable (fun z => Real.exp (d*U x z)*(A x z*DU x z)) P at h2
  have hde : (∫ z, Real.exp (d*U x z)*(d*DU x z) ∂P) =
      d*(∫ z, Real.exp (d*U x z)*DU x z ∂P) := by
    rw [← integral_const_mul]; congr 1; ext z; ring
  have hne : (∫ z, Real.exp (d*U x z)*DA x z + d*(Real.exp (d*U x z)*(A x z*DU x z)) ∂P) =
      (∫ z, Real.exp (d*U x z)*DA x z ∂P) + d*(∫ z, Real.exp (d*U x z)*(A x z*DU x z) ∂P) := by
    rw [integral_add h1 (h2.const_mul d),integral_const_mul]
  convert hnum.div hden hp.ne' using 1 <;> try rfl
  · ext t; exact integral_tilted_eq_div _ _ _
  · simp only [integral_tilted_eq_div]
    rw [hde,hne]
    field_simp
    ring

lemma gaussianTiltAverage_hasDerivAt {U D A B : ℝ → ℝ}
    (hU : Measurable U) (hD : Measurable D) (hA : Measurable A) (hB : Measurable B)
    {K C M L : ℝ} (hK : ∀ y, |U y| ≤ K) (hC : ∀ y, |D y| ≤ C)
    (hM : ∀ y, |A y| ≤ M) (hL : ∀ y, |B y| ≤ L)
    (dU : ∀ y, HasDerivAt U (D y) y) (dA : ∀ y, HasDerivAt A (B y) y) (s d x : ℝ) :
    HasDerivAt (gaussianTiltAverage s d U A)
      (gaussianTiltAverage s d U B x + d*(gaussianTiltAverage s d U (fun y => A y*D y) x -
        gaussianTiltAverage s d U A x*gaussianTiltAverage s d U D x)) x := by
  exact bounded_tilt_hasDerivAt (gaussianReal 0 1)
    (U := fun t z => U (t+Real.sqrt s*z)) (A := fun t z => A (t+Real.sqrt s*z))
    (DU := fun t z => D (t+Real.sqrt s*z)) (DA := fun t z => B (t+Real.sqrt s*z))
    (Filter.univ_mem : Set.univ ∈ 𝓝 x)
    (fun t => hU.comp (by fun_prop)) (fun t => hA.comp (by fun_prop))
    (hD.comp (by fun_prop)) (hB.comp (by fun_prop))
    (fun _ _ z => hK _) (fun _ _ z => hM _) (fun _ _ z => hC _) (fun _ _ z => hL _)
    (fun t _ z => by convert (dU (t+Real.sqrt s*z)).comp t ((hasDerivAt_id t).add_const _) using 1 <;> first | rfl | simp only [mul_one])
    (fun t _ z => by convert (dA (t+Real.sqrt s*z)).comp t ((hasDerivAt_id t).add_const _) using 1 <;> first | rfl | simp only [mul_one]) d

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma bounded_generator {D DD : ℝ → ℝ} {C L : ℝ}
    (hC : ∀ y, |D y| ≤ C) (hL : ∀ y, |DD y| ≤ L) (d y : ℝ) :
    |DD y + d*(D y)^2| ≤ L + |d| * C^2 := by
  refine (abs_add_le _ _).trans (add_le_add (hL y) ?_)
  rw [abs_mul,abs_pow]
  exact mul_le_mul_of_nonneg_left (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (hC y)) |>.mpr (hC y)) (abs_nonneg _)

lemma gaussian_tilted_ibp {U D DD : ℝ → ℝ}
    (hU : Measurable U) (hD : Measurable D) (hDD : Measurable DD)
    {K C L : ℝ} (hK : ∀ y, |U y| ≤ K) (hC : ∀ y, |D y| ≤ C)
    (hL : ∀ y, |DD y| ≤ L)
    (dU : ∀ y, HasDerivAt U (D y) y) (dD : ∀ y, HasDerivAt D (DD y) y)
    (r d x : ℝ) :
    (∫ z, z*D (x+r*z) ∂(gaussianReal 0 1).tilted (fun z => d*U (x+r*z))) =
      r*(∫ z, DD (x+r*z)+d*(D (x+r*z))^2
        ∂(gaussianReal 0 1).tilted (fun z => d*U (x+r*z))) := by
  let F := fun z => Real.exp (d*U (x+r*z))*D (x+r*z)
  let DF := fun z => r*(Real.exp (d*U (x+r*z))*(DD (x+r*z)+d*(D (x+r*z))^2))
  have hm : Measurable DF := by dsimp [DF]; fun_prop
  have he : ∀ z, Real.exp (d*U (x+r*z)) ≤ Real.exp (|d| * K) := by
    intro z
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK _) (abs_nonneg _)))
  have hF : ∀ z, |F z| ≤ Real.exp (|d| * K)*C := by
    intro z
    dsimp [F]
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (he z) (hC _) (abs_nonneg _) (Real.exp_pos _).le
  have hDF : ∀ z, |DF z| ≤ |r| * Real.exp (|d| * K)*(L+|d| * C^2) := by
    intro z
    dsimp [DF]
    rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
    rw [← mul_assoc]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (he z) (abs_nonneg _))
      (bounded_generator hC hL d _) (abs_nonneg _)
      (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
  have hd : ∀ z, HasDerivAt F (DF z) z := by
    intro z
    have ha : HasDerivAt (fun z => x+r*z) r z := by
      convert (((hasDerivAt_id z).const_mul r).const_add x) using 1 <;> first | rfl | simp
    have h1 := (dU (x+r*z)).comp z ha
    have h2 := (dD (x+r*z)).comp z ha
    convert ((h1.const_mul d).exp).mul h2 using 1 <;> first | rfl | dsimp [F,DF]; ring
  have hibp := gaussian_integration_by_parts_bounded hd hm hF hDF
  dsimp [F,DF] at hibp
  simp only [integral_tilted_eq_div]
  have hnum : (∫ z, Real.exp (d*U (x+r*z))*(z*D (x+r*z)) ∂gaussianReal 0 1) =
      r*(∫ z, Real.exp (d*U (x+r*z))*(DD (x+r*z)+d*(D (x+r*z))^2) ∂gaussianReal 0 1) := by
    rw [← integral_const_mul]
    calc
      _ = ∫ z, z*(Real.exp (d*U (x+r*z))*D (x+r*z)) ∂gaussianReal 0 1 := by
        congr 1; ext z; ring
      _ = _ := hibp
  rw [hnum]
  ring

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma bounded_expIntegral_hasFDerivAt {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) [IsFiniteMeasure P] {U : E → Ω → ℝ}
    {D : E → Ω → E →L[ℝ] ℝ} {S : Set E} {x : E}
    (hS : S ∈ 𝓝 x) (hU : ∀ y, Measurable (U y))
    (hD : AEStronglyMeasurable (D x) P) {K : ℝ} {B : Ω → ℝ}
    (hK : ∀ y ∈ S, ∀ z, |U y z| ≤ K)
    (hB : ∀ y ∈ S, ∀ z, ‖D y z‖ ≤ B z) (hBi : Integrable B P)
    (hd : ∀ y ∈ S, ∀ z, HasFDerivAt (fun t => U t z) (D y z) y) :
    HasFDerivAt (fun t => ∫ z, Real.exp (U t z) ∂P)
      (∫ z, Real.exp (U x z) • D x z ∂P) x := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le hS
    (Eventually.of_forall (fun y => (hU y).exp.aestronglyMeasurable))
    (bounded_integrable P (hU x).exp (K := Real.exp K) (fun z => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hK x (mem_of_mem_nhds hS) z))))
    ((hU x).exp.aestronglyMeasurable.smul hD) (bound := fun z => Real.exp K * B z)
  · exact ae_of_all _ (fun z y hy => by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (Real.exp_le_exp.mpr ((le_abs_self _).trans (hK y hy z)))
        (hB y hy z) (norm_nonneg _) (Real.exp_pos _).le)
  · exact hBi.const_mul _
  · exact ae_of_all _ (fun z y hy => (hd y hy z).exp)

lemma bounded_logIntegral_hasFDerivAt {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) [IsProbabilityMeasure P] {U : E → Ω → ℝ}
    {D : E → Ω → E →L[ℝ] ℝ} {S : Set E} {x : E}
    (hS : S ∈ 𝓝 x) (hU : ∀ y, Measurable (U y))
    (hD : AEStronglyMeasurable (D x) P) {K : ℝ} {B : Ω → ℝ}
    (hK : ∀ y ∈ S, ∀ z, |U y z| ≤ K)
    (hB : ∀ y ∈ S, ∀ z, ‖D y z‖ ≤ B z) (hBi : Integrable B P)
    (hd : ∀ y ∈ S, ∀ z, HasFDerivAt (fun t => U t z) (D y z) y) :
    HasFDerivAt (fun t => Real.log (∫ z, Real.exp (U t z) ∂P))
      (∫ z, D x z ∂P.tilted (U x)) x := by
  have hh := bounded_expIntegral_hasFDerivAt P hS hU hD hK hB hBi hd
  have hp := integral_pos_exp_of_bound P (hU x) (hK x (mem_of_mem_nhds hS)) 1
  simp only [one_mul] at hp
  have he : (∫ z, D x z ∂P.tilted (U x)) =
      (∫ z, Real.exp (U x z) ∂P)⁻¹ • (∫ z, Real.exp (U x z) • D x z ∂P) := by
    rw [integral_tilted,← integral_smul]
    congr 1; ext z
    rw [smul_smul]
    congr 1; ring_nf
  rw [he]
  exact hh.log hp.ne'

lemma bounded_average_hasFDerivAt {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) [IsProbabilityMeasure P] {U : E → Ω → ℝ}
    {D : E → Ω → E →L[ℝ] ℝ} {S : Set E} {x : E}
    (hS : S ∈ 𝓝 x) (hU : ∀ y, Measurable (U y))
    (hD : AEStronglyMeasurable (D x) P) {K : ℝ} {B : Ω → ℝ}
    (hK : ∀ y ∈ S, ∀ z, |U y z| ≤ K)
    (hB : ∀ y ∈ S, ∀ z, ‖D y z‖ ≤ B z) (hBi : Integrable B P)
    (hd : ∀ y ∈ S, ∀ z, HasFDerivAt (fun t => U t z) (D y z) y) (d : ℝ) :
    HasFDerivAt (fun t => if d = 0 then ∫ z, U t z ∂P
      else Real.log (∫ z, Real.exp (d*U t z) ∂P) / d)
      (∫ z, D x z ∂P.tilted (fun z => d*U x z)) x := by
  by_cases hz : d = 0
  · subst d
    simp only [ite_true,zero_mul,tilted_const]
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le hS
      (Eventually.of_forall (fun y => (hU y).aestronglyMeasurable))
      (bounded_integrable P (hU x) (hK x (mem_of_mem_nhds hS))) hD
      (ae_of_all _ (fun z y hy => hB y hy z)) hBi (ae_of_all _ (fun z y hy => hd y hy z))
  · have hh := bounded_logIntegral_hasFDerivAt P hS
      (U := fun t z => d*U t z) (D := fun t z => d • D t z)
      (fun y => measurable_const.mul (hU y)) (hD.const_smul d)
      (K := |d| * K) (B := fun z => |d| * B z)
      (fun y hy z => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK y hy z) (abs_nonneg _))
      (fun y hy z => by rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hB y hy z) (abs_nonneg _))
      (hBi.const_mul _) (fun y hy z => (hd y hy z).const_mul d)
    convert hh.const_mul d⁻¹ using 1 <;> try rfl
    · ext y; simp only [hz,ite_false]; ring
    · rw [integral_smul,smul_smul,inv_mul_cancel₀ hz,one_smul]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussianTransform_abs_le {U : ℝ → ℝ} (hU : Measurable U)
    {K : ℝ} (hK : ∀ y, |U y| ≤ K) (s : ℝ) {d : ℝ} (hd : 0 ≤ d) (x : ℝ) :
    |gaussianTransform s d U x| ≤ K := by
  by_cases hz : d = 0
  · subst d
    simp only [gaussianTransform,ite_true]
    simpa [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1)
        (f := fun z => U (x+Real.sqrt s*z)) (C := K)
        (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hK (x+Real.sqrt s*z)))
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hz)
    let Z := ∫ z, Real.exp (d*U (x+Real.sqrt s*z)) ∂gaussianReal 0 1
    have hi := exp_mul_integrable_of_bound (gaussianReal 0 1)
      (hU.comp (by fun_prop : Measurable (fun z => x+Real.sqrt s*z))) (fun z => hK _) d
    have hlo : Real.exp (-d*K) ≤ Z := by
      calc
        _ = ∫ _ : ℝ, Real.exp (-d*K) ∂gaussianReal 0 1 := by simp
        _ ≤ Z := integral_mono (integrable_const _) hi (fun z => Real.exp_le_exp.mpr (by
          have h := (abs_le.mp (hK (x+Real.sqrt s*z))).1
          nlinarith))
    have hhi : Z ≤ Real.exp (d*K) := by
      calc
        Z ≤ ∫ _ : ℝ, Real.exp (d*K) ∂gaussianReal 0 1 :=
          integral_mono hi (integrable_const _) (fun z => Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (abs_le.mp (hK _)).2 hd))
        _ = _ := by simp
    have hZ : 0 < Z := (Real.exp_pos _).trans_le hlo
    have hloglo := Real.log_le_log (Real.exp_pos _) hlo
    have hloghi := Real.log_le_log hZ hhi
    simp only [Real.log_exp] at hloglo hloghi
    simp only [gaussianTransform,hz,ite_false]
    change |Real.log Z/d| ≤ K
    apply abs_le.mpr
    exact ⟨(le_div_iff₀ hdpos).mpr (by nlinarith), (div_le_iff₀ hdpos).mpr (by nlinarith)⟩

lemma measurable_gaussianTransform_param {E : Type*} [MeasurableSpace E]
    {U : E → ℝ → ℝ} {s x : E → ℝ}
    (hU : Measurable (fun p : E × ℝ => U p.1 p.2)) (hs : Measurable s)
    (hx : Measurable x) (d : ℝ) :
    Measurable (fun t => gaussianTransform (s t) d (U t) (x t)) := by
  have hm : Measurable (fun p : E × ℝ => U p.1 (x p.1+Real.sqrt (s p.1)*p.2)) :=
    hU.comp (f := fun p : E × ℝ => (p.1,x p.1+Real.sqrt (s p.1)*p.2)) (by fun_prop)
  by_cases hz : d = 0
  · subst d
    simp only [gaussianTransform,ite_true]
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  · simp only [gaussianTransform,hz,ite_false]
    exact ((measurable_const.mul hm).exp.stronglyMeasurable.integral_prod_right'.measurable.log).div_const _

lemma measurable_gaussianTiltAverage_param {E : Type*} [MeasurableSpace E]
    {U A : E → ℝ → ℝ} {s x : E → ℝ}
    (hU : Measurable (fun p : E × ℝ => U p.1 p.2))
    (hA : Measurable (fun p : E × ℝ => A p.1 p.2)) (hs : Measurable s)
    (hx : Measurable x) (d : ℝ) :
    Measurable (fun t => gaussianTiltAverage (s t) d (U t) (A t) (x t)) := by
  have hm : Measurable (fun p : E × ℝ => U p.1 (x p.1+Real.sqrt (s p.1)*p.2)) :=
    hU.comp (f := fun p : E × ℝ => (p.1,x p.1+Real.sqrt (s p.1)*p.2)) (by fun_prop)
  have hn : Measurable (fun p : E × ℝ => A p.1 (x p.1+Real.sqrt (s p.1)*p.2)) :=
    hA.comp (f := fun p : E × ℝ => (p.1,x p.1+Real.sqrt (s p.1)*p.2)) (by fun_prop)
  simp only [gaussianTiltAverage_eq_div]
  exact ((measurable_const.mul hm).exp.mul hn).stronglyMeasurable.integral_prod_right'.measurable.div
    ((measurable_const.mul hm).exp.stronglyMeasurable.integral_prod_right'.measurable)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def pairLinear (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] lemma pairLinear_apply (a b : ℝ) (p : ℝ × ℝ) :
    pairLinear a b p = a*p.1+b*p.2 := rfl

lemma norm_pairLinear_le (a b : ℝ) : ‖pairLinear a b‖ ≤ |a|+|b| := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ) (abs_nonneg _)).trans_eq (mul_one _)
  · rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ) (abs_nonneg _)).trans_eq (mul_one _)

lemma measurable_pairLinear {Ω : Type*} [MeasurableSpace Ω] {A B : Ω → ℝ}
    (hA : Measurable A) (hB : Measurable B) : Measurable (fun z => pairLinear (A z) (B z)) := by
  exact (hA.smul measurable_const).add (hB.smul measurable_const)

lemma integral_pairLinear {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {A B : Ω → ℝ} (hA : Integrable A P) (hB : Integrable B P) :
    (∫ z, pairLinear (A z) (B z) ∂P) = pairLinear (∫ z, A z ∂P) (∫ z, B z ∂P) := by
  simp only [pairLinear]
  rw [integral_add (hA.smul_const _) (hB.smul_const _),integral_smul_const,integral_smul_const]

lemma integrable_tilt_of_bound {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) [IsFiniteMeasure P] {U : Ω → ℝ} {A : Ω → E} {B : Ω → ℝ}
    (hU : Measurable U) (hA : AEStronglyMeasurable A P) {K : ℝ}
    (hK : ∀ z, |U z| ≤ K) (hB : ∀ z, ‖A z‖ ≤ B z) (hBi : Integrable B P) (d : ℝ) :
    Integrable A (P.tilted (fun z => d*U z)) := by
  rw [integrable_tilted_iff (exp_mul_integrable_of_bound P hU hK d)]
  apply (hBi.const_mul (Real.exp (|d| * K))).mono'
    ((measurable_const.mul hU).exp.aestronglyMeasurable.smul hA)
  exact ae_of_all _ (fun z => by
    change ‖Real.exp (d*U z) • A z‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul _ (hB z) (norm_nonneg _) (Real.exp_pos _).le
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK z) (abs_nonneg _))))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma abs_div_two_sqrt_le {m s : ℝ} (hm : 0 < m) (hs : m ≤ s) (v : ℝ) :
    |v / (2*Real.sqrt s)| ≤ |v| / (2*Real.sqrt m) := by
  rw [abs_div,abs_of_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (hm.trans_le hs)))]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs) (by norm_num))

lemma affine_gaussian_shift_hasFDerivAt {U T X : ℝ × ℝ → ℝ} {I : Set ℝ}
    (hd : ∀ p, p.1 ∈ I → HasFDerivAt U (pairLinear (T p) (X p)) p)
    (a v z : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I) (hs : 0 < a+v*p.1) :
    HasFDerivAt (fun q : ℝ × ℝ => U (q.1,q.2+Real.sqrt (a+v*q.1)*z))
      (pairLinear (T (p.1,p.2+Real.sqrt (a+v*p.1)*z) +
        X (p.1,p.2+Real.sqrt (a+v*p.1)*z)*(v/(2*Real.sqrt (a+v*p.1))*z))
        (X (p.1,p.2+Real.sqrt (a+v*p.1)*z))) p := by
  have hf : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hg : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have hr := ((hf.const_mul v).const_add a).sqrt hs.ne'
  have hh := (hd (p.1,p.2+Real.sqrt (a+v*p.1)*z) hp).comp p (hf.prodMk (hg.add (hr.mul_const z)))
  convert hh using 1 <;> try rfl
  all_goals
    apply ContinuousLinearMap.ext
    intro w
    simp [pairLinear]
    ring

lemma gaussianFamily_raw_hasFDerivAt {U T X : ℝ × ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hU : Measurable U) (hT : Measurable T) (hX : Measurable X)
    {K CT CX : ℝ} (hK : ∀ p, |U p| ≤ K)
    (hCT : ∀ p, p.1 ∈ I → |T p| ≤ CT) (hCX : ∀ p, |X p| ≤ CX)
    (hd : ∀ p, p.1 ∈ I → HasFDerivAt U (pairLinear (T p) (X p)) p)
    (a v d : ℝ) {m : ℝ} (hm : 0 < m) (hs : ∀ t ∈ I, m ≤ a+v*t)
    {p : ℝ × ℝ} (hp : p.1 ∈ I) :
    HasFDerivAt (fun q : ℝ × ℝ => gaussianTransform (a+v*q.1) d (fun y => U (q.1,y)) q.2)
      (∫ z, pairLinear (T (p.1,p.2+Real.sqrt (a+v*p.1)*z) +
        X (p.1,p.2+Real.sqrt (a+v*p.1)*z)*(v/(2*Real.sqrt (a+v*p.1))*z))
        (X (p.1,p.2+Real.sqrt (a+v*p.1)*z))
        ∂(gaussianReal 0 1).tilted (fun z => d*U (p.1,p.2+Real.sqrt (a+v*p.1)*z))) p := by
  let S : Set (ℝ × ℝ) := Prod.fst ⁻¹' I
  let R := |v|/(2*Real.sqrt m)
  have hCX0 : 0 ≤ CX := (abs_nonneg _).trans (hCX (0,0))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hnm : S ∈ 𝓝 p := (hI.preimage continuous_fst).mem_nhds hp
  apply bounded_average_hasFDerivAt (gaussianReal 0 1) hnm
    (U := fun q z => U (q.1,q.2+Real.sqrt (a+v*q.1)*z))
    (D := fun q z => pairLinear (T (q.1,q.2+Real.sqrt (a+v*q.1)*z) +
      X (q.1,q.2+Real.sqrt (a+v*q.1)*z)*(v/(2*Real.sqrt (a+v*q.1))*z))
      (X (q.1,q.2+Real.sqrt (a+v*q.1)*z)))
    (fun q => hU.comp (by fun_prop))
    ((measurable_pairLinear ((hT.comp (by fun_prop)).add ((hX.comp (by fun_prop)).mul (by fun_prop)))
      (hX.comp (by fun_prop))).aestronglyMeasurable)
    (K := K) (B := fun z => CT+CX*(R*|z|)+CX)
    (fun q _ z => hK _) ?_ ?_ ?_ d
  · intro q hq z
    refine (norm_pairLinear_le _ _).trans (add_le_add ?_ (hCX _))
    refine (abs_add_le _ _).trans (add_le_add (hCT _ hq) ?_)
    rw [abs_mul,abs_mul]
    exact mul_le_mul (hCX _) (mul_le_mul_of_nonneg_right (abs_div_two_sqrt_le hm (hs q.1 hq) v) (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hCX0
  · exact ((integrable_const CT).add (((memLp_id_gaussianReal 1).integrable le_rfl).abs.const_mul R |>.const_mul CX)).add
      (integrable_const CX)
  · intro q hq z
    exact affine_gaussian_shift_hasFDerivAt hd a v z hq (hm.trans_le (hs q.1 hq))

end IsingPerceptron

end

end OAI
