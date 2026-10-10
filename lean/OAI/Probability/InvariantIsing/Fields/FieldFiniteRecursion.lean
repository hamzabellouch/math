import OAI.Probability.InvariantIsing.Fields.FieldFiniteTransformBounds

namespace OAI

/-! Closure of the finite scalar Ising recursion under joint height and
spatial derivatives. The Hessian symmetry is part of the constructed data. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma measurable_value (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) :
    Measurable (F.value a v ζ) :=
  measurable_gaussianTransform_param (F.mU.comp (by fun_prop))
    (by dsimp only [fieldFiniteVariance]; fun_prop) measurable_snd ζ

def transform (hI : IsOpen I) (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    (V R D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hlo : ∀ t ∈ I, 0 < fieldFiniteVariance a v t)
    (hhi : ∀ t ∈ I, fieldFiniteVariance a v t ≤ V)
    (hc : ∀ t ∈ I, ∀ i, |fieldFiniteSlope a v t i| ≤ R)
    (hd : ∀ t ∈ I, ∀ i j, |fieldFiniteCurvature a v t i j| ≤ D) : FieldFiniteFamily n I := by
  have hX := F.kx_nonneg
  have hXX := F.kxx_nonneg
  have hP := F.kp_nonneg
  have hPX := F.kpx_nonneg
  have hPP := F.kpp_nonneg
  have hM := (F.affineMomentCap_pos ζ V).le
  exact
  { U := F.value a v ζ
    X := F.mean a v ζ
    XX := F.curvature a v ζ
    P := F.tangent a v ζ
    PX := F.mixedMean a v ζ
    PP := F.secondMean a v ζ
    KX := F.KX
    KXX := F.KXX + 2 * |ζ| * F.KX ^ 2
    KP := F.tangentCap R ζ V
    KPX := F.mixedMeanCap R ζ V
    KPP := F.secondMeanCap R D ζ V
    kx_nonneg := hX
    kxx_nonneg := by positivity
    kp_nonneg := by unfold tangentCap; positivity
    kpx_nonneg := by unfold mixedMeanCap; positivity
    kpp_nonneg := by unfold secondMeanCap; positivity
    mU := F.measurable_value a v ζ
    mX := F.measurable_mean a v ζ
    mXX := F.measurable_curvature a v ζ
    mP := F.measurable_tangent a v ζ
    mPX := F.measurable_mixedMean a v ζ
    mPP := F.measurable_secondMean a v ζ
    bX := fun p hp => F.bound_mean a v ζ hp
    bXX := fun p hp => F.bound_curvature a v ζ hp
    bP := fun i p hp => F.bound_tangent a v ζ i hp hR (hc p.1 hp i) (hhi p.1 hp)
    bPX := fun i p hp => F.bound_mixedMean a v ζ i hp hR (hc p.1 hp i) (hhi p.1 hp)
    bPP := fun i j p hp => F.bound_secondMean a v ζ i j hp hR hD
      (hc p.1 hp i) (hc p.1 hp j) (hd p.1 hp i j) (hhi p.1 hp)
    derivative := fun p hp => F.value_coordinate_derivative hI a v ζ hR hlo hhi hc hp
    derivativeX := fun p hp => F.mean_hasFDerivAt hI a v ζ hR hlo hhi hc hp
    derivativeP := fun i p hp => F.tangent_hasFDerivAt hI a v ζ i hR hD hlo hhi hc hd hp
    symmetric := fun i j p hp => F.secondMean_symmetric a v ζ i j hp }

end FieldFiniteFamily

structure FieldFiniteStep (n : ℕ) where
  base : ℝ
  slope : Fin n → ℝ
  exponent : ℝ

def fieldFiniteValue {n : ℕ} : List (FieldFiniteStep n) → FieldCovariate n → ℝ
  | [], p => Real.log (Real.cosh p.2)
  | av :: L, p => gaussianTransform (fieldFiniteVariance av.base av.slope p.1)
      av.exponent (fun y => fieldFiniteValue L (p.1, y)) p.2

def fieldFiniteFamily {n : ℕ} (I : Set (Fin n → ℝ)) (hI : IsOpen I)
    (V R D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    (L : List (FieldFiniteStep n)) →
      (∀ av ∈ L, ∀ t ∈ I, 0 < fieldFiniteVariance av.base av.slope t ∧
        fieldFiniteVariance av.base av.slope t ≤ V) →
      (∀ av ∈ L, ∀ t ∈ I, ∀ i, |fieldFiniteSlope av.base av.slope t i| ≤ R) →
      (∀ av ∈ L, ∀ t ∈ I, ∀ i j, |fieldFiniteCurvature av.base av.slope t i j| ≤ D) →
      FieldFiniteFamily n I
  | [], _, _, _ => fieldFiniteLogCosh n I
  | av :: L, hL, hc, hd =>
      (fieldFiniteFamily I hI V R D hR hD L
        (fun bv hb => hL bv (List.mem_cons_of_mem av hb))
        (fun bv hb => hc bv (List.mem_cons_of_mem av hb))
        (fun bv hb => hd bv (List.mem_cons_of_mem av hb))).transform hI av.base av.slope av.exponent
          V R D hR hD (fun t ht => (hL av List.mem_cons_self t ht).1)
          (fun t ht => (hL av List.mem_cons_self t ht).2)
          (hc av List.mem_cons_self) (hd av List.mem_cons_self)

theorem fieldFiniteFamily_value {n : ℕ} (I : Set (Fin n → ℝ)) (hI : IsOpen I)
    (V R D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (L : List (FieldFiniteStep n))
    (hL : ∀ av ∈ L, ∀ t ∈ I, 0 < fieldFiniteVariance av.base av.slope t ∧
      fieldFiniteVariance av.base av.slope t ≤ V)
    (hc : ∀ av ∈ L, ∀ t ∈ I, ∀ i, |fieldFiniteSlope av.base av.slope t i| ≤ R)
    (hd : ∀ av ∈ L, ∀ t ∈ I, ∀ i j, |fieldFiniteCurvature av.base av.slope t i j| ≤ D) :
    (fieldFiniteFamily I hI V R D hR hD L hL hc hd).U = fieldFiniteValue L := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    funext p
    simp only [fieldFiniteFamily, FieldFiniteFamily.transform, FieldFiniteFamily.value,
      fieldFiniteValue]
    rw [ih]

end InvariantIsing

end

end OAI
