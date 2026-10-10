import OAI.Probability.PosteriorReplicas.Geometry.TupleMoments
import OAI.Probability.PosteriorReplicas.Measures.ProductFibers

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

abbrev EqualSpace (d k m : ℕ) := Rows d k × Labels k × Tuple d m
abbrev LeftSource (d k m : ℕ) := Rows d k × Vec d × Rows d m

def leftBaseSource (d k m : ℕ) (base : BaseLaw) : Measure (LeftSource d k m) :=
  (gaussianRows d k).prod ((base.measure d).prod (gaussianRows d m))

instance {d k m : ℕ} [NeZero d] (base : BaseLaw) :
    IsProbabilityMeasure (leftBaseSource d k m base) := by
  unfold leftBaseSource
  infer_instance

def leftBasePoint {d k m : ℕ} (base : BaseLaw) (z : LeftSource d k m) : EqualSpace d k m :=
  (z.1, labels z.1 z.2.1,
    Fin.cons z.2.1 (fun i => basePoint base z.1 (labels z.1 z.2.1) (z.2.2 i)))

def leftBaseWeight {d k m : ℕ} (base : BaseLaw) (z : LeftSource d k m) : ℝ≥0∞ :=
  baseDensity base z.1 (labels z.1 z.2.1) ^ m

@[fun_prop] lemma measurable_leftBasePoint {d k m : ℕ} (base : BaseLaw) :
    Measurable (@leftBasePoint d k m base) := by
  unfold leftBasePoint
  fun_prop

@[fun_prop] lemma measurable_leftBaseWeight {d k m : ℕ} (base : BaseLaw) :
    Measurable (@leftBaseWeight d k m base) := by
  unfold leftBaseWeight
  fun_prop

def leftBaseMeasure (d k m : ℕ) (base : BaseLaw) : Measure (EqualSpace d k m) :=
  ((leftBaseSource d k m base).withDensity (leftBaseWeight base)).map (leftBasePoint base)

lemma leftBaseWeight_integral_finite {d k m : ℕ} (hd : k + m + 2 ≤ d) (hk : 1 ≤ k)
    (base : BaseLaw) : (∫⁻ z, leftBaseWeight base z ∂leftBaseSource d k m base) < ∞ := by
  let : NeZero d := ⟨by omega⟩
  have hb (z : LeftSource d k m) : leftBaseWeight base z ≤
      ENNReal.ofReal (baseProjectionConstant base d k / Real.sqrt (rowGram z.1).det)^m :=
    pow_le_pow_left' (baseDensity_le_sup (by omega) base _ _) _
  apply lt_of_le_of_lt (lintegral_mono hb)
  unfold leftBaseSource
  rw [lintegral_prod _ (by fun_prop)]
  simp only [lintegral_const, measure_univ, mul_one]
  exact base_density_sup_moment_finite hd hk base

lemma leftBaseMeasure_finite {d k m : ℕ} (hd : k + m + 2 ≤ d) (hk : 1 ≤ k)
    (base : BaseLaw) : IsFiniteMeasure (leftBaseMeasure d k m base) := by
  let := isFiniteMeasure_withDensity (leftBaseWeight_integral_finite hd hk base).ne
  unfold leftBaseMeasure
  infer_instance

lemma leftBaseMeasure_lintegral {d k m : ℕ} (base : BaseLaw) [NeZero d]
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ z, H z ∂leftBaseMeasure d k m base =
      ∫⁻ A, ∫⁻ p, baseDensity base A (labels A p)^m *
        ∫⁻ R, H (A, labels A p, Fin.cons p
          (fun i => basePoint base A (labels A p) (R i))) ∂gaussianRows d m
        ∂base.measure d ∂gaussianRows d k := by
  rw [leftBaseMeasure, lintegral_map hH (measurable_leftBasePoint base),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_leftBaseWeight base)
      (show Measurable (fun z => H (leftBasePoint base z)) from hH.comp (measurable_leftBasePoint base))]
  change (∫⁻ z, leftBaseWeight base z * H (leftBasePoint base z) ∂leftBaseSource d k m base) = _
  unfold leftBaseSource leftBaseWeight leftBasePoint
  rw [lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro A
  rw [lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro p
  dsimp only [Prod.fst, Prod.snd]
  rw [lintegral_const_mul _ (by fun_prop)]

lemma leftBaseMeasure_lintegral_fibers {d k m : ℕ} (hd : 3 ≤ d) (hk : k < d)
    (base : BaseLaw) {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ z, H z ∂leftBaseMeasure d k m base =
      ∫⁻ A, ∫⁻ y, baseDensity base A y^(m+1) *
        ∫⁻ u, H (A,y,u) ∂Measure.pi (fun _ : Fin (m+1) => baseFiber base A y)
        ∂volume ∂gaussianRows d k := by
  let : NeZero d := ⟨by omega⟩
  rw [leftBaseMeasure_lintegral base hH]
  apply lintegral_congr_ae
  filter_upwards [ae_gaussian_rows_full_rank hd hk] with A hA
  rw [base_lintegral hA hk base (by fun_prop)]
  apply lintegral_congr
  intro y
  conv_lhs => rw [baseFiber_eq_map,
    lintegral_map (by fun_prop) (measurable_basePoint_fixed base A y)]
  simp_rw [labels_basePoint hA]
  rw [lintegral_const_mul _ (by fun_prop)]
  rw [lintegral_pi_cons (baseFiber base A y) (by fun_prop)]
  have hpi (p : Vec d) := baseFiber_pi_lintegral base A y
    (g := fun v : Fin m → Vec d => H (A,y,Fin.cons p v)) (by fun_prop)
  simp_rw [hpi]
  rw [baseFiber_eq_map, lintegral_map (by fun_prop) (measurable_basePoint_fixed base A y)]
  rw [← mul_assoc, ← pow_succ']

@[simp] lemma tiltMass_one {d k : ℕ} (base : BaseLaw) (A : Rows d k) (y : Labels k) :
    tiltMass base (fun _ => 1) A y = 1 := by simp [tiltMass]

@[simp] lemma tiltedFiber_one {d k : ℕ} (base : BaseLaw) (A : Rows d k) (y : Labels k) :
    tiltedFiber base (fun _ => 1) A y = baseFiber base A y := by
  simp [tiltedFiber]

lemma leftBaseMeasure_eq_equalLabelLeft {d k m : ℕ} (hd : 3 ≤ d) (hk : k < d)
    (base : BaseLaw) {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ z, H z ∂leftBaseMeasure d k m base = equalLabelLeft base (fun _ => 1) H := by
  rw [leftBaseMeasure_lintegral_fibers hd hk base hH]
  simp only [equalLabelLeft, projectedDensity, tiltMass_one, mul_one, tiltedFiber_one]

end PosteriorReplicas
end

end OAI
