import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.DensityPassage
import OAI.Probability.MemoryPrecision.SharpGaussian

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

def MatrixLabelReference (d m : ℕ) : @Measure ((Fin m → Space d) × (Fin m → ℝ))
    (@MeasurableSpace.prod (Fin m → Space d) (Fin m → ℝ)
      (@MeasurableSpace.pi (Fin m) (fun _ => Space d)
        (fun _ => WithLp.measurableSpace
          (@OfNat.ofNat ℝ≥0∞ 2
            (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
              (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)))
      inferInstance) :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let euclideanMeasurable := WithLp.measurableSpace exponent (Fin d → ℝ)
  let rowMeasurable := @MeasurableSpace.pi (Fin m) (fun _ => Space d)
    (fun _ => euclideanMeasurable)
  let rowLaw := @Measure.pi (Fin m) (fun _ => Space d) inferInstance
    (fun _ => euclideanMeasurable)
    (fun _ => @stdGaussian (Space d)
      (PiLp.normedAddCommGroup exponent (fun _ : Fin d => ℝ))
      (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ))
      inferInstance euclideanMeasurable)
  @Measure.prod _ _ rowMeasurable inferInstance rowLaw volume

def ProjectionLaw {d : ℕ}
    (μ : @Measure (Space d)
      (WithLp.measurableSpace
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
            (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)))
    (m : ℕ) : @Measure ((Fin m → Space d) × (Fin m → ℝ))
      (@MeasurableSpace.prod (Fin m → Space d) (Fin m → ℝ)
        (@MeasurableSpace.pi (Fin m) (fun _ => Space d)
          (fun _ => WithLp.measurableSpace
            (@OfNat.ofNat ℝ≥0∞ 2
              (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
                (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)))
        inferInstance) :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let euclideanMeasurable := WithLp.measurableSpace exponent (Fin d → ℝ)
  let rowMeasurable := @MeasurableSpace.pi (Fin m) (fun _ => Space d)
    (fun _ => euclideanMeasurable)
  let rowLaw := @Measure.pi (Fin m) (fun _ => Space d) inferInstance
    (fun _ => euclideanMeasurable)
    (fun _ => @stdGaussian (Space d)
      (PiLp.normedAddCommGroup exponent (fun _ : Fin d => ℝ))
      (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ))
      inferInstance euclideanMeasurable)
  @Measure.map ((Fin m → Space d) × Space d) ((Fin m → Space d) × (Fin m → ℝ))
    (@MeasurableSpace.prod _ _ rowMeasurable euclideanMeasurable)
    (@MeasurableSpace.prod _ _ rowMeasurable inferInstance)
    (fun pair => (pair.1, fun index => @inner ℝ (Space d)
      (@InnerProductSpace.toInner ℝ (Space d) _
        (PiLp.seminormedAddCommGroup exponent (fun _ : Fin d => ℝ))
        (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)))
      pair.2 (pair.1 index)))
    (@Measure.prod _ _ rowMeasurable euclideanMeasurable rowLaw μ)
def ProjectedEllipsoid {d m : ℕ} (z : Space d) (R : ℝ) :
    Set ((Fin m → Space d) × (Fin m → ℝ)) :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let euclideanInner := @InnerProductSpace.toInner ℝ (Space d) _
    (PiLp.seminormedAddCommGroup exponent (fun _ : Fin d => ℝ))
    (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ))
  {pair | ∃ displacement ∈ @Metric.closedBall (Space d)
      (PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin d => ℝ))
      (WithLp.toLp exponent (fun _ => (0 : ℝ))) R,
    pair.2 = fun index => @inner ℝ (Space d) euclideanInner z (pair.1 index) +
      @inner ℝ (Space d) euclideanInner displacement (pair.1 index)}
def ProjectionNormScale (m p : ℕ) (H β R : ℝ) : ℝ :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  (two * Real.pi) ^ (-(m : ℝ) * ((p : ℝ)-1) / (two*(p : ℝ))) * H *
    R ^ (β - (m : ℝ)*(1-1/(p : ℝ))) *
    (∏ j ∈ Finset.range (p-1), J β m j) ^ (1/(p : ℝ))

lemma isClosed_projectedEllipsoid {d m : ℕ} (z : Space d) (R : ℝ) :
    IsClosed (ProjectedEllipsoid (m := m) z R) := by
  let K := Metric.closedBall (0 : Space d) R
  have hK : IsCompact K := isCompact_closedBall _ _
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let D : Set (((Fin m → Space d) × (Fin m → ℝ)) × K) :=
    {w | w.1.2 = fun j => ⟪z, w.1.1 j⟫ + ⟪(w.2 : Space d), w.1.1 j⟫}
  have hD : IsClosed D := isClosed_eq (by fun_prop) (by fun_prop)
  have he : ProjectedEllipsoid (m := m) z R = Prod.fst '' D := by
    ext Ay
    constructor
    · rintro ⟨v, hv, he⟩
      exact ⟨(Ay, ⟨v,hv⟩), he, rfl⟩
    · rintro ⟨⟨Ay,v⟩, hv, rfl⟩
      exact ⟨v, v.property, hv⟩
  rw [he]
  exact isClosedMap_fst_of_compactSpace D hD

lemma projectionLaw_ellipsoid_compl {d m : ℕ} (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {z : Space d} {R : ℝ} (hsupport : μ.support ⊆ Metric.closedBall z R) :
    projectionLaw μ m (ProjectedEllipsoid z R)ᶜ = 0 := by
  rw [projectionLaw, Measure.map_apply (by fun_prop)
    (isClosed_projectedEllipsoid z R).measurableSet.compl]
  apply measure_mono_null (t := Set.univ ×ˢ μ.supportᶜ)
  · rintro ⟨A,s⟩ hs
    refine ⟨mem_univ _, ?_⟩
    intro hss
    apply hs
    refine ⟨s-z, ?_, ?_⟩
    · change dist (s - z) (0 : Space d) ≤ R
      simpa [Metric.mem_closedBall, dist_eq_norm] using hsupport hss
    · ext j
      simp [inner_sub_left]
  · rw [Measure.prod_prod]
    simp [μ.measure_compl_support]

lemma projectionNormScale_pos {m p : ℕ} {H β R : ℝ} (hp : 2 ≤ p) (hH : 0 < H)
    (hR : 0 < R) (hgap : (m:ℝ)+(p:ℝ)-2 < β) :
    0 < ProjectionNormScale m p H β R := by
  have hJ : 0 < ∏ j ∈ Finset.range (p-1), J β m j := by
    apply Finset.prod_pos
    intro j hj
    apply J_pos
    have hj' : j+2 ≤ p := by have := Finset.mem_range.mp hj; omega
    have hj'' : (j:ℝ)+2 ≤ p := by exact_mod_cast hj'
    linarith
  unfold ProjectionNormScale
  positivity

lemma moment_root_eq_scale {m p : ℕ} {H β R : ℝ} (hp : 2 ≤ p) (hH : 0 < H)
    (hR : 0 < R) (hgap : (m:ℝ)+(p:ℝ)-2 < β) :
    (gaussianPeak ^ ((p-1)*m) * ENNReal.ofReal
      (H^p * R^(β*(p:ℝ)-(m:ℝ)*((p-1:ℕ):ℝ)) * ∏ j : Fin (p-1), J β m j)) ^ (1/(p:ℝ)) =
      ENNReal.ofReal (ProjectionNormScale m p H β R) := by
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hp1 : 1 ≤ p := by omega
  have hprod : 0 < ∏ j : Fin (p-1), J β m j := by
    apply Finset.prod_pos
    intro j _
    apply J_pos
    have hj : (j:ℝ)+2 ≤ p := by exact_mod_cast (show (j:ℕ)+2 ≤ p by have := j.isLt; omega)
    linarith
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), gaussianPeak,
    ← ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_rpow_of_pos (by positivity),
    ENNReal.ofReal_rpow_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.mul_rpow (by positivity : 0 ≤ H^p * R^(β*p-m*((p-1:ℕ):ℝ))) hprod.le,
    Real.mul_rpow (by positivity : 0 ≤ H^p) (by positivity),
    ← Real.rpow_natCast_mul hH.le, mul_one_div_cancel hp0, Real.rpow_one,
    ← Real.rpow_mul hR.le,
    ← Real.rpow_natCast_mul (by positivity : 0 ≤ (Real.sqrt (2*Real.pi))⁻¹),
    Real.inv_rpow (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_mul hpi.le,
    ← Real.rpow_neg hpi.le]
  have he1 : -(1/2 * (((p-1:ℕ):ℝ)*(m:ℝ) * (1/(p:ℝ)))) =
      -(m:ℝ)*((p:ℝ)-1)/(2*(p:ℝ)) := by rw [Nat.cast_sub hp1]; push_cast; ring
  have he2 : (β*(p:ℝ)-(m:ℝ)*((p-1:ℕ):ℝ)) * (1/(p:ℝ)) =
      β-(m:ℝ)*(1-1/(p:ℝ)) := by rw [Nat.cast_sub hp1]; push_cast; field_simp
  simp only [Nat.cast_mul] at *
  rw [he1, he2, Fin.prod_univ_eq_prod_range]
  unfold ProjectionNormScale
  ring

local instance final_reference_sigmaFinite (d m : ℕ) :
    SigmaFinite (matrixLabelReference (E := Space d) m) := by
  unfold matrixLabelReference
  infer_instance
local instance final_projection_finite {d : ℕ} (μ : Measure (Space d)) [IsFiniteMeasure μ] (m : ℕ) :
    IsFiniteMeasure (projectionLaw μ m) := by
  unfold projectionLaw
  infer_instance

lemma exact_finite_density (d m p : ℕ) (hp : 2 ≤ p) (hm : 1 ≤ m)
    (β H R : ℝ) (hgap : (m:ℝ)+(p:ℝ)-2 < β) (hH : 0 < H) (hR : 0 < R)
    (z : Space d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hsupport : μ.support ⊆ Metric.closedBall z R) (hball : AmbientBallBound μ H β) :
    ∃ F : ((Fin m → Space d) × (Fin m → ℝ)) → ℝ,
      Measurable F ∧ (∀ x, 0 ≤ F x) ∧
      (MatrixLabelReference d m).withDensity (fun x => ENNReal.ofReal (F x)) =
        ProjectionLaw μ m ∧
      (∀ᵐ x ∂MatrixLabelReference d m, x ∉ ProjectedEllipsoid z R → F x = 0) ∧
      eLpNorm F (p : ℝ≥0∞) (MatrixLabelReference d m) ≤
        ENNReal.ofReal (ProjectionNormScale m p H β R) := by
  let C := gaussianPeak ^ ((p-1)*m) * ENNReal.ofReal
    (H^p * R^(β*(p:ℝ)-(m:ℝ)*((p-1:ℕ):ℝ)) * ∏ j : Fin (p-1), J β m j)
  have hC : C ≠ ∞ := by unfold C gaussianPeak; finiteness
  have hp1 : p-1+1 = p := by omega
  have hmom : ∀ φ : ℝ → ℝ≥0∞, Measurable φ → (∫⁻ x, φ x = 1) →
      (∫⁻ Ay, projectionSmoothing μ φ m Ay ^ (p-1+1) ∂matrixLabelReference m) ≤ C := by
    intro φ hφ hφ1
    have hg : ((p-1:ℕ):ℝ)+(m:ℝ)-1 < β := by
      rw [Nat.cast_sub (by omega : 1 ≤ p)]
      push_cast
      linarith
    simpa only [hp1] using sharp_projectionSmoothing_moment hH hR hsupport hball φ hφ hφ1 hm (p-1) hg
  have hac := projectionLaw_ac_of_moment μ m (p-1) (by omega) C hC hmom
  let G := (projectionLaw μ m).rnDeriv (matrixLabelReference m)
  have hG : Measurable G := Measure.measurable_rnDeriv _ _
  have hden : (matrixLabelReference m).withDensity G = projectionLaw μ m :=
    Measure.withDensity_rnDeriv_eq _ _ hac
  have hGtop : ∀ᵐ x ∂matrixLabelReference m, G x ≠ ∞ := Measure.rnDeriv_ne_top _ _
  have hGmom : (∫⁻ x, G x^p ∂matrixLabelReference m) ≤ C := by
    simpa only [hp1] using projectionLaw_rnDeriv_moment μ m (p-1) (by omega) C hC hmom
  let F := fun x => (G x).toReal
  have hFG : (fun x => ENNReal.ofReal (F x)) =ᵐ[matrixLabelReference m] G := by
    filter_upwards [hGtop] with x hx
    exact ENNReal.ofReal_toReal hx
  refine ⟨F, hG.ennreal_toReal, fun _ => ENNReal.toReal_nonneg, ?_, ?_, ?_⟩
  · change (matrixLabelReference m).withDensity _ = projectionLaw μ m
    rw [withDensity_congr_ae hFG, hden]
  · have hnull := projectionLaw_ellipsoid_compl μ hsupport (m := m)
    rw [← hden, withDensity_apply _ (isClosed_projectedEllipsoid z R).measurableSet.compl] at hnull
    have hz := (lintegral_eq_zero_iff' hG.aemeasurable).mp hnull
    change ∀ᵐ x ∂(matrixLabelReference m).restrict (ProjectedEllipsoid z R)ᶜ, G x = 0 at hz
    rw [ae_restrict_iff' (isClosed_projectedEllipsoid z R).measurableSet.compl] at hz
    filter_upwards [hz] with x hx hnot
    dsimp [F]
    rw [hx hnot]
    rfl
  · change eLpNorm F (p:ℝ≥0∞) (matrixLabelReference m) ≤ _
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast (by omega : p ≠ 0))
      (by finiteness) hG.ennreal_toReal.aestronglyMeasurable]
    simp only [ENNReal.toReal_natCast]
    have he : (fun x => ‖F x‖ₑ ^ (p:ℝ)) =ᵐ[matrixLabelReference m] (fun x => G x^p) := by
      filter_upwards [hFG] with x hx
      rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, hx, ENNReal.rpow_natCast]
    rw [lintegral_congr_ae he]
    exact (ENNReal.rpow_le_rpow hGmom (by positivity)).trans_eq
      (moment_root_eq_scale hp hH hR hgap)

def FiniteDensityStatement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∀ d m p : ℕ,
  letI : MeasurableSpace (Space d) := WithLp.measurableSpace exponent (Fin d → ℝ)
  1 ≤ d → 1 ≤ m → 2 ≤ p →
  ∀ β H R : ℝ, (m : ℝ)+(p : ℝ)-two < β → 0 < H → 0 < R →
  ∀ z : Space d, ∀ μ : Measure (Space d), IsFiniteMeasure μ →
    @Measure.support (Space d)
      (PiLp.topologicalSpace (p := exponent) (β := fun _ : Fin d => ℝ))
      (WithLp.measurableSpace exponent (Fin d → ℝ)) μ ⊆
      @Metric.closedBall (Space d)
        (PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin d => ℝ)) z R →
    AmbientBallBound μ H β →
    ∃ F : ((Fin m → Space d) × (Fin m → ℝ)) → ℝ,
      Measurable F ∧ (∀ x, 0 ≤ F x) ∧
      (MatrixLabelReference d m).withDensity (fun x => ENNReal.ofReal (F x)) =
        ProjectionLaw μ m ∧
      (∀ᵐ x ∂MatrixLabelReference d m, x ∉ ProjectedEllipsoid z R → F x = 0) ∧
      eLpNorm F (p : ℝ≥0∞) (MatrixLabelReference d m) ≤
        ENNReal.ofReal (ProjectionNormScale m p H β R)

theorem finite_density : FiniteDensityStatement := by
  intro d m p _ hm hp β H R hgap hH hR z μ hμ hs hb
  let := hμ
  exact exact_finite_density d m p hp hm β H R hgap hH hR z μ hs hb
end MemoryPrecision


end

end OAI
