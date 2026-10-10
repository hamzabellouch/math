import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.ParticleDensity
import OAI.Analysis.CoulombIonization.RadialBounds.SharpFreshPatchBarrier

namespace OAI

noncomputable section

namespace CoulombLT

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_LocalDensityTrace_barrier_scope

open MeasureTheory Filter
open scoped BigOperators ENNReal

open CoulombAtom

lemma infiniteDensity_aemeasurable {ι : Type*} [Countable ι]
    (f : ι → Lp ℂ 2 (volume : Measure Space)) :
    AEMeasurable (infiniteDensity f) volume :=
  AEMeasurable.tsum (fun j => ((Lp.memLp (f j)).aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal)

lemma family_trace_eq_lintegral {ι : Type*} [Countable ι]
    (f : ι → Lp ℂ 2 (volume : Measure Space)) :
    (∑' j, ENNReal.ofReal (‖f j‖^2)) = ∫⁻ x, infiniteDensity f x := by
  unfold infiniteDensity
  rw [lintegral_tsum (f := fun j x => ENNReal.ofReal (‖f j x‖^2))
    (fun j => ((Lp.memLp (f j)).aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal)]
  apply tsum_congr
  intro j
  rw [CoulombPauli.l2_norm_sq]
  exact ofReal_integral_eq_lintegral_ofReal (Lp.memLp (f j)).norm.integrable_sq
    (ae_of_all _ (fun _ => sq_nonneg _))

lemma smoothMultiply_trace {ι : Type*} [Countable ι]
    (f : ι → Lp ℂ 2 (volume : Measure Space)) (p : SmoothMultiplier spaceDirections) :
    (∑' j, ENNReal.ofReal (‖smoothMultiplyL2 p (f j)‖^2)) =
      ∫⁻ x, ENNReal.ofReal (p.value x^2)*infiniteDensity f x := by
  rw [family_trace_eq_lintegral]
  exact lintegral_congr_ae (infiniteDensity_smoothMultiply f p)

lemma complex_norm_add_sq_bound (u v : ℂ) : ‖u+v‖^2 ≤ 2*‖u‖^2+2*‖v‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (u+v)) (norm_add_le u v) 2
  nlinarith [sq_nonneg (‖u‖-‖v‖)]

lemma smoothDerivative_density_bound {ι : Type*} [Countable ι]
    (f g : ι → Lp ℂ 2 (volume : Measure Space)) (p : SmoothMultiplier spaceDirections)
    (a : Fin 3) :
    ∀ᵐ x ∂volume, infiniteDensity (fun j => smoothDerivativeProductL2 p a (f j) (g j)) x ≤
      2*ENNReal.ofReal (p.value x^2)*infiniteDensity g x+
        2*ENNReal.ofReal ((lineDeriv ℝ p.value x (spaceDirections a))^2)*infiniteDensity f x := by
  filter_upwards [ae_all_iff.mpr (fun j => smoothDerivativeProductL2_ae p a (f j) (g j))] with x hx
  have hh (j : ι) : ENNReal.ofReal (‖smoothDerivativeProductL2 p a (f j) (g j) x‖^2) ≤
      2*ENNReal.ofReal (p.value x^2)*ENNReal.ofReal (‖g j x‖^2)+
        2*ENNReal.ofReal ((lineDeriv ℝ p.value x (spaceDirections a))^2)*ENNReal.ofReal (‖f j x‖^2) := by
    rw [hx j]
    have hb := complex_norm_add_sq_bound ((p.value x:ℂ)*g j x)
      (Complex.ofReal (lineDeriv ℝ p.value x (spaceDirections a))*f j x)
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs] at hb
    have he : ENNReal.ofReal (2*(p.value x^2*‖g j x‖^2)+
        2*((lineDeriv ℝ p.value x (spaceDirections a))^2*‖f j x‖^2)) =
        2*ENNReal.ofReal (p.value x^2)*ENNReal.ofReal (‖g j x‖^2)+
        2*ENNReal.ofReal ((lineDeriv ℝ p.value x (spaceDirections a))^2)*ENNReal.ofReal (‖f j x‖^2) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      simp only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_mul (sq_nonneg _),
        ENNReal.ofReal_ofNat,mul_assoc]
    exact (ENNReal.ofReal_le_ofReal hb).trans_eq he
  change (∑' j, _) ≤ _
  calc
    _ ≤ ∑' j, (2*ENNReal.ofReal (p.value x^2)*ENNReal.ofReal (‖g j x‖^2)+
        2*ENNReal.ofReal ((lineDeriv ℝ p.value x (spaceDirections a))^2)*ENNReal.ofReal (‖f j x‖^2)) :=
      ENNReal.tsum_le_tsum hh
    _ = _ := by rw [ENNReal.tsum_add,ENNReal.tsum_mul_left,ENNReal.tsum_mul_left]; rfl

lemma smoothDerivative_trace_bound {ι : Type*} [Countable ι]
    (f g : ι → Lp ℂ 2 (volume : Measure Space)) (p : SmoothMultiplier spaceDirections)
    (a : Fin 3) :
    (∑' j, ENNReal.ofReal (‖smoothDerivativeProductL2 p a (f j) (g j)‖^2)) ≤
      2*(∫⁻ x, ENNReal.ofReal (p.value x^2)*infiniteDensity g x)+
      2*(∫⁻ x, ENNReal.ofReal ((lineDeriv ℝ p.value x (spaceDirections a))^2)*infiniteDensity f x) := by
  rw [family_trace_eq_lintegral]
  calc
    _ ≤ ∫⁻ x, (2*ENNReal.ofReal (p.value x^2)*infiniteDensity g x+
        2*ENNReal.ofReal ((lineDeriv ℝ p.value x (spaceDirections a))^2)*infiniteDensity f x) :=
      lintegral_mono_ae (smoothDerivative_density_bound f g p a)
    _ = _ := by
      have hm : AEMeasurable (fun x : Space =>
          2*(ENNReal.ofReal (p.value x^2)*infiniteDensity g x)) volume :=
        ((p.regular.continuous.pow 2).measurable.ennreal_ofReal.aemeasurable.mul
          (infiniteDensity_aemeasurable g)).const_mul (2:ℝ≥0∞)
      simp only [mul_assoc]
      rw [lintegral_add_left' hm,
        lintegral_const_mul' _ _ (by norm_num),lintegral_const_mul' _ _ (by norm_num)]

end Work_LocalDensityTrace_barrier_scope

open MeasureTheory Filter
open scoped BigOperators ENNReal

open CoulombPauli CoulombPackets CoulombAtom
variable {N : ℕ} {κ : Type*}

 def indexedFermionFamily
    (b : HilbertBasis κ ℂ (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := Space)))))
    (ψ : Fin (N+1) → fermionL2 (V := Space) (N+1))
    (p : Fin (N+1) × Fin 2 × κ) : Lp ℂ 2 (volume : Measure Space) :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • spinMarginal (splitFermion p.1 (ψ p.1)) p.2.1 (b p.2.2)

lemma indexed_density_eq [Countable κ]
    (b : HilbertBasis κ ℂ (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := Space)))))
    (ψ : Fin (N+1) → fermionL2 (V := Space) (N+1)) :
    ∀ᵐ x ∂(volume : Measure Space), infiniteDensity (indexedFermionFamily b ψ) x =
      ENNReal.ofReal (1/2:ℝ) * (∑ i : Fin (N+1), ∑ s : Fin 2, ∫⁻ y,
        ENNReal.ofReal (‖splitFermion i (ψ i) ((x,s),y)‖^2)
          ∂(configMeasure N (spinSpaceMeasure (V := Space)))) := by
  have he (p : Fin (N+1) × Fin 2 × κ) :
      (fun x => indexedFermionFamily b ψ p x) =ᵐ[volume]
        (fun x => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
          spinMarginal (splitFermion p.1 (ψ p.1)) p.2.1 (b p.2.2) x) :=
    Lp.coeFn_smul _ _
  filter_upwards [ae_all_iff.mpr he,
    ae_all_iff.mpr (fun i : Fin (N+1) => spinMarginal_slice_parseval b (splitFermion i (ψ i)))]
      with x hx hy
  unfold infiniteDensity
  simp_rw [hx,half_scale_norm_sq,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [ENNReal.tsum_mul_left,ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_prod',hy,tsum_fintype]

lemma indexed_density_weighted [Countable κ]
    (b : HilbertBasis κ ℂ (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := Space)))))
    (ψ : Fin (N+1) → fermionL2 (V := Space) (N+1))
    (w : Space → ℝ) (hw : Measurable w) :
    (∫⁻ x, ENNReal.ofReal (w x)*infiniteDensity (indexedFermionFamily b ψ) x) =
      ENNReal.ofReal (1/2:ℝ)*(∑ i : Fin (N+1), ∫⁻ q,
        ENNReal.ofReal (w (q i).1)*ENNReal.ofReal (‖ψ i q‖^2)
          ∂(configMeasure (N+1) (spinSpaceMeasure (V := Space)))) := by
  calc
    _ = ∫⁻ x, ENNReal.ofReal (1/2:ℝ)*(∑ i : Fin (N+1),
        ENNReal.ofReal (w x)*(∑ s : Fin 2, ∫⁻ y,
          ENNReal.ofReal (‖splitFermion i (ψ i) ((x,s),y)‖^2)
            ∂(configMeasure N (spinSpaceMeasure (V := Space))))) := by
      apply lintegral_congr_ae
      filter_upwards [indexed_density_eq b ψ] with x hx
      rw [hx,← Finset.mul_sum]
      ac_rfl
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finsetSum' (f := fun i x => ENNReal.ofReal (w x)*
          (∑ s : Fin 2, ∫⁻ y, ENNReal.ofReal (‖splitFermion i (ψ i) ((x,s),y)‖^2)
            ∂(configMeasure N (spinSpaceMeasure (V := Space))))) Finset.univ (fun i _ =>
          hw.ennreal_ofReal.aemeasurable.mul (coordinateDensity_aemeasurable (ψ i) i))]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => coordinate_density_weighted (ψ i) i w hw)

 def coordinateWeightedTrace (ψ : Fin (N+1) → fermionL2 (V := Space) (N+1))
    (w : Space → ℝ) : ℝ≥0∞ :=
   ∑ i : Fin (N+1), ∫⁻ q, ENNReal.ofReal (w (q i).1)*ENNReal.ofReal (‖ψ i q‖^2)
     ∂(configMeasure (N+1) (spinSpaceMeasure (V := Space)))

lemma fermionFamily_weighted [Countable κ]
    (b : HilbertBasis κ ℂ (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := Space)))))
    (ψ : fermionL2 (V := Space) (N+1)) (w : Space → ℝ) (hw : Measurable w) :
    (∫⁻ x, ENNReal.ofReal (w x)*infiniteDensity (fermionFamily b ψ) x) =
      ENNReal.ofReal (1/2:ℝ)* coordinateWeightedTrace (fun _ => ψ) w :=
  indexed_density_weighted b (fun _ => ψ) w hw

end CoulombLT

end

end OAI
