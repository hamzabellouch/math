import Mathlib
import OAI.Geometry.PrescribedRicci.ComplexIntegrationByParts

namespace OAI

/-! Local Kahler Energy. -/

noncomputable section
open Matrix Filter Set Topology MeasureTheory
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth
namespace KaehlerMetric
variable {d : ℕ}

def holRealForm (j : Fin d) : (Coordinates d →L[ℝ] ℝ) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun L => (2 : ℂ)⁻¹ * ((L (coordinateVector j) : ℂ) -
        Complex.I * (L (Complex.I • coordinateVector j) : ℂ))
      map_add' := by intro L M; simp; ring
      map_smul' := by intro c L; simp [smul_eq_mul, Complex.real_smul]; ring }

def holRealDeriv (φ : Coordinates d → ℝ) (z : Coordinates d) (j : Fin d) : ℂ :=
  holRealForm j (fderiv ℝ φ z)

lemma contDiffAt_holRealDeriv {φ : Coordinates d → ℝ} {z : Coordinates d}
    (hφ : ContDiffAt ℝ ∞ φ z) (j : Fin d) :
    ContDiffAt ℝ ∞ (fun y => holRealDeriv φ y j) z :=
  (holRealForm j).contDiff.contDiffAt.comp z (hφ.fderiv_right (by simp))

lemma fderiv_holRealDeriv {φ : Coordinates d → ℝ} {z : Coordinates d}
    (hφ : ContDiffAt ℝ ∞ φ z) (j : Fin d) (v : Coordinates d) :
    fderiv ℝ (fun y => holRealDeriv φ y j) z v =
      holRealForm j (fderiv ℝ (fderiv ℝ φ) z v) := by
  have hd := ((holRealForm j).hasFDerivAt.comp z
    ((hφ.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt).fderiv
  exact congrArg (fun L : Coordinates d →L[ℝ] ℂ => L v) hd

lemma barDeriv_holRealDeriv {φ : Coordinates d → ℝ} {z : Coordinates d}
    (hφ : ContDiffAt ℝ ∞ φ z) (i j : Fin d) :
    barDeriv (fun y => holRealDeriv φ y j) z i = PotentialKaehler.potentialMatrix φ z i j := by
  unfold barDeriv
  rw [fderiv_holRealDeriv hφ, fderiv_holRealDeriv hφ]
  simp only [PotentialKaehler.potentialMatrix, PotentialKaehler.hermitianPartMatrix_apply,
    PotentialKaehler.hermitianPart, holRealForm]
  apply Complex.ext <;> simp <;> ring

lemma barDeriv_mul {f h : Coordinates d → ℂ} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) (i : Fin d) :
    barDeriv (fun y => f y * h y) z i =
      barDeriv f z i * h z + f z * barDeriv h z i := by
  unfold barDeriv
  rw [fderiv_fun_mul hf hh]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

def entryCLM (i j : Fin d) : Matrix (Fin d) (Fin d) ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℝ] ℂ).comp
    (ContinuousLinearMap.proj i : Matrix (Fin d) (Fin d) ℂ →L[ℝ] (Fin d → ℂ))

lemma fderiv_entry {f : Coordinates d → Matrix (Fin d) (Fin d) ℂ} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (i j : Fin d) (v : Coordinates d) :
    fderiv ℝ (fun y => f y i j) z v = fderiv ℝ f z v i j := by
  exact congrArg (fun L : Coordinates d →L[ℝ] ℂ => L v)
    (((entryCLM i j).hasFDerivAt.comp z hf.hasFDerivAt).fderiv)

lemma barDeriv_entry {f : Coordinates d → Matrix (Fin d) (Fin d) ℂ} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (i j k : Fin d) :
    barDeriv (fun y => f y j k) z i = barDerivative f z i j k := by
  unfold barDeriv barDerivative
  rw [fderiv_entry hf, fderiv_entry hf]
  rfl

lemma barDeriv_sum {ι : Type*} [Fintype ι] {f : ι → Coordinates d → ℂ}
    {z : Coordinates d} (hf : ∀ k, DifferentiableAt ℝ (f k) z) (i : Fin d) :
    barDeriv (fun y => ∑ k, f k y) z i = ∑ k, barDeriv (f k) z i := by
  unfold barDeriv
  rw [fderiv_fun_sum (fun k _ => hf k)]
  simp only [_root_.sum_apply, Finset.mul_sum, mul_add, Finset.sum_add_distrib]

lemma contDiffAt_barDeriv {f : Coordinates d → ℂ} {z : Coordinates d}
    (hf : ContDiffAt ℝ ∞ f z) (i : Fin d) :
    ContDiffAt ℝ ∞ (fun y => barDeriv f y i) z :=
  contDiffAt_const.mul ((contDiffAt_deriv_direction hf _).add
    (contDiffAt_const.mul (contDiffAt_deriv_direction hf _)))

variable {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma contDiffAt_weightedInverse_matrix (g : KaehlerMetric A) (a : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart a).target) :
    ContDiffAt ℝ ∞ (MongeAmpere.weightedInverse ∘ g.matrix a) z := by
  have hd : IsUnit (g.matrix a z).det := isUnit_iff_ne_zero.mpr
    (ne_of_gt (g.positive a z hz).det_pos)
  exact ((MongeAmpere.contDiffAt_weightedInverse _ hd).restrict_scalars ℝ).comp z
    ((g.smooth a).contDiffAt ((A.chart a).open_target.mem_nhds hz))

lemma weightedInverse_entry_divergence (g : KaehlerMetric A) (a : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart a).target) (k : Fin d) :
    ∑ i, barDeriv (fun y => MongeAmpere.weightedInverse (g.matrix a y) k i) z i = 0 := by
  have hd := (g.contDiffAt_weightedInverse_matrix a hz).differentiableAt (by simp)
  calc
    _ = ∑ i, barDerivative (MongeAmpere.weightedInverse ∘ g.matrix a) z i k i :=
      Finset.sum_congr rfl (fun i _ => barDeriv_entry hd i k i)
    _ = 0 := g.weightedInverse_divergence a hz k

def cofactorFlux (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (a : Fin A.count) (z : Coordinates d) (i : Fin d) : ℂ :=
  ∑ j, MongeAmpere.weightedInverse (g.matrix a z) j i * holRealDeriv (φ.localExpression a) z j

lemma contDiffAt_cofactorFlux (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (a : Fin A.count) {z : Coordinates d} (hz : z ∈ (A.chart a).target) (i : Fin d) :
    ContDiffAt ℝ ∞ (fun y => g.cofactorFlux φ a y i) z := by
  apply ContDiffAt.sum
  intro j _
  exact ((entryCLM j i).contDiff.contDiffAt.comp z
    (g.contDiffAt_weightedInverse_matrix a hz)).mul
      (contDiffAt_holRealDeriv
        ((φ.smooth a).contDiffAt ((A.chart a).open_target.mem_nhds hz)) j)

theorem cofactorFlux_divergence (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (a : Fin A.count) {z : Coordinates d} (hz : z ∈ (A.chart a).target) :
    ∑ i, barDeriv (fun y => g.cofactorFlux φ a y i) z i =
      (g.matrix a z).det * ((g.matrix a z)⁻¹ * φ.hessian a z).trace := by
  have hφ := (φ.smooth a).contDiffAt ((A.chart a).open_target.mem_nhds hz)
  have hQ := g.contDiffAt_weightedInverse_matrix a hz
  have hent (j i : Fin d) : DifferentiableAt ℝ
      (fun y => MongeAmpere.weightedInverse (g.matrix a y) j i) z :=
    ((entryCLM j i).contDiff.contDiffAt.comp z hQ).differentiableAt (by simp)
  have hhol (j : Fin d) := (contDiffAt_holRealDeriv hφ j).differentiableAt (by simp)
  have he (i : Fin d) : barDeriv (fun y => g.cofactorFlux φ a y i) z i =
      ∑ j, (barDeriv (fun y => MongeAmpere.weightedInverse (g.matrix a y) j i) z i *
        holRealDeriv (φ.localExpression a) z j +
        MongeAmpere.weightedInverse (g.matrix a z) j i * φ.hessian a z i j) := by
    calc
      _ = ∑ j, barDeriv (fun y => MongeAmpere.weightedInverse (g.matrix a y) j i *
          holRealDeriv (φ.localExpression a) y j) z i :=
        barDeriv_sum (f := fun j y => MongeAmpere.weightedInverse (g.matrix a y) j i *
          holRealDeriv (φ.localExpression a) y j) (fun j => (hent j i).mul (hhol j)) i
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        exact (barDeriv_mul (hent j i) (hhol j) i).trans
          (congrArg (fun c : ℂ => barDeriv
            (fun y => MongeAmpere.weightedInverse (g.matrix a y) j i) z i *
              holRealDeriv (φ.localExpression a) z j +
              MongeAmpere.weightedInverse (g.matrix a z) j i * c)
            (barDeriv_holRealDeriv hφ i j))
  simp_rw [he, Finset.sum_add_distrib]
  have hc : (∑ i, ∑ j,
      barDeriv (fun y => MongeAmpere.weightedInverse (g.matrix a y) j i) z i *
        holRealDeriv (φ.localExpression a) z j) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, g.weightedInverse_entry_divergence a hz, zero_mul,
      Finset.sum_const_zero]
  rw [hc, zero_add]
  simp only [MongeAmpere.weightedInverse, Matrix.smul_apply, smul_eq_mul,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma integrable_mul_barDeriv_local {f h : Coordinates d → ℂ}
    (hf : ContDiff ℝ ∞ f) (hh : ∀ z ∈ tsupport f, ContDiffAt ℝ ∞ h z)
    (hc : HasCompactSupport f) (i : Fin d) :
    Integrable (fun z => f z * barDeriv h z i) := by
  have he : (fun z => f z * barDeriv h z i) =
      fun z => (2 : ℂ)⁻¹ * (f z * fderiv ℝ h z (coordinateVector i)) +
        ((2 : ℂ)⁻¹ * Complex.I) * (f z * fderiv ℝ h z (Complex.I • coordinateVector i)) := by
    funext z
    unfold barDeriv
    ring
  rw [he]
  exact ((integrable_mul_deriv_local hf hh hc _).const_mul _).add
    ((integrable_mul_deriv_local hf hh hc _).const_mul _)

lemma integrable_barDeriv_mul_local {f h : Coordinates d → ℂ}
    (hf : ContDiff ℝ ∞ f) (hh : ∀ z ∈ tsupport f, ContDiffAt ℝ ∞ h z)
    (hc : HasCompactSupport f) (i : Fin d) :
    Integrable (fun z => barDeriv f z i * h z) := by
  have he : (fun z => barDeriv f z i * h z) =
      fun z => (2 : ℂ)⁻¹ * (fderiv ℝ f z (coordinateVector i) * h z) +
        ((2 : ℂ)⁻¹ * Complex.I) * (fderiv ℝ f z (Complex.I • coordinateVector i) * h z) := by
    funext z
    unfold barDeriv
    ring
  rw [he]
  exact ((integrable_deriv_mul_local hf hh hc _).const_mul _).add
    ((integrable_deriv_mul_local hf hh hc _).const_mul _)

theorem integral_cofactorFlux (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (a : Fin A.count) {ψ : Coordinates d → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ (A.chart a).target) :
    (∫ z, ψ z * ((g.matrix a z).det * ((g.matrix a z)⁻¹ * φ.hessian a z).trace)) =
      -(∫ z, ∑ i, barDeriv ψ z i * g.cofactorFlux φ a z i) := by
  have hd (i : Fin d) : ∀ z ∈ tsupport ψ,
      ContDiffAt ℝ ∞ (fun y => g.cofactorFlux φ a y i) z :=
    fun z hz => g.contDiffAt_cofactorFlux φ a (hs hz) i
  have hleft : (fun z => ψ z * ((g.matrix a z).det *
      ((g.matrix a z)⁻¹ * φ.hessian a z).trace)) =
      fun z => ∑ i, ψ z * barDeriv (fun y => g.cofactorFlux φ a y i) z i := by
    funext z
    rw [← Finset.mul_sum]
    by_cases hz : z ∈ tsupport ψ
    · rw [g.cofactorFlux_divergence φ a (hs hz)]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  rw [hleft, integral_finsetSum _ (fun i _ =>
    integrable_mul_barDeriv_local hψ (hd i) hc i)]
  simp_rw [integral_mul_barDeriv_local hψ (hd _) hc]
  rw [Finset.sum_neg_distrib, integral_finsetSum _ (fun i _ =>
    integrable_barDeriv_mul_local hψ (hd i) hc i)]

end KaehlerMetric
end Anticanonical.SourceSmooth

end

end OAI
