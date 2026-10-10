import Mathlib
import OAI.Analysis.AffineBernstein.MatrixConcavity
import OAI.Analysis.AffineBernstein.ParametricVariationAlgebra

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/- The actual first derivative of the horizontal component, in graph coordinates. -/
def horizontalJacobian {n : ℕ} (a : Fin n → Space n → ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => dirDeriv (coordinateVector n j) (a i) x

/- The graph's normal component of an arbitrary parametrized velocity. -/
def normalVariation {n : ℕ} (u β : Space n → ℝ) (a : Fin n → Space n → ℝ)
    (x : Space n) : ℝ := β x - ∑ k, dirDeriv (coordinateVector n k) u x * a k x

/- The vertical velocity reconstructed from its normal part and horizontal part. -/
def verticalVariation {n : ℕ} (u η : Space n → ℝ) (a : Fin n → Space n → ℝ)
    (x : Space n) : ℝ := η x + ∑ k, dirDeriv (coordinateVector n k) u x * a k x

/- Actual affine-area density of the variation, in its exact graph jets. -/
def graphVariationArea {n : ℕ} (u β : Space n → ℝ) (a : Fin n → Space n → ℝ)
    (x : Space n) (t : ℝ) : ℝ :=
  variationAreaDensity (hessian u x) (hessian β x) (horizontalJacobian a x)
    (fun k => dirDeriv (coordinateVector n k) u x)
    (fun k => dirDeriv (coordinateVector n k) β x)
    (fun k => hessian (a k) x) (1 / ((n : ℝ) + 2)) t

lemma third_dirDeriv_comm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    {x : E} (hx : x ∈ Ω) (v w z : E) :
    dirDeriv v (dirDeriv w (dirDeriv z u)) x =
      dirDeriv z (dirDeriv v (dirDeriv w u)) x := by
  have he : dirDeriv w (dirDeriv z u) =ᶠ[nhds x] dirDeriv z (dirDeriv w u) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact dirDeriv_comm (hu.contDiffAt (hΩ.mem_nhds hy)) w z
  calc
    _ = dirDeriv v (dirDeriv z (dirDeriv w u)) x :=
      congrArg (fun L : E →L[ℝ] ℝ => L v) he.fderiv_eq
    _ = _ := dirDeriv_comm (contDiffAt_dirDeriv (hu.contDiffAt (hΩ.mem_nhds hx)) w) v z

lemma hessian_dirDeriv {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) {x : Space n} (hx : x ∈ Ω)
    (k i j : Fin n) :
    hessian (dirDeriv (coordinateVector n k) u) x i j =
      dirDeriv (coordinateVector n k) (fun y => hessian u y i j) x :=
  third_dirDeriv_comm hΩ hu hx _ _ _

lemma hessian_sum_on {κ : Type*} [Fintype κ] {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {f : κ → Space n → ℝ} (hf : ∀ k, ContDiffOn ℝ ∞ (f k) Ω)
    {x : Space n} (hx : x ∈ Ω) (i j : Fin n) :
    hessian (fun y => ∑ k, f k y) x i j = ∑ k, hessian (f k) x i j := by
  have he : dirDeriv (coordinateVector n j) (fun y => ∑ k, f k y) =ᶠ[nhds x]
      (fun y => ∑ k, dirDeriv (coordinateVector n j) (f k) y) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact dirDeriv_sum f (fun k => ((hf k).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)) _
  calc
    _ = dirDeriv (coordinateVector n i) (fun y => ∑ k, dirDeriv (coordinateVector n j) (f k) y) x :=
      congrArg (fun L : Space n →L[ℝ] ℝ => L (coordinateVector n i)) he.fderiv_eq
    _ = _ := dirDeriv_sum (fun k => dirDeriv (coordinateVector n j) (f k))
      (fun k => (contDiffAt_dirDeriv ((hf k).contDiffAt (hΩ.mem_nhds hx)) _).differentiableAt (by simp)) _

lemma contDiffOn_dirDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (v : E) :
    ContDiffOn ℝ ∞ (dirDeriv v f) Ω := by
  intro x hx
  exact (contDiffAt_dirDeriv (hf.contDiffAt (hΩ.mem_nhds hx)) v).contDiffWithinAt

lemma inverse_column_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : H.PosDef) (k : ι) (p : ι → ℝ) :
    (∑ i, ∑ j, H⁻¹ i j * H i k * p j) = p k := by
  have hs := Matrix.isHermitian_iff_isSymm.mp hH.isHermitian
  have hh := inverse_radial_contraction hH (Pi.single k 1) p
  simpa [Pi.single_apply, hs.apply k] using hh

lemma trace_hessian_verticalVariation {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u η : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hη : ContDiffOn ℝ ∞ η Ω)
    {a : Fin n → Space n → ℝ} (ha : ∀ k, ContDiffOn ℝ ∞ (a k) Ω)
    {x : Space n} (hx : x ∈ Ω) (hp : (hessian u x).PosDef) :
    (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian (verticalVariation u η a) x i j) =
      (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian η x i j) +
      ∑ k, (a k x * (∑ i, ∑ j, (hessian u x)⁻¹ i j *
          dirDeriv (coordinateVector n k) (fun y => hessian u y i j) x) +
        dirDeriv (coordinateVector n k) u x * (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian (a k) x i j) +
        2 * dirDeriv (coordinateVector n k) (a k) x) := by
  have hg (k : Fin n) : ContDiffOn ℝ ∞
      (fun y => dirDeriv (coordinateVector n k) u y * a k y) Ω :=
    (contDiffOn_dirDeriv hΩ hu _).mul (ha k)
  have he (i j : Fin n) : hessian (verticalVariation u η a) x i j =
      hessian η x i j + ∑ k, hessian (fun y => dirDeriv (coordinateVector n k) u y * a k y) x i j := by
    change hessian (fun y => η y + ∑ k, dirDeriv (coordinateVector n k) u y * a k y) x i j = _
    rw [hessian_add_on hΩ hη (ContDiffOn.sum (fun k _ => hg k)) hx,
      Matrix.add_apply, hessian_sum_on hΩ hg hx]
  conv_lhs => simp only [he, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  rw [hessian_product_trace hΩ (contDiffOn_dirDeriv hΩ hu _) (ha k) hx
    (inverseHessian_isSymm hp)]
  simp_rw [hessian_dirDeriv hΩ hu hx]
  congr 2
  change (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian u x i k *
    dirDeriv (coordinateVector n j) (a k) x) = _
  exact inverse_column_contraction hp k _

end AffineBernstein
end

end OAI
