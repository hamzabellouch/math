import Mathlib

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility.MetricDensity
open scoped BigOperators
open Matrix
variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def gram (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ) : Matrix ι ι ℝ :=
  fun i j => B (b i) (b j)

lemma gram_posDef (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ u v, B u v = B v u) (hp : ∀ u : E, u ≠ 0 → 0 < B u u) :
    (gram b B).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    exact hs _ _
  · intro x hx
    let v : E := ∑ i, x i • b i
    have hv : v ≠ 0 := by
      intro h
      apply hx
      funext i
      have hi := congrArg (fun w => b.repr w i) h
      simpa [v, Finsupp.single_apply] using hi
    have he : B v v = star x ⬝ᵥ (gram b B *ᵥ x) := by
      simp [v, gram, Matrix.mulVec, dotProduct, Finset.mul_sum,
        map_sum, map_smul, mul_comm, hs]
    rw [← he]
    exact hp v hv

def density (A : Matrix ι ι ℝ) : ℝ := Real.sqrt A.det

lemma density_pos (A : Matrix ι ι ℝ) (hA : A.PosDef) : 0 < density A :=
  Real.sqrt_pos.2 hA.det_pos

lemma density_sq (A : Matrix ι ι ℝ) (hA : A.PosDef) : density A ^ 2 = A.det :=
  Real.sq_sqrt hA.det_pos.le

lemma density_transform (A L : Matrix ι ι ℝ) :
    density (L.transpose * A * L) = |L.det| * density A := by
  unfold density
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rw [show L.det * A.det * L.det = L.det ^ 2 * A.det by ring]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

lemma contDiffOn_det {n : WithTop ℕ∞} {A : D → Matrix ι ι ℝ} {U : Set D}
    (hA : ∀ i j, ContDiffOn ℝ n (fun x => A x i j) U) :
    ContDiffOn ℝ n (fun x => (A x).det) U := by
  simp only [Matrix.det_apply']
  apply ContDiffOn.sum
  intro s _
  apply contDiffOn_const.mul
  exact contDiffOn_prod (fun i _ => hA (s i) i)

lemma contDiffOn_density {n : WithTop ℕ∞} {A : D → Matrix ι ι ℝ} {U : Set D}
    (hA : ∀ i j, ContDiffOn ℝ n (fun x => A x i j) U)
    (hp : ∀ x ∈ U, (A x).PosDef) :
    ContDiffOn ℝ n (fun x => density (A x)) U := by
  exact (contDiffOn_det hA).sqrt (fun x hx => (hp x hx).det_pos.ne')

lemma contDiffOn_gram_density {n : WithTop ℕ∞} (b : Module.Basis ι ℝ E)
    {B : D → E →L[ℝ] E →L[ℝ] ℝ} {U : Set D}
    (hB : ContDiffOn ℝ n B U)
    (hs : ∀ x ∈ U, ∀ u v, B x u v = B x v u)
    (hp : ∀ x ∈ U, ∀ u : E, u ≠ 0 → 0 < B x u u) :
    ContDiffOn ℝ n (fun x => density (gram b (B x))) U := by
  apply contDiffOn_density
  · intro i j
    exact (hB.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  · intro x hx
    exact gram_posDef b (B x) (hs x hx) (hp x hx)

def pullMetric (B : E →L[ℝ] E →L[ℝ] ℝ) (L : E →L[ℝ] E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ E E ℝ).flip L ∘L B) ∘L L

@[simp] lemma pullMetric_apply (B : E →L[ℝ] E →L[ℝ] ℝ) (L : E →L[ℝ] E) (u v : E) :
    pullMetric B L u v = B (L u) (L v) := rfl

lemma gram_pullMetric (b : Module.Basis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (L : E →L[ℝ] E) :
    gram b (pullMetric B L) =
      (LinearMap.toMatrix b b L.toLinearMap).transpose * gram b B *
        LinearMap.toMatrix b b L.toLinearMap := by
  ext i j
  change B (L (b i)) (L (b j)) = _
  conv_lhs => rw [← b.sum_repr (L (b i)), ← b.sum_repr (L (b j))]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
    gram, Matrix.mul_apply, Matrix.transpose_apply, LinearMap.toMatrix_apply,
    ContinuousLinearMap.coe_coe, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma density_pullMetric (b : Module.Basis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (L : E →L[ℝ] E) :
    density (gram b (pullMetric B L)) =
      |LinearMap.det L.toLinearMap| * density (gram b B) := by
  rw [gram_pullMetric, density_transform, LinearMap.det_toMatrix]

end TamingCompatibility.MetricDensity

end

end OAI
