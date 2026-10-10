import Mathlib
import OAI.Geometry.PrescribedRicci.MatrixWirtinger
import OAI.Geometry.PrescribedRicci.MatrixWirtingerSecond

namespace OAI

/-! Chern Lu Algebra. -/

noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace MongeAmpere
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma trace_lu_identity (B G Pg Qg Ph Qh Rg Rh : Matrix n n ℂ)
    (hG : IsUnit G.det) :
    (B*Rg-B*Qh*B*Pg-B*Ph*B*Qg-B*Rh*B*G+
      B*Qh*B*Ph*B*G+B*Ph*B*Qh*B*G).trace =
    (-(B*(-Rg+Qg*G⁻¹*Pg))).trace +
      (B*(Qg-Qh*B*G)*G⁻¹*(Pg-G*B*Ph)).trace +
      (B*(-Rh+Qh*B*Ph)*B*G).trace := by
  have he : B*(Qg-Qh*B*G)*G⁻¹*(Pg-G*B*Ph) =
      B*Qg*G⁻¹*Pg-B*Qg*B*Ph-B*Qh*B*Pg+B*Qh*B*G*B*Ph := by
    simp only [mul_sub,sub_mul]
    simp only [mul_assoc,Matrix.mul_nonsing_inv_cancel_left G _ hG,
      Matrix.nonsing_inv_mul_cancel_left G _ hG]
    noncomm_ring
  rw [he]
  simp only [mul_add,add_mul,mul_neg,neg_mul,trace_add,trace_sub,trace_neg]
  have h1 : (B*Ph*B*Qg).trace = (B*Qg*B*Ph).trace := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (B*Ph) (B*Qg)
  have h2 : (B*Ph*B*Qh*B*G).trace = (B*Qh*B*G*B*Ph).trace := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (B*Ph) (B*Qh*B*G)
  simp only [mul_assoc] at h1 h2 ⊢
  linear_combination h2 - h1

end MongeAmpere
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

def curvatureMatrix (g : KaehlerMetric A) (q : Fin A.count) (z : Coordinates d)
    (b a : Fin d) : Mat :=
  -barDerivative (fun y => holDerivative (g.matrix q) y a) z b +
    barDerivative (g.matrix q) z b*(g.matrix q z)⁻¹*holDerivative (g.matrix q) z a

lemma curvatureMatrix_exchange (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a b i j : Fin d) :
    g.curvatureMatrix q z b a i j = g.curvatureMatrix q z i j b a := by
  unfold curvatureMatrix
  simp only [Matrix.add_apply,Matrix.neg_apply]
  rw [g.secondDerivative_row_symm q hz a b i j,
    g.secondDerivative_col_symm q hz a i b j]
  congr 1
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [g.holDerivative_symm q hz a k j]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [g.barDerivative_symm q hz b i l]

def curvatureRicci (g : KaehlerMetric A) (q : Fin A.count) (z : Coordinates d) : Mat :=
  fun b a => ((g.matrix q z)⁻¹*g.curvatureMatrix q z b a).trace

lemma curvature_contraction (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) :
    ∑ a, ∑ b, ((g.matrix q z)⁻¹ a b) • g.curvatureMatrix q z b a =
      g.curvatureRicci q z := by
  ext i j
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,curvatureRicci,
    Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [g.curvatureMatrix_exchange q hz a b i j]

lemma curvature_trace_contraction (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (G : Mat) :
    ∑ a, ∑ b, (g.matrix q z)⁻¹ a b *
      ((g.matrix q z)⁻¹*g.curvatureMatrix q z b a*(g.matrix q z)⁻¹*G).trace =
      ((g.matrix q z)⁻¹*g.curvatureRicci q z*(g.matrix q z)⁻¹*G).trace := by
  rw [← g.curvature_contraction q hz]
  simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,
    trace_sum,trace_smul,smul_eq_mul]

end Anticanonical.SourceSmooth.KaehlerMetric

end

end OAI
