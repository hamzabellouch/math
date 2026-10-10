import OAI.Analysis.Pureness.Projections.OrthogonalPartialIsometry

namespace OAI
noncomputable section
namespace CuntzPureness
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

structure ProjectionDimension (D : Type*) [CStarAlgebra D] where
  toFun : D → ℝ
  map_zero : toFun 0=0
  map_one : toFun 1=1
  nonneg : ∀ p, IsStarProjection p → 0 ≤ toFun p
  add : ∀ p q, IsStarProjection p → IsStarProjection q → p*q=0 →
    toFun (p+q)=toFun p+toFun q
  polar : ∀ v, IsStarProjection (star v*v) → toFun (star v*v)=toFun (v*star v)

instance projectionDimensionCoeFun : CoeFun (ProjectionDimension D) (fun _ => D → ℝ) := ⟨ProjectionDimension.toFun⟩
namespace ProjectionDimension
variable (d : ProjectionDimension D)

lemma sub {p q : D} (hp : IsStarProjection p) (hq : IsStarProjection q) (hqp : q ≤ p) :
    d (p-q)=d p-d q := by
  have hd := (hq.le_iff_sub hp).mp hqp
  have ho := projection_residual_orthogonal hp hq hd hqp le_rfl
  have he := d.add q (p-q) hq hd ho.1
  rw [add_sub_cancel] at he
  linarith

lemma mono {p q : D} (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p ≤ q) :
    d p ≤ d q := by
  have hn := d.nonneg (q-p) ((hp.le_iff_sub hq).mp hpq)
  rw [d.sub hq hp hpq] at hn
  linarith

lemma le_one {p : D} (hp : IsStarProjection p) : d p ≤ 1 := by
  have h := d.mono hp (IsStarProjection.one _) (sub_nonneg.mp hp.one_sub.nonneg)
  rwa [d.map_one] at h

lemma one_sub {p : D} (hp : IsStarProjection p) : d (1-p)=1-d p := by
  rw [d.sub (IsStarProjection.one _) hp (sub_nonneg.mp hp.one_sub.nonneg),d.map_one]
end ProjectionDimension
end CuntzPureness

end

end OAI
