import OAI.Analysis.CircleDomains.Selection.VerticalCylinderCover

namespace OAI

/-! Turn a countable base-ball cover of a scalar level slab into an
explicit small-diameter graph cover, retaining the quadratic cost. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma graph_cover_of_base_balls {U : Set (ℝ × ℝ)} (hU : U.Countable)
    (r : (ℝ × ℝ) → ℝ) {R : ℝ} (hR : 0 < R)
    (hr : ∀ x ∈ U, 0 < r x ∧ r x ≤ 4*R)
    {A : Set (ℝ × ℝ)} (hcover : A ⊆ ⋃ x : U, closedBall (x : ℝ × ℝ) (r x))
    (f : (ℝ × ℝ) → ℝ) (t : ℝ) (hband : ∀ x ∈ A, f x ∈ Icc (t-R) (t+R)) :
    ∃ (N : U → ℕ) (T : (x : U) → Fin (N x) → Set ((ℝ × ℝ) × ℝ)),
      (fun x => (x,f x)) '' A ⊆ ⋃ x : U, ⋃ j : Fin (N x), T x j ∧
      (∀ x j, ediam (T x j) ≤ ENNReal.ofReal (8*R)) ∧
      (∑' x : U, ∑' j : Fin (N x), ediam (T x j)^2) ≤
        32*ENNReal.ofReal R * ∑' x : U, ENNReal.ofReal (r x) := by
  have : Countable U := hU.to_subtype
  choose N T hT hdiam hcost using fun x : U =>
    vertical_cylinder_cover (x : ℝ × ℝ) t (hr x x.property).1 hR (hr x x.property).2
  refine ⟨N,T,?_,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy⟩ := mem_iUnion.mp (hcover hx)
    have htmem : (x,f x) ∈ ⋃ j, T y j := hT y ⟨hy,hband x hx⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp htmem
    exact mem_iUnion.mpr ⟨y,mem_iUnion.mpr ⟨j,hj⟩⟩
  · intro x j
    exact (hdiam x j).trans (ENNReal.ofReal_le_ofReal (by linarith [(hr x x.property).2]))
  · have hbound (x : U) : (∑' j : Fin (N x), ediam (T x j)^2) ≤
        32*ENNReal.ofReal R*ENNReal.ofReal (r x) := by
      calc
        _ ≤ ∑' _j : Fin (N x), (ENNReal.ofReal (2*r x))^2 :=
          ENNReal.tsum_le_tsum (fun j => pow_le_pow_left' (hdiam x j) 2)
        _ = ENNReal.ofReal ((N x : ℝ)*(2*r x)^2) := by
          rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg (N x)),
            ENNReal.ofReal_pow (mul_nonneg (by norm_num) (hr x x.property).1.le)]
          simp
        _ ≤ ENNReal.ofReal (32*R*r x) := ENNReal.ofReal_le_ofReal (hcost x)
        _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
          norm_num
    exact (ENNReal.tsum_le_tsum hbound).trans_eq ENNReal.tsum_mul_left

end CircleDomainRigidity

end

end OAI
