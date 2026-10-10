import OAI.Geometry.PolarProducts.Nonsqueezing

namespace OAI

universe u128

section
namespace ConvexPolar
open Set Filter
open scoped Topology
noncomputable section
variable {E : Type u128} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inner_lt_one_of_mem_interior {K : Set E} {p x : E}
    (hp : p ∈ polar K) (hp0 : p ≠ 0) (hx : x ∈ interior K) :
    inner (𝕜 := ℝ) p x < 1 := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  let t := r/(2*‖p‖)
  have ht : 0 < t := div_pos hr (mul_pos (by norm_num) (norm_pos_iff.mpr hp0))
  have htn : t*‖p‖ = r/2 := by dsimp [t]; field_simp
  have hy : x+t • p ∈ K := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht, htn]
    exact half_lt_self hr
  have hh := hp _ hy
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm] at hh
  have hpos : 0 < t*‖p‖^2 := mul_pos ht (sq_pos_of_pos (norm_pos_iff.mpr hp0))
  linarith

theorem abs_inner_lt_one_of_mem_interior {K : Set E}
    (hs : ∀ x, x ∈ K ↔ -x ∈ K) {p x : E}
    (hp : p ∈ polar K) (hp0 : p ≠ 0) (hx : x ∈ interior K) :
    |inner (𝕜 := ℝ) p x| < 1 := by
  have hpneg : -p ∈ polar K := by
    intro q hq
    have hh := hp (-q) ((hs q).mp hq)
    simpa only [inner_neg_left, inner_neg_right] using hh
  have hpos := inner_lt_one_of_mem_interior hp hp0 hx
  have hneg := inner_lt_one_of_mem_interior hpneg (neg_ne_zero.mpr hp0) hx
  rw [inner_neg_left] at hneg
  exact abs_lt.mpr ⟨by linarith, hpos⟩

theorem polar_symmetric {K : Set E} (hs : ∀ x, x ∈ K ↔ -x ∈ K) :
    ∀ p, p ∈ polar K ↔ -p ∈ polar K := by
  have hh : ∀ p ∈ polar K, -p ∈ polar K := by
    intro p hp x hx
    simpa only [inner_neg_left, inner_neg_right] using hp (-x) ((hs x).mp hx)
  intro p
  exact ⟨hh p, fun hp => by simpa using hh (-p) hp⟩

theorem exists_support_pair {K : Set E}
    (hc : IsCompact K) (h0 : (0 : E) ∈ interior K) {v : E} (hv : v ≠ 0) :
    ∃ q ∈ K, ∃ p ∈ polar K, inner (𝕜 := ℝ) p q = 1 := by
  obtain ⟨q, hq, hmax⟩ := hc.exists_isMaxOn ⟨0, interior_subset h0⟩
    (show ContinuousOn (fun x : E => inner (𝕜 := ℝ) v x) K from by fun_prop)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  have hx : (r/(2*‖v‖)) • v ∈ K := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr (mul_pos (by norm_num) (norm_pos_iff.mpr hv)))]
    have he : r/(2*‖v‖)*‖v‖ = r/2 := by field_simp
    rw [he]
    exact half_lt_self hr
  have hspos : 0 < inner (𝕜 := ℝ) v q := by
    have hh : inner (𝕜 := ℝ) v ((r/(2*‖v‖)) • v) ≤ inner (𝕜 := ℝ) v q := hmax hx
    have he : inner (𝕜 := ℝ) v ((r/(2*‖v‖)) • v) = r/2*‖v‖ := by
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    rw [he] at hh
    exact (mul_pos (half_pos hr) (norm_pos_iff.mpr hv)).trans_le hh
  refine ⟨q, hq, (inner (𝕜 := ℝ) v q)⁻¹ • v, ?_, ?_⟩
  · intro x hx
    rw [real_inner_smul_right, show inner (𝕜 := ℝ) x v = inner (𝕜 := ℝ) v x from real_inner_comm _ _, ← div_eq_inv_mul]
    exact (div_le_one hspos).mpr (hmax hx)
  · rw [real_inner_smul_left, inv_mul_cancel₀ hspos.ne']

end
end ConvexPolar

namespace SymmetricPolar
open Set
noncomputable section
variable {n : ℕ}

def canonicalSquareCylinder (q₀ p₀ : Position n) : Set (Phase n) :=
  {z | |inner (𝕜 := ℝ) p₀ z.1| < 1 ∧ |inner (𝕜 := ℝ) q₀ z.2| < 1}

theorem polarProduct_subset_squareCylinder {K : Set (Position n)}
    (hK : IsSymmetricConvexBody K) {q₀ p₀ : Position n}
    (hq : q₀ ∈ K) (hp : p₀ ∈ polar K) (hqp : inner (𝕜 := ℝ) p₀ q₀ = 1) :
    polarProduct K ⊆ canonicalSquareCylinder q₀ p₀ := by
  have hp0 : p₀ ≠ 0 := by intro he; simp [he] at hqp
  have hq0 : q₀ ≠ 0 := by intro he; simp [he] at hqp
  intro z hz
  have hqp' : q₀ ∈ ConvexPolar.polar (ConvexPolar.polar K) := by
    intro p hp
    rw [real_inner_comm]
    exact hp _ hq
  exact ⟨ConvexPolar.abs_inner_lt_one_of_mem_interior hK.2.2.2 hp hp0 hz.1,
    ConvexPolar.abs_inner_lt_one_of_mem_interior (ConvexPolar.polar_symmetric hK.2.2.2) hqp' hq0 hz.2⟩

theorem exists_squareCylinder {K : Set (Position n)} (hK : IsSymmetricConvexBody K)
    (hn : 0 < n) : ∃ q₀ p₀ : Position n, inner (𝕜 := ℝ) p₀ q₀ = 1 ∧
      polarProduct K ⊆ canonicalSquareCylinder q₀ p₀ := by
  let v : Position n := (EuclideanSpace.basisFun (Fin n) ℝ) ⟨0, hn⟩
  have hv : v ≠ 0 := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ne_zero _
  obtain ⟨q₀, hq, p₀, hp, hqp⟩ := ConvexPolar.exists_support_pair hK.1
    (ConvexPolar.zero_mem_interior_of_symmetric hK.2.1 hK.2.2.1 hK.2.2.2) hv
  exact ⟨q₀, p₀, hqp, polarProduct_subset_squareCylinder hK hq hp hqp⟩

end
end SymmetricPolar
end

end OAI
