import OAI.Analysis.HyperbolicCones.MatrixLinear

namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

universe u

namespace Paper256

theorem posSemidef_pair_kernel {n : ℕ} {A H : Mat n ℝ}
    (hplus : (A + H).PosSemidef) (hminus : (A - H).PosSemidef)
    (v : Fin n → ℝ) (hv : A *ᵥ v = 0) : H *ᵥ v = 0 := by
  have hp := hplus.dotProduct_mulVec_nonneg v
  have hm := hminus.dotProduct_mulVec_nonneg v
  simp only [star_trivial, add_mulVec, sub_mulVec, hv, zero_add, zero_sub,
    dotProduct_neg] at hp hm
  have hz : v ⬝ᵥ ((A + H) *ᵥ v) = 0 := by
    simp only [add_mulVec, hv, zero_add]
    linarith
  have hh := hplus.dotProduct_mulVec_zero_iff.mp (by simpa only [star_trivial] using hz)
  simpa only [add_mulVec, hv, zero_add] using hh

theorem interior_line_pair {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Set V} {e : V} (he : e ∈ interior K) (x : V) :
    ∃ ε : ℝ, 0 < ε ∧ e + ε • x ∈ K ∧ e - ε • x ∈ K := by
  have hp : Tendsto (fun t : ℝ => e + t • x) (𝓝 0) (𝓝 e) := by
    have h : Continuous (fun t : ℝ => e + t • x) := by fun_prop
    simpa using h.tendsto (0 : ℝ)
  have hm : Tendsto (fun t : ℝ => e - t • x) (𝓝 0) (𝓝 e) := by
    have h : Continuous (fun t : ℝ => e - t • x) := by fun_prop
    simpa using h.tendsto (0 : ℝ)
  have hh := (hp.eventually (mem_interior_iff_mem_nhds.mp he)).and
    (hm.eventually (mem_interior_iff_mem_nhds.mp he))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hh
  refine ⟨r / 2, by positivity, hball ?_⟩
  simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  linarith

theorem pencil_common_kernel {N : ℕ} (K : Set Ambient)
    (L : Ambient →ₗ[ℝ] Sym N) (hL : K = {x | (L x : Mat N ℝ).PosSemidef})
    (he : basePoint ∈ interior K) (x : Ambient) (v : Fin N → ℝ)
    (hv : (L basePoint : Mat N ℝ) *ᵥ v = 0) :
    (L x : Mat N ℝ) *ᵥ v = 0 := by
  obtain ⟨ε, hε, hp, hm⟩ := interior_line_pair he x
  rw [hL] at hp hm
  have hp' : ((L basePoint : Mat N ℝ) + ε • (L x : Mat N ℝ)).PosSemidef := by
    simpa using hp
  have hm' : ((L basePoint : Mat N ℝ) - ε • (L x : Mat N ℝ)).PosSemidef := by
    simpa using hm
  have hz := posSemidef_pair_kernel hp' hm' v hv
  rw [smul_mulVec] at hz
  exact (smul_eq_zero.mp hz).resolve_left hε.ne'

end Paper256

end

end OAI
