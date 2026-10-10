import OAI.Geometry.SurfaceImmersion.Geometry.C1ImmersionJets

namespace OAI

/-! A compact family of injective chart differentials has one positive
lower bound, retained by a fixed operator-norm perturbation. -/
noncomputable section
open Set Metric
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial

theorem compact_injective_lower_bound {K : Set (Base →L[ℝ] Space)}
    (hK : IsCompact K) (hI : ∀ L ∈ K, Function.Injective L) :
    ∃ c : ℝ, 0 < c ∧ ∀ L ∈ K, ∀ H : Base →L[ℝ] Space, ‖H-L‖ ≤ c →
      ∀ v : Base, c*‖v‖ ≤ ‖H v‖ := by
  let S : Set ((Base →L[ℝ] Space) × Base) := K ×ˢ sphere 0 1
  have hS : IsCompact S := hK.prod (isCompact_sphere 0 1)
  have hf : Continuous (fun z : (Base →L[ℝ] Space) × Base => ‖z.1 z.2‖) := by fun_prop
  have hp : ∀ z ∈ S, 0 < ‖z.1 z.2‖ := by
    rintro ⟨L,v⟩ ⟨hL,hv⟩
    apply norm_pos_iff.mpr
    intro hz
    have hv0 : v = 0 := hI L hL (hz.trans L.map_zero.symm)
    have hnorm : ‖v‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hv
    rw [hv0,norm_zero] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨μ,hμ,hbound⟩ := hS.exists_forall_le' hf.continuousOn hp
  have hbase (L : Base →L[ℝ] Space) (hL : L ∈ K) (v : Base) : μ*‖v‖ ≤ ‖L v‖ := by
    by_cases hv : v = 0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let u := ‖v‖⁻¹ • v
    have hu : ‖u‖ = 1 := by
      simp only [u,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm]
      exact inv_mul_cancel₀ hn.ne'
    have hh := hbound (L,u) ⟨hL,by simpa only [mem_sphere,dist_zero_right] using hu⟩
    change μ ≤ ‖L u‖ at hh
    rw [show L u = ‖v‖⁻¹ • L v from L.map_smul _ _] at hh
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm] at hh
    exact (le_div_iff₀ hn).mp (by simpa only [div_eq_inv_mul] using hh)
  refine ⟨μ/2,half_pos hμ,?_⟩
  intro L hL H hHL v
  have hd : ‖(L-H) v‖ ≤ (μ/2)*‖v‖ := by
    exact ((L-H).le_opNorm v).trans (mul_le_mul_of_nonneg_right
      (by simpa only [norm_sub_rev] using hHL) (norm_nonneg v))
  have he : L v = H v+(L-H) v := by simp
  have ht : ‖L v‖ ≤ ‖H v‖+‖(L-H) v‖ := by rw [he]; exact norm_add_le _ _
  have hb := hbase L hL v
  nlinarith

lemma linear_lower_bound_metric_comparison (L : Base →L[ℝ] Space)
    (B : Base →L[ℝ] Base →L[ℝ] ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hL : ∀ v, a*‖v‖ ≤ ‖L v‖) (hB : ‖B‖ ≤ b) (v : Base) :
    a^2/(b+1) * B v v ≤ ‖L v‖^2 := by
  have hBv : B v v ≤ b*‖v‖^2 := by
    calc
      B v v ≤ ‖B v v‖ := le_abs_self _
      _ ≤ ‖B‖*‖v‖*‖v‖ := B.le_opNorm₂ v v
      _ ≤ b*‖v‖^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sq_nonneg ‖v‖)]
  have hLv : a^2*‖v‖^2 ≤ ‖L v‖^2 := by
    have hh := hL v
    nlinarith [norm_nonneg (L v),mul_nonneg ha.le (norm_nonneg v)]
  have hdiv : 0 ≤ a^2/(b+1) := div_nonneg (sq_nonneg a) (by positivity)
  calc
    a^2/(b+1) * B v v ≤ a^2/(b+1)*(b*‖v‖^2) :=
      mul_le_mul_of_nonneg_left hBv hdiv
    _ = (a^2*(b*‖v‖^2))/(b+1) := by ring
    _ ≤ a^2*‖v‖^2 := by
      apply (div_le_iff₀ (by positivity : 0 < b+1)).2
      nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg ‖v‖)]
    _ ≤ ‖L v‖^2 := hLv

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
