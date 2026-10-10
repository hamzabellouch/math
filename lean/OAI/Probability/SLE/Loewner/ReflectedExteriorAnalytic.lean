import OAI.Probability.SLE.Loewner.ReflectedCapacityChart

namespace OAI

/-! The retained chart is univalent and holomorphic on the full
complement of the reflected slit, not only on its upper side. -/
noncomputable section
open Set Function Filter Complex Metric
open scoped Topology ComplexConjugate

namespace SLEExactGauge

lemma ReflectedCapacityChart.inverse_mem {p : C(unitInterval,ℂ)} (_R : ReflectedCapacityChart p)
    {z : ℂ} (hz : z∉reflectedArcSet p) : z⁻¹∈invertedExterior (reflectedArcSet p) := by
  exact Or.inr (by simpa only [inv_inv] using hz)

lemma ReflectedCapacityChart.exterior_norm {p : C(unitInterval,ℂ)} (R : ReflectedCapacityChart p)
    (h0 : p 0=0) {z : ℂ} (hz : z∉reflectedArcSet p) :
    1<‖slitExteriorMap R.diskMap z‖ := by
  have hz0 : z≠0 := by
    intro he
    subst z
    exact hz (Or.inl ⟨0,h0⟩)
  have hm := R.inverse_mem hz
  have hn : ‖R.diskMap z⁻¹‖<1 := by
    simpa only [mem_ball_zero_iff] using R.disk_bijOn.mapsTo hm
  have hf0 : R.diskMap z⁻¹≠0 := by
    intro he
    have hh := R.disk_bijOn.injOn hm (zero_mem_invertedExterior _) (he.trans R.disk_zero.symm)
    exact inv_ne_zero hz0 hh
  change 1<‖(R.diskMap z⁻¹)⁻¹‖
  rw [norm_inv]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hf0)).mpr hn

theorem ReflectedCapacityChart.forward_differentiable {p : C(unitInterval,ℂ)}
    (R : ReflectedCapacityChart p) (h0 : p 0=0) :
    DifferentiableOn ℂ R.chart.forward (reflectedArcSet p)ᶜ := by
  intro z hz
  have hz0 : z≠0 := by
    intro he
    subst z
    exact hz (Or.inl ⟨0,h0⟩)
  have hK : IsCompact (reflectedArcSet p) := (isCompact_range p.continuous).union
    ((isCompact_range p.continuous).image Complex.continuous_conj)
  have hm := R.inverse_mem hz
  have hf := (R.disk_differentiable.differentiableAt
    ((invertedExterior_isOpen hK).mem_nhds hm)).comp z (differentiableAt_id.inv hz0)
  have hf0 : R.diskMap z⁻¹≠0 := by
    intro he
    exact inv_ne_zero hz0 (R.disk_bijOn.injOn hm (zero_mem_invertedExterior _)
      (he.trans R.disk_zero.symm))
  have hh := (((hf.inv hf0).add hf).const_mul (R.slope:ℂ)).sub_const
    (deriv (slitInfinityFactor R.diskMap R.slope) 0)
  change DifferentiableAt ℂ (fun y : ℂ => (R.slope:ℂ)*
    ((R.diskMap y⁻¹)⁻¹+R.diskMap y⁻¹)-deriv (slitInfinityFactor R.diskMap R.slope) 0) z at hh
  rw [R.forward_eq]
  have he : slitHydrodynamicMap R.diskMap R.slope = fun y : ℂ => (R.slope:ℂ)*
      ((R.diskMap y⁻¹)⁻¹+R.diskMap y⁻¹)-deriv (slitInfinityFactor R.diskMap R.slope) 0 := by
    funext y
    simp only [slitHydrodynamicMap,exteriorJoukowski,slitExteriorMap,inv_inv]
  rw [he]
  exact hh.differentiableWithinAt

theorem ReflectedCapacityChart.forward_injOn {p : C(unitInterval,ℂ)}
    (R : ReflectedCapacityChart p) (h0 : p 0=0) :
    InjOn R.chart.forward (reflectedArcSet p)ᶜ := by
  intro z hz w hw he
  rw [R.forward_eq] at he
  have hj : exteriorJoukowski (slitExteriorMap R.diskMap z)=
      exteriorJoukowski (slitExteriorMap R.diskMap w) := by
    apply mul_left_cancel₀ (ofReal_ne_zero.mpr R.slope_pos.ne')
    exact sub_left_inj.mp he
  have hW := exteriorJoukowski_injOn (R.exterior_norm h0 hz) (R.exterior_norm h0 hw) hj
  have hf := inv_injective hW
  exact inv_injective (R.disk_bijOn.injOn (R.inverse_mem hz) (R.inverse_mem hw) hf)

end SLEExactGauge

end

end OAI
