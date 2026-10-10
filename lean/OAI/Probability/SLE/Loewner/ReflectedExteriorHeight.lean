import OAI.Probability.SLE.Loewner.ReflectedExteriorAnalytic

namespace OAI

/-! Reflection supplies the lower-half-plane version of the normalized
height inequality. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology ComplexConjugate

namespace SLEExactGauge

lemma ReflectedCapacityChart.forward_reflection {p : C(unitInterval,ℂ)}
    (R : ReflectedCapacityChart p) {z : ℂ} (hz : z∉reflectedArcSet p) :
    R.chart.forward (conj z)=conj (R.chart.forward z) := by
  have hK : IsCompact (reflectedArcSet p) := (isCompact_range p.continuous).union
    ((isCompact_range p.continuous).image Complex.continuous_conj)
  have hD := (invertedExterior_isOpen hK).mem_nhds (zero_mem_invertedExterior _)
  have hd := derivative_real_of_reflection hD
    (slitInfinityFactor_reflection hD R.disk_reflection R.slope)
  have hf : R.diskMap ((conj z)⁻¹)=conj (R.diskMap z⁻¹) := by
    simpa only [map_inv₀] using R.disk_reflection z⁻¹ (R.inverse_mem hz)
  rw [R.forward_eq]
  simp only [slitHydrodynamicMap,exteriorJoukowski,slitExteriorMap,
    map_inv₀,inv_inv,map_sub,map_mul,map_add,conj_ofReal,hd,hf]

lemma ReflectedCapacityChart.height_displacement_sign {p : C(unitInterval,ℂ)}
    (R : ReflectedCapacityChart p) {z : ℂ} (hz : z∉reflectedArcSet p) :
    z.im*(R.chart.forward z-z).im≤0 := by
  rcases lt_trichotomy z.im 0 with hneg|heq|hpos
  · have hcz : conj z∉reflectedArcSet p := by
      intro hh
      have hh' := reflectedArcSet_conj p hh
      exact hz (by simpa only [conj_conj] using hh')
    have hH : conj z∈upperHalfPlane := by
      change 0<(conj z).im
      simpa only [conj_im] using neg_pos.mpr hneg
    have hn : conj z∉range p := fun hh => hcz (Or.inl hh)
    have hh := R.chart.height_le (conj z) ⟨hH,hn⟩
    rw [R.forward_reflection hz] at hh
    simp only [conj_im] at hh
    apply mul_nonpos_of_nonpos_of_nonneg hneg.le
    simp only [sub_im]
    linarith
  · simp only [heq,zero_mul,le_refl]
  · have hn : z∉range p := fun hh => hz (Or.inl hh)
    exact mul_nonpos_of_nonneg_of_nonpos hpos.le
      (sub_nonpos.mpr (R.chart.height_le z ⟨hpos,hn⟩))

end SLEExactGauge

end

end OAI
