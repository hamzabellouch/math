import OAI.Analysis.CircleDomains.Uniformization.RiemannRootCompetitor

namespace OAI

/-! Normalizing the root competitor strictly increases the derivative
at the base point. This forces a derivative extremum to omit no disk value. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

lemma disk_root_gain {t : ℝ} (ht0 : 0<t) (ht1 : t<1) :
    1 < (1-t^4)/((1-t^2)*(2*t)) := by
  have hd : 0<1-t^2 := by nlinarith
  have he : (1-t^4)/((1-t^2)*(2*t)) = (1+t^2)/(2*t) := by
    field_simp [ne_of_gt hd,ne_of_gt ht0]
    ring
  rw [he,lt_div_iff₀ (by positivity : 0<2*t)]
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr ht1.ne)]

lemma norm_one_sub_star_mul {z : ℂ} (hz : ‖z‖<1) :
    ‖1-star z*z‖=1-‖z‖^2 := by
  have hp : 0<1-‖z‖^2 := by nlinarith [norm_nonneg z]
  rw [Complex.star_def,Complex.conj_mul']
  simp only [← Complex.ofReal_pow,← Complex.ofReal_one,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]

lemma improve_disk_embedding_of_omitted_value {U : Set ℂ}
    (hU : IsOpen U) (hc : IsSimplyConnected U) {a : ℂ} (ha : a ∈ U)
    {f : ℂ → ℂ} (hf : NormalizedDiskEmbedding U a f) (hdf : deriv f a ≠ 0)
    {b : ℂ} (hb : ‖b‖<1) (hmiss : b ∉ f '' U) :
    ∃ g : ℂ → ℂ, NormalizedDiskEmbedding U a g ∧ ‖deriv f a‖<‖deriv g a‖ := by
  obtain ⟨r,_hrcont,hrinj,hrmap,_hpow,hrnz,hrderiv,hbase⟩ :=
    exists_root_disk_competitor hU hc hf hb hmiss
  let v := r a
  have hv : ‖v‖<1 := mem_ball_zero_iff.mp (hrmap ha)
  have hv0 : 0<‖v‖ := norm_pos_iff.mpr (hrnz a ha)
  have hbnorm : ‖b‖=‖v‖^2 := by
    have hh := congrArg norm hbase
    simpa only [norm_pow,norm_neg,v] using hh.symm
  let g : ℂ → ℂ := diskFractionalMap v ∘ r
  have hdg (z : ℂ) (hz : z ∈ U) : HasDerivAt g
      (((1-star v*v)/(1-star v*r z)^2)*
        (((1-star b*b)/(1-star b*f z)^2*deriv f z)/(2*r z))) z :=
    (diskFractionalMap_hasDerivAt hv (mem_ball_zero_iff.mp (hrmap hz))).comp z (hrderiv z hz)
  have hg : NormalizedDiskEmbedding U a g := by
    refine ⟨fun z hz => (hdg z hz).differentiableAt.differentiableWithinAt,?_,?_,?_⟩
    · exact (diskFractionalMap_injective hv).comp hrinj hrmap
    · intro z hz
      exact mem_ball_zero_iff.mpr
        (diskFractionalMap_mem_ball hv (mem_ball_zero_iff.mp (hrmap hz)))
    · exact diskFractionalMap_self
  refine ⟨g,hg,?_⟩
  have hnormv := norm_one_sub_star_mul hv
  have hnormb := norm_one_sub_star_mul hb
  have hformula : ‖deriv g a‖ =
      ((1-‖v‖^4)/((1-‖v‖^2)*(2*‖v‖)))*‖deriv f a‖ := by
    rw [(hdg a ha).deriv,hf.at_base]
    change ‖((1-star v*v)/(1-star v*v)^2)*
      (((1-star b*b)/(1-star b*0)^2*deriv f a)/(2*v))‖ = _
    simp only [mul_zero,sub_zero,one_pow,div_one,norm_mul,norm_div,norm_pow,
      hnormv,hnormb,Complex.norm_ofNat,hbnorm]
    have hvp : 0<1-‖v‖^2 := by nlinarith [norm_nonneg v]
    field_simp
  rw [hformula]
  have hgain := disk_root_gain hv0 hv
  nlinarith [norm_pos_iff.mpr hdf]

end CircleDomainRigidity

end

end OAI
