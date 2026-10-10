import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace Kadison.CyclicColumns

variable {A H ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype ι]

theorem regularized_factorization (a : ι → A) (η : ℝ) (hη : 0 < η) :
    ∃ (b : A) (v : ι → A), star b=b ∧
      b*b=(∑ i, star (a i)*a i)+η • (1:A) ∧
      (∑ i, star (v i)*v i) ≤ 1 ∧ ∀ i, v i*b=a i := by
  let q : A := (∑ i, star (a i)*a i)+η • (1:A)
  have hp : IsStrictlyPositive q :=
    IsStrictlyPositive.nonneg_add (Finset.sum_nonneg (fun i _ => star_mul_self_nonneg (a i)))
      (isStrictlyPositive_one.smul hη)
  let b : A := CFC.sqrt q
  have hb : star b=b := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg q)).star_eq
  have hbb : b*b=q := CFC.sqrt_mul_sqrt_self q hp.nonneg
  have hu : IsUnit b := (CFC.isUnit_sqrt_iff q hp.nonneg).mpr hp.isUnit
  let c : A := Ring.inverse b
  have hcb : c*b=1 := Ring.inverse_mul_cancel b hu
  have hbc : b*c=1 := Ring.mul_inverse_cancel b hu
  have hc : star c=c := by dsimp [c]; rw [←Ring.inverse_star,hb]
  let v : ι → A := fun i => a i*c
  refine ⟨b,v,hb,hbb,?_,?_⟩
  · have hle : (∑ i,star (a i)*a i) ≤ q :=
      le_add_of_nonneg_right (smul_nonneg hη.le zero_le_one)
    have h := star_left_conjugate_le_conjugate hle c
    have hright : star c*q*c=1 := by rw [hc,←hbb,←mul_assoc,hcb,one_mul,hbc]
    rw [hright] at h
    convert h using 1
    dsimp only [v]
    simp only [star_mul,Finset.mul_sum,Finset.sum_mul,mul_assoc]
  · intro i
    dsimp only [v]
    rw [mul_assoc,hcb,mul_one]

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_image_sq (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A) (Ω : H) :
    ‖σ a Ω‖^2 = (inner ℂ Ω (σ (star a*a) Ω)).re := by
  rw [map_mul,map_star,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact (inner_self_eq_norm_sq (𝕜:=ℂ) (σ a Ω)).symm

theorem regularized_vector_factorization (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Ω : H) (a : ι → A) (η : ℝ) (hη : 0 < η) :
    ∃ (ζ : H) (v : ι → A), (∑ i, star (v i)*v i) ≤ 1 ∧
      (∀ i, σ (v i) ζ=σ (a i) Ω) ∧
      ‖ζ‖^2=(∑ i, ‖σ (a i) Ω‖^2)+η*‖Ω‖^2 := by
  obtain ⟨b,v,hb,hbb,hv,hvb⟩ := regularized_factorization a η hη
  refine ⟨σ b Ω,v,hv,?_,?_⟩
  · intro i
    rw [←mul_apply_eq_comp,←map_mul,hvb]
  · rw [norm_image_sq,hb,hbb,map_add,map_sum]
    have hsmul : σ (η • (1:A))=η • (1:H →L[ℂ] H) := by
      change σ ((η:ℂ) • (1:A))=(η:ℂ) • (1:H →L[ℂ] H)
      rw [map_smul,map_one]
    rw [hsmul]
    simp only [add_apply,sum_apply,
      smul_apply,one_apply_eq_self,inner_add_right,
      inner_sum,Complex.add_re,Complex.re_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      exact (norm_image_sq σ (a i) Ω).symm
    · change (inner ℂ Ω ((η:ℂ) • Ω)).re=η*‖Ω‖^2
      rw [inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im]
      simp only [zero_mul,sub_zero]
      congr 1
      exact inner_self_eq_norm_sq (𝕜:=ℂ) Ω

theorem bounded_vector_factorization (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Ω : H) (a : ι → A) (ha : (∑ i, ‖σ (a i) Ω‖^2) ≤ 2) :
    ∃ (ζ : H) (v : ι → A), ‖ζ‖ ≤ 2 ∧ (∑ i, star (v i)*v i) ≤ 1 ∧
      ∀ i, σ (v i) ζ=σ (a i) Ω := by
  let η : ℝ := 1/(‖Ω‖^2+1)
  have ht : 0 < ‖Ω‖^2+1 := by positivity
  have hη : 0 < η := one_div_pos.mpr ht
  obtain ⟨ζ,v,hv,hva,hζ⟩ := regularized_vector_factorization σ Ω a η hη
  have hr : η*‖Ω‖^2 ≤ 1 := by
    dsimp only [η]
    rw [one_div_mul_eq_div]
    exact (div_le_one ht).mpr (by linarith)
  refine ⟨ζ,v,?_,hv,hva⟩
  have hn := norm_nonneg ζ
  nlinarith

omit [PartialOrder A] [StarOrderedRing A] [Fintype ι] in
lemma denseRange_cyclic_columns (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Ω : H) (hΩ : DenseRange (fun a : A => σ a Ω)) :
    DenseRange (fun a : ι → A => WithLp.toLp 2 (fun i => σ (a i) Ω)) := by
  have hpi : DenseRange (Pi.map (fun (_ : ι) (a : A) => σ a Ω)) :=
    DenseRange.piMap (fun _ => hΩ)
  exact (PiLp.homeomorph 2 (fun _ : ι => H)).symm.surjective.denseRange.comp hpi
    (PiLp.homeomorph 2 (fun _ : ι => H)).symm.continuous

theorem approximate_unit_column (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Ω : H) (hΩ : DenseRange (fun a : A => σ a Ω))
    (ξ : PiLp 2 (fun _ : ι => H)) (hξ : ‖ξ‖=1) (ε : ℝ) (hε : 0<ε) :
    ∃ (ζ : H) (v : ι → A), ‖ζ‖ ≤ 2 ∧ (∑ i, star (v i)*v i) ≤ 1 ∧
      ‖ξ-WithLp.toLp 2 (fun i => σ (v i) ζ)‖ < ε := by
  obtain ⟨a,ha⟩ := Metric.denseRange_iff.mp (denseRange_cyclic_columns σ Ω hΩ)
    ξ (min ε (1/4)) (lt_min hε (by norm_num))
  rw [dist_eq_norm] at ha
  have hnorm : ‖WithLp.toLp 2 (fun i => σ (a i) Ω)‖ < 5/4 := by
    have hh := norm_le_norm_add_norm_sub ξ (WithLp.toLp 2 (fun i => σ (a i) Ω))
    rw [hξ] at hh
    have ht := lt_of_lt_of_le ha (min_le_right ε (1/4))
    linarith
  have hb : (∑ i, ‖σ (a i) Ω‖^2) ≤ 2 := by
    rw [←PiLp.norm_sq_eq_of_L2 (fun _ : ι => H) (WithLp.toLp 2 (fun i => σ (a i) Ω))]
    have hn := norm_nonneg (WithLp.toLp 2 (fun i => σ (a i) Ω))
    nlinarith
  obtain ⟨ζ,v,hζ,hv,heq⟩ := bounded_vector_factorization σ Ω a hb
  refine ⟨ζ,v,hζ,hv,?_⟩
  simpa only [heq] using lt_of_lt_of_le ha (min_le_left ε (1/4))

end Kadison.CyclicColumns

end

end
end

end OAI
