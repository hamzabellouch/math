import OAI.Analysis.Pureness.Projections.PartialIsometryExtension

namespace OAI
noncomputable section
namespace CuntzPureness
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma projection_residual_orthogonal {q e a : D}
    (hq : IsStarProjection q) (he : IsStarProjection e) (ha : IsStarProjection a)
    (heq : e ≤ q) (haq : a ≤ q-e) : e*a=0 ∧ a*e=0 := by
  have hd := (he.le_iff_sub hq).mp heq
  have hea : (q-e)*a=a := (ha.le_iff_mul_eq_right hd).mp haq
  have hed : e*(q-e)=0 := by
    rw [mul_sub,(he.le_iff_mul_eq_left hq).mp heq,he.isIdempotentElem.eq,sub_self]
  have hz : e*a=0 := by rw [← hea,← mul_assoc,hed,zero_mul]
  exact ⟨hz,by simpa only [star_mul,he.isSelfAdjoint.star_eq,ha.isSelfAdjoint.star_eq,star_zero]
    using congrArg star hz⟩

omit [PartialOrder D] [StarOrderedRing D] in
lemma projection_add_of_orthogonal {e a : D}
    (he : IsStarProjection e) (ha : IsStarProjection a) (h : e*a=0) (h' : a*e=0) :
    IsStarProjection (e+a) := by
  refine ⟨?_,he.isSelfAdjoint.add ha.isSelfAdjoint⟩
  change (e+a)*(e+a)=e+a
  simp only [add_mul,mul_add,he.isIdempotentElem.eq,ha.isIdempotentElem.eq,h,h',add_zero,zero_add]

theorem partial_isometry_orthogonal_extension (p q u w : D)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (he : IsStarProjection (star u*u)) (hg : IsStarProjection (u*star u))
    (ha : IsStarProjection (star w*w)) (hb : IsStarProjection (w*star w))
    (heq : star u*u ≤ q) (hgp : u*star u ≤ p)
    (haq : star w*w ≤ q-star u*u) (hbp : w*star w ≤ p-u*star u) :
    star (u+w)*(u+w)=star u*u+star w*w ∧
    (u+w)*star (u+w)=u*star u+w*star w ∧
    IsStarProjection (star (u+w)*(u+w)) ∧
    IsStarProjection ((u+w)*star (u+w)) ∧
    star (u+w)*(u+w) ≤ q ∧ (u+w)*star (u+w) ≤ p ∧
    (u+w)*(star u*u)=u := by
  obtain ⟨hea,hae⟩ := projection_residual_orthogonal hq he ha heq haq
  obtain ⟨hgb,hbg⟩ := projection_residual_orthogonal hp hg hb hgp hbp
  have hu := partial_isometry_mul_initial u he
  have hw := partial_isometry_mul_initial w ha
  have hus : star u*(u*star u)=star u := by
    simpa only [star_star] using partial_isometry_mul_initial (star u) (by simpa only [star_star] using hg)
  have hws : star w*(w*star w)=star w := by
    simpa only [star_star] using partial_isometry_mul_initial (star w) (by simpa only [star_star] using hb)
  have hbw : (w*star w)*w=w := by simpa only [mul_assoc] using hw
  have hcw : star u*w=0 := by
    calc
      _ = (star u*(u*star u))*((w*star w)*w) := by rw [hus,hbw]
      _ = star u*((u*star u)*(w*star w))*w := by noncomm_ring
      _ = 0 := by rw [hgb,mul_zero,zero_mul]
  have hcw' : star w*u=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hcw
  have hcw₂ : u*star w=0 := by
    calc
      _ = (u*(star u*u))*((star w*w)*star w) := by rw [hu,mul_assoc, hws]
      _ = u*((star u*u)*(star w*w))*star w := by noncomm_ring
      _ = 0 := by rw [hea,mul_zero,zero_mul]
  have hcw₂' : w*star u=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hcw₂
  have hi : star (u+w)*(u+w)=star u*u+star w*w := by
    simp only [star_add,add_mul,mul_add,hcw,hcw',add_zero,zero_add]
  have hr : (u+w)*star (u+w)=u*star u+w*star w := by
    simp only [star_add,add_mul,mul_add,hcw₂,hcw₂',add_zero,zero_add]
  refine ⟨hi,hr,hi.symm ▸ projection_add_of_orthogonal he ha hea hae,
    hr.symm ▸ projection_add_of_orthogonal hg hb hgb hbg,?_,?_,?_⟩
  · rw [hi]; simpa only [add_comm] using (le_sub_iff_add_le.mp haq)
  · rw [hr]; simpa only [add_comm] using (le_sub_iff_add_le.mp hbp)
  · have hz : w*(star u*u)=0 := by
      calc
        _ = (w*(star w*w))*(star u*u) := by rw [hw]
        _ = 0 := by rw [mul_assoc,hae,mul_zero]
    rw [add_mul,hu,hz,add_zero]
end CuntzPureness

end

end OAI
