import OAI.Analysis.FiniteFactor.Diffuse.SupportTrace
import OAI.Analysis.FiniteFactor.Diffuse.ProjectionTrace

namespace OAI

noncomputable section
open scoped BigOperators
namespace Nonhyperlinear.Diffuseness
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A faithful tracial concrete algebra with finite identity partitions of
arbitrarily small projection trace has no minimal projection. -/
theorem no_minimal_projection_of_small_partitions (M:VonNeumannAlgebra H) (v:H)
    (hcyclic:∀a b:M.toStarSubalgebra,
      inner ℂ v (((a*b:M.toStarSubalgebra):H→L[ℂ]H) v)=
      inner ℂ v (((b*a:M.toStarSubalgebra):H→L[ℂ]H) v))
    (hfaithful:∀T:M.toStarSubalgebra,(T:H→L[ℂ]H) v=0→T=0)
    (hpart:∀ε:ℝ,0<ε→∃n:ℕ,∃e:Fin n→M.toStarSubalgebra,
      (∀j,IsStarProjection (e j:H→L[ℂ]H)) ∧ (∑j,e j)=1 ∧
      ∀j,(inner ℂ v ((e j:H→L[ℂ]H) v)).re<ε)
    (p:M.toStarSubalgebra) (hps:star p=p) (hpi:p*p=p) (hp0:p≠0) :
    ∃q:M.toStarSubalgebra,star q=q ∧ q*q=q ∧ q≠0 ∧ q≠p ∧ q*p=q := by
  classical
  have hpp:IsStarProjection (p:H→L[ℂ]H) :=
    isStarProjection_iff'.mpr ⟨congrArg Subtype.val hpi,congrArg Subtype.val hps⟩
  have hpv:(p:H→L[ℂ]H) v≠0 := fun hz=>hp0 (hfaithful p hz)
  have htpos:0<(inner ℂ v ((p:H→L[ℂ]H) v)).re := by
    rw [projection_vector_trace v hpp]
    simp only [←Complex.ofReal_pow,Complex.ofReal_re]
    exact sq_pos_of_pos (norm_pos_iff.mpr hpv)
  obtain ⟨n,e,hep,hes,het⟩:=hpart _ htpos
  obtain ⟨j,hj⟩:∃j,p*e j≠0 := by
    by_contra hn
    have hh:∀j,p*e j=0 := by simpa only [not_exists,not_not] using hn
    apply hp0
    calc
      p=p*1 := (mul_one p).symm
      _=p*(∑j,e j) := by rw [hes]
      _=∑j,p*e j := Finset.mul_sum _ _ _
      _=0 := by simp [hh]
  by_contra hnone
  let T:H→L[ℂ]H := (p*e j:M.toStarSubalgebra)
  have hT0:T≠0 := fun hh=>hj (Subtype.ext hh)
  have hTnorm:‖T‖≤1 := by
    exact (norm_mul_le (p:H→L[ℂ]H) (e j:H→L[ℂ]H)).trans
      ((mul_le_mul (IsStarProjection.norm_le _ hpp) (IsStarProjection.norm_le _ (hep j))
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have hpT:(p:H→L[ℂ]H)*T=T := by
    change ((p*p)*e j:M.toStarSubalgebra).val=(p*e j).val
    rw [hpi]
  let q:M.toStarSubalgebra := ⟨rangeSupport T,rangeSupport_mem M (p*e j).property⟩
  have hqp:q*p=q := Subtype.ext (rangeSupport_mul_projection hpp hpT)
  have hq0:q≠0 := fun hh=>rangeSupport_ne_zero hT0 (congrArg Subtype.val hh)
  have hqeq:q=p := by
    by_contra hh
    exact hnone ⟨q,Subtype.ext (rangeSupport_projection T).isSelfAdjoint.star_eq,
      Subtype.ext (rangeSupport_projection T).isIdempotentElem.eq,hq0,hh,hqp⟩
  have heT:(e j:H→L[ℂ]H)*star T=star T := by
    change (e j:H→L[ℂ]H)*star ((p:H→L[ℂ]H)*(e j:H→L[ℂ]H))=star ((p:H→L[ℂ]H)*(e j:H→L[ℂ]H))
    rw [star_mul,hpp.isSelfAdjoint.star_eq,(hep j).isSelfAdjoint.star_eq,←mul_assoc,
      (hep j).isIdempotentElem.eq]
  have hright:=rangeSupport_mul_projection (hep j) heT
  have hle:=projection_vector_trace_mono v (hep j) (rangeSupport_projection (star T)) hright
  have heq:=support_trace_eq M v hcyclic (p*e j) hTnorm
  have hleft:rangeSupport T=(p:H→L[ℂ]H) := congrArg Subtype.val hqeq
  change inner ℂ v (rangeSupport T v)=inner ℂ v (rangeSupport (star T) v) at heq
  rw [hleft] at heq
  rw [←heq] at hle
  exact (not_lt_of_ge hle) (het j)

end Nonhyperlinear.Diffuseness

end

end OAI
