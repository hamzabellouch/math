import OAI.Analysis.FactorGeneration.OrbitMinima
import OAI.Analysis.FactorGeneration.PartialIsometries
import OAI.Analysis.FactorGeneration.Supports

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero coefficient linking two projections produces an actual nonzero
partial isometry between subprojections. Scalar center supplies such coefficients. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem exists_partialIsometry_of_link (p q : AlgebraProjection M)
    (x : M.toStarSubalgebra) (hxp : x*p.val=x) (hqx : q.val*x=x) (hx : x≠0) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧ v.support.val≠0 := by
  obtain ⟨v,hvx,hvi,hvf⟩ := exists_polar_with_supports x
  let w : PartialIsometry M := ⟨rangeProjection (star x),v,hvi⟩
  refine ⟨w,?_,?_,?_⟩
  · apply (rangeProjection_le_iff (star x) p).mpr
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq] using congrArg star hxp
  · have ht : w.target=rangeProjection x := Subtype.ext hvf
    rw [ht]
    exact (rangeProjection_le_iff x q).mpr hqx
  · intro hz
    have hv0 : v=0 := (CStarRing.star_mul_self_eq_zero_iff _).mp (hvi.trans hz)
    rw [hv0,zero_mul] at hvx
    exact hx hvx.symm

theorem exists_nonzero_partialIsometry_between_projections
    (τ : TracialRepresentation M)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (p q : AlgebraProjection M) (hp : p.val≠0) (hq : q.val≠0) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧ v.support.val≠0 := by
  classical
  let P : StarSubalgebra ℂ M.toStarSubalgebra := ⊤
  let : CompleteSpace P := isClosed_univ.completeSpace_coe
  have hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : P, (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra) := by
    intro c hc
    exact hfactor c (fun a => hc ⟨a,StarSubalgebra.mem_top⟩)
  have hex : ∃ a : P, q.val*(a : M.toStarSubalgebra)*p.val≠0 := by
    by_contra hn
    have hz : ∀ a : P, q.val*(a : M.toStarSubalgebra)*p.val=0 := by
      simpa only [not_exists,not_not] using hn
    exact (projection_eq_zero_or_eq_zero_of_no_links τ P hirr p q hz).elim hp hq
  obtain ⟨a,ha⟩ := hex
  apply exists_partialIsometry_of_link p q (q.val*(a : M.toStarSubalgebra)*p.val)
  · rw [mul_assoc,p.property.isIdempotentElem.eq]
  · rw [← mul_assoc,← mul_assoc,q.property.isIdempotentElem.eq]
  · exact ha

end

/-! Projection comparison and equal-trace equivalence in the actual factor.
Both polar decomposition and the maximal partial isometry are constructed. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

include τ hfactor in
theorem exists_partialIsometry_comparison (p q : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧
      (v.support=p ∨ v.target=q) := by
  obtain ⟨v,hvp,hvq,hmax⟩ := PartialIsometry.exists_maximal_between τ p q
  let r : AlgebraProjection M :=
    ⟨p.val-v.support.val,v.support.property.sub_of_mul_eq_right p.property hvp⟩
  let s : AlgebraProjection M :=
    ⟨q.val-v.target.val,v.target.property.sub_of_mul_eq_right q.property hvq⟩
  have hrp : r ≤ p := by
    change p.val*(p.val-v.support.val)=p.val-v.support.val
    rw [mul_sub,p.property.isIdempotentElem.eq,hvp]
  have hsq : s ≤ q := by
    change q.val*(q.val-v.target.val)=q.val-v.target.val
    rw [mul_sub,q.property.isIdempotentElem.eq,hvq]
  have hzero : r.val=0 ∨ s.val=0 := by
    by_contra hn
    have hr : r.val≠0 := fun h => hn (Or.inl h)
    have hs : s.val≠0 := fun h => hn (Or.inr h)
    obtain ⟨w,hwr,hws,hw0⟩ :=
      exists_nonzero_partialIsometry_between_projections τ hfactor r s hr hs
    have hpw : v.support.val*w.support.val=0 := by
      calc _ = v.support.val*(r.val*w.support.val) := by rw [hwr]
           _ = (v.support.val*r.val)*w.support.val := (mul_assoc _ _ _).symm
           _ = 0 := by
             change (v.support.val*(p.val-v.support.val))*w.support.val=0
             rw [mul_sub,projection_mul_of_le hvp,v.support.property.isIdempotentElem.eq,
               sub_self,zero_mul]
    have hqw : v.target.val*w.target.val=0 := by
      calc _ = v.target.val*(s.val*w.target.val) := by rw [hws]
           _ = (v.target.val*s.val)*w.target.val := (mul_assoc _ _ _).symm
           _ = 0 := by
             change (v.target.val*(q.val-v.target.val))*w.target.val=0
             rw [mul_sub,projection_mul_of_le hvq,v.target.property.isIdempotentElem.eq,
               sub_self,zero_mul]
    let u := PartialIsometry.patch v w hpw hqw
    have hup : u.support ≤ p := by
      change p.val*(v.support.val+w.support.val)=v.support.val+w.support.val
      rw [mul_add,hvp,show p.val*w.support.val=w.support.val from hwr.trans hrp]
    have huq : u.target ≤ q := by
      apply (u.target_le_iff_mul q).mpr
      change q.val*(v.val+w.val)=v.val+w.val
      rw [mul_add,(v.target_le_iff_mul q).mp hvq,
        (w.target_le_iff_mul q).mp (hws.trans hsq)]
    have hvu : v ≤ u := v.le_patch w hpw hqw
    exact (v.patch_ne w hpw hqw hw0) (le_antisymm (hmax u hup huq hvu) hvu)
  refine ⟨v,hvp,hvq,?_⟩
  rcases hzero with hr | hs
  · exact Or.inl (Subtype.ext (sub_eq_zero.mp hr).symm)
  · exact Or.inr (Subtype.ext (sub_eq_zero.mp hs).symm)

theorem projection_eq_of_le_of_trace_eq {p q : AlgebraProjection M}
    (hpq : p ≤ q) (ht : τ.trace p.val=τ.trace q.val) : p=q := by
  let r : AlgebraProjection M := ⟨q.val-p.val,p.property.sub_of_mul_eq_right q.property hpq⟩
  have hz : τ.trace r.val=0 := by
    change τ.trace (q.val-p.val)=0
    rw [trace_sub,ht,sub_self]
  have hr : r.val=0 := by
    by_contra hn
    have hh := projection_trace_pos τ r.val r.property hn
    rw [hz,Complex.zero_re] at hh
    exact (lt_irrefl _ hh)
  exact Subtype.ext (sub_eq_zero.mp hr).symm

include hfactor in
theorem exists_partialIsometry_of_trace_eq (p q : AlgebraProjection M)
    (ht : τ.trace p.val=τ.trace q.val) :
    ∃ v : M.toStarSubalgebra, star v*v=p.val ∧ v*star v=q.val := by
  obtain ⟨v,hvp,hvq,hfull⟩ := exists_partialIsometry_comparison τ hfactor p q
  have he := v.trace_support_eq_target τ
  have hboth : v.support=p ∧ v.target=q := by
    rcases hfull with hp | hq
    · refine ⟨hp,projection_eq_of_le_of_trace_eq τ hvq ?_⟩
      rw [← he,hp,ht]
    · refine ⟨projection_eq_of_le_of_trace_eq τ hvp ?_,hq⟩
      rw [he,hq,ht]
  exact ⟨v.val,v.initial.trans (congrArg (fun z : AlgebraProjection M => z.val) hboth.1),
    congrArg (fun z : AlgebraProjection M => z.val) hboth.2⟩

end Generator.Tracial

end

end OAI
