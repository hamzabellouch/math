import OAI.Analysis.KadisonKastler.PartialSupportSpan

namespace OAI

/-! An orthogonal family of initial projections equivalent to subprojections
of e fills the central support of e. This is the geometric step in the
localized row-averaging proof; no countability is imposed. -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def IsCentralSupportFamily (e : AlgebraProjection M) (S : Set (PartialIsometry M)) : Prop :=
  (∀ v ∈ S, v.target ≤ e ∧ v.support.val ≠ 0) ∧
    S.Pairwise (fun v w => v.support.val * w.support.val = 0)

theorem exists_maximal_centralSupportFamily (e : AlgebraProjection M) :
    ∃ S : Set (PartialIsometry M), Maximal (IsCentralSupportFamily e) S := by
  apply zorn_subset
  intro C hC hc
  refine ⟨⋃₀ C, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
  · rintro v ⟨s, hs, hv⟩
    exact (hC hs).1 v hv
  · rintro v ⟨s, hs, hv⟩ w ⟨t, ht, hw⟩ hvw
    obtain rfl | hst := eq_or_ne s t
    · exact (hC hs).2 hv hw hvw
    rcases hc hs ht hst with h | h
    · exact (hC ht).2 (h hv) hw hvw
    · exact (hC hs).2 hv (h hw) hvw

theorem centralSupportFamily_fills (e : AlgebraProjection M)
    (S : Set (PartialIsometry M)) (hS : Maximal (IsCentralSupportFamily e) S) :
    partialSupportProjection S = centralSupport e := by
  let P := partialSupportProjection S
  have hPc : P ≤ centralSupport e := partialSupportProjection_le S _
    (fun v hv => support_le_centralSupport_of_target_le e v (hS.prop.1 v hv).1)
  let r : AlgebraProjection M := ⟨(centralSupport e).val - P.val,
    P.property.sub_of_mul_eq_right (centralSupport e).property hPc⟩
  have hPr : P.val * r.val = 0 := by
    change P.val * ((centralSupport e).val - P.val) = 0
    rw [mul_sub, projection_mul_of_le hPc, P.property.isIdempotentElem.eq, sub_self]
  have her : ∀ a : Algebra M, e.val * a * r.val = 0 := by
    intro a
    by_contra hn
    obtain ⟨v, hvr, hve, hv0⟩ := exists_partialIsometry_of_link r e
      (e.val * a * r.val)
      (by rw [mul_assoc, r.property.isIdempotentElem.eq])
      (by rw [← mul_assoc, ← mul_assoc, e.property.isIdempotentElem.eq]) hn
    have hvo (w : PartialIsometry M) (hw : w ∈ S) :
        w.support.val * v.support.val = 0 :=
      projection_orthogonal_of_le hPr (support_le_partialSupportProjection S w hw) hvr
    have hins : IsCentralSupportFamily e (insert v S) := by
      constructor
      · intro w hw
        rcases hw with rfl | hw
        · exact ⟨hve, hv0⟩
        · exact hS.prop.1 w hw
      · apply hS.prop.2.insert
        intro w hw _
        exact ⟨PartialIsometry.orthogonal_reverse _ _ (hvo w hw), hvo w hw⟩
    have hvS : v ∈ S := (hS.2 hins (Set.subset_insert v S)) (Set.mem_insert v S)
    exact hv0 (v.support.property.isIdempotentElem.eq.symm.trans (hvo v hvS))
  have hrc : r.val * (centralSupport e).val = 0 := by
    apply mul_centralSupport_eq_zero_of_no_links e r
    intro a
    have h := congrArg star (her (star a))
    simpa only [star_mul, star_star, r.property.isSelfAdjoint.star_eq,
      e.property.isSelfAdjoint.star_eq, star_zero, mul_assoc] using h
  have hr0 : r.val = 0 := by
    have hr : r.val * (centralSupport e).val = r.val := by
      change ((centralSupport e).val - P.val) * (centralSupport e).val =
        (centralSupport e).val - P.val
      rw [sub_mul, (centralSupport e).property.isIdempotentElem.eq, projection_mul_of_le hPc]
    exact hr.symm.trans hrc
  apply Subtype.ext
  exact (sub_eq_zero.mp hr0).symm

theorem exists_centralSupportCover (e : AlgebraProjection M) :
    ∃ S : Set (PartialIsometry M), IsCentralSupportFamily e S ∧
      partialSupportProjection S = centralSupport e := by
  obtain ⟨S, hS⟩ := exists_maximal_centralSupportFamily e
  exact ⟨S, hS.prop, centralSupportFamily_fills e S hS⟩

end

end KadisonKastler

end OAI
