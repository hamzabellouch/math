import OAI.Analysis.KadisonKastler.TypeIIIDixmier
import OAI.Analysis.KadisonKastler.ScalarNormMinimizer
import OAI.Analysis.KadisonKastler.DixmierImplementerBound

namespace OAI

/-! # Constructed norm bounds for type III inner implementers -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  {P : VonNeumannAlgebra H}

/-- Finite spectral averages center a self-adjoint implementer with the exact
bound needed by normalizer factorization. -/
theorem TypeIIIFactor.exists_centered_selfAdjoint_implementer (hP : TypeIIIFactor P)
    (h : H →L[ℂ] H) (a : Algebra P) (ha : IsSelfAdjoint a)
    (hb : h - a.val ∈ P.commutant) :
    ∃ z : ℂ, ‖a.val - z • (1 : H →L[ℂ] H)‖ ≤ 2 * ‖h‖ := by
  obtain ⟨z, hz⟩ := exists_scalar_norm_minimizer a.val
  refine ⟨z, le_of_forall_pos_le_add (fun ε hε => ?_)⟩
  obtain ⟨A, w, hw⟩ := hP.exists_selfAdjoint_scalar_average a ha ε hε
  have hu (u : unitary (Algebra P)) :
      ‖unitaryConj (ambientAlgebraUnitary u) a.val - a.val‖ ≤ 2 * ‖h‖ := by
    let v := ambientAlgebraUnitary u
    have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp hb v.val u.val.property
    have hfix : unitaryConj v (h - a.val) = h - a.val := by
      dsimp [unitaryConj]
      rw [hcomm, mul_assoc, Unitary.mul_star_self_of_mem v.property, mul_one]
    rw [unitaryConj_sub] at hfix
    have he : unitaryConj v a.val - a.val = unitaryConj v h - h :=
      (sub_eq_sub_iff_sub_eq_sub.mp hfix).symm
    rw [he]
    exact (norm_sub_le _ _).trans (by rw [norm_unitaryConj]; linarith)
  have hav := norm_sub_le_of_closed_convex_orbit P a.val a.val (A.apply a.val)
    (2 * ‖h‖) hu (subset_closure (A.apply_mem_orbitHull a.val))
  calc
    ‖a.val - z • (1 : H →L[ℂ] H)‖ ≤ ‖a.val - w • 1‖ := hz w
    _ ≤ ‖a.val - A.apply a.val‖ + ‖A.apply a.val - w • 1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖h‖ + ε := by rw [norm_sub_rev] at hav; linarith

/-- A bounded centered splitting for a type III normalizer. -/
theorem TypeIIIFactor.exists_bounded_selfAdjoint_split (hP : TypeIIIFactor P)
    (h : selfAdjoint (H →L[ℂ] H)) (a : Algebra P) (ha : IsSelfAdjoint a)
    (hb : (h : H →L[ℂ] H) - a.val ∈ P.commutant) :
    ∃ a' b' : selfAdjoint (H →L[ℂ] H),
      (a' : H →L[ℂ] H) ∈ P ∧ (b' : H →L[ℂ] H) ∈ P.commutant ∧
      h = a' + b' ∧ ‖(a' : H →L[ℂ] H)‖ ≤ 2 * ‖(h : H →L[ℂ] H)‖ ∧
      ‖(b' : H →L[ℂ] H)‖ ≤ 3 * ‖(h : H →L[ℂ] H)‖ := by
  obtain ⟨z, hnorm⟩ := hP.exists_centered_selfAdjoint_implementer h a ha hb
  let w : H →L[ℂ] H := z • 1
  have hw : w ∈ concreteCenter P := (concreteCenter P).smul_mem (concreteCenter P).one_mem z
  let a' := realPart (a.val - w)
  let b' := realPart ((h : H →L[ℂ] H) - a.val + w)
  have he : (a' : H →L[ℂ] H) + b' = h := by
    have he' : (a.val - w) + ((h : H →L[ℂ] H) - a.val + w) = h := by abel
    change ((realPart (a.val - w) + realPart ((h : H →L[ℂ] H) - a.val + w) :
      selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H) = h
    rw [← map_add, he', h.property.coe_realPart]
  have han : ‖(a' : H →L[ℂ] H)‖ ≤ 2 * ‖(h : H →L[ℂ] H)‖ :=
    (realPart.norm_le (a.val - w)).trans hnorm
  refine ⟨a', b', realPart_mem_vonNeumann P (P.sub_mem a.property hw.1),
    realPart_mem_vonNeumann P.commutant (P.commutant.add_mem hb hw.2),
    Subtype.ext he.symm, han, ?_⟩
  have hb' : (b' : H →L[ℂ] H) = h - a' := by rw [← he]; abel
  rw [hb']
  exact (norm_sub_le _ _).trans (by linarith)

end

end KadisonKastler

end OAI
