import OAI.Analysis.KadisonKastler.PublishedDixmier
import OAI.Analysis.KadisonKastler.SelfAdjointApproximation

namespace OAI

/-! # Centering an inner implementer by Dixmier averaging

Normalized Dixmier averaging centers self-adjoint implementers while
controlling their ambient operator norm.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_centered_implementer (P : VonNeumannAlgebra H)
    (hDixmier : PublishedDixmierAveraging P)
    (h a : H →L[ℂ] H) (ha : a ∈ P) (hb : h - a ∈ P.commutant) :
    ∃ w ∈ concreteCenter P, ‖a - w‖ ≤ 2 * ‖h‖ := by
  let t : ℝ := ‖a‖ + 1
  have ht : 0 < t := by dsimp [t]; positivity
  let y : H →L[ℂ] H := ((t⁻¹ : ℝ) : ℂ) • a
  have hy : y ∈ unitBall P := by
    refine ⟨P.smul_mem ha _, ?_⟩
    dsimp [y]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    apply (inv_mul_le_iff₀ ht).mpr
    dsimp [t]
    linarith
  obtain ⟨z, hz, hzHull⟩ := hDixmier y hy
  have hu (u : unitary (Algebra P)) :
      ‖unitaryConj (ambientAlgebraUnitary u) y - y‖ ≤ t⁻¹ * (2 * ‖h‖) := by
    let v := ambientAlgebraUnitary u
    have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp hb v.val u.val.property
    have hfix : unitaryConj v (h - a) = h - a := by
      dsimp [unitaryConj]
      rw [hcomm, mul_assoc, Unitary.mul_star_self_of_mem v.property, mul_one]
    rw [unitaryConj_sub] at hfix
    have he : unitaryConj v a - a = unitaryConj v h - h :=
      (sub_eq_sub_iff_sub_eq_sub.mp hfix).symm
    have hn : ‖unitaryConj v a - a‖ ≤ 2 * ‖h‖ := by
      rw [he]
      exact (norm_sub_le _ _).trans (by rw [norm_unitaryConj]; linarith)
    change ‖unitaryConj v (((t⁻¹ : ℝ) : ℂ) • a) - ((t⁻¹ : ℝ) : ℂ) • a‖ ≤ _
    have he' : unitaryConj v (((t⁻¹ : ℝ) : ℂ) • a) - ((t⁻¹ : ℝ) : ℂ) • a =
        ((t⁻¹ : ℝ) : ℂ) • (unitaryConj v a - a) := by
      simp only [unitaryConj, mul_smul_comm, smul_mul_assoc, smul_sub]
    rw [he', norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    exact mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr ht.le)
  have hn := norm_sub_le_of_closed_convex_orbit P y y z _ hu hzHull
  refine ⟨(t : ℂ) • z, (concreteCenter P).smul_mem hz _, ?_⟩
  have hy' : (t : ℂ) • y = a := by
    change (t : ℝ) • ((t⁻¹ : ℝ) • a) = a
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hnorm : ‖(t : ℂ) • (z - y)‖ ≤ 2 * ‖h‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    calc
      _ ≤ t * (t⁻¹ * (2 * ‖h‖)) := mul_le_mul_of_nonneg_left hn ht.le
      _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  simpa only [smul_sub, hy', norm_sub_rev] using hnorm

/-- Self-adjoint centering keeps the algebra/commutant decomposition and
bounds both summands by the original ambient implementer. -/
theorem exists_bounded_selfAdjoint_split (P : VonNeumannAlgebra H)
    (hDixmier : PublishedDixmierAveraging P)
    (h : selfAdjoint (H →L[ℂ] H)) (a : H →L[ℂ] H)
    (ha : a ∈ P) (hb : (h : H →L[ℂ] H) - a ∈ P.commutant) :
    ∃ a' b' : selfAdjoint (H →L[ℂ] H),
      (a' : H →L[ℂ] H) ∈ P ∧ (b' : H →L[ℂ] H) ∈ P.commutant ∧
      h = a' + b' ∧ ‖(a' : H →L[ℂ] H)‖ ≤ 2 * ‖(h : H →L[ℂ] H)‖ ∧
      ‖(b' : H →L[ℂ] H)‖ ≤ 3 * ‖(h : H →L[ℂ] H)‖ := by
  obtain ⟨w, hw, hnorm⟩ := exists_centered_implementer P hDixmier h a ha hb
  let a' := realPart (a - w)
  let b' := realPart ((h : H →L[ℂ] H) - a + w)
  have he : (a' : H →L[ℂ] H) + b' = h := by
    have he' : (a - w) + ((h : H →L[ℂ] H) - a + w) = h := by abel
    change ((realPart (a - w) + realPart ((h : H →L[ℂ] H) - a + w) :
      selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H) = h
    rw [← map_add, he', h.property.coe_realPart]
  have han : ‖(a' : H →L[ℂ] H)‖ ≤ 2 * ‖(h : H →L[ℂ] H)‖ :=
    (realPart.norm_le (a - w)).trans hnorm
  refine ⟨a', b', realPart_mem_vonNeumann P (P.sub_mem ha hw.1),
    realPart_mem_vonNeumann P.commutant (P.commutant.add_mem hb hw.2),
    Subtype.ext he.symm, han, ?_⟩
  have hb' : (b' : H →L[ℂ] H) = h - a' := by rw [← he]; abel
  rw [hb']
  exact (norm_sub_le _ _).trans (by linarith)

end

end KadisonKastler

end OAI
