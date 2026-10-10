import OAI.Analysis.KadisonKastler.TracialSpatialGeometry
import Mathlib.Analysis.CStarAlgebra.Unitary.Span

namespace OAI

/-! # Spatial splitting with a faithful tracial commutant vector

The weakly compact convex family of bounded implementers has a unique
center for the commutant trace metric. Unitary invariance of that metric
forces the center into the original algebra. No injectivity is needed.
-/

namespace KadisonKastler

noncomputable section

open ContinuousLinearMapWOT Generator.Tracial UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_selfAdjoint_split_of_tracial_commutant
    (M : VonNeumannAlgebra H) (τ : TracialRepresentation M.commutant)
    (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      T - a ∈ M.commutant := by
  let K := boundedSelfAdjointImplementers M T
  let v : (H →WOT[ℂ] H) → H := fun S => (S.toCLM - T) τ.vector
  have hne : K.Nonempty := ⟨ofCLM T, hTsa, le_rfl, by
    change T - T ∈ M.commutant
    rw [sub_self]
    exact M.commutant.zero_mem⟩
  have hdist (η : H) : LowerSemicontinuous (fun S => ‖v S - η‖ ^ 2) := by
    convert wot_vector_sqDistance_lowerSemicontinuous τ.vector (T τ.vector + η) using 1
    ext S
    congr 2
    change S τ.vector - T τ.vector - η = S τ.vector - (T τ.vector + η)
    abel
  have hmid (S : H →WOT[ℂ] H) (hS : S ∈ K) (V : H →WOT[ℂ] H) (hV : V ∈ K) :
      ∃ Z ∈ K, v Z = (1 / 2 : ℝ) • (v S + v V) := by
    refine ⟨(1 / 2 : ℝ) • (S + V), boundedSelfAdjointImplementers_midpoint M T hS hV, ?_⟩
    change ((1 / 2 : ℝ) • (S.toCLM + V.toCLM) - T) τ.vector =
      (1 / 2 : ℝ) • ((S.toCLM - T) τ.vector + (V.toCLM - T) τ.vector)
    simp only [_root_.sub_apply, _root_.smul_apply, _root_.add_apply]
    module
  have hbound (S : H →WOT[ℂ] H) (hS : S ∈ K) : ‖v S‖ ≤ 2 * ‖T‖ := by
    calc
      ‖v S‖ ≤ ‖S.toCLM - T‖ * ‖τ.vector‖ := (S.toCLM - T).le_opNorm _
      _ ≤ (‖S.toCLM‖ + ‖T‖) * 1 := by rw [τ.norm_vector]; gcongr; exact norm_sub_le _ _
      _ ≤ 2 * ‖T‖ := by have hh := hS.2.1; nlinarith
  obtain ⟨S, hS, hcenter⟩ := exists_unique_compact_hilbert_center K
    (boundedSelfAdjointImplementers_compact M T) hne v hdist hmid (2 * ‖T‖) hbound
  have hfix (w : unitary (Algebra M.commutant)) :
      unitaryConj (ambientAlgebraUnitary w) S.toCLM = S.toCLM := by
    let u := ambientAlgebraUnitary w
    let Y := ofCLM (unitaryConj u S.toCLM)
    have hu : u.val ∈ M.commutant := (w : Algebra M.commutant).property
    have hY : Y ∈ K := boundedSelfAdjointImplementers_conjugate M T hT u hu hS
    have hvY : v Y = v S := by
      apply hcenter Y hY
      intro Z hZ
      let V := ofCLM (unitaryConj (star u) Z.toCLM)
      have hV : V ∈ K := boundedSelfAdjointImplementers_conjugate M T hT (star u)
        (M.commutant.toStarSubalgebra.star_mem' hu) hZ
      have hSV : S.toCLM - V.toCLM ∈ M.commutant := by
        change S.toCLM - V.toCLM ∈ M.commutant.toSubalgebra
        have hh := M.commutant.sub_mem hS.2.2 hV.2.2
        simpa only [sub_sub_sub_cancel_right] using hh
      have hn := tracial_conjugation_difference_norm M.commutant τ w S.toCLM V.toCLM hSV
      have hback : unitaryConj u V.toCLM = Z.toCLM := by
        change unitaryConj u (unitaryConj (star u) Z.toCLM) = Z.toCLM
        simpa only [star_star] using unitaryConj_star_unitaryConj (star u) Z.toCLM
      have he : ‖v Y - v Z‖ = ‖v S - v V‖ := by
        change ‖(Y.toCLM - T) τ.vector - (Z.toCLM - T) τ.vector‖ =
          ‖(S.toCLM - T) τ.vector - (V.toCLM - T) τ.vector‖
        change ‖(unitaryConj u S.toCLM - unitaryConj u V.toCLM) τ.vector‖ =
          ‖(S.toCLM - V.toCLM) τ.vector‖ at hn
        rw [hback] at hn
        simpa only [← _root_.sub_apply, sub_sub_sub_cancel_right] using hn
      rw [he]
      have hbd : BddAbove (Set.range (fun Z : K => ‖v S - v Z‖ ^ 2)) := by
        refine ⟨(4 * ‖T‖) ^ 2, ?_⟩
        rintro _ ⟨Z, rfl⟩
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        exact (norm_sub_le _ _).trans (by linarith [hbound S hS, hbound Z Z.property])
      exact le_ciSup hbd (⟨V, hV⟩ : K)
    have hYS : Y.toCLM - S.toCLM ∈ M.commutant := by
      change Y.toCLM - S.toCLM ∈ M.commutant.toSubalgebra
      have hh := M.commutant.sub_mem hY.2.2 hS.2.2
      simpa only [sub_sub_sub_cancel_right] using hh
    have hz : (⟨Y.toCLM - S.toCLM, hYS⟩ : Algebra M.commutant) = 0 := by
      apply τ.separating
      change (Y.toCLM - S.toCLM) τ.vector = 0
      have hh := sub_eq_zero.mpr hvY
      simpa only [v, ← _root_.sub_apply, sub_sub_sub_cancel_right] using hh
    exact sub_eq_zero.mp (congrArg Subtype.val hz)
  have hSM : S.toCLM ∈ M := by
    rw [← M.commutant_commutant]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    let L : Algebra M.commutant →ₗ[ℂ] (H →L[ℂ] H) :=
      { toFun := fun b => b.val * S.toCLM - S.toCLM * b.val
        map_add' := by intro a b; simp only [AddMemClass.coe_add]; noncomm_ring
        map_smul' := by
          intro c b
          simp only [SetLike.val_smul, RingHom.id_apply, smul_mul_assoc, mul_smul_comm, smul_sub] }
    have hker : (⊤ : Submodule ℂ (Algebra M.commutant)) ≤ L.ker := by
      rw [← CStarAlgebra.span_unitary]
      apply Submodule.span_le.mpr
      intro b hb
      let w : unitary (Algebra M.commutant) := ⟨b, hb⟩
      have hh := congrArg (fun R : H →L[ℂ] H => R * b.val) (hfix w)
      change b.val * S.toCLM * star b.val * b.val = S.toCLM * b.val at hh
      have hstar : star b.val * b.val = 1 :=
        congrArg Subtype.val w.property.1
      rw [mul_assoc, mul_assoc, hstar, mul_one] at hh
      exact sub_eq_zero.mpr hh
    intro b hb
    exact sub_eq_zero.mp (hker (show (⟨b, hb⟩ : Algebra M.commutant) ∈ ⊤ from trivial))
  refine ⟨S.toCLM, hSM, hS.1, hS.2.1, ?_⟩
  change T - S.toCLM ∈ M.commutant.toSubalgebra
  simpa only [neg_sub] using M.commutant.neg_mem hS.2.2

end

end KadisonKastler

end OAI
