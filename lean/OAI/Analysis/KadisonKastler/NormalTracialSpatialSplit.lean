import OAI.Analysis.KadisonKastler.TracialCommutantSpatialSplit
import OAI.Analysis.KadisonKastler.CompactHilbertFixedPoint

namespace OAI

/-! # Transporting the tracial splitting argument through a normal representation -/

namespace KadisonKastler

noncomputable section

open ContinuousLinearMapWOT Generator.Tracial UltrapowerBridge

variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

theorem mem_of_fixed_commutant_unitaries (M : VonNeumannAlgebra H)
    (S : H →L[ℂ] H)
    (hfix : ∀ w : unitary (Algebra M.commutant),
      unitaryConj (ambientAlgebraUnitary w) S = S) : S ∈ M := by
  rw [← M.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  let L : Algebra M.commutant →ₗ[ℂ] (H →L[ℂ] H) :=
    { toFun := fun b => b.val * S - S * b.val
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
    change b.val * S * star b.val * b.val = S * b.val at hh
    have hstar : star b.val * b.val = 1 := congrArg Subtype.val w.property.1
    rw [mul_assoc, mul_assoc, hstar, mul_one] at hh
    exact sub_eq_zero.mpr hh
  intro b hb
  exact sub_eq_zero.mp (hker (show (⟨b, hb⟩ : Algebra M.commutant) ∈ ⊤ from trivial))

/-- The trace vector may live in a different faithful normal representation. -/
theorem exists_selfAdjoint_split_of_normal_tracial_commutant
    (M : VonNeumannAlgebra H) (P : VonNeumannAlgebra J)
    (ρ : Algebra M.commutant ≃⋆ₐ[ℂ] Algebra P) (τ : TracialRepresentation P)
    (hρ : ∀ C : ℝ, Continuous (fun b : weakOperatorBall M.commutant C =>
      ofCLM (ρ ⟨b.val.toCLM, b.property.1⟩).val))
    (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      T - a ∈ M.commutant := by
  let K := boundedSelfAdjointImplementers M T
  let : CompactSpace K := isCompact_iff_compactSpace.mp
    (boundedSelfAdjointImplementers_compact M T)
  let L : Algebra M.commutant →ₗ[ℝ] J :=
    ((algebraVectorMap P τ.vector).comp ρ.toStarAlgHom.toLinearMap).restrictScalars ℝ
  let a (S : K) : Algebra M.commutant := ⟨S.val.toCLM - T, S.property.2.2⟩
  let v (S : K) : J := L (a S)
  have han (S : K) : ‖a S‖ ≤ 2 * ‖T‖ := by
    exact (norm_sub_le S.val.toCLM T).trans (by linarith [S.property.2.1])
  let B (S : K) : weakOperatorBall M.commutant (2 * ‖T‖) :=
    ⟨ofCLM (a S).val, (a S).property, han S⟩
  have hB : Continuous B := by
    have hc : Continuous (fun S : K => S.val - ofCLM T) :=
      continuous_subtype_val.sub continuous_const
    apply Continuous.subtype_mk
    change Continuous (fun S : K => S.val - ofCLM T)
    exact hc
  have hv (η : J) : LowerSemicontinuous (fun S : K => ‖v S - η‖ ^ 2) := by
    have hc : Continuous (fun S : K => ofCLM (ρ (a S)).val) :=
      (hρ (2 * ‖T‖)).comp hB
    change LowerSemicontinuous (fun S : K => ‖(ρ (a S)).val τ.vector - η‖ ^ 2)
    exact (wot_vector_sqDistance_lowerSemicontinuous (H := J) τ.vector η).comp hc
  have hne : (Set.univ : Set K).Nonempty := by
    refine ⟨⟨ofCLM T, hTsa, le_rfl, ?_⟩, Set.mem_univ _⟩
    change T - T ∈ M.commutant
    rw [sub_self]
    exact M.commutant.zero_mem
  have hmid (S : K) (_ : S ∈ Set.univ) (V : K) (_ : V ∈ Set.univ) :
      ∃ Z ∈ (Set.univ : Set K), v Z = (1 / 2 : ℝ) • (v S + v V) := by
    let Z : K := ⟨(1 / 2 : ℝ) • (S.val + V.val),
      boundedSelfAdjointImplementers_midpoint M T S.property V.property⟩
    refine ⟨Z, Set.mem_univ _, ?_⟩
    have he : a Z = (1 / 2 : ℝ) • (a S + a V) := by
      apply Subtype.ext
      change (1 / 2 : ℝ) • (S.val.toCLM + V.val.toCLM) - T =
        (1 / 2 : ℝ) • ((S.val.toCLM - T) + (V.val.toCLM - T))
      module
    change L (a Z) = _
    rw [he, L.map_smul, L.map_add]
  have hbound (S : K) (_ : S ∈ Set.univ) : ‖v S‖ ≤ 2 * ‖T‖ := by
    calc
      ‖v S‖ ≤ ‖ρ (a S)‖ := τ.norm₂_le_norm _
      _ = ‖a S‖ := by
        apply le_antisymm (NonUnitalStarAlgHom.norm_apply_le ρ.toStarAlgHom _)
        have hh := NonUnitalStarAlgHom.norm_apply_le ρ.symm.toStarAlgHom (ρ (a S))
        change ‖ρ.symm (ρ (a S))‖ ≤ ‖ρ (a S)‖ at hh
        rw [ρ.symm_apply_apply] at hh
        exact hh
      _ ≤ 2 * ‖T‖ := han S
  have hfaith : Set.InjOn v Set.univ := by
    intro S _ V _ h
    have he : ρ (a S - a V) = 0 := by
      apply τ.separating
      change (ρ (a S - a V)).val τ.vector = 0
      rw [map_sub]
      exact sub_eq_zero.mpr h
    have ha0 : a S - a V = 0 := by
      have hh := congrArg ρ.symm he
      simpa only [ρ.symm_apply_apply, map_zero] using hh
    have ha : a S = a V := sub_eq_zero.mp ha0
    apply Subtype.ext
    apply toCLM_injective
    have hh := congrArg Subtype.val ha
    change S.val.toCLM - T = V.val.toCLM - T at hh
    have hh' := congrArg (fun x : H →L[ℂ] H => x + T) hh
    simpa only [sub_add_cancel] using hh'
  let F (w : unitary (Algebra M.commutant)) (S : K) : K :=
    ⟨ofCLM (unitaryConj (ambientAlgebraUnitary w) S.val.toCLM),
      boundedSelfAdjointImplementers_conjugate M T hT (ambientAlgebraUnitary w)
        (w : Algebra M.commutant).property S.property⟩
  have honto (w : unitary (Algebra M.commutant)) (S : K) (_ : S ∈ Set.univ) :
      ∃ V ∈ (Set.univ : Set K), F w V = S := by
    refine ⟨F (star w) S, Set.mem_univ _, ?_⟩
    apply Subtype.ext
    apply toCLM_injective
    change unitaryConj (ambientAlgebraUnitary w)
      (unitaryConj (ambientAlgebraUnitary (star w)) S.val.toCLM) = S.val.toCLM
    have he : ambientAlgebraUnitary (star w) = star (ambientAlgebraUnitary w) := by
      apply Subtype.ext
      rfl
    rw [he]
    simpa only [star_star] using
      unitaryConj_star_unitaryConj (star (ambientAlgebraUnitary w)) S.val.toCLM
  have hiso (w : unitary (Algebra M.commutant)) (S : K) (_ : S ∈ Set.univ)
      (V : K) (_ : V ∈ Set.univ) : ‖v (F w S) - v (F w V)‖ = ‖v S - v V‖ := by
    let w' : unitary (Algebra P) := Unitary.map (StarMonoidHom.ofClass ρ.toStarAlgHom) w
    have he : a (F w S) - a (F w V) =
        (w : Algebra M.commutant) * (a S - a V) * star (w : Algebra M.commutant) := by
      apply Subtype.ext
      change unitaryConj (ambientAlgebraUnitary w) S.val.toCLM - T -
        (unitaryConj (ambientAlgebraUnitary w) V.val.toCLM - T) = _
      simp only [sub_sub_sub_cancel_right, ← unitaryConj_sub]
      change (w : Algebra M.commutant).val * (S.val.toCLM - V.val.toCLM) *
        star (w : Algebra M.commutant).val =
        (w : Algebra M.commutant).val * ((S.val.toCLM - T) - (V.val.toCLM - T)) *
        star (w : Algebra M.commutant).val
      rw [sub_sub_sub_cancel_right]
    change ‖L (a (F w S)) - L (a (F w V))‖ = ‖L (a S) - L (a V)‖
    rw [← L.map_sub, he, ← L.map_sub]
    change τ.norm₂ (ρ.toStarAlgHom ((w : Algebra M.commutant) * (a S - a V) *
      star (w : Algebra M.commutant))) = τ.norm₂ (ρ.toStarAlgHom (a S - a V))
    rw [map_mul, map_mul, map_star]
    exact conjugate_norm₂ τ w' (ρ (a S - a V))
  obtain ⟨S, _, hS⟩ := exists_fixed_of_compact_hilbert_image Set.univ isCompact_univ
    hne v hv hmid (2 * ‖T‖) hbound hfaith F (fun _ _ _ => Set.mem_univ _) honto hiso
  have hm : S.val.toCLM ∈ M := by
    apply mem_of_fixed_commutant_unitaries M
    intro w
    exact congrArg (fun Z : K => Z.val.toCLM) (hS w)
  refine ⟨S.val.toCLM, hm, S.property.1, S.property.2.1, ?_⟩
  change T - S.val.toCLM ∈ M.commutant.toSubalgebra
  simpa only [neg_sub] using M.commutant.neg_mem S.property.2.2

end

end KadisonKastler

end OAI
