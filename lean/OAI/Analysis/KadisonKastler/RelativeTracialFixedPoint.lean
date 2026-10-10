import OAI.Analysis.KadisonKastler.NormalTracialSpatialSplit

namespace OAI

/-! # Fixed points of relative unitary averaging in a finite algebra

The trace may be realized on a different Hilbert space. A bounded weakly
compact convex family invariant under the subalgebra's unitaries has a
fixed element, by the constructed compact Hilbert-center theorem.
-/

namespace KadisonKastler

noncomputable section

open ContinuousLinearMapWOT Generator.Tracial UltrapowerBridge

variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

omit [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J] in
theorem mem_commutant_of_unitaryConj_fixed (R : VonNeumannAlgebra H)
    (S : H →L[ℂ] H)
    (hfix : ∀ w : unitary (Algebra R),
      unitaryConj (ambientAlgebraUnitary w) S = S) : S ∈ R.commutant := by
  apply mem_of_fixed_commutant_unitaries R.commutant S
  rw [R.commutant_commutant]
  exact hfix

theorem exists_relative_tracial_fixed_point
    (M R : VonNeumannAlgebra H) (hRM : R ≤ M) (P : VonNeumannAlgebra J)
    (ρ : Algebra M ≃⋆ₐ[ℂ] Algebra P) (τ : TracialRepresentation P)
    (hρ : ∀ C : ℝ, Continuous (fun b : weakOperatorBall M C =>
      ofCLM (ρ ⟨b.val.toCLM, b.property.1⟩).val))
    (K : Set (H →WOT[ℂ] H)) (hK : IsCompact K) (hne : K.Nonempty)
    (hKM : ∀ S ∈ K, S.toCLM ∈ M)
    (hmid : ∀ S ∈ K, ∀ V ∈ K, (1 / 2 : ℝ) • (S + V) ∈ K)
    (C : ℝ) (hbound : ∀ S ∈ K, ‖S.toCLM‖ ≤ C)
    (hinv : ∀ w : unitary (Algebra R), ∀ S ∈ K,
      ofCLM (unitaryConj (ambientAlgebraUnitary w) S.toCLM) ∈ K) :
    ∃ S ∈ K, ∀ w : unitary (Algebra R),
      unitaryConj (ambientAlgebraUnitary w) S.toCLM = S.toCLM := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let a (S : K) : Algebra M := ⟨S.val.toCLM, hKM S.val S.property⟩
  let L : Algebra M →ₗ[ℝ] J :=
    ((algebraVectorMap P τ.vector).comp ρ.toStarAlgHom.toLinearMap).restrictScalars ℝ
  let v (S : K) : J := L (a S)
  let B (S : K) : weakOperatorBall M C :=
    ⟨S.val, hKM S.val S.property, hbound S.val S.property⟩
  have hB : Continuous B := continuous_subtype_val.subtype_mk _
  have hv (η : J) : LowerSemicontinuous (fun S : K => ‖v S - η‖ ^ 2) := by
    have hc : Continuous (fun S : K => ofCLM (ρ (a S)).val) := (hρ C).comp hB
    change LowerSemicontinuous (fun S : K => ‖(ρ (a S)).val τ.vector - η‖ ^ 2)
    exact (wot_vector_sqDistance_lowerSemicontinuous (H := J) τ.vector η).comp hc
  have hn : (Set.univ : Set K).Nonempty := by
    obtain ⟨S, hS⟩ := hne
    exact ⟨⟨S, hS⟩, Set.mem_univ _⟩
  have hm (S : K) (_ : S ∈ Set.univ) (V : K) (_ : V ∈ Set.univ) :
      ∃ Z ∈ (Set.univ : Set K), v Z = (1 / 2 : ℝ) • (v S + v V) := by
    let Z : K := ⟨(1 / 2 : ℝ) • (S.val + V.val), hmid S.val S.property V.val V.property⟩
    refine ⟨Z, Set.mem_univ _, ?_⟩
    have he : a Z = (1 / 2 : ℝ) • (a S + a V) := Subtype.ext rfl
    change L (a Z) = _
    rw [he, L.map_smul, L.map_add]
  have hb (S : K) (_ : S ∈ Set.univ) : ‖v S‖ ≤ C :=
    (τ.norm₂_le_norm (ρ (a S))).trans
      ((NonUnitalStarAlgHom.norm_apply_le ρ.toStarAlgHom (a S)).trans (hbound S.val S.property))
  have hf : Set.InjOn v Set.univ := by
    intro S _ V _ he
    have hz : ρ (a S - a V) = 0 := by
      apply τ.separating
      change (ρ (a S - a V)).val τ.vector = 0
      rw [map_sub]
      exact sub_eq_zero.mpr he
    have haz : a S - a V = 0 := ρ.injective (hz.trans (map_zero ρ.toStarAlgHom).symm)
    apply Subtype.ext
    apply toCLM_injective
    exact congrArg Subtype.val (sub_eq_zero.mp haz)
  let F (w : unitary (Algebra R)) (S : K) : K :=
    ⟨ofCLM (unitaryConj (ambientAlgebraUnitary w) S.val.toCLM), hinv w S.val S.property⟩
  have ho (w : unitary (Algebra R)) (S : K) (_ : S ∈ Set.univ) :
      ∃ V ∈ (Set.univ : Set K), F w V = S := by
    refine ⟨F (star w) S, Set.mem_univ _, ?_⟩
    apply Subtype.ext
    apply toCLM_injective
    change unitaryConj (ambientAlgebraUnitary w)
      (unitaryConj (ambientAlgebraUnitary (star w)) S.val.toCLM) = S.val.toCLM
    have he : ambientAlgebraUnitary (star w) = star (ambientAlgebraUnitary w) :=
      Subtype.ext rfl
    rw [he]
    simpa only [star_star] using
      unitaryConj_star_unitaryConj (star (ambientAlgebraUnitary w)) S.val.toCLM
  have hi (w : unitary (Algebra R)) (S : K) (_ : S ∈ Set.univ)
      (V : K) (_ : V ∈ Set.univ) : ‖v (F w S) - v (F w V)‖ = ‖v S - v V‖ := by
    let wM : unitary (Algebra M) := Unitary.map
      (StarMonoidHom.ofClass (StarSubalgebra.inclusion hRM)) w
    let wP : unitary (Algebra P) := Unitary.map (StarMonoidHom.ofClass ρ.toStarAlgHom) wM
    have he : a (F w S) - a (F w V) =
        (wM : Algebra M) * (a S - a V) * star (wM : Algebra M) := by
      apply Subtype.ext
      change unitaryConj (ambientAlgebraUnitary w) S.val.toCLM -
        unitaryConj (ambientAlgebraUnitary w) V.val.toCLM = _
      exact (unitaryConj_sub (ambientAlgebraUnitary w) S.val.toCLM V.val.toCLM).symm
    change ‖L (a (F w S)) - L (a (F w V))‖ = ‖L (a S) - L (a V)‖
    rw [← L.map_sub, he, ← L.map_sub]
    change τ.norm₂ (ρ.toStarAlgHom ((wM : Algebra M) * (a S - a V) *
      star (wM : Algebra M))) = τ.norm₂ (ρ.toStarAlgHom (a S - a V))
    rw [map_mul, map_mul, map_star]
    exact conjugate_norm₂ τ wP (ρ (a S - a V))
  obtain ⟨S, _, hS⟩ := exists_fixed_of_compact_hilbert_image Set.univ isCompact_univ
    hn v hv hm C hb hf F (fun _ _ _ => Set.mem_univ _) ho hi
  exact ⟨S.val, S.property, fun w => congrArg (fun Z : K => Z.val.toCLM) (hS w)⟩

end

end KadisonKastler

end OAI
