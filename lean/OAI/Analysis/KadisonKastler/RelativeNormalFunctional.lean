import OAI.Analysis.KadisonKastler.RelativeTracialFixedPoint

namespace OAI

/-! # Normal functionals invariant under an irreducible finite inclusion

A compact slice of the operator ball preserves both a normal functional
and the trace. Relative tracial averaging makes an element of that slice
scalar, so the functional is its value at one times the trace.
-/

namespace KadisonKastler

noncomputable section

open ContinuousLinearMapWOT Generator.Tracial UltrapowerBridge

variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

theorem normal_invariant_functional_eq_trace
    (M R : VonNeumannAlgebra H) (hRM : R ≤ M) (P : VonNeumannAlgebra J)
    (ρ : Algebra M ≃⋆ₐ[ℂ] Algebra P) (τ : TracialRepresentation P)
    (hρ : ∀ C : ℝ, Continuous (fun b : weakOperatorBall M C =>
      ofCLM (ρ ⟨b.val.toCLM, b.property.1⟩).val))
    (hirr : ∀ a : Algebra M, a.val ∈ R.commutant → ∃ c : ℂ, a = c • 1)
    (φ : Algebra M →ₗ[ℂ] ℂ)
    (hφ : ∀ C : ℝ, Continuous (fun b : weakOperatorBall M C =>
      φ ⟨b.val.toCLM, b.property.1⟩))
    (hinv : ∀ (w : unitary (Algebra R)) (a : Algebra M),
      φ ((coordinateInclusion hRM (w : Algebra R)) * a *
        star (coordinateInclusion hRM (w : Algebra R))) = φ a)
    (x : Algebra M) : φ x = τ.trace (ρ x) * φ 1 := by
  let ψ : Algebra M →ₗ[ℂ] ℂ := (innerSL ℂ τ.vector).toLinearMap.comp
    ((algebraVectorMap P τ.vector).comp ρ.toStarAlgHom.toLinearMap)
  have hψ (a : Algebra M) : ψ a = τ.trace (ρ a) := rfl
  have hcψ (C : ℝ) : Continuous (fun b : weakOperatorBall M C =>
      ψ ⟨b.val.toCLM, b.property.1⟩) :=
    continuous_inner_apply (hρ C) τ.vector τ.vector
  let : CompactSpace (weakOperatorBall M ‖x‖) :=
    isCompact_iff_compactSpace.mp (weakOperatorBall_isCompact M ‖x‖)
  let L : Set (weakOperatorBall M ‖x‖) := {b |
    φ ⟨b.val.toCLM, b.property.1⟩ = φ x ∧ ψ ⟨b.val.toCLM, b.property.1⟩ = ψ x}
  have hLc : IsClosed L :=
    (isClosed_eq (hφ ‖x‖) continuous_const).inter (isClosed_eq (hcψ ‖x‖) continuous_const)
  let K : Set (H →WOT[ℂ] H) := Subtype.val '' L
  have hK : IsCompact K := hLc.isCompact.image continuous_subtype_val
  have hn : K.Nonempty := by
    refine ⟨ofCLM x.val, ?_⟩
    exact ⟨⟨ofCLM x.val, x.property, le_rfl⟩, ⟨rfl, rfl⟩, rfl⟩
  have hk (S : H →WOT[ℂ] H) (hS : S ∈ K) :
      ∃ h : S ∈ weakOperatorBall M ‖x‖,
        φ ⟨S.toCLM, h.1⟩ = φ x ∧ ψ ⟨S.toCLM, h.1⟩ = ψ x := by
    obtain ⟨b, hb, rfl⟩ := hS
    exact ⟨b.property, hb⟩
  have hm (S) (hS : S ∈ K) : S.toCLM ∈ M := (hk S hS).choose.1
  have hb (S) (hS : S ∈ K) : ‖S.toCLM‖ ≤ ‖x‖ := (hk S hS).choose.2
  have hmid (S) (hS : S ∈ K) (V) (hV : V ∈ K) :
      (1 / 2 : ℝ) • (S + V) ∈ K := by
    obtain ⟨hs, hsφ, hsψ⟩ := hk S hS
    obtain ⟨hv, hvφ, hvψ⟩ := hk V hV
    let s : Algebra M := ⟨S.toCLM, hs.1⟩
    let v : Algebra M := ⟨V.toCLM, hv.1⟩
    let z : Algebra M := (1 / 2 : ℝ) • (s + v)
    have hz : ‖z‖ ≤ ‖x‖ := by
      calc
        ‖z‖ = (1 / 2 : ℝ) * ‖s + v‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        _ ≤ (1 / 2 : ℝ) * (‖s‖ + ‖v‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
        _ ≤ ‖x‖ := by change (1 / 2 : ℝ) * (‖S.toCLM‖ + ‖V.toCLM‖) ≤ ‖x‖; linarith [hs.2, hv.2]
    refine ⟨⟨ofCLM z.val, z.property, hz⟩, ?_, rfl⟩
    change φ z = φ x ∧ ψ z = ψ x
    constructor
    · change φ ((1 / 2 : ℝ) • (s + v)) = φ x
      rw [φ.map_smul_of_tower, φ.map_add, hsφ, hvφ]
      module
    · change ψ ((1 / 2 : ℝ) • (s + v)) = ψ x
      rw [ψ.map_smul_of_tower, ψ.map_add, hsψ, hvψ]
      module
  have hi (w : unitary (Algebra R)) (S) (hS : S ∈ K) :
      ofCLM (unitaryConj (ambientAlgebraUnitary w) S.toCLM) ∈ K := by
    obtain ⟨hs, hsφ, hsψ⟩ := hk S hS
    let s : Algebra M := ⟨S.toCLM, hs.1⟩
    let u : unitary (Algebra M) := Unitary.map
      (StarMonoidHom.ofClass (coordinateInclusion hRM)) w
    let z : Algebra M := (u : Algebra M) * s * star (u : Algebra M)
    have hz : ‖z‖ ≤ ‖x‖ := by
      change ‖unitaryConj (ambientAlgebraUnitary w) S.toCLM‖ ≤ ‖x‖
      rw [norm_unitaryConj]
      exact hs.2
    refine ⟨⟨ofCLM z.val, z.property, hz⟩, ?_, rfl⟩
    change φ z = φ x ∧ ψ z = ψ x
    constructor
    · exact (hinv w s).trans hsφ
    · rw [hψ]
      have hu : star (ρ.toStarAlgHom (u : Algebra M)) * ρ.toStarAlgHom (u : Algebra M) = 1 := by
        have h := congrArg ρ.toStarAlgHom u.property.1
        simpa only [map_mul, map_star, map_one] using h
      change τ.trace (ρ.toStarAlgHom ((u : Algebra M) * s * star (u : Algebra M))) = ψ x
      rw [map_mul, map_mul, map_star, τ.trace_mul_comm, ← mul_assoc,
        hu, one_mul]
      exact hsψ
  obtain ⟨S, hS, hfix⟩ := exists_relative_tracial_fixed_point M R hRM P ρ τ hρ
    K hK hn hm hmid ‖x‖ hb hi
  obtain ⟨hs, hsφ, hsψ⟩ := hk S hS
  let s : Algebra M := ⟨S.toCLM, hs.1⟩
  obtain ⟨c, hc⟩ := hirr s (mem_commutant_of_unitaryConj_fixed R S.toCLM hfix)
  have hψs : ψ s = c := by
    rw [hc, ψ.map_smul, hψ]
    simp only [map_one, TracialRepresentation.trace_one, smul_eq_mul, mul_one]
  have hφs : φ s = c * φ 1 := by rw [hc, φ.map_smul, smul_eq_mul]
  exact hsφ.symm.trans (hφs.trans (congrArg (fun t : ℂ => t * φ 1) (hψs.symm.trans hsψ)))

/-- A unit vector whose state is central over the irreducible subalgebra
implements the unique normalized trace. -/
theorem vector_state_eq_trace_of_relative_central
    (M R : VonNeumannAlgebra H) (hRM : R ≤ M) (P : VonNeumannAlgebra J)
    (ρ : Algebra M ≃⋆ₐ[ℂ] Algebra P) (τ : TracialRepresentation P)
    (hρ : ∀ C : ℝ, Continuous (fun b : weakOperatorBall M C =>
      ofCLM (ρ ⟨b.val.toCLM, b.property.1⟩).val))
    (hirr : ∀ a : Algebra M, a.val ∈ R.commutant → ∃ c : ℂ, a = c • 1)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (hcentral : ∀ (r : Algebra R) (a : Algebra M),
      inner ℂ ξ ((coordinateInclusion hRM r * a).val ξ) =
      inner ℂ ξ ((a * coordinateInclusion hRM r).val ξ))
    (x : Algebra M) : inner ℂ ξ (x.val ξ) = τ.trace (ρ x) := by
  let φ : Algebra M →ₗ[ℂ] ℂ :=
    (innerSL ℂ ξ).toLinearMap.comp (algebraVectorMap M ξ)
  have hc (C : ℝ) : Continuous (fun b : weakOperatorBall M C =>
      φ ⟨b.val.toCLM, b.property.1⟩) :=
    continuous_inner_apply continuous_subtype_val ξ ξ
  have hi (w : unitary (Algebra R)) (a : Algebra M) :
      φ (coordinateInclusion hRM (w : Algebra R) * a *
        star (coordinateInclusion hRM (w : Algebra R))) = φ a := by
    let b := coordinateInclusion hRM (w : Algebra R)
    have hu : star b * b = 1 := by
      have h := congrArg (coordinateInclusion hRM) w.property.1
      simpa only [map_mul, map_star, map_one] using h
    change φ (b * a * star b) = φ a
    calc
      φ (b * a * star b) = φ (b * (a * star b)) := congrArg φ (mul_assoc _ _ _)
      _ = φ ((a * star b) * b) := hcentral (w : Algebra R) (a * star b)
      _ = φ a := by rw [mul_assoc, hu, mul_one]
  have h := normal_invariant_functional_eq_trace M R hRM P ρ τ hρ hirr φ hc hi x
  have h1 : φ 1 = 1 := by
    change inner ℂ ξ ξ = 1
    rw [inner_self_eq_norm_sq_to_K, hξ]
    norm_num
  rw [h1, mul_one] at h
  change inner ℂ ξ (x.val ξ) = _ at h
  exact h

end

end KadisonKastler

end OAI
