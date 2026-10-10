import OAI.Analysis.KadisonKastler.TraceInvariantVectors
import Mathlib.GroupTheory.FreeGroup.Basic

namespace OAI

/-! # A countable group dense in the trace topology

The boundary argument only needs a countable discrete group whose unitary
image approximates every unitary in trace two-norm. A free group on a
countable dense set supplies an actual subgroup with this property.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- There is a countable subgroup of the unitary group that is dense for
the faithful trace two-norm. -/
theorem exists_countable_traceDense_unitary_subgroup
    [TopologicalSpace.SeparableSpace H]
    (τ : FaithfulTracialState (Algebra M)) (hτ : FiniteVectorTrace τ) :
    ∃ G : Subgroup (unitary (Algebra M)), (G : Set (unitary (Algebra M))).Countable ∧
      ∀ u : unitary (Algebra M), ∀ ε : ℝ, 0 < ε →
        ∃ g : G, traceTwoNorm τ ((u : Algebra M) - (g.val : Algebra M)) < ε := by
  classical
  obtain ⟨D, hDc, hDS, hDdense⟩ := hτ.traceSeparable
    (unitary (Algebra M) : Set (Algebra M))
  let : Countable D := hDc.to_subtype
  let f : D → unitary (Algebra M) := fun d => ⟨d.val, hDS d.property⟩
  let ρ : FreeGroup D →* unitary (Algebra M) := FreeGroup.lift f
  let G := ρ.range
  have hGc : (G : Set (unitary (Algebra M))).Countable := by
    change (Set.range ρ).Countable
    exact Set.countable_range ρ
  refine ⟨G, hGc, ?_⟩
  intro u ε hε
  obtain ⟨d, hd, hdu⟩ := hDdense u u.property ε hε
  let v : D := ⟨d, hd⟩
  have hf : ρ (FreeGroup.of v) = f v := FreeGroup.lift_apply_of
  refine ⟨⟨f v, ?_⟩, hdu⟩
  exact ⟨FreeGroup.of v, hf⟩

/-- Unitary conjugation of a fixed bounded element is Lipschitz in the
trace two-norm, with constant twice its operator norm. -/
theorem traceTwoNorm_unitary_conj_sub_le
    (τ : FaithfulTracialState (Algebra M)) (u v : unitary (Algebra M))
    (a : Algebra M) :
    traceTwoNorm τ ((u : Algebra M) * a * star (u : Algebra M) -
      (v : Algebra M) * a * star (v : Algebra M)) ≤
        2 * ‖a‖ * traceTwoNorm τ ((u : Algebra M) - v) := by
  have he : (u : Algebra M) * a * star (u : Algebra M) -
      (v : Algebra M) * a * star (v : Algebra M) =
      ((u : Algebra M) - v) * a * star (u : Algebra M) +
        (v : Algebra M) * (a * (star (u : Algebra M) - star (v : Algebra M))) := by
    noncomm_ring
  have hstar : traceTwoNorm τ (star (u : Algebra M) - star (v : Algebra M)) =
      traceTwoNorm τ ((u : Algebra M) - v) := by rw [← star_sub, traceTwoNorm_star]
  rw [he]
  calc
    _ ≤ traceTwoNorm τ (((u : Algebra M) - v) * a * star (u : Algebra M)) +
        traceTwoNorm τ ((v : Algebra M) *
          (a * (star (u : Algebra M) - star (v : Algebra M)))) := traceTwoNorm_add_le τ _ _
    _ = traceTwoNorm τ (((u : Algebra M) - v) * a) +
        traceTwoNorm τ (a * (star (u : Algebra M) - star (v : Algebra M))) := by
      rw [← Unitary.coe_star, traceTwoNorm_mul_unitary, traceTwoNorm_unitary_mul]
    _ ≤ traceTwoNorm τ ((u : Algebra M) - v) * ‖a‖ +
        ‖a‖ * traceTwoNorm τ (star (u : Algebra M) - star (v : Algebra M)) :=
      add_le_add (traceTwoNorm_mul_le_right τ _ _) (traceTwoNorm_mul_le_left τ _ _)
    _ = _ := by rw [hstar]; ring

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Invariance of coefficients extends from a trace-dense family of
unitaries to all unitaries. -/
theorem inner_conjugation_invariant_of_traceDense
    (τ : FaithfulTracialState (Algebra M)) (J : Algebra M →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τ a)
    (ρ : I → unitary (Algebra M))
    (hρ : ∀ u : unitary (Algebra M), ∀ ε : ℝ, 0 < ε →
      ∃ i, traceTwoNorm τ ((u : Algebra M) - ρ i) < ε)
    (v : E) (hinv : ∀ i a, inner ℂ v
      (J ((ρ i : Algebra M) * a * star (ρ i : Algebra M))) = inner ℂ v (J a))
    (u : unitary (Algebra M)) (a : Algebra M) :
    inner ℂ v (J ((u : Algebra M) * a * star (u : Algebra M))) = inner ℂ v (J a) := by
  apply eq_of_forall_dist_le
  intro ε hε
  let C : ℝ := 2 * ‖v‖ * ‖a‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCp : 0 < C + 1 := by linarith
  obtain ⟨i, hi⟩ := hρ u (ε / (C + 1)) (div_pos hε hCp)
  calc
    _ = ‖inner ℂ v (J ((u : Algebra M) * a * star (u : Algebra M) -
        (ρ i : Algebra M) * a * star (ρ i : Algebra M)))‖ := by
      rw [map_sub, inner_sub_right, hinv, dist_eq_norm]
    _ ≤ ‖v‖ * traceTwoNorm τ ((u : Algebra M) * a * star (u : Algebra M) -
        (ρ i : Algebra M) * a * star (ρ i : Algebra M)) := by
      rw [← hJ]
      exact norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (2 * ‖a‖ * traceTwoNorm τ ((u : Algebra M) - ρ i)) :=
      mul_le_mul_of_nonneg_left (traceTwoNorm_unitary_conj_sub_le τ u (ρ i) a)
        (norm_nonneg v)
    _ = C * traceTwoNorm τ ((u : Algebra M) - ρ i) := by dsimp [C]; ring
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hi.le hC
    _ ≤ ε := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hCp).mpr
      nlinarith

/-- Invariance under the chosen trace-dense group already forces a
scalar trace vector. No strong-density assumption is added. -/
theorem concreteTrace_scalar_of_traceDense_invariant
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (ρ : I → unitary (Algebra M))
    (hρ : ∀ u : unitary (Algebra M), ∀ ε : ℝ, 0 < ε →
      ∃ i, traceTwoNorm (concreteFactorTrace hM) ((u : Algebra M) - ρ i) < ε)
    (v : ConcreteTraceHilbert hM)
    (hinv : ∀ i, concreteTraceLeftAction hM (ρ i)
      (concreteTraceRightAction hM (star (ρ i : Algebra M)) v) = v) :
    ∃ z : ℂ, v = z • concreteTraceEmbedding hM 1 := by
  apply scalar_of_relative_invariant_coefficients (concreteFactorTrace hM)
    (concreteTraceEmbedding hM) (concreteTraceEmbedding_norm hM)
    (concreteFactorTrace_finiteVector hM) (concreteTraceEmbedding_denseRange hM)
    (fun x => by simp only [concreteTraceEmbedding_inner, star_one, one_mul])
    (StarAlgHom.id ℂ (Algebra M)) (traceHilbert_factor hM) v
  intro u a
  exact inner_conjugation_invariant_of_traceDense (concreteFactorTrace hM)
    (concreteTraceEmbedding hM) (concreteTraceEmbedding_norm hM) ρ hρ v
    (fun i a => concreteTrace_inner_conjugation_of_fixed hM (ρ i) v (hinv i) a) u a

end

end KadisonKastler

end OAI
