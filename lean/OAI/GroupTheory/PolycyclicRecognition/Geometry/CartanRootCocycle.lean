import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCocycleRestriction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CocycleContractingFlow
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSupportLegs

namespace OAI

/-! # Sublinear logarithmic bounds on actual Cartan root coordinates

First approximate the cocycle on the nilpotent Cartan factor. A contracting
one-parameter subgroup then carries every root vector into a fixed compact
ball in logarithmic time. This retains the nilpotent correction in the
generalized root action.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped Manifold Matrix.Norms.Operator Topology

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] rootNormedAddCommGroup rootNormedSpace rootNontrivial

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (M : CartanWordModel H) (hExpG : IsGroupExponential ExpG)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (hρ : ∀ v, Continuous (fun g => ρ g v))
  (hfix : ∀ v, (∀ g, ρ g v = v) → v = 0)

include T M hExpG realize haarN dynkinN hρ hfix in
theorem cartan_root_cocycle_sublinear_log
    (b : G → E) (hbc : Continuous b) (hb : IsUnitaryCocycle ρ b)
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ v : rootSpace H χ,
      ‖b (ExpG v)‖ ≤ ε * Real.log (2 + ‖v‖) + B := by
  let : TopologicalSpace (rootSpace H χ) :=
    (inferInstance : NormedAddCommGroup (rootSpace H χ)).toUniformSpace.toTopologicalSpace
  obtain ⟨m, hm, τ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hτ : Function.Injective τ := by
    intro g k he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  let Exp : rootSpace H χ → G := fun v => ExpG v
  have hc : Continuous Exp := by
    apply hind.continuous_iff.mpr
    change Continuous (fun v : rootSpace H χ => (τ (ExpG v) : Matrix (Fin m) (Fin m) ℝ))
    simp_rw [hmatch]
    exact Units.continuous_val.comp
      (algebraExpUnit_continuous.comp (representedRootVector H χ j).continuous)
  obtain ⟨h, hh⟩ := exists_contracting_root_direction H χ hχ
  let N := rootAction H χ h + 1
  have hn : _root_.IsNilpotent N := by
    simpa only [hh, neg_smul, one_smul, sub_neg_eq_add, N] using
      rootAction_nilpotent_correction H χ h
  obtain ⟨c, hcN⟩ := hn
  have hN : N ^ (c + 1) = 0 := by rw [pow_succ, hcN, zero_mul]
  let dD : ℝ → F.D.carrier := fun t => F.ExpD (F.D.equiv ((-t) • h))
  let d : ℝ → G := fun t => F.inclusionD (dD t)
  have hd (t : ℝ) : d t = ExpG (t • (-(h : GroupLieAlgebra (𝓘(ℝ, EG)) G))) := by
    dsimp [d, dD]
    rw [F.compatibleD]
    change ExpG ((-t) • (h : GroupLieAlgebra (𝓘(ℝ, EG)) G)) = _
    rw [neg_smul, smul_neg]
  have hdD : Continuous dD := by
    apply F.closedD.isEmbedding.continuous_iff.mpr
    change Continuous d
    rw [show d = (fun t => ExpG (t • (-(h : GroupLieAlgebra (𝓘(ℝ, EG)) G)))) from funext hd]
    exact continuous_exp_line_of_published_realization T ExpG hExpG realize _
  have hd0 : d 0 = 1 := by rw [hd, zero_smul, hExpG.map_zero]
  have hdmul (s t : ℝ) : d (s + t) = d s * d t := by
    simp only [hd]
    exact hExpG.map_add_smul _ s t
  have hpath : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧
      ∀ t, 1 ≤ t → ‖b (d t)‖ ≤ ε * t + B := by
    apply hb.sublinear_flow_of_approximation d hd0 hdmul
    intro ε hε
    obtain ⟨φ, hφ⟩ := cartan_cocycle_approximation T F M hExpG realize haarN dynkinN
      ρ hρ hfix b hbc hb (dD '' Icc (0 : ℝ) 1) (isCompact_Icc.image hdD) hε
    exact ⟨φ, fun t ht => hφ (dD t) ⟨t, ht, rfl⟩⟩
  let A : ℝ → rootSpace H χ → rootSpace H χ :=
    fun t v => (NormedSpace.exp (t • rootAction H χ h)) v
  have hconj (v : rootSpace H χ) (t : ℝ) (_ht : 0 ≤ t) :
      Exp v = d t * Exp (A t v) * (d t)⁻¹ := by
    apply hτ
    simp only [Exp, map_mul, map_inv, hd, hmatch, map_smul, map_neg, smul_neg]
    exact represented_root_exp_inverse_conjugation H χ j h t v
  have hcontract (v : rootSpace H χ) (t : ℝ) (ht : 0 ≤ t) :
      ‖A t v‖ ≤ (((c : ℝ) + 1) * (1 + ‖N‖) ^ c) *
        (1 + t) ^ c * Real.exp (-t) * ‖v‖ := by
    have he : rootAction H χ h = N - 1 := by simp [N]
    simpa only [A, he, exp_smul_sub_one, smul_apply] using
      norm_contracted_nilpotent_flow_le N hN v ht
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : rootSpace H χ) 1).exists_bound_of_continuousOn
    (hbc.comp hc).continuousOn
  have hlocal : ∃ B : ℝ, 0 ≤ B ∧ ∀ v, ‖v‖ ≤ 1 → ‖b (Exp v)‖ ≤ B := by
    refine ⟨max B 0, le_max_right _ _, fun v hv => ?_⟩
    exact (hB v (by simpa only [Metric.mem_closedBall, dist_zero_right] using hv)).trans
      (le_max_left _ _)
  exact hb.sublinear_log_of_contracting_flow Exp d A (by positivity) c hconj hcontract hlocal hpath

end PolycyclicRecognition

end

end OAI
