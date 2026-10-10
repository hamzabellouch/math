import OAI.Analysis.KadisonKastler.WeakTraceTransfer
import OAI.Analysis.FactorGeneration.OperatorLimits

namespace OAI

/-! # Strong trace transfer in a concrete finite representation

A finite vector-functional formula for the trace is enough: weak
compactness of the positive operator ball and faithfulness prove the
uniform two-norm-to-strong implication. No transfer theorem is assumed.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

local instance concreteTraceOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance concreteTracePreorder : Preorder (Algebra M) := (CStarAlgebra.spectralOrder _).toPreorder
local instance concreteTraceLE : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE
local instance concreteTraceStarOrder : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

/-- A finite vector-functional formula, used below for the factor trace. -/
def FiniteVectorTrace (τ : FaithfulTracialState (Algebra M)) : Prop :=
  ∃ (n : ℕ) (ξ η : Fin n → H), ∀ a : Algebra M,
    τ.toLinearMap a = ∑ i, inner ℂ (η i) ((a : H →L[ℂ] H) (ξ i))

theorem FiniteVectorTrace.tendsto {τ : FaithfulTracialState (Algebra M)}
    (hτ : FiniteVectorTrace τ) {J : Type*} {l : Filter J}
    (a : J → Algebra M) (b : Algebra M)
    (h : ∀ ξ η, Tendsto (fun j => inner ℂ η ((a j : H →L[ℂ] H) ξ)) l
      (𝓝 (inner ℂ η ((b : H →L[ℂ] H) ξ)))) :
    Tendsto (fun j => τ.toLinearMap (a j)) l (𝓝 (τ.toLinearMap b)) := by
  obtain ⟨n, ξ, η, hrep⟩ := hτ
  simp_rw [hrep]
  exact tendsto_finsetSum Finset.univ (fun i _ => h (ξ i) (η i))

/-- Faithfulness and weak compactness turn the normal trace into a
uniform strong-topology control on each operator-norm ball. -/
theorem FiniteVectorTrace.strongContinuous {τ : FaithfulTracialState (Algebra M)}
    (hτ : FiniteVectorTrace τ) : TraceStrongContinuous τ M.toStarSubalgebra.subtype := by
  intro z C hC ε hε
  by_contra! hbad
  have hex (n : ℕ) := hbad (1 / ((n : ℝ) + 1)) (by positivity)
  choose x hxC hx2 hxε using hex
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  have htwo : Tendsto (fun n => traceTwoNorm τ (x n)) (ω : Filter ℕ) (𝓝 0) := by
    apply squeeze_zero (fun n => traceTwoNorm_nonneg τ (x n)) (fun n => (hx2 n).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat.mono_left hω
  let a : ℕ → Algebra M := fun n => star (x n) * x n
  have ha : ∀ n, ‖a n‖ ≤ C ^ 2 := by
    intro n
    dsimp [a]
    rw [CStarRing.norm_star_mul_self, ← pow_two]
    exact pow_le_pow_left₀ (norm_nonneg _) (hxC n) 2
  obtain ⟨T, _, hT⟩ := Generator.Tracial.exists_weak_operator_ultralimit ω
    (fun n => (a n : H →L[ℂ] H)) (C ^ 2) (sq_nonneg C) ha
  have hm : T ∈ M := Generator.Tracial.weak_operator_limit_mem M a T hT
  let b : Algebra M := ⟨T, hm⟩
  have hWOT : Tendsto (fun n => ContinuousLinearMapWOT.ofCLM (a n : H →L[ℂ] H))
      (ω : Filter ℕ) (𝓝 (ContinuousLinearMapWOT.ofCLM T)) :=
    ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr hT
  have hposT : 0 ≤ T := (Generator.weakOperator_nonneg_isClosed (H := H)).mem_of_tendsto
    hWOT (Eventually.of_forall fun n => by
      change 0 ≤ star (x n : H →L[ℂ] H) * (x n : H →L[ℂ] H)
      exact star_mul_self_nonneg _)
  have hpos : 0 ≤ b := by
    apply (NonUnitalStarAlgHom.map_le_map_iff M.toStarSubalgebra.subtype
      Subtype.val_injective).mp
    simpa only [map_zero, b, StarSubalgebra.subtype_apply] using hposT
  have htτ := hτ.tendsto a b hT
  have htzero : Tendsto (fun n => τ.toLinearMap (a n)) (ω : Filter ℕ) (𝓝 0) := by
    have he (n : ℕ) : τ.toLinearMap (a n) = ((traceTwoNorm τ (x n) ^ 2 : ℝ) : ℂ) := by
      apply Complex.ext
      · simp only [Complex.ofReal_re, a, traceTwoNorm_sq]
      · simp only [a, τ.positive_im, Complex.ofReal_im]
    simp_rw [he]
    simpa only [Function.comp_def, zero_pow (by decide : (2 : ℕ) ≠ 0), Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).comp (by simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using htwo.pow 2)
  have hbτ : τ.toLinearMap b = 0 := tendsto_nhds_unique htτ htzero
  obtain ⟨v, hv⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpos
  have hvτ : τ.toLinearMap (star v * v) = 0 := by rw [← hv, hbτ]
  have hv0 := τ.faithful v hvτ
  have hb0 : b = 0 := by rw [hv, hv0, star_zero, zero_mul]
  have hT0 : T = 0 := congrArg Subtype.val hb0
  have ht := (Complex.continuous_re.tendsto _).comp (hT z z)
  have hlo : ε ^ 2 ≤ (inner ℂ z (T z)).re := by
    apply ge_of_tendsto ht
    apply Eventually.of_forall
    intro n
    have he : (inner ℂ z ((a n : H →L[ℂ] H) z)).re = ‖(x n : H →L[ℂ] H) z‖ ^ 2 := by
      change (inner ℂ z ((star (x n : H →L[ℂ] H)) ((x n : H →L[ℂ] H) z))).re = _
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
      simpa only [RCLike.re_eq_complex_re] using
        (inner_self_eq_norm_sq (𝕜 := ℂ) ((x n : H →L[ℂ] H) z))
    change ε ^ 2 ≤ (inner ℂ z ((a n : H →L[ℂ] H) z)).re
    rw [he]
    exact pow_le_pow_left₀ hε.le (hxε n) 2
  rw [hT0] at hlo
  simp only [zero_apply, inner_zero_right, Complex.zero_re] at hlo
  nlinarith

end

end KadisonKastler

end OAI
