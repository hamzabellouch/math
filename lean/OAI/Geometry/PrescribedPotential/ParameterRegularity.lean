import Mathlib
import OAI.Geometry.PrescribedPotential.LocalRegularity
import OAI.Geometry.PrescribedPotential.ParameterLocal

namespace OAI

/-! Parameter Regularity. -/

section

 

noncomputable section
open Filter Topology MeasureTheory FourierTransform TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ContDiff Real ComplexOrder MatrixOrder

namespace FrozenPoisson.ParameterRegularity
open FrozenPoisson SobolevChart EllipticKernel
variable {n : ℕ} {ι : Type*} [Fintype ι]

def schwartzResolvent (H : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    𝓢(EC n, ℂ) →L[ℂ] 𝓢(EC n, ℂ) :=
  SchwartzMap.fourierMultiplierCLM ℂ (parameterSymbol H t)

lemma schwartzResolvent_distribution (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (f : 𝓢(EC n, ℂ)) :
    SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume (schwartzResolvent H t f) =
      parameterResolvent H t (SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume f) :=
  (fourierMultiplierCLM_toTemperedDistributionCLM_eq
    (parameterSymbol_temperate H hH (lt_of_lt_of_le zero_lt_one ht)) f).symm

lemma schwartzCoord_resolvent (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (s : ℝ) (f : 𝓢(EC n, ℂ)) :
    schwartzCoord (s + 2) (schwartzResolvent H t f) =
      parameterHilbert H hH t ht (schwartzCoord s f) := by
  apply realize_injective (s + 2)
  rw [realize_schwartzCoord, parameterHilbert_realize, realize_schwartzCoord]
  exact schwartzResolvent_distribution H hH t ht f

lemma weak_deriv_resolvent (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : EC n) (u : 𝓢'(EC n, ℂ)) :
    ∂_{v} (parameterResolvent H t u) = parameterResolvent H t (∂_{v} u) := by
  simp only [lineDeriv_eq_fourierMultiplierCLM, parameterResolvent, map_smul]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply
    (parameterSymbol_temperate H hH (lt_of_lt_of_le zero_lt_one ht)) (by fun_prop),
    fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop)
      (parameterSymbol_temperate H hH (lt_of_lt_of_le zero_lt_one ht))]
  simp only [mul_comm]

lemma schwartz_deriv_resolvent (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : EC n) (f : 𝓢(EC n, ℂ)) :
    ∂_{v} (schwartzResolvent H t f) = schwartzResolvent H t (∂_{v} f) := by
  apply schwartz_distribution_injective
  rw [← lineDerivOp_toTemperedDistributionCLM_eq, schwartzResolvent_distribution H hH t ht,
    schwartzResolvent_distribution H hH t ht, ← lineDerivOp_toTemperedDistributionCLM_eq]
  exact weak_deriv_resolvent H hH t ht v (SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume f)

lemma schwartz_word_resolvent (ws : List (EC n)) (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (t : ℝ) (ht : 1 ≤ t) (f : 𝓢(EC n, ℂ)) :
    schwartzWord ws (schwartzResolvent H t f) = schwartzResolvent H t (schwartzWord ws f) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change ∂_{w} (schwartzWord ws (schwartzResolvent H t f)) = _
    rw [ih, schwartz_deriv_resolvent H hH t ht]
    rfl

 
def schwartzNeumann (H : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (v : ι → EC n)
    (a : SmoothCoefficients ι (EC n)) : 𝓢(EC n, ℂ) →L[ℂ] 𝓢(EC n, ℂ) :=
  schwartzResolvent H t ∘L smoothPerturbation v a

lemma schwartzResolvent_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (t : ℝ) (ht : 1 ≤ t)
    (f : 𝓢(EC n, ℂ)) :
    ‖schwartzCoord 2 (schwartzResolvent H t f)‖ ≤
      ellipticBound H hH * ‖schwartzCoord 0 f‖ := by
  have hc := schwartzCoord_resolvent H hH t ht 0 f
  norm_num at hc
  rw [hc]
  exact parameterHilbert_bound H hH t ht _

lemma schwartzNeumann_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (t : ℝ) (ht : 1 ≤ t)
    (v : ι → EC n) (a : SmoothCoefficients ι (EC n)) (f : 𝓢(EC n, ℂ)) :
    ‖schwartzCoord 2 (schwartzNeumann H t v a f)‖ ≤
      (ellipticBound H hH * perturbationBound v (coefficientBCF a)) *
        ‖schwartzCoord 2 f‖ := by
  calc
    _ ≤ ellipticBound H hH * ‖schwartzCoord 0 (smoothPerturbation v a f)‖ :=
      schwartzResolvent_bound H hH t ht _
    _ ≤ ellipticBound H hH * (perturbationBound v (coefficientBCF a) *
        ‖schwartzCoord 2 f‖) :=
      mul_le_mul_of_nonneg_left (smoothPerturbation_bound v a f) (ellipticBound_pos H hH).le
    _ = _ := by ring

lemma schwartz_word_neumann (ws : List (EC n)) (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (a : SmoothCoefficients ι (EC n)) (f : 𝓢(EC n, ℂ)) :
    schwartzWord ws (schwartzNeumann H t v a f) =
      schwartzNeumann H t v a (schwartzWord ws f) +
        ((commutatorTerms ws a).map
          (fun term => schwartzNeumann H t v term.1 (schwartzWord term.2 f))).sum := by
  change schwartzWord ws (schwartzResolvent H t (smoothPerturbation v a f)) = _
  rw [schwartz_word_resolvent ws H hH t ht, schwartz_word_perturbation, map_add, map_list_sum]
  simp only [List.map_map, Function.comp_def]
  rfl

def schwartzIterate (H : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (v : ι → EC n)
    (a : SmoothCoefficients ι (EC n)) (f : 𝓢(EC n, ℂ)) (N : ℕ) : 𝓢(EC n, ℂ) :=
  (schwartzNeumann H t v a)^[N] f

lemma schwartzIterate_succ (H : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (v : ι → EC n)
    (a : SmoothCoefficients ι (EC n)) (f : 𝓢(EC n, ℂ)) (N : ℕ) :
    schwartzIterate H t v a f (N+1) = schwartzNeumann H t v a (schwartzIterate H t v a f N) :=
  Function.iterate_succ_apply' _ _ _

lemma summable_norm_neumann_of (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (t : ℝ) (ht : 1 ≤ t)
    (v : ι → EC n) (a : SmoothCoefficients ι (EC n)) (f : ℕ → 𝓢(EC n, ℂ))
    (hf : Summable (fun m => ‖schwartzCoord 2 (f m)‖)) :
    Summable (fun m => ‖schwartzCoord 2 (schwartzNeumann H t v a (f m))‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun m => schwartzNeumann_bound H hH t ht v a (f m))
  exact hf.mul_left _

 

theorem neumann_summable_word (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (t : ℝ) (ht : 1 ≤ t)
    (v : ι → EC n) (a : SmoothCoefficients ι (EC n))
    (hsmall : perturbationBound v (coefficientBCF a) * ellipticBound H hH < 1)
    (f : 𝓢(EC n, ℂ)) (ws : List (EC n)) :
    Summable (fun m => ‖schwartzCoord 2 (schwartzWord ws (schwartzIterate H t v a f m))‖) := by
  induction hlen : ws.length using Nat.strong_induction_on generalizing ws with
  | h k ih =>
    let err : ℕ → 𝓢(EC n, ℂ) := fun m => ((commutatorTerms ws a).map
      (fun term => schwartzNeumann H t v term.1 (schwartzWord term.2 (schwartzIterate H t v a f m)))).sum
    have hs : Summable (fun m => ‖schwartzCoord 2 (err m)‖) := by
      apply summable_norm_schwartzCoord_list
      intro term hterm
      apply summable_norm_neumann_of H hH t ht
      exact ih term.2.length (hlen ▸ commutatorTerms_order ws a term hterm) term.2 rfl
    apply summable_of_contracting_recurrence (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _) (q := ellipticBound H hH * perturbationBound v (coefficientBCF a))
      (by simpa only [mul_comm] using hsmall) hs
    intro m
    rw [schwartzIterate_succ, schwartz_word_neumann ws H hH t ht, schwartzCoord_add]
    exact (norm_add_le _ _).trans (add_le_add
      (schwartzNeumann_bound H hH t ht v a _) le_rfl)

def neumannSum (H : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (v : ι → EC n)
    (a : SmoothCoefficients ι (EC n)) (f : 𝓢(EC n, ℂ)) : L2 (EC n) :=
  ∑' m, schwartzCoord 2 (schwartzIterate H t v a f m)

lemma schwartzCoord_neumann (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (t : ℝ) (ht : 1 ≤ t)
    (v : ι → EC n) (a : SmoothCoefficients ι (EC n)) (f : 𝓢(EC n, ℂ)) :
    schwartzCoord 2 (schwartzNeumann H t v a f) =
      parameterHilbert H hH t ht (perturbation v (coefficientBCF a) (schwartzCoord 2 f)) := by
  have he := schwartzCoord_resolvent H hH t ht 0 (smoothPerturbation v a f)
  norm_num at he
  rw [schwartzCoord_perturbation] at he
  exact he

lemma neumannSum_fixed (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (t : ℝ) (ht : 1 ≤ t)
    (v : ι → EC n) (a : SmoothCoefficients ι (EC n))
    (hsmall : perturbationBound v (coefficientBCF a) * ellipticBound H hH < 1)
    (f : 𝓢(EC n, ℂ)) :
    neumannSum H t v a f = schwartzCoord 2 f +
      parameterHilbert H hH t ht (perturbation v (coefficientBCF a) (neumannSum H t v a f)) := by
  have hs := (neumann_summable_word H hH t ht v a hsmall f []).of_norm
  change Summable (fun m => schwartzCoord 2 (schwartzIterate H t v a f m)) at hs
  let T := parameterHilbert H hH t ht ∘L perturbation v (coefficientBCF a)
  have hmap := T.map_tsum hs
  simp only [T, ContinuousLinearMap.comp_apply, ← schwartzCoord_neumann,
    ← schwartzIterate_succ] at hmap
  change (∑' m, schwartzCoord 2 (schwartzIterate H t v a f m)) = _
  rw [hs.tsum_eq_zero_add]
  change schwartzCoord 2 f + _ = schwartzCoord 2 f + _
  exact congrArg (schwartzCoord 2 f + ·) hmap.symm

lemma fixed_unique (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (hsmall : perturbationBound v a * ellipticBound H hH < 1)
    (u w f : L2 (EC n))
    (hu : u = parameterHilbert H hH t ht (f + perturbation v a u))
    (hw : w = parameterHilbert H hH t ht (f + perturbation v a w)) : u = w := by
  have he : u - w = parameterHilbert H hH t ht (perturbation v a (u - w)) := by
    rw [map_sub, map_sub]
    rw [map_add] at hu hw
    calc
      u - w = (parameterHilbert H hH t ht f + parameterHilbert H hH t ht (perturbation v a u)) -
          (parameterHilbert H hH t ht f + parameterHilbert H hH t ht (perturbation v a w)) :=
        congrArg₂ (· - ·) hu hw
      _ = _ := by abel
  have hb : ‖u - w‖ ≤ (perturbationBound v a * ellipticBound H hH) * ‖u - w‖ := by
    calc
      _ = ‖parameterHilbert H hH t ht (perturbation v a (u - w))‖ := congrArg norm he
      _ ≤ _ := (parameterHilbert_bound H hH t ht _).trans
        (by nlinarith [perturbation_bound v a (u - w), ellipticBound_pos H hH])
  have : ‖u - w‖ = 0 := by nlinarith [norm_nonneg (u - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

lemma parameterLocal_fixed (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (hsmall : perturbationBound v a * ellipticBound H hH < 1) (f : L2 (EC n)) :
    parameterLocal H hH t ht v a hsmall f = parameterHilbert H hH t ht
      (f + perturbation v a (parameterLocal H hH t ht v a hsmall f)) := by
  change parameterHilbert H hH t ht (parameterCorrection H hH t ht v a hsmall f) = _
  congr 1
  exact sub_eq_iff_eq_add.mp (parameterCorrection_equation H hH t ht v a hsmall f)

lemma neumannSum_eq_local (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (a : SmoothCoefficients ι (EC n))
    (hsmall : perturbationBound v (coefficientBCF a) * ellipticBound H hH < 1)
    (f : 𝓢(EC n, ℂ)) :
    neumannSum H t v a (schwartzResolvent H t f) =
      parameterLocal H hH t ht v (coefficientBCF a) hsmall (schwartzCoord 0 f) := by
  apply fixed_unique H hH t ht v (coefficientBCF a) hsmall _ _ (schwartzCoord 0 f)
  · rw [map_add]
    have hr := schwartzCoord_resolvent H hH t ht 0 f
    norm_num at hr
    rw [← hr]
    exact neumannSum_fixed H hH t ht v a hsmall (schwartzResolvent H t f)
  · exact parameterLocal_fixed H hH t ht v (coefficientBCF a) hsmall _

 

theorem parameterLocal_schwartz_memSobolev (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (a : SmoothCoefficients ι (EC n))
    (hsmall : perturbationBound v (coefficientBCF a) * ellipticBound H hH < 1)
    (f : 𝓢(EC n, ℂ)) (k : ℕ) :
    MemSobolev (2 * (k : ℝ)) 2
      (realize 2 (parameterLocal H hH t ht v (coefficientBCF a) hsmall (schwartzCoord 0 f))) := by
  rw [← neumannSum_eq_local H hH t ht v a hsmall f]
  apply memSobolev_even_of_words _ _ k []
  intro ws
  exact memSobolev_word_of_summable (schwartzIterate H t v a (schwartzResolvent H t f)) ws
    (neumann_summable_word H hH t ht v a hsmall (schwartzResolvent H t f) [])
    (neumann_summable_word H hH t ht v a hsmall (schwartzResolvent H t f) ws)

end FrozenPoisson.ParameterRegularity

end
end

end OAI
