import Mathlib
import OAI.Geometry.PrescribedPotential.CoreBounds
import OAI.Geometry.PrescribedPotential.ParameterSchwartz

namespace OAI

/-! Parameter Core Bounds. -/

section

 

noncomputable section
open Filter Topology MeasureTheory FourierTransform TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ContDiff Real ComplexOrder MatrixOrder Classical

namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma CoreBound.list_sum {α : Type*} {s t : ℝ} (I : List α)
    (T : α → 𝓢(E, ℂ) → 𝓢(E, ℂ)) (hh : ∀ i ∈ I, CoreBound s t (T i)) :
    CoreBound s t (fun f => (I.map (fun i => T i f)).sum) := by
  induction I with
  | nil => exact ⟨0, le_rfl, by simp [schwartzCoord_zero]⟩
  | cons i I ih =>
    exact (hh i (List.mem_cons_self ..)).add (ih (fun j hj => hh j (List.mem_cons_of_mem _ hj)))

lemma coreBound_perturbation {ι : Type*} [Fintype ι] (v : ι → E)
    (a : SmoothCoefficients ι E) : CoreBound 2 0 (smoothPerturbation v a) :=
  ⟨perturbationBound v (coefficientBCF a), perturbationBound_nonneg v _, smoothPerturbation_bound v a⟩

 
lemma coreBound_of_words_base (k : ℕ) {s r : ℝ} (T : 𝓢(E, ℂ) → 𝓢(E, ℂ))
    (h : ∀ ws : List E, ws.length ≤ 2 * k → CoreBound s r (fun f => schwartzWord ws (T f))) :
    CoreBound s (r + 2 * (k : ℝ)) T := by
  induction k generalizing T with
  | zero => simpa [schwartzWord] using h [] (by simp)
  | succ k ih =>
    have ht := ih T (fun ws hw => h ws (by omega))
    have hd (j : Fin (Module.finrank ℝ E)) := ih
      (fun f => ∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E j} (T f)))
      (fun ws hw => by
        have hh := h (ws ++ [stdOrthonormalBasis ℝ E j, stdOrthonormalBasis ℝ E j])
          (by simp only [List.length_append, List.length_cons, List.length_nil] ; omega)
        simpa only [schwartzWord_append, schwartzWord, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply, lineDerivOpCLM_apply] using hh)
    convert coreBound_raise_two T ht hd using 1; push_cast; ring

end SobolevChart

namespace FrozenPoisson.ParameterRegularity
open FrozenPoisson SobolevChart EllipticKernel
variable {n : ℕ} {ι : Type*} [Fintype ι]
variable (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
  (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (a : SmoothCoefficients ι (EC n))
  (hsmall : perturbationBound v (coefficientBCF a) * ellipticBound H hH < 1)

lemma schwartzLocal_fixed (f : 𝓢(EC n, ℂ)) :
    schwartzLocal H hH t ht v a hsmall f = schwartzResolvent H t
      (f + smoothPerturbation v a (schwartzLocal H hH t ht v a hsmall f)) := by
  apply schwartz_distribution_injective
  rw [schwartzResolvent_distribution H hH t ht]
  rw [show SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume
    (schwartzLocal H hH t ht v a hsmall f) = _ from
    schwartzLocalValue_distribution H hH t ht v a hsmall f]
  have hr := parameterHilbert_realize H hH t ht 0
    (schwartzCoord 0 f + perturbation v (coefficientBCF a)
      (parameterLocal H hH t ht v (coefficientBCF a) hsmall (schwartzCoord 0 f)))
  norm_num only [zero_add] at hr
  rw [← schwartzLocal_coord H hH t ht v a hsmall f] at hr
  rw [← schwartzCoord_perturbation, ← schwartzCoord_add, realize_schwartzCoord] at hr
  rw [← hr, schwartzCoord_add, schwartzCoord_perturbation,
    schwartzLocal_coord H hH t ht v a hsmall f]
  exact congrArg (realize (E := EC n) 2)
    (parameterLocal_fixed H hH t ht v (coefficientBCF a) hsmall (schwartzCoord 0 f))

 

theorem schwartzLocal_word_bound (ws : List (EC n)) {s : ℝ} (hws : (ws.length : ℝ) ≤ s) :
    CoreBound s 2 (fun f => schwartzWord ws (schwartzLocal H hH t ht v a hsmall f)) := by
  induction hlen : ws.length using Nat.strong_induction_on generalizing ws s with
  | h k ih =>
    subst k
    let T := schwartzLocal H hH t ht v a hsmall
    have hlow : CoreBound s 0 (fun f => ((commutatorTerms ws a).map
        (fun b => smoothPerturbation v b.1 (schwartzWord b.2 (T f)))).sum) := by
      apply CoreBound.list_sum
      intro b hb
      exact (coreBound_perturbation v b.1).comp
        (ih b.2.length (commutatorTerms_order ws a b hb) b.2 (le_trans (by exact_mod_cast
          (commutatorTerms_order ws a b hb).le) hws) rfl)
    have hforce := (coreBound_word ws (t := 0) (by linarith : 0 ≤ s - ws.length)).add hlow
    obtain ⟨C, hC, hforce⟩ := hforce
    let q := ellipticBound H hH * perturbationBound v (coefficientBCF a)
    have hq : q < 1 := by simpa [q, mul_comm] using hsmall
    have hq' : 0 < 1 - q := sub_pos.mpr hq
    refine ⟨ellipticBound H hH * C / (1 - q),
      div_nonneg (mul_nonneg (ellipticBound_pos H hH).le hC) hq'.le, fun f => ?_⟩
    have he := congrArg (schwartzWord ws) (schwartzLocal_fixed H hH t ht v a hsmall f)
    rw [schwartz_word_resolvent ws H hH t ht, map_add, schwartz_word_perturbation] at he
    have hb := schwartzResolvent_bound H hH t ht
      (smoothPerturbation v a (schwartzWord ws (T f)) +
        (schwartzWord ws f + ((commutatorTerms ws a).map
          (fun b => smoothPerturbation v b.1 (schwartzWord b.2 (T f)))).sum))
    have he' : schwartzWord ws (T f) = schwartzResolvent H t
        (smoothPerturbation v a (schwartzWord ws (T f)) +
          (schwartzWord ws f + ((commutatorTerms ws a).map
            (fun b => smoothPerturbation v b.1 (schwartzWord b.2 (T f)))).sum)) := by
      change schwartzWord ws (T f) = _ at he
      rw [add_left_comm] at he
      exact he
    rw [← he', schwartzCoord_add] at hb
    have hbound := hb.trans (mul_le_mul_of_nonneg_left (norm_add_le _ _)
      (ellipticBound_pos H hH).le)
    have hp := smoothPerturbation_bound v a (schwartzWord ws (T f))
    have hf := hforce f
    have hfinal : (1 - q) * ‖schwartzCoord 2 (schwartzWord ws (T f))‖ ≤
        ellipticBound H hH * C * ‖schwartzCoord s f‖ := by
      dsimp only [q]
      nlinarith [mul_le_mul_of_nonneg_left hp (ellipticBound_pos H hH).le,
        mul_le_mul_of_nonneg_left hf (ellipticBound_pos H hH).le]
    rw [div_mul_eq_mul_div, le_div_iff₀ hq']
    simpa only [mul_comm] using hfinal

 

theorem schwartzLocal_even_bound (k : ℕ) :
    CoreBound (2 * (k : ℝ)) (2 * (k : ℝ) + 2) (schwartzLocal H hH t ht v a hsmall) := by
  rw [add_comm]
  apply coreBound_of_words_base k
  intro ws hw
  apply schwartzLocal_word_bound H hH t ht v a hsmall ws
  exact_mod_cast hw

end FrozenPoisson.ParameterRegularity

end
end

end OAI
