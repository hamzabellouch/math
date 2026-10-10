import Mathlib
import OAI.Geometry.PrescribedPotential.CutoffHigher
import OAI.Geometry.PrescribedPotential.StrongSobolevEmbedding

namespace OAI

/-! Sobolev Product. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ContDiff Classical
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma boundedDistribution_schwartz (f : 𝓢(E, ℂ)) :
    boundedDistributionCLM f.toBoundedContinuousFunction = (f : 𝓢'(E, ℂ)) := by
  ext φ
  rw [boundedDistributionCLM_apply, boundedDistribution_apply]
  rfl

lemma strongEmbedding_schwartz (s : ℝ) (hs : (Module.finrank ℝ E : ℝ) < 2*s)
    (f : 𝓢(E, ℂ)) : strongEmbedding s hs (schwartzCoord s f) = f.toBoundedContinuousFunction := by
  apply boundedDistribution_injective
  rw [strongEmbedding_distribution, realize_schwartzCoord, boundedDistribution_schwartz]

lemma schwartz_word_sup_bound (ws : List E) (s : ℝ)
    (hs : (Module.finrank ℝ E : ℝ) < 2*(s-ws.length)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(E, ℂ),
      ‖(schwartzWord ws f).toBoundedContinuousFunction‖ ≤ C * ‖schwartzCoord s f‖ := by
  obtain ⟨C,hC,hb⟩ := coreBound_word ws (s := s) (t := s-ws.length) le_rfl
  refine ⟨‖strongEmbedding (E := E) (s-ws.length) hs‖*C,
    mul_nonneg (norm_nonneg _) hC, fun f => ?_⟩
  rw [← strongEmbedding_schwartz (s-ws.length) hs]
  exact ((strongEmbedding (s-ws.length) hs).le_opNorm _).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb f)
      (norm_nonneg (strongEmbedding (E := E) (s-ws.length) hs)))

 
def BinaryCoreBound (s t : ℝ) (T : 𝓢(E, ℂ) → 𝓢(E, ℂ) → 𝓢(E, ℂ)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ f g,
    ‖schwartzCoord t (T f g)‖ ≤ C * (‖schwartzCoord s f‖ * ‖schwartzCoord s g‖)

lemma BinaryCoreBound.add {s t : ℝ} {T U : 𝓢(E, ℂ) → 𝓢(E, ℂ) → 𝓢(E, ℂ)}
    (hT : BinaryCoreBound s t T) (hU : BinaryCoreBound s t U) :
    BinaryCoreBound s t (fun f g => T f g + U f g) := by
  obtain ⟨C,hC,hc⟩ := hT
  obtain ⟨D,hD,hd⟩ := hU
  refine ⟨C+D, add_nonneg hC hD, fun f g => ?_⟩
  rw [schwartzCoord_add, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hc f g) (hd f g))

lemma binaryBound_raise_one {s t : ℝ} (T : 𝓢(E, ℂ) → 𝓢(E, ℂ) → 𝓢(E, ℂ))
    (hT : BinaryCoreBound s t T)
    (hD : ∀ j, BinaryCoreBound s t (fun f g => ∂_{stdOrthonormalBasis ℝ E j} (T f g))) :
    BinaryCoreBound s (t+1) T := by
  obtain ⟨C,hC,hc⟩ := hT
  choose D hD0 hd using hD
  let c : ℝ := ‖(((2*Real.pi)^2 : ℝ) : ℂ)⁻¹‖
  refine ⟨‖raiseZero (E := E) t‖*C + c*∑ j, ‖raiseDeriv t (stdOrthonormalBasis ℝ E j)‖*D j,
    add_nonneg (mul_nonneg (norm_nonneg _) hC)
      (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (hD0 j)))),
    fun f g => ?_⟩
  rw [schwartzCoord_raise_one]
  calc
    _ ≤ ‖raiseZero t (schwartzCoord t (T f g))‖ +
        c*‖∑ j, raiseDeriv t (stdOrthonormalBasis ℝ E j)
          (schwartzCoord t (∂_{stdOrthonormalBasis ℝ E j} (T f g)))‖ := by
      simpa only [norm_smul] using norm_sub_le
        (raiseZero t (schwartzCoord t (T f g)))
        ((((2*Real.pi)^2 : ℝ) : ℂ)⁻¹ • ∑ j, raiseDeriv t (stdOrthonormalBasis ℝ E j)
          (schwartzCoord t (∂_{stdOrthonormalBasis ℝ E j} (T f g))))
    _ ≤ (‖raiseZero (E := E) t‖*C)*(‖schwartzCoord s f‖*‖schwartzCoord s g‖) +
        c*∑ j, (‖raiseDeriv t (stdOrthonormalBasis ℝ E j)‖*D j)*
          (‖schwartzCoord s f‖*‖schwartzCoord s g‖) := by
      apply add_le_add
      · exact ((raiseZero t).le_opNorm _).trans (by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hc f g)
            (norm_nonneg (raiseZero (E := E) t)))
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro j _
        exact ((raiseDeriv t (stdOrthonormalBasis ℝ E j)).le_opNorm _).trans (by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hd j f g)
            (norm_nonneg (raiseDeriv t (stdOrthonormalBasis ℝ E j))))
    _ = _ := by rw [← Finset.sum_mul]; ring

lemma binaryBound_of_words (k : ℕ) {s : ℝ}
    (T : 𝓢(E, ℂ) → 𝓢(E, ℂ) → 𝓢(E, ℂ))
    (h : ∀ ws : List E, ws.length ≤ k →
      BinaryCoreBound s 0 (fun f g => schwartzWord ws (T f g))) :
    BinaryCoreBound s (k : ℝ) T := by
  induction k generalizing T with
  | zero => simpa [schwartzWord] using h [] (by simp)
  | succ k ih =>
    have ht := ih T (fun ws hw => h ws (by omega))
    have hd (j : Fin (Module.finrank ℝ E)) := ih
      (fun f g => ∂_{stdOrthonormalBasis ℝ E j} (T f g))
      (fun ws hw => by
        have hh := h (ws ++ [stdOrthonormalBasis ℝ E j])
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        simpa only [schwartzWord_append, schwartzWord, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply, lineDerivOpCLM_apply] using hh)
    simpa only [Nat.cast_succ] using binaryBound_raise_one T ht hd

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma schwartz_product_swap (f g : 𝓢(E, ℂ)) :
    SchwartzMap.smulLeftCLM ℂ f g = SchwartzMap.smulLeftCLM ℂ g f := by
  ext x
  simp only [SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth, smul_eq_mul, mul_comm]

lemma binaryBound_product_words_zero (m : ℕ) (hm : Module.finrank ℝ E < m)
    (p q : List E) (hpq : p.length+q.length ≤ m) :
    BinaryCoreBound (m : ℝ) 0 (fun f g =>
      SchwartzMap.smulLeftCLM ℂ (schwartzWord p f) (schwartzWord q g)) := by
  have base (p q : List E) (hpq : p.length+q.length ≤ m) (hp : 2*p.length ≤ m) :
      BinaryCoreBound (m : ℝ) 0 (fun f g =>
        SchwartzMap.smulLeftCLM ℂ (schwartzWord p f) (schwartzWord q g)) := by
    have hs : (Module.finrank ℝ E : ℝ) < 2*((m : ℝ)-p.length) := by
      have h₁ : (Module.finrank ℝ E : ℝ) < m := by exact_mod_cast hm
      have h₂ : 2*(p.length : ℝ) ≤ m := by exact_mod_cast hp
      linarith
    obtain ⟨C,hC,hc⟩ := schwartz_word_sup_bound p (m : ℝ) hs
    obtain ⟨D,hD,hd⟩ := coreBound_word q (s := (m : ℝ)) (t := 0) (by
      have hh : (q.length : ℝ) ≤ m := by exact_mod_cast (show q.length ≤ m by omega)
      linarith)
    refine ⟨C*D, mul_nonneg hC hD, fun f g => ?_⟩
    rw [schwartzCoord_product_zero]
    exact (multiply_norm_le _ _).trans (by
      have hh := mul_le_mul (hc f) (hd g) (norm_nonneg _)
        (mul_nonneg hC (norm_nonneg _))
      convert hh using 1; ring)
  by_cases hp : 2*p.length ≤ m
  · exact base p q hpq hp
  · obtain ⟨C,hC,hc⟩ := base q p (by omega) (by omega)
    refine ⟨C,hC, fun f g => ?_⟩
    dsimp only
    rw [schwartz_product_swap (schwartzWord p f) (schwartzWord q g)]
    simpa only [mul_comm] using hc g f

lemma binaryBound_word_product (m : ℕ) (hm : Module.finrank ℝ E < m)
    (ws p q : List E) (hw : ws.length+p.length+q.length ≤ m) :
    BinaryCoreBound (m : ℝ) 0 (fun f g => schwartzWord ws
      (SchwartzMap.smulLeftCLM ℂ (schwartzWord p f) (schwartzWord q g))) := by
  induction ws generalizing p q with
  | nil => exact binaryBound_product_words_zero m hm p q (by simpa using hw)
  | cons v ws ih =>
    have h₁ := ih (v::p) q (by simp only [List.length_cons] at *; omega)
    have h₂ := ih p (v::q) (by simp only [List.length_cons] at *; omega)
    convert h₁.add h₂ using 1
    funext f g
    change ∂_{v} (schwartzWord ws (SchwartzMap.smulLeftCLM ℂ (schwartzWord p f) (schwartzWord q g))) = _
    rw [← GlobalElliptic.word_deriv_comm, schwartz_deriv_product, map_add]
    rfl

 
theorem schwartz_sobolev_product_bound (m : ℕ) (hm : Module.finrank ℝ E < m) :
    BinaryCoreBound (m : ℝ) (m : ℝ) (fun f g : 𝓢(E, ℂ) => SchwartzMap.smulLeftCLM ℂ f g) := by
  apply binaryBound_of_words m
  intro ws hw
  exact binaryBound_word_product m hm ws [] [] (by simpa using hw)

end SobolevChart

end
end

end OAI
