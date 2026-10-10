import Mathlib
import OAI.Geometry.PrescribedRicci.ComplexJet
import OAI.Geometry.PrescribedRicci.HolderFiniteProduct

namespace OAI

/-! Complex Jet Product. -/

section

 
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal Classical BigOperators
namespace TameInterpolation
variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}

lemma lpNorm_complex_mul_le {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    {f g : Y → ℂ} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    lpNorm (fun x => f x*g x) r μ ≤ lpNorm f p μ*lpNorm g q μ := by
  have he := eLpNorm_smul_le_mul_eLpNorm (p:=p) (q:=q) (r:=r)
    hf.aestronglyMeasurable hg.aestronglyMeasurable
  change eLpNorm (fun x => f x*g x) r μ ≤ eLpNorm f p μ * eLpNorm g q μ at he
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) he
  simpa only [ENNReal.toReal_mul,toReal_eLpNorm] using hh

lemma lpNorm_complex_finite_prod {ι : Type*} (s : Finset ι) (f : ι → Y → ℂ) (p : ι → ℝ≥0∞)
    (hf : ∀ i ∈ s, MemLp (f i) (p i) μ) :
    lpNorm (fun x => ∏ i ∈ s, f i x) (∑ i ∈ s, (p i)⁻¹)⁻¹ μ ≤
      ∏ i ∈ s, lpNorm (f i) (p i) μ := by
  induction s using Finset.cons_induction with
  | empty =>
    by_cases hμ : μ = 0
    · simp [hμ]
    · simp [lpNorm_const, hμ]
  | cons i s hi ih =>
    have hfi : MemLp (f i) (p i) μ := hf i (Finset.mem_cons_self ..)
    have hfs : ∀ a ∈ s, MemLp (f a) (p a) μ := fun a ha => hf a (Finset.mem_cons_of_mem ha)
    have hprod := MemLp.fun_prod hfs
    let : ENNReal.HolderTriple (p i) (∑ a ∈ s, (p a)⁻¹)⁻¹ (∑ a ∈ Finset.cons i s hi, (p a)⁻¹)⁻¹ :=
      ⟨by simp only [inv_inv,Finset.sum_cons]⟩
    simp only [Finset.prod_cons]
    exact (lpNorm_complex_mul_le hfi hprod).trans (mul_le_mul_of_nonneg_left (ih hfs) lpNorm_nonneg)

lemma exponent_one_le {m j : ℕ} (hm : 0 < m) (hj : j ≤ m) : 1 ≤ exponent m j := by
  by_cases hj0 : j = 0
  · subst j; simp [exponent_zero]
  · rw [exponent_of_pos hm (Nat.pos_of_ne_zero hj0)]
    apply ENNReal.one_le_ofReal.mpr
    apply (le_div_iff₀ (by exact_mod_cast (Nat.pos_of_ne_zero hj0) : 0 < (j:ℝ))).mpr
    have hh : (j:ℝ) ≤ (m:ℝ) := by exact_mod_cast hj
    have h0 : 0 ≤ (m:ℝ) := by positivity
    linarith only [hh,h0]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]

theorem cjet_product_L2 (e : ι → E) (f : κ → E → ℂ)
    (hf : ∀ a, ContDiff ℝ ∞ (f a)) (hc : ∀ a, HasCompactSupport (f a))
    (m : ℕ) (hm : 0 < m) {ν : Type*} (s : Finset ν)
    (a : ν → κ) (j : ν → ℕ) (w : (i : ν) → Fin (j i) → ι)
    (hs : ∑ i ∈ s, j i = m) :
    lpNorm (fun x => ∏ i ∈ s, cjet e (f (a i)) (w i) x) 2 volume ≤
      2^s.card * ((2*(m:ℝ))^(∑ i ∈ s, j i*(m-j i)) *
        (familyJetNorm e (realComponents f) 0 ∞)^(s.card-1) *
          familyJetNorm e (realComponents f) m 2) := by
  have hi (i : ν) : MemLp (cjet e (f (a i)) (w i)) (exponent m (j i)) volume :=
    (cjet_smooth e (hf (a i)) (w i)).continuous.memLp_of_hasCompactSupport
      (cjet_compact e (hc (a i)) (w i))
  have hh := lpNorm_complex_finite_prod (μ:=volume) s
    (fun i => cjet e (f (a i)) (w i)) (fun i => exponent m (j i)) (fun i _ => hi i)
  rw [exponent_sum_inverse s j m hm hs] at hh
  apply hh.trans
  have hprod : (∏ i ∈ s, lpNorm (cjet e (f (a i)) (w i)) (exponent m (j i)) volume) ≤
      ∏ i ∈ s, 2*familyJetNorm e (realComponents f) (j i) (exponent m (j i)) := by
    apply Finset.prod_le_prod₀
    · intro i _; exact lpNorm_nonneg
    · intro i hmem
      have hj : j i ≤ m := by
        rw [← hs]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
      exact cjet_lpNorm_le e f hf hc _ _ (exponent_one_le hm hj)
  apply hprod.trans
  rw [Finset.prod_mul_distrib,Finset.prod_const]
  exact mul_le_mul_of_nonneg_left
    (family_jet_tame_many e (realComponents f) (realComponents_smooth f hf)
      (realComponents_compact f hc) m hm s j hs) (by positivity)
end TameInterpolation

end
end

end OAI
