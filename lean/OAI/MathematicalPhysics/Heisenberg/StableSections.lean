import OAI.MathematicalPhysics.Heisenberg.StablePolynomials

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter Metric

open scoped ComplexConjugate
namespace Heisenberg.Pin

section

def biaffine (a b c e z w : ℂ) : ℂ := a + b * z + c * w + e * z * w

def StableSection (a b c e : ℂ) : Prop :=
  ∀ z w : ℂ, 0 < z.im → 0 < w.im → biaffine a b c e z w ≠ 0

def rootCriterion (a b c e z : ℂ) : ℝ :=
  ((a + b * z) * conj (c + e * z)).im

lemma quotient_im (x y : ℂ) :
    (-(x / y)).im = -((x * conj y).im) / Complex.normSq y := by
  simp only [Complex.neg_im, Complex.div_im, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

lemma section_swap {a b c e : ℂ} (h : StableSection a b c e) :
    StableSection a c b e := by
  intro z w hz hw
  have hs := h w z hw hz
  have he : biaffine a c b e z w = biaffine a b c e w z := by
    unfold biaffine
    ring
  exact he ▸ hs

lemma rootCriterion_nonneg {a b c e : ℂ} (h : StableSection a b c e)
    {z : ℂ} (hz : 0 < z.im) : 0 ≤ rootCriterion a b c e z := by
  by_cases hc : c + e * z = 0
  · simp [rootCriterion, hc]
  · by_contra hn
    have hn' : rootCriterion a b c e z < 0 := lt_of_not_ge hn
    have hip : 0 < (-( (a + b * z) / (c + e * z))).im := by
      rw [quotient_im]
      exact div_pos (neg_pos.mpr hn') (Complex.normSq_pos.mpr hc)
    apply h z (-( (a + b * z) / (c + e * z))) hz hip
    calc
      _ = (a + b * z) - ((a + b * z) / (c + e * z)) * (c + e * z) := by
        unfold biaffine
        ring
      _ = 0 := by rw [div_mul_cancel₀ _ hc, sub_self]

lemma symmetrization_identity (a b c e z : ℂ) (u : ℝ) :
    rootCriterion a ((1 - (u : ℂ)) * b + (u : ℂ) * c)
      ((1 - (u : ℂ)) * c + (u : ℂ) * b) e z =
      (1 - u) * rootCriterion a b c e z + u * rootCriterion a c b e z +
        u * (1 - u) * Complex.normSq (b - c) * z.im := by
  simp only [rootCriterion, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
    Complex.one_im, Complex.normSq_apply]
  ring

lemma criterion_ne_zero {a b c e z w : ℂ}
    (hn : 0 < rootCriterion a b c e z) (hw : 0 < w.im) :
    biaffine a b c e z w ≠ 0 := by
  intro he
  have hc : c + e * z ≠ 0 := by
    intro hc
    simp [rootCriterion, hc] at hn
  have hw' : w = -((a + b * z) / (c + e * z)) := by
    rw [← neg_div]
    apply (eq_div_iff hc).mpr
    dsimp [biaffine] at he
    linear_combination he
  rw [hw', quotient_im] at hw
  have hneg : -rootCriterion a b c e z / Complex.normSq (c + e * z) < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos hn) (Complex.normSq_pos.mpr hc)
  exact (not_lt_of_ge hneg.le) hw

theorem partial_symmetrization {a b c e : ℂ} (h : StableSection a b c e)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    StableSection a ((1 - (u : ℂ)) * b + (u : ℂ) * c)
      ((1 - (u : ℂ)) * c + (u : ℂ) * b) e := by
  by_cases hu : u = 0
  · simpa [hu] using h
  by_cases hv : u = 1
  · simpa [hv] using section_swap h
  by_cases hbc : b = c
  · have hb : (1 - (u : ℂ)) * b + (u : ℂ) * c = b := by rw [← hbc]; ring
    have hc : (1 - (u : ℂ)) * c + (u : ℂ) * b = c := by rw [hbc]; ring
    rw [hb, hc]
    exact h
  intro z w hz hw
  apply criterion_ne_zero (hw := hw)
  rw [symmetrization_identity]
  have h₁ := rootCriterion_nonneg h hz
  have h₂ := rootCriterion_nonneg (section_swap h) hz
  have hp : 0 < u * (1 - u) * Complex.normSq (b - c) * z.im := by
    exact mul_pos (mul_pos (mul_pos (lt_of_le_of_ne hu0 (Ne.symm hu))
      (sub_pos.mpr (lt_of_le_of_ne hu1 hv)))
      (Complex.normSq_pos.mpr (sub_ne_zero.mpr hbc))) hz
  exact add_pos_of_nonneg_of_pos (add_nonneg (mul_nonneg (sub_nonneg.mpr hu1) h₁)
    (mul_nonneg hu0 h₂)) hp

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def subsetMonomial (A : Finset σ) : MvPolynomial σ ℂ := ∏ i ∈ A, MvPolynomial.X i

omit [Fintype σ] [DecidableEq σ] in
@[simp] lemma subsetMonomial_empty : subsetMonomial (∅ : Finset σ) = 1 := by
  simp [subsetMonomial]

omit [Fintype σ] in
lemma subsetMonomial_insert (i : σ) (A : Finset σ) (hi : i ∉ A) :
    subsetMonomial (insert i A) = MvPolynomial.X i * subsetMonomial A := by
  simp [subsetMonomial, hi]

omit [Fintype σ] in
lemma pderiv_subsetMonomial (i : σ) (A : Finset σ) :
    MvPolynomial.pderiv i (subsetMonomial A) =
      if i ∈ A then subsetMonomial (A.erase i) else 0 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
    rw [subsetMonomial_insert a A ha, Derivation.leibniz, ih]
    simp only [smul_eq_mul]
    by_cases hia : i = a
    · subst a
      simp [ha]
    · simp only [MvPolynomial.pderiv_X_of_ne (Ne.symm hia), mul_zero, add_zero,
        Finset.mem_insert, hia, false_or]
      by_cases hi : i ∈ A
      · rw [ite_eq_left hi, ite_eq_left hi, Finset.erase_insert_of_ne (Ne.symm hia)]
        rw [subsetMonomial_insert a (A.erase i) (fun h => ha (Finset.mem_of_mem_erase h))]
      · simp [hi]

def presence (μ : Finset σ → ℝ) (B : Finset σ) : ℝ :=
  ∑ A : Finset σ, if B ⊆ A then μ A else 0

def presencePolynomial (μ : Finset σ → ℝ) (B : Finset σ) : MvPolynomial σ ℂ :=
  ∑ A : Finset σ, if B ⊆ A then MvPolynomial.C (μ A : ℂ) * subsetMonomial (A \ B) else 0

lemma eval_presencePolynomial_one (μ : Finset σ → ℝ) (B : Finset σ) :
    MvPolynomial.eval (fun _ => 1) (presencePolynomial μ B) = (presence μ B : ℂ) := by
  simp [presencePolynomial, presence, subsetMonomial, apply_ite]

lemma pderiv_presencePolynomial (μ : Finset σ → ℝ) (B : Finset σ) (i : σ)
    (hi : i ∉ B) :
    MvPolynomial.pderiv i (presencePolynomial μ B) = presencePolynomial μ (insert i B) := by
  unfold presencePolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hB : B ⊆ A
  · by_cases hiA : i ∈ A
    · rw [ite_eq_left hB, ite_eq_left (Finset.insert_subset hiA hB), MvPolynomial.pderiv_C_mul,
        pderiv_subsetMonomial, ite_eq_left (Finset.mem_sdiff.mpr ⟨hiA, hi⟩)]
      congr 2
      ext j
      simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
      tauto
    · rw [ite_eq_left hB, ite_eq_right (fun h => hiA (h (Finset.mem_insert_self _ _))), MvPolynomial.pderiv_C_mul,
        pderiv_subsetMonomial, ite_eq_right (fun h => hiA (Finset.mem_sdiff.mp h).1), mul_zero]
  · have hB' : ¬ insert i B ⊆ A := fun h => hB (Finset.Subset.trans (Finset.subset_insert _ _) h)
    simp [hB, hB']

lemma presence_nonneg {μ : Finset σ → ℝ} (hμ : ∀ A, 0 ≤ μ A) (B : Finset σ) :
    0 ≤ presence μ B := by
  unfold presence
  exact Finset.sum_nonneg fun A _ => by split_ifs; exact hμ A; exact le_rfl

lemma presence_polynomial_ne_zero {μ : Finset σ → ℝ} {B : Finset σ}
    (hB : 0 < presence μ B) : presencePolynomial μ B ≠ 0 := by
  intro h
  have hv := eval_presencePolynomial_one μ B
  rw [h, map_zero] at hv
  exact hB.ne' (by exact_mod_cast hv.symm)

theorem stable_presencePolynomial {μ : Finset σ → ℝ}
    (hs : Stable (presencePolynomial μ ∅)) (B : Finset σ) :
    presencePolynomial μ B = 0 ∨ Stable (presencePolynomial μ B) := by
  induction B using Finset.induction_on with
  | empty => exact Or.inr hs
  | @insert i B hi ih =>
    rw [← pderiv_presencePolynomial μ B i hi]
    rcases ih with h | h
    · simp [h]
    · exact stable_pderiv h i

end

def boundarySection {σ τ : Type*} (p : MvPolynomial σ ℂ) (f : σ → Option τ)
    (a : σ → ℂ) : MvPolynomial τ ℂ :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun j => (f j).elim (MvPolynomial.C (a j)) MvPolynomial.X) p

lemma eval_boundarySection {σ τ : Type*} (p : MvPolynomial σ ℂ)
    (f : σ → Option τ) (a : σ → ℂ) (z : τ → ℂ) :
    MvPolynomial.eval z (boundarySection p f a) =
      MvPolynomial.eval (fun j => (f j).elim (a j) z) p := by
  rw [boundarySection, MvPolynomial.eval_eval₂]
  have hc : (MvPolynomial.eval z).comp MvPolynomial.C = RingHom.id ℂ := by ext; simp
  simp only [hc, MvPolynomial.eval₂_id]
  apply congrArg (fun z => MvPolynomial.eval z p)
  funext j
  cases f j <;> simp

theorem stable_boundarySection {σ τ : Type*} [Fintype τ]
    {p : MvPolynomial σ ℂ} (hp : Stable p) (f : σ → Option τ) (a : σ → ℝ)
    (hn : boundarySection p f (fun j => (a j : ℂ)) ≠ 0) :
    Stable (boundarySection p f (fun j => (a j : ℂ))) := by
  let ar : ℝ → σ → ℂ := fun r j => (a j : ℂ) + (r : ℂ) * Complex.I
  apply stable_locallyUniform_limit (φ := 𝓝[>] (0 : ℝ))
    (P := fun r => boundarySection p f (ar r)) hn
  · simp_rw [eval_boundarySection]
    apply locallyUniform_eval
    · intro j
      cases h : f j with
      | none =>
        simp only [Option.elim_none]
        have ht : Tendsto (fun r : ℝ => ar r j) (𝓝[>] 0) (𝓝 (a j : ℂ)) := by
          have hc : Continuous (fun r : ℝ => ar r j) := by fun_prop
          simpa [ar] using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
        exact (ht.tendstoUniformlyOn_const Upper).tendstoLocallyUniformlyOn
      | some k =>
        simp only [Option.elim_some]
        exact locallyUniform_const _ _ _
    · apply Continuous.continuousOn
      apply continuous_pi
      intro j
      cases h : f j <;> simp only [Option.elim_none, Option.elim_some] <;> fun_prop
  · filter_upwards [self_mem_nhdsWithin] with r hr z hz
    rw [eval_boundarySection]
    apply hp
    intro j
    cases h : f j with
    | none => simpa [h, ar] using hr
    | some k => simpa [h] using hz k

lemma stable_section_real_rayleigh {a b c e : ℝ}
    (h : StableSection (a : ℂ) (b : ℂ) (c : ℂ) (e : ℂ)) : a * e ≤ b * c := by
  have hn := rootCriterion_nonneg h (z := Complex.I) (by simp)
  have he : rootCriterion (a : ℂ) (b : ℂ) (c : ℂ) (e : ℂ) Complex.I = b * c - a * e := by
    simp [rootCriterion, Complex.mul_im, Complex.mul_re]
    ring
  rw [he] at hn
  linarith

end Heisenberg.Pin
end

end OAI
