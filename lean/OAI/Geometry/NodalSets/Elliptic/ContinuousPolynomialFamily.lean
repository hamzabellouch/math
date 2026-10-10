import Mathlib.Data.Finsupp.Weight
import OAI.Geometry.NodalSets.Elliptic.UniformPolynomial

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
variable {T : Type*} [TopologicalSpace T]

def ContinuousPolyFamily (P : T → CPoly) : Prop :=
  (∀ d, Continuous (fun t ↦ (P t).coeff d)) ∧
    ∃ s : Finset (Fin 4 →₀ ℕ), ∀ t, (P t).support ⊆ s

lemma polynomial_sum_of_support_subset (p : CPoly) (s : Finset (Fin 4 →₀ ℕ))
    (hs : p.support ⊆ s) : p = ∑ d ∈ s, p.coeff d • monomial d (1 : ℂ) := by
  simp only [smul_monomial, smul_eq_mul, mul_one]
  conv_lhs => rw [p.as_sum]
  exact Finset.sum_subset hs (fun d _ hd ↦ by simp [notMem_support_iff.mp hd])

lemma continuousPolyFamily_of_representation {ι : Type*} (s : Finset ι)
    (p : ι → CPoly) (c : T → ι → ℂ) (hc : ∀ i ∈ s, Continuous (fun t ↦ c t i)) :
    ContinuousPolyFamily (fun t ↦ ∑ i ∈ s, c t i • p i) := by
  classical
  constructor
  · intro d
    simp only [coeff_sum, coeff_smul, smul_eq_mul]
    exact continuous_finsetSum _ (fun i hi ↦ (hc i hi).mul continuous_const)
  · refine ⟨s.biUnion (fun i ↦ (p i).support), ?_⟩
    intro t d hd
    by_contra hn
    have hz (i : ι) (hi : i ∈ s) : (p i).coeff d = 0 := by
      apply notMem_support_iff.mp
      intro h
      exact hn (Finset.mem_biUnion.mpr ⟨i, hi, h⟩)
    have : (∑ i ∈ s, c t i • p i).coeff d = 0 := by
      simp only [coeff_sum, coeff_smul]
      exact Finset.sum_eq_zero (fun i hi ↦ by rw [hz i hi, smul_zero])
    exact (mem_support_iff.mp hd) this

lemma ContinuousPolyFamily.const (p : CPoly) : ContinuousPolyFamily (fun _ : T ↦ p) :=
  ⟨fun _ ↦ continuous_const, ⟨p.support, fun _ ↦ Finset.Subset.refl _⟩⟩

lemma ContinuousPolyFamily.add {P Q : T → CPoly}
    (hp : ContinuousPolyFamily P) (hq : ContinuousPolyFamily Q) :
    ContinuousPolyFamily (fun t ↦ P t + Q t) := by
  obtain ⟨s, hs⟩ := hp.2
  obtain ⟨r, hr⟩ := hq.2
  refine ⟨fun d ↦ by
    convert (hp.1 d).add (hq.1 d) using 1
    funext t
    simp, s ∪ r, ?_⟩
  intro t d hd
  have h := support_add hd
  rcases Finset.mem_union.mp h with h | h
  · exact Finset.mem_union_left _ (hs t h)
  · exact Finset.mem_union_right _ (hr t h)

lemma ContinuousPolyFamily.smul {P : T → CPoly} (hp : ContinuousPolyFamily P)
    {c : T → ℂ} (hc : Continuous c) : ContinuousPolyFamily (fun t ↦ c t • P t) := by
  obtain ⟨s, hs⟩ := hp.2
  refine ⟨fun d ↦ by
    convert hc.mul (hp.1 d) using 1
    funext t
    rw [coeff_smul]
    rfl, s, ?_⟩
  intro t d hd
  apply hs t
  rw [mem_support_iff] at hd ⊢
  simp only [coeff_smul, smul_eq_mul] at hd
  exact right_ne_zero_of_mul hd

lemma ContinuousPolyFamily.sum {ι : Type*} (s : Finset ι) {P : ι → T → CPoly}
    (hp : ∀ i ∈ s, ContinuousPolyFamily (P i)) :
    ContinuousPolyFamily (fun t ↦ ∑ i ∈ s, P i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (ContinuousPolyFamily.const (T := T) 0)
  | @insert i s hi ih =>
    simpa [Finset.sum_insert, hi] using (hp i (by simp)).add
      (ih (fun j hj ↦ hp j (by simp [hj])))

lemma ContinuousPolyFamily.linearMap {P : T → CPoly} (hp : ContinuousPolyFamily P)
    (L : CPoly →ₗ[ℂ] CPoly) : ContinuousPolyFamily (fun t ↦ L (P t)) := by
  obtain ⟨s, hs⟩ := hp.2
  have he : (fun t ↦ L (P t)) = fun t ↦
      ∑ d ∈ s, (P t).coeff d • L (monomial d (1 : ℂ)) := by
    funext t
    conv_lhs => rw [polynomial_sum_of_support_subset (P t) s (hs t)]
    simp
  rw [he]
  exact continuousPolyFamily_of_representation s _ _ (fun d _ ↦ hp.1 d)

lemma ContinuousPolyFamily.mul {P Q : T → CPoly}
    (hp : ContinuousPolyFamily P) (hq : ContinuousPolyFamily Q) :
    ContinuousPolyFamily (fun t ↦ P t * Q t) := by
  obtain ⟨s, hs⟩ := hp.2
  have he : (fun t ↦ P t * Q t) = fun t ↦
      ∑ d ∈ s, (P t).coeff d • (monomial d (1 : ℂ) * Q t) := by
    funext t
    conv_lhs => rw [polynomial_sum_of_support_subset (P t) s (hs t)]
    simp [Finset.sum_mul]
  rw [he]
  apply ContinuousPolyFamily.sum
  intro d _
  exact (hq.linearMap (LinearMap.mulLeft ℂ (monomial d (1 : ℂ)))).smul (hp.1 d)

lemma ContinuousPolyFamily.C {c : T → ℂ} (hc : Continuous c) :
    ContinuousPolyFamily (fun t ↦ C (c t)) := by
  simpa [Algebra.smul_def] using (ContinuousPolyFamily.const (T := T) 1).smul hc

lemma continuousPolyFamily_aeval_fixed (p : CPoly) (q : Fin 4 → T → CPoly)
    (hq : ∀ i, ContinuousPolyFamily (q i)) :
    ContinuousPolyFamily (fun t ↦ MvPolynomial.aeval (fun i ↦ q i t) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (ContinuousPolyFamily.const (T := T) (C a))
  | add p r hp hr => simpa using hp.add hr
  | mul_X p i hp => simpa using hp.mul (hq i)

lemma ContinuousPolyFamily.aeval {P : T → CPoly} (hp : ContinuousPolyFamily P)
    (q : Fin 4 → T → CPoly) (hq : ∀ i, ContinuousPolyFamily (q i)) :
    ContinuousPolyFamily (fun t ↦ MvPolynomial.aeval (fun i ↦ q i t) (P t)) := by
  obtain ⟨s, hs⟩ := hp.2
  have he : (fun t ↦ MvPolynomial.aeval (fun i ↦ q i t) (P t)) = fun t ↦
      ∑ d ∈ s, (P t).coeff d • MvPolynomial.aeval (fun i ↦ q i t) (monomial d (1 : ℂ)) := by
    funext t
    conv_lhs => rw [polynomial_sum_of_support_subset (P t) s (hs t)]
    simp only [Algebra.smul_def, map_sum, map_mul, aeval_C, algebraMap_eq]
  rw [he]
  exact ContinuousPolyFamily.sum s (fun d _ ↦
    (continuousPolyFamily_aeval_fixed _ q hq).smul (hp.1 d))

theorem ContinuousPolyFamily.uniform_derivative_bound {P : T → CPoly}
    (hp : ContinuousPolyFamily P) (s : Set T) (hs : IsCompact s) (R : ℝ) (k : ℕ) :
    ∃ C > 0, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ k (reval (P t)) x‖ ≤ C := by
  obtain ⟨r, hr⟩ := hp.2
  have he (t : T) : reval (P t) = polynomialFamily
      (fun d : r ↦ monomial d.val (1 : ℂ)) (fun t d ↦ (P t).coeff d.val) t := by
    funext x
    rw [polynomial_sum_of_support_subset (P t) r (hr t)]
    simp [polynomialFamily, reval, Algebra.smul_def]
    exact (Finset.sum_attach r (fun d ↦ (P t).coeff d *
      eval (fun i ↦ (x i : ℂ)) (monomial d (1 : ℂ)))).symm
  obtain ⟨C, hC, hb⟩ := polynomialFamily_uniform_derivative_bound
    (fun d : r ↦ monomial d.val (1 : ℂ)) (fun t d ↦ (P t).coeff d.val)
    (fun d ↦ hp.1 d.val) s hs R k
  refine ⟨C, hC, ?_⟩
  intro t ht x hx
  rw [he t]
  exact hb t ht x hx

end
end Yau.Jets

end OAI
