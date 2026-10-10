import Mathlib
import OAI.Combinatorics.StripMass.PfaffianRecursion

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
open Polynomial
lemma clearedPf_eval (N : ℕ) (a : Fin N → ℂ) (z : ℂ)
    (hz : ∀ i, D (a i) z ≠ 0) :
    (clearedPf N a).eval z = (denominatorPoly N a).eval z * actualPf (N + 1) (Fin.snoc a z) := by
  rw [clearedPf, polyLift_eval]
  have he : (fun i : Fin (N + 1) => Polynomial.eval z ((Fin.snoc (kernelNumerator N a) (denominatorPoly N a) : Fin (N + 1) → Polynomial ℂ) i)) =
      (denominatorPoly N a).eval z • Fin.snoc (fun i => kernel (a i) z) 1 := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [kernelNumerator_eval N a z hz]
  rw [he, map_smul, incrementLinear_eval, smul_eq_mul]

lemma clearedPf_root (N : ℕ) (a : Fin N → ℂ)
    (hD : ∀ i j, i ≠ j → D (a i) (a j) ≠ 0) (i : Fin N) :
    (clearedPf N a).eval (a i) = 0 := by
  by_cases hii : D (a i) (a i) = 0
  · have hH : (denominatorPoly N a).eval (a i) = 0 := by
      rw [denominatorPoly_eval]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hii
    have hK : ∀ j, (kernelNumerator N a j).eval (a i) = 0 := by
      intro j
      by_cases hji : j = i
      · subst j
        simp [kernelNumerator, pairNumerator]
      · have hj : (deletedDenominator N a j).eval (a i) = 0 := by
          rw [deletedDenominator, eval_prod]
          apply Finset.prod_eq_zero (i := i)
          · simp [Ne.symm hji]
          · simpa using hii
        simp [kernelNumerator, hj]
    rw [clearedPf, polyLift_eval]
    convert (incrementLinear N a).map_zero using 1
    congr 1
    ext j
    refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [hH, hK]
  · have hz : ∀ j, D (a j) (a i) ≠ 0 := by
      intro j
      by_cases hji : j = i
      · simpa [hji] using hii
      · exact hD j i hji
    rw [clearedPf_eval N a (a i) hz]
    have hzero := actualPf_duplicate (Fin.snoc a (a i)) i.castSucc (Fin.last N)
      (by simp) (by simp)
    rw [hzero, mul_zero]

def nodalPoly (N : ℕ) (a : Fin N → ℂ) : Polynomial ℂ := ∏ i, (X - C (a i))

lemma nodalPoly_monic (N : ℕ) (a : Fin N → ℂ) : (nodalPoly N a).Monic :=
  monic_prod_X_sub_C a Finset.univ

lemma nodalPoly_degree (N : ℕ) (a : Fin N → ℂ) : (nodalPoly N a).natDegree = N := by
  rw [nodalPoly, natDegree_prod _ _ (fun i _ => (monic_X_sub_C (a i)).ne_zero)]
  simp

lemma nodalPoly_dvd (N : ℕ) (a : Fin N → ℂ) (ha : Function.Injective a)
    (hD : ∀ i j, i ≠ j → D (a i) (a j) ≠ 0) : nodalPoly N a ∣ clearedPf N a := by
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact pairwise_coprime_X_sub_C ha hij
  · intro i hi
    exact dvd_iff_isRoot.mpr (clearedPf_root N a hD i)

lemma normalized_cleared_monic (N : ℕ) (a : Fin N → ℂ) (hpf : actualPf N a ≠ 0) :
    let Q := C (((-1 : ℂ) ^ N * actualPf N a)⁻¹) * clearedPf N a
    Q.Monic ∧ Q.natDegree = 2 * N := by
  dsimp only
  have hne : (-1 : ℂ) ^ N * actualPf N a ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hpf
  have hd : (C (((-1 : ℂ) ^ N * actualPf N a)⁻¹) * clearedPf N a).natDegree ≤ 2 * N :=
    (natDegree_C_mul_le _ _).trans (clearedPf_degree N a)
  have hc : (C (((-1 : ℂ) ^ N * actualPf N a)⁻¹) * clearedPf N a).coeff (2 * N) = 1 := by
    rw [coeff_C_mul, clearedPf_coeff, inv_mul_cancel₀ hne]
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one _ hd hc,
    natDegree_eq_of_le_of_coeff_ne_zero hd (by rw [hc]; exact one_ne_zero)⟩

def prefactor (N : ℕ) (a : Fin N → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.Ioi i, D (a i) (a j) / (a i - a j)

lemma p_eq (N : ℕ) (a : Fin N → ℂ) : p N a = prefactor N a * actualPf N a := rfl

lemma prod_Ioi_castSucc {n : ℕ} (f : Fin (n + 1) → ℂ) (i : Fin n) :
    (∏ j ∈ Finset.Ioi i.castSucc, f j) = (∏ j ∈ Finset.Ioi i, f j.castSucc) * f (Fin.last n) := by
  have h1 : Finset.Ioi i.castSucc = Finset.univ.filter (fun j => i.castSucc < j) := by ext; simp
  have h2 : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by ext; simp
  rw [h1, h2, Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_castSucc]
  simp

lemma prod_Ioi_last {n : ℕ} (f : Fin (n + 1) → ℂ) :
    (∏ j ∈ Finset.Ioi (Fin.last n), f j) = 1 := by
  apply Finset.prod_eq_one
  intro j hj
  have h := Finset.mem_Ioi.mp hj
  have hj := j.isLt
  change n < j.val at h
  omega

lemma prefactor_snoc (N : ℕ) (a : Fin N → ℂ) (z : ℂ) :
    prefactor (N + 1) (Fin.snoc a z) = prefactor N a * ∏ i, D (a i) z / (a i - z) := by
  unfold prefactor
  rw [Fin.prod_univ_castSucc, prod_Ioi_last, mul_one]
  simp_rw [prod_Ioi_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  exact Finset.prod_mul_distrib

lemma nodalPoly_eval (N : ℕ) (a : Fin N → ℂ) (z : ℂ) :
    (nodalPoly N a).eval z = ∏ i, (z - a i) := by
  simp only [nodalPoly, eval_prod, eval_sub, eval_X, eval_C]

lemma difference_prod (N : ℕ) (a : Fin N → ℂ) (z : ℂ) :
    (∏ i, (a i - z)) = (-1 : ℂ) ^ N * (nodalPoly N a).eval z := by
  rw [nodalPoly_eval]
  calc (∏ i, (a i - z)) = ∏ i, ((-1 : ℂ) * (z - a i)) := by
        apply Finset.prod_congr rfl
        intro i hi
        ring
    _ = (-1 : ℂ) ^ N * ∏ i, (z - a i) := by rw [Finset.prod_mul_distrib]; simp

lemma generic_arch_quotient_factor (N : ℕ) (a : Fin N → ℂ)
    (ha : Function.Injective a)
    (hD : ∀ i j, i ≠ j → D (a i) (a j) ≠ 0)
    (hp : p N a ≠ 0) :
    ∃ g : Polynomial ℂ, g.Monic ∧ g.natDegree = N ∧
      nodalPoly N a * g = C (((-1 : ℂ) ^ N * actualPf N a)⁻¹) * clearedPf N a ∧
      ∀ z : ℂ, (∀ i, z ≠ a i ∧ D (a i) z ≠ 0) →
        g.eval z = p (N + 1) (Fin.snoc a z) / p N a := by
  have hpre : prefactor N a ≠ 0 := left_ne_zero_of_mul (p_eq N a ▸ hp)
  have hpf : actualPf N a ≠ 0 := right_ne_zero_of_mul (p_eq N a ▸ hp)
  let Q := C (((-1 : ℂ) ^ N * actualPf N a)⁻¹) * clearedPf N a
  have hQ := normalized_cleared_monic N a hpf
  change Q.Monic ∧ Q.natDegree = 2 * N at hQ
  have hd : nodalPoly N a ∣ Q := dvd_mul_of_dvd_right (nodalPoly_dvd N a ha hD) _
  obtain ⟨g, hg⟩ := hd
  have hgm : g.Monic := (nodalPoly_monic N a).of_mul_monic_left (hg ▸ hQ.1)
  have hgn : g.natDegree = N := by
    have h := hQ.2
    rw [hg, (nodalPoly_monic N a).natDegree_mul hgm, nodalPoly_degree] at h
    omega
  refine ⟨g, hgm, hgn, hg.symm, ?_⟩
  intro z hz
  have hn : (nodalPoly N a).eval z ≠ 0 := by
    rw [nodalPoly_eval]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hz i).1)
  have hs : (-1 : ℂ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
  have he := congrArg (Polynomial.eval z) hg
  dsimp only [Q] at he
  rw [eval_mul, eval_C, clearedPf_eval N a z (fun i => (hz i).2), eval_mul] at he
  rw [p_eq, prefactor_snoc, p_eq, Finset.prod_div_distrib, difference_prod,
    ← denominatorPoly_eval]
  apply (eq_div_iff (mul_ne_zero hpre hpf)).mpr
  have he' : ((-1 : ℂ) ^ N * actualPf N a)⁻¹ *
      ((denominatorPoly N a).eval z * actualPf (N + 1) (Fin.snoc a z)) =
      (nodalPoly N a).eval z * g.eval z := he
  field_simp [hs, hpf] at he'
  field_simp [hn, hs]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using he'.symm

 
theorem generic_arch_quotient_monic (N : ℕ) (a : Fin N → ℂ)
    (ha : Function.Injective a)
    (hD : ∀ i j, i ≠ j → D (a i) (a j) ≠ 0)
    (hp : p N a ≠ 0) :
    ∃ g : Polynomial ℂ, g.Monic ∧ g.natDegree = N ∧
      ∀ z : ℂ, (∀ i, z ≠ a i ∧ D (a i) z ≠ 0) →
        g.eval z = p (N + 1) (Fin.snoc a z) / p N a :=
by
  obtain ⟨g, hgm, hgn, _, hg⟩ := generic_arch_quotient_factor N a ha hD hp
  exact ⟨g, hgm, hgn, hg⟩

end
noncomputable section
open Polynomial
open scoped BigOperators

def flatC : ℂ := (Real.cos (Real.pi / 8) : ℝ)
def harmonicPoly : Polynomial ℂ := X ^ 2 * (1 - X ^ 2)
def Epoly (a : ℂ) : Polynomial ℂ := X ^ 2 - C (2 * d * a) * X + C (a ^ 2 - d ^ 2)
def perturbedRootC {N : ℕ} (a : Fin N → ℂ) : Polynomial ℂ :=
  (X - C flatC) * ∏ i, ((X - C (a i)) * Epoly (a i))
def HasProjectionC (N : ℕ) (Q : Polynomial ℂ) : Prop :=
  ∃ P J E : Polynomial ℂ,
    P.natDegree ≤ N ∧ J.natDegree ≤ N ∧ E.degree < (N : WithBot ℕ) ∧
    Q = P.comp harmonicPoly + X * J.comp harmonicPoly + X ^ 2 * E.comp harmonicPoly


lemma constant_relations : d ^ 2 = (1 / 2 : ℂ) ∧ flatC * rho = (1 / 2 : ℂ) ∧
    rho * (1 + 2 * d) = 2 * flatC * d := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 := Real.sq_sqrt (by positivity)
  have ht0 : Real.sqrt (2 + Real.sqrt 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hd : Real.cos (2 * (Real.pi / 8)) = Real.sqrt 2 / 2 := by
    rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.cos_pi_div_four]
  have h1 : (Real.cos (2 * (Real.pi / 8))) ^ 2 = (1 / 2 : ℝ) := by rw [hd]; nlinarith
  have h2 : Real.cos (Real.pi / 8) * (1 / Real.sqrt (2 + Real.sqrt 2)) = (1 / 2 : ℝ) := by
    rw [Real.cos_pi_div_eight]
    field_simp
  have h3 : (1 / Real.sqrt (2 + Real.sqrt 2)) * (1 + 2 * Real.cos (2 * (Real.pi / 8))) =
      2 * Real.cos (Real.pi / 8) * Real.cos (2 * (Real.pi / 8)) := by
    rw [hd, Real.cos_pi_div_eight]
    field_simp
    nlinarith
  unfold d flatC rho
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg Complex.ofReal h1
  · simpa using congrArg Complex.ofReal h2
  · exact_mod_cast h3

def invariantFactor (a : ℂ) : Polynomial ℂ := C ((a ^ 2 - d ^ 2) ^ 2) - X

def kernelProjectP (a : ℂ) : Polynomial ℂ :=
  C (-flatC * (a ^ 2 + a * rho) * (a ^ 2 - d ^ 2)) - C (2 * d * a - rho + flatC) * X

def kernelProjectJ (a : ℂ) : Polynomial ℂ :=
  C ((a ^ 2 + a * rho) * (a ^ 2 - d ^ 2) +
    flatC * (2 * d * a * (a ^ 2 + a * rho) + rho * (a ^ 2 - d ^ 2))) + X

def kernelProjectE (a : ℂ) : Polynomial ℂ :=
  C (-2 * d * a * (a ^ 2 + a * rho) - rho * (a ^ 2 - d ^ 2) -
    flatC * (a * rho * (1 + 2 * d) + d ^ 2) + (2 * d * a - rho + flatC))

lemma paired_invariant (a : ℂ) : Dpoly a * Epoly a = (invariantFactor a).comp harmonicPoly := by
  have hd : 2 * d ^ 2 = (1 : ℂ) := by rw [constant_relations.1]; norm_num
  have hc := congrArg (Polynomial.C : ℂ → Polynomial ℂ) hd
  simp only [map_mul, map_pow, map_ofNat, map_one] at hc
  simp only [Dpoly, Epoly, invariantFactor, harmonicPoly, sub_comp, C_comp, X_comp,
    pow_comp, map_mul, map_sub, map_pow, map_ofNat]
  linear_combination -(2 * Polynomial.C a ^ 2 + 1) * X ^ 2 * hc

lemma kernel_projection_identity (a : ℂ) :
    (X - C flatC) * pairNumerator a * Epoly a =
      (kernelProjectP a).comp harmonicPoly + X * (kernelProjectJ a).comp harmonicPoly +
        X ^ 2 * (kernelProjectE a).comp harmonicPoly := by
  have hc : a * rho * (1 + 2 * d) + d ^ 2 - flatC * (2 * d * a - rho) - 1 = 0 := by
    calc a * rho * (1 + 2 * d) + d ^ 2 - flatC * (2 * d * a - rho) - 1 =
        a * (rho * (1 + 2 * d) - 2 * flatC * d) + d ^ 2 + flatC * rho - 1 := by ring
      _ = 0 := by rw [constant_relations.2.2, constant_relations.1, constant_relations.2.1]; ring
  calc (X - C flatC) * pairNumerator a * Epoly a =
      (kernelProjectP a).comp harmonicPoly + X * (kernelProjectJ a).comp harmonicPoly +
        X ^ 2 * (kernelProjectE a).comp harmonicPoly +
          C (a * rho * (1 + 2 * d) + d ^ 2 - flatC * (2 * d * a - rho) - 1) * X ^ 3 := by
        simp only [pairNumerator, Epoly, kernelProjectP, kernelProjectJ, kernelProjectE,
          harmonicPoly, sub_comp, add_comp, mul_comp, C_comp, X_comp,
          pow_comp, neg_comp, ofNat_comp, one_comp,
          map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]
        ring
    _ = _ := by rw [hc]; simp

lemma HasProjectionC.zero (N : ℕ) : HasProjectionC N 0 := by
  refine ⟨0, 0, 0, ?_, ?_, ?_, ?_⟩ <;> simp

lemma HasProjectionC.add {N : ℕ} {Q R : Polynomial ℂ}
    (hQ : HasProjectionC N Q) (hR : HasProjectionC N R) : HasProjectionC N (Q + R) := by
  obtain ⟨P, J, E, hp, hj, he, rfl⟩ := hQ
  obtain ⟨P', J', E', hp', hj', he', rfl⟩ := hR
  refine ⟨P + P', J + J', E + E', (natDegree_add_le _ _).trans (max_le hp hp'),
    (natDegree_add_le _ _).trans (max_le hj hj'),
    (degree_add_le _ _).trans_lt (max_lt he he'), ?_⟩
  simp only [add_comp]
  ring

lemma HasProjectionC.const_mul {N : ℕ} {Q : Polynomial ℂ}
    (hQ : HasProjectionC N Q) (t : ℂ) : HasProjectionC N (C t * Q) := by
  obtain ⟨P, J, E, hp, hj, he, rfl⟩ := hQ
  refine ⟨C t * P, C t * J, C t * E, (natDegree_C_mul_le _ _).trans hp,
    (natDegree_C_mul_le _ _).trans hj, ?_, ?_⟩
  · by_cases ht : t = 0
    · simp [ht]
    · rw [degree_C_mul ht]
      exact he
  · simp only [mul_comp, C_comp]
    ring

lemma HasProjectionC.mul_comp {N M : ℕ} {Q R : Polynomial ℂ}
    (hQ : HasProjectionC N Q) (hR : R.natDegree ≤ M) :
    HasProjectionC (N + M) (Q * R.comp harmonicPoly) := by
  obtain ⟨P, J, E, hp, hj, he, rfl⟩ := hQ
  refine ⟨P * R, J * R, E * R, natDegree_mul_le.trans (add_le_add hp hR),
    natDegree_mul_le.trans (add_le_add hj hR), ?_, ?_⟩
  · by_cases hE : E = 0
    · simp [hE]
    · rw [degree_eq_natDegree hE] at he
      have hE' : E.natDegree < N := by exact_mod_cast he
      exact degree_le_natDegree.trans_lt (by exact_mod_cast
        ((natDegree_mul_le : (E * R).natDegree ≤ E.natDegree + R.natDegree).trans_lt
          (Nat.add_lt_add_of_lt_of_le hE' hR)))
  · simp only [Polynomial.mul_comp]
    ring

lemma HasProjectionC.sum {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ)
    (hf : ∀ i ∈ s, HasProjectionC N (f i)) : HasProjectionC N (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasProjectionC.zero N
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma base_projected : HasProjectionC 0 (X - C flatC) := by
  refine ⟨C (-flatC), 1, 0, ?_, ?_, ?_, ?_⟩ <;> simp; ring

lemma kernel_projected (a : ℂ) : HasProjectionC 1 ((X - C flatC) * pairNumerator a * Epoly a) := by
  refine ⟨kernelProjectP a, kernelProjectJ a, kernelProjectE a, ?_, ?_, ?_, kernel_projection_identity a⟩
  · unfold kernelProjectP; compute_degree!
  · unfold kernelProjectJ; compute_degree!
  · unfold kernelProjectE; compute_degree!

lemma invariant_product_degree {ι : Type*} (s : Finset ι) (a : ι → ℂ) :
    (∏ i ∈ s, invariantFactor (a i)).natDegree ≤ s.card := by
  apply (natDegree_prod_le _ _).trans
  calc ∑ i ∈ s, (invariantFactor (a i)).natDegree ≤ ∑ _i ∈ s, 1 := by
          apply Finset.sum_le_sum
          intro i hi
          unfold invariantFactor
          compute_degree!
    _ = s.card := by simp

lemma paired_product {ι : Type*} (s : Finset ι) (a : ι → ℂ) :
    (∏ i ∈ s, Dpoly (a i)) * (∏ i ∈ s, Epoly (a i)) =
      (∏ i ∈ s, invariantFactor (a i)).comp harmonicPoly := by
  rw [← Finset.prod_mul_distrib]
  simp_rw [paired_invariant]
  exact (Polynomial.prod_comp _ _ _).symm

lemma denominator_projected (N : ℕ) (a : Fin N → ℂ) :
    HasProjectionC N ((X - C flatC) * denominatorPoly N a * ∏ i, Epoly (a i)) := by
  have h := base_projected.mul_comp (invariant_product_degree Finset.univ a)
  simpa only [zero_add, Finset.card_univ, Fintype.card_fin, ← paired_product,
    ← mul_assoc, denominatorPoly] using h

lemma numerator_projected (N : ℕ) (a : Fin N → ℂ) (i : Fin N) :
    HasProjectionC N ((X - C flatC) * kernelNumerator N a i * ∏ j, Epoly (a j)) := by
  have h := (kernel_projected (a i)).mul_comp
    (invariant_product_degree (Finset.univ.erase i) a)
  have hcard : 1 + (Finset.univ.erase i).card = N := by
    have hi := i.isLt
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  rw [hcard, ← paired_product] at h
  rw [← Finset.mul_prod_erase Finset.univ (fun j => Epoly (a j)) (Finset.mem_univ i)]
  convert h using 1
  unfold kernelNumerator deletedDenominator
  ring

lemma polyLift_projected {n M : ℕ} (L : Vec n →ₗ[ℂ] ℂ)
    (f : Fin n → Polynomial ℂ) (Q R : Polynomial ℂ)
    (hf : ∀ i, HasProjectionC M (Q * f i * R)) :
    HasProjectionC M (Q * polyLift L f * R) := by
  have h := HasProjectionC.sum Finset.univ
    (fun i => C (L (standardBasis n i)) * (Q * f i * R))
    (fun i _ => (hf i).const_mul (L (standardBasis n i)))
  convert h using 1
  simp only [polyLift, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma cleared_projected (N : ℕ) (a : Fin N → ℂ) :
    HasProjectionC N ((X - C flatC) * clearedPf N a * ∏ i, Epoly (a i)) := by
  apply polyLift_projected
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using denominator_projected N a
  · simpa only [Fin.snoc_castSucc] using numerator_projected N a j

 
theorem generic_pfaffian_projection (N : ℕ) (a : Fin N → ℂ)
    (ha : Function.Injective a)
    (hD : ∀ i j, i ≠ j → D (a i) (a j) ≠ 0)
    (hp : p N a ≠ 0) :
    ∃ g : Polynomial ℂ, g.Monic ∧ g.natDegree = N ∧
      HasProjectionC N (perturbedRootC a * g) ∧
      ∀ z : ℂ, (∀ i, z ≠ a i ∧ D (a i) z ≠ 0) →
        g.eval z = p (N + 1) (Fin.snoc a z) / p N a := by
  obtain ⟨g, hgm, hgn, hgf, hg⟩ := generic_arch_quotient_factor N a ha hD hp
  refine ⟨g, hgm, hgn, ?_, hg⟩
  have h := (cleared_projected N a).const_mul (((-1 : ℂ) ^ N * actualPf N a)⁻¹)
  convert h using 1
  unfold perturbedRootC
  rw [Finset.prod_mul_distrib]
  change (X - C flatC) * (nodalPoly N a * ∏ i, Epoly (a i)) * g = _
  calc (X - C flatC) * (nodalPoly N a * ∏ i, Epoly (a i)) * g =
      (X - C flatC) * (nodalPoly N a * g) * ∏ i, Epoly (a i) := by ring
    _ = _ := by rw [hgf]; ring

end
end StripPfaffian

namespace StripComplexification
noncomputable section
open Polynomial
open scoped BigOperators

def component (l : ℂ →ₗ[ℝ] ℝ) (p : Polynomial ℂ) : Polynomial ℝ :=
  .ofFinsupp (.ofCoeff (Finsupp.mapRange l (map_zero l) p.toFinsupp.coeff))

@[simp] lemma component_coeff (l : ℂ →ₗ[ℝ] ℝ) (p : Polynomial ℂ) (n : ℕ) :
    (component l p).coeff n = l (p.coeff n) := rfl

@[simp] lemma component_add (l : ℂ →ₗ[ℝ] ℝ) (p q : Polynomial ℂ) :
    component l (p + q) = component l p + component l q := by
  ext n
  simp

@[simp] lemma component_C (l : ℂ →ₗ[ℝ] ℝ) (c : ℂ) :
    component l (C c) = C (l c) := by
  ext n
  by_cases hn : n = 0
  · simp [hn]
  · simp [coeff_C, hn]

lemma component_real_mul (l : ℂ →ₗ[ℝ] ℝ) (q : Polynomial ℝ) (p : Polynomial ℂ) :
    component l (q.map Complex.ofRealHom * p) = q * component l p := by
  ext n
  simp only [component_coeff, coeff_mul, map_sum, coeff_map, Complex.ofRealHom_eq_coe]
  apply Finset.sum_congr rfl
  intro ij hij
  exact l.map_smul (q.coeff ij.1) (p.coeff ij.2)

end
end StripComplexification

end OAI
