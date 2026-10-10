import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Differentials.TorusQuotientDimensionPosCotangentFinrankThree
import OAI.NumberTheory.SiegelZeros.Selection.WeightedJetIndices
import OAI.NumberTheory.SiegelZeros.Structure.EvalOneInvariantJetMonomial

namespace OAI

namespace SiegelZeros


open scoped BigOperators

namespace WeightedTorusJets.Geometry

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

theorem invariantJet_add_multiindex (c : Fin 3 → ι → R) (a b : Fin 3 → ℕ)
    (f : MvPolynomial ι R) : invariantJet c (a + b) f = invariantJet c a (invariantJet c b f) := by
  ext m
  simp only [coeff_invariantJet, Pi.add_apply, pow_add]
  ring

noncomputable def invariantJetLinearMap (c : Fin 3 → ι → R) (a : Fin 3 → ℕ) :
    Module.End R (MvPolynomial ι R) where
  toFun := invariantJet c a
  map_add' f g := by
    ext m
    simp only [coeff_invariantJet, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add]
  map_smul' r f := by
    ext m
    simp only [coeff_invariantJet, MvPolynomial.coeff_smul, smul_eq_mul, RingHom.id_apply]
    ring

theorem invariantJet_mem_span_monomials {κ : Type*} (c : Fin 3 → ι → R) (a : Fin 3 → ℕ)
    (m : κ → ι →₀ ℕ) {f : MvPolynomial ι R}
    (hf : f ∈ Submodule.span R (Set.range fun k => MvPolynomial.monomial (m k) (1 : R))) :
    invariantJet c a f ∈
      Submodule.span R (Set.range fun k => MvPolynomial.monomial (m k) (1 : R)) := by
  change invariantJetLinearMap c a f ∈ _
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, rfl⟩ := hf
    change invariantJet c a (MvPolynomial.monomial (m k) 1) ∈ _
    rw [invariantJet_monomial]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul r f _ hf => simpa only [map_smul] using Submodule.smul_mem _ r hf

theorem invariantJet_map {S : Type*} [CommSemiring S] (φ : R →+* S)
    (c : Fin 3 → ι → R) (a : Fin 3 → ℕ) (f : MvPolynomial ι R) :
    invariantJet (fun j i => φ (c j i)) a (MvPolynomial.map φ f) =
      MvPolynomial.map φ (invariantJet c a f) := by
  ext m
  simp [coeff_invariantJet, MvPolynomial.coeff_map, map_sum]

theorem eval_one_invariantJet_sum_monomials {κ : Type*} [Fintype κ]
    (c : Fin 3 → ι → R) (a : Fin 3 → ℕ) (m : κ → ι →₀ ℕ) (w : κ → R) :
    MvPolynomial.eval (fun _ => 1)
      (invariantJet c a (∑ k, MvPolynomial.monomial (m k) (w k))) =
      ∑ k,
        ((∑ i, c 0 i * (m k i : R)) ^ a 0 *
          (∑ i, c 1 i * (m k i : R)) ^ a 1 *
          (∑ i, c 2 i * (m k i : R)) ^ a 2) * w k := by
  change MvPolynomial.eval (fun _ => 1)
    (invariantJetLinearMap c a (∑ k, MvPolynomial.monomial (m k) (w k))) = _
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact eval_one_invariantJet_monomial c a (m k) (w k)

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

theorem detects_jet_rows_of_polynomial_detection
    (c : Fin 3 → ι → K) (m : κ → ι →₀ ℕ) (hm : Function.Injective m)
    (s : Finset (Fin 3 → ℕ))
    (hzero : ∀ f : MvPolynomial ι K,
      f ∈ Submodule.span K (Set.range fun k => MvPolynomial.monomial (m k) (1 : K)) →
      (∀ a ∈ s, MvPolynomial.eval (fun _ => 1) (invariantJet c a f) = 0) → f = 0) :
    ∀ w : κ → K, w ≠ 0 → ∃ a ∈ s,
      ∑ k, ((∑ i, c 0 i * (m k i : K)) ^ a 0 *
        (∑ i, c 1 i * (m k i : K)) ^ a 1 *
        (∑ i, c 2 i * (m k i : K)) ^ a 2) * w k ≠ 0 := by
  classical
  intro w hw
  by_contra! h
  have hmem : (∑ k, MvPolynomial.monomial (m k) (w k)) ∈
      Submodule.span K (Set.range fun k => MvPolynomial.monomial (m k) (1 : K)) := by
    apply Submodule.sum_mem
    intro k _
    have hmono := Submodule.smul_mem
      (Submodule.span K (Set.range fun k => MvPolynomial.monomial (m k) (1 : K)))
      (w k) (Submodule.subset_span ⟨k, rfl⟩)
    simpa only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one] using hmono
  have hF := hzero _ hmem (fun a ha => by
    rw [eval_one_invariantJet_sum_monomials]
    exact h a ha)
  have hlin : LinearIndependent K (fun k => MvPolynomial.monomial (m k) (1 : K)) :=
    (MvPolynomial.basisMonomials ι K).linearIndependent.comp m hm
  apply hw
  funext k
  apply Fintype.linearIndependent_iff.mp hlin w _ k
  simpa only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one] using hF

end WeightedTorusJets.Geometry


namespace WeightedTorusJets.Geometry

variable {K L ι κ : Type*} [Field K] [Field L] [Fintype ι] [Fintype κ]

theorem span_jet_rows_eq_top_of_polynomial_detection
    (c : Fin 3 → ι → K) (m : κ → ι →₀ ℕ) (hm : Function.Injective m)
    (s : Finset (Fin 3 → ℕ))
    (hzero : ∀ f : MvPolynomial ι K,
      f ∈ Submodule.span K (Set.range fun k => MvPolynomial.monomial (m k) (1 : K)) →
      (∀ a ∈ s, MvPolynomial.eval (fun _ => 1) (invariantJet c a f) = 0) → f = 0) :
    Submodule.span K ((fun a : Fin 3 → ℕ => fun k =>
      (∑ i, c 0 i * (m k i : K)) ^ a 0 *
        (∑ i, c 1 i * (m k i : K)) ^ a 1 *
        (∑ i, c 2 i * (m k i : K)) ^ a 2) '' (s : Set (Fin 3 → ℕ))) = ⊤ :=
  WeightedTorusJets.span_rows_eq_top_of_detects s _
    (detects_jet_rows_of_polynomial_detection c m hm s hzero)

theorem span_jet_rows_eq_top_of_polynomial_detection_over
    (φ : K →+* L) (c : Fin 3 → ι → K)
    (m : κ → ι →₀ ℕ) (hm : Function.Injective m) (s : Finset (Fin 3 → ℕ))
    (hzero : ∀ f : MvPolynomial ι L,
      f ∈ Submodule.span L (Set.range fun k => MvPolynomial.monomial (m k) (1 : L)) →
      (∀ a ∈ s, MvPolynomial.eval (fun _ => 1)
        (invariantJet (fun j i => φ (c j i)) a f) = 0) → f = 0) :
    Submodule.span K ((fun a : Fin 3 → ℕ => fun k =>
      (∑ i, c 0 i * (m k i : K)) ^ a 0 *
        (∑ i, c 1 i * (m k i : K)) ^ a 1 *
        (∑ i, c 2 i * (m k i : K)) ^ a 2) '' (s : Set (Fin 3 → ℕ))) = ⊤ := by
  apply WeightedTorusJets.span_rows_eq_top_of_detects
  apply WeightedTorusJets.detects_of_field_embedding _ _ φ
  intro w hw
  obtain ⟨a, ha, hsum⟩ := detects_jet_rows_of_polynomial_detection
    (fun j i => φ (c j i)) m hm s hzero w hw
  refine ⟨a, ha, ?_⟩
  simpa only [map_mul, map_pow, map_sum, map_natCast] using hsum

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry
theorem detects_jet_rows_of_polynomial_detection_set
    {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
    (c : Fin 3 → ι → K) (m : κ → ι →₀ ℕ) (hm : Function.Injective m)
    (s : Set (Fin 3 → ℕ))
    (hzero : ∀ f : MvPolynomial ι K,
      f ∈ Submodule.span K (Set.range fun k => MvPolynomial.monomial (m k) (1 : K)) →
      (∀ a ∈ s, MvPolynomial.eval (fun _ => 1) (invariantJet c a f) = 0) → f = 0) :
    ∀ w : κ → K, w ≠ 0 → ∃ a ∈ s,
      ∑ k, ((∑ i, c 0 i * (m k i : K)) ^ a 0 *
        (∑ i, c 1 i * (m k i : K)) ^ a 1 *
        (∑ i, c 2 i * (m k i : K)) ^ a 2) * w k ≠ 0 := by
  classical
  intro w hw
  by_contra! h
  have hmem : (∑ k, MvPolynomial.monomial (m k) (w k)) ∈
      Submodule.span K (Set.range fun k => MvPolynomial.monomial (m k) (1 : K)) := by
    apply Submodule.sum_mem
    intro k _
    have hmono := Submodule.smul_mem
      (Submodule.span K (Set.range fun k => MvPolynomial.monomial (m k) (1 : K)))
      (w k) (Submodule.subset_span ⟨k, rfl⟩)
    simpa only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one] using hmono
  have hF := hzero _ hmem (fun a ha => by
    rw [eval_one_invariantJet_sum_monomials]
    exact h a ha)
  have hlin : LinearIndependent K (fun k => MvPolynomial.monomial (m k) (1 : K)) :=
    (MvPolynomial.basisMonomials ι K).linearIndependent.comp m hm
  apply hw
  funext k
  apply Fintype.linearIndependent_iff.mp hlin w _ k
  simpa only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one] using hF

end WeightedTorusJets.Geometry

namespace WeightedTorusJets
theorem span_rows_eq_top_of_detects_set
    {K ι n : Type*} [Field K] [Fintype n]
    (s : Set ι) (R : ι → n → K)
    (hdetect : ∀ c : n → K, c ≠ 0 → ∃ a ∈ s, ∑ j, R a j * c j ≠ 0) :
    Submodule.span K (R '' s) = ⊤ := by
  classical
  apply (Submodule.map_eq_top_iff (e := dotProductEquiv K n)).mp
  rw [Submodule.map_span]
  apply Submodule.span_eq_top_of_ne_zero
  intro c hc
  obtain ⟨a, ha, hsum⟩ := hdetect c hc
  exact ⟨dotProductEquiv K n (R a),
    Set.mem_image_of_mem _ (Set.mem_image_of_mem R ha), hsum⟩

end WeightedTorusJets

namespace WeightedTorusJets.Geometry

variable {K L ι κ : Type*} [Field K] [Field L] [Fintype ι] [Fintype κ]

theorem span_jet_rows_eq_top_of_polynomial_detection_set_over
    (φ : K →+* L) (c : Fin 3 → ι → K)
    (m : κ → ι →₀ ℕ) (hm : Function.Injective m) (s : Set (Fin 3 → ℕ))
    (hzero : ∀ f : MvPolynomial ι L,
      f ∈ Submodule.span L (Set.range fun k => MvPolynomial.monomial (m k) (1 : L)) →
      (∀ a ∈ s, MvPolynomial.eval (fun _ => 1)
        (invariantJet (fun j i => φ (c j i)) a f) = 0) → f = 0) :
    Submodule.span K ((fun a : Fin 3 → ℕ => fun k =>
      (∑ i, c 0 i * (m k i : K)) ^ a 0 *
        (∑ i, c 1 i * (m k i : K)) ^ a 1 *
        (∑ i, c 2 i * (m k i : K)) ^ a 2) '' s) = ⊤ := by
  apply WeightedTorusJets.span_rows_eq_top_of_detects_set
  intro w hw
  have hfw : (fun k => φ (w k)) ≠ 0 := by
    intro h
    apply hw
    funext k
    exact φ.injective (by simpa only [Pi.zero_apply, map_zero] using congr_fun h k)
  obtain ⟨a, ha, hsum⟩ := detects_jet_rows_of_polynomial_detection_set
    (fun j i => φ (c j i)) m hm s hzero (fun k => φ (w k)) hfw
  refine ⟨a, ha, fun h => hsum ?_⟩
  simpa only [map_sum, map_mul, map_pow, map_natCast, map_zero] using congr_arg φ h

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem source_eigenvalue_row_eq_galois_row {K : Type*} [Field K]
    (u : Fin 4 → K) (σ τ : K →+* K) (n : Fin 4 → ℕ) (a : Fin 3 → ℕ) :
    (∑ i, ![u, (fun i => σ (u i)), (fun i => (σ.comp τ) (u i))] 0 i * (n i : K)) ^ a 0 *
      (∑ i, ![u, (fun i => σ (u i)), (fun i => (σ.comp τ) (u i))] 1 i * (n i : K)) ^ a 1 *
      (∑ i, ![u, (fun i => σ (u i)), (fun i => (σ.comp τ) (u i))] 2 i * (n i : K)) ^ a 2 =
    (∑ i, (n i : K) * u i) ^ a 0 *
      σ (∑ i, (n i : K) * u i) ^ a 1 *
      (σ.comp τ) (∑ i, (n i : K) * u i) ^ a 2 := by
  simp [map_sum, mul_comm]

theorem source_rectangle_span_of_polynomial_zero_test
    {K κ : Type*} [Field K] [Fintype κ]
    (φ : K →+* ℂ) (u : Fin 4 → K) (σ τ : K →+* K)
    (H N : ℕ) (n : κ → Fin 4 → ℕ) (hninj : Function.Injective n)
    (hn : ∀ j i, n j i < N)
    (hzero : ∀ F : MvPolynomial (Fin 4) ℂ, F ∈ polynomialBox ℂ N →
      (∀ a : Fin 3 → ℕ,
        (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) →
        (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) →
        (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) →
        MvPolynomial.eval (fun _ => 1)
          (invariantJet (fun j i => φ (![u, (fun i => σ (u i)),
            (fun i => (σ.comp τ) (u i))] j i)) a F) = 0) → F = 0) :
    let θ := fun j => ∑ i : Fin 4, (n j i : K) * u i
    Submodule.span K
      ((fun a : Fin 3 → ℕ => fun j => θ j ^ a 0 * σ (θ j) ^ a 1 *
        (σ.comp τ) (θ j) ^ a 2) '' {a : Fin 3 → ℕ |
          (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
          (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
          (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)}) = ⊤ := by
  let m : κ → Fin 4 →₀ ℕ := fun j => Finsupp.equivFunOnFinite.symm (n j)
  let c : Fin 3 → Fin 4 → K := ![u, (fun i => σ (u i)), (fun i => (σ.comp τ) (u i))]
  have hm : Function.Injective m := by
    intro i j h
    apply hninj
    funext k
    exact congrArg (fun d : Fin 4 →₀ ℕ => d k) h
  have hmem : Submodule.span ℂ
      (Set.range fun j => MvPolynomial.monomial (m j) (1 : ℂ)) ≤ polynomialBox ℂ N := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨fun i => (⟨n j i, hn j i⟩ : Fin N), rfl⟩
  have hs := span_jet_rows_eq_top_of_polynomial_detection_set_over φ c m hm
    {a : Fin 3 → ℕ |
      (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)}
    (fun F hF hvan => hzero F (hmem hF) (fun a h0 h1 h2 => hvan a ⟨h0, h1, h2⟩))
  simpa only [m, c, Finsupp.coe_equivFunOnFinite_symm,
    source_eigenvalue_row_eq_galois_row] using hs




theorem source_weighted_cutoff_span_of_polynomial_zero_test
    {K κ : Type*} [Field K] [Fintype κ]
    (φ : K →+* ℂ) (u : Fin 4 → K) (σ τ : K →+* K)
    (H N : ℕ) (hH : 0 < H) (n : κ → Fin 4 → ℕ) (hninj : Function.Injective n)
    (hn : ∀ j i, n j i < N)
    (hzero : ∀ F : MvPolynomial (Fin 4) ℂ, F ∈ polynomialBox ℂ N →
      (∀ a : Fin 3 → ℕ,
        (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) →
        (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) →
        (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) →
        MvPolynomial.eval (fun _ => 1)
          (invariantJet (fun j i => φ (![u, (fun i => σ (u i)),
            (fun i => (σ.comp τ) (u i))] j i)) a F) = 0) → F = 0) :
    let θ := fun j => ∑ i : Fin 4, (n j i : K) * u i
    Submodule.span K
      ((fun a : Fin 3 → ℕ => fun j => θ j ^ a 0 * σ (θ j) ^ a 1 *
        (σ.comp τ) (θ j) ^ a 2) ''
        (WeightedTorusJets.weightedJetIndices H
          ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)⌋₊ : Set (Fin 3 → ℕ))) = ⊤ := by
  exact WeightedTorusJets.span_cutoff_eq_top_of_rectangle hH _
    (source_rectangle_span_of_polynomial_zero_test φ u σ τ H N n hninj hn hzero)

end WeightedTorusJets.Geometry

namespace WeightedTorusJets

variable {K : Type*} [Field K]

def biquadraticDirections (a b : K) : Fin 3 → Fin 4 → K :=
  ![![1, a, b, a * b], ![1, -a, b, -(a * b)], ![1, -a, -b, a * b]]

def biquadraticCoefficients (a b : K) : Fin 4 → K :=
  ![1, a⁻¹, -b⁻¹, -(a * b)⁻¹]

def biquadraticForm (a b : K) : (Fin 4 → K) →ₗ[K] K :=
  dotProductBilin K K (biquadraticCoefficients a b)

theorem biquadraticForm_apply (a b : K) (v : Fin 4 → K) :
    biquadraticForm a b v = v 0 + a⁻¹ * v 1 - b⁻¹ * v 2 - (a * b)⁻¹ * v 3 := by
  simp [biquadraticForm, biquadraticCoefficients, dotProductBilin, dotProduct,
    Fin.sum_univ_succ, sub_eq_add_neg, add_assoc]

theorem biquadraticForm_ne_zero (a b : K) : biquadraticForm a b ≠ 0 := by
  intro h
  have h' := LinearMap.congr_fun h (![1, 0, 0, 0] : Fin 4 → K)
  simp [biquadraticForm_apply] at h'

theorem biquadraticForm_direction {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (i : Fin 3) : biquadraticForm a b (biquadraticDirections a b i) = 0 := by
  fin_cases i <;> simp [biquadraticForm_apply, biquadraticDirections, ha, hb, mul_assoc]

theorem biquadraticDirections_linearIndependent [CharZero K] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent K (biquadraticDirections a b) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp [Fin.sum_univ_succ, biquadraticDirections] at h0 h1 h2
  have hc0 : c 0 = 0 := by
    apply (mul_eq_zero.mp (show 2 * a * c 0 = 0 by linear_combination a * h0 + h1)).resolve_left
    exact mul_ne_zero two_ne_zero ha
  have hc2 : c 2 = 0 := by
    apply (mul_eq_zero.mp (show 2 * b * c 2 = 0 by linear_combination b * h0 - h2)).resolve_left
    exact mul_ne_zero two_ne_zero hb
  have hc1 : c 1 = 0 := by linear_combination h0 - hc0 - hc2
  fin_cases i <;> assumption

theorem finrank_ker_biquadraticForm (a b : K) :
    Module.finrank K (LinearMap.ker (biquadraticForm a b)) = 3 := by
  have hs : Function.Surjective (biquadraticForm a b) := fun y =>
    ⟨![y, 0, 0, 0], by simp [biquadraticForm_apply]⟩
  have h := (biquadraticForm a b).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs] at h
  simp only [finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  exact Nat.add_left_cancel h

theorem span_biquadraticDirections_eq_ker [CharZero K] {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Submodule.span K (Set.range (biquadraticDirections a b)) =
      LinearMap.ker (biquadraticForm a b) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact biquadraticForm_direction ha hb i
  · rw [finrank_span_eq_card (biquadraticDirections_linearIndependent ha hb),
      finrank_ker_biquadraticForm]
    rfl

theorem biquadraticCoefficients_linearIndependent [Algebra ℚ K] {a b : K}
    (h : LinearIndependent ℚ (![1, a, b, a * b] : Fin 4 → K)) :
    LinearIndependent ℚ (biquadraticCoefficients a b) := by
  have ha : a ≠ 0 := by simpa using h.ne_zero 1
  have hb : b ≠ 0 := by simpa using h.ne_zero 2
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hscaled : ∑ j, (![ -c 3, -c 2, c 1, c 0] : Fin 4 → ℚ) j •
      (![1, a, b, a * b] : Fin 4 → K) j = 0 := by
    simp [Fin.sum_univ_succ, biquadraticCoefficients, Algebra.smul_def] at hc ⊢
    field_simp at hc
    linear_combination hc
  have hz := Fintype.linearIndependent_iff.mp h _ hscaled
  fin_cases i
  · simpa using hz 3
  · simpa using hz 2
  · simpa using hz 1
  · simpa using hz 0

theorem mul_biquadraticCoefficients {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    (fun i => (a * b) * biquadraticCoefficients a b i) =
      (![a * b, b, -a, -1] : Fin 4 → K) := by
  ext i
  fin_cases i <;> simp [biquadraticCoefficients, hb] <;> field_simp

theorem exists_basis_scaled_biquadraticCoefficients [Algebra ℚ K] {a b : K}
    (e : Module.Basis (Fin 4) ℚ K) (he : ⇑e = ![1, a, b, a * b]) :
    ∃ e' : Module.Basis (Fin 4) ℚ K, ⇑e' = ![a * b, b, -a, -1] := by
  refine ⟨(e.reindex Fin.revPerm).unitsSMul ![1, 1, -1, -1], ?_⟩
  ext i
  fin_cases i <;> simp [Module.Basis.unitsSMul_apply, Module.Basis.reindex_apply, he,
    Fin.revPerm]

theorem map_biquadraticCoefficients {L : Type*} [Field L] (f : K →+* L) (a b : K) :
    f ∘ biquadraticCoefficients a b = biquadraticCoefficients (f a) (f b) := by
  ext i
  fin_cases i <;> simp [biquadraticCoefficients]

theorem map_biquadraticDirections {L : Type*} [Field L] (f : K →+* L) (a b : K)
    (i : Fin 3) :
    f ∘ biquadraticDirections a b i = biquadraticDirections (f a) (f b) i := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [biquadraticDirections]

theorem biquadraticCoefficients_linearIndependent_map [Algebra ℚ K]
    {L : Type*} [Field L] [Algebra ℚ L] (f : K →ₐ[ℚ] L) {a b : K}
    (h : LinearIndependent ℚ (![1, a, b, a * b] : Fin 4 → K)) :
    LinearIndependent ℚ (biquadraticCoefficients (f a) (f b)) := by
  have h' := (biquadraticCoefficients_linearIndependent h).map' f.toLinearMap
    (LinearMap.ker_eq_bot.mpr f.injective)
  exact (map_biquadraticCoefficients f.toRingHom a b) ▸ h'

noncomputable def biquadraticDirectionBasis [CharZero K] {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.Basis (Fin 3) K (LinearMap.ker (biquadraticForm a b)) :=
  (Module.Basis.span (biquadraticDirections_linearIndependent ha hb)).map
    (LinearEquiv.ofEq _ _ (span_biquadraticDirections_eq_ker ha hb))

theorem coe_biquadraticDirectionBasis [CharZero K] {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (i : Fin 3) :
    (biquadraticDirectionBasis ha hb i : Fin 4 → K) = biquadraticDirections a b i := by
  simp [biquadraticDirectionBasis]

end WeightedTorusJets

namespace WeightedTorusJets

 theorem source_same_witness_hyperplane {K : Type*} [Field K] [CharZero K]
    (a b : K) (φ : K →+* ℂ) (v : Module.Basis (Fin 4) ℚ K)
    (hv : ∀ i, v i = ![1, a, b, a * b] i) (σ τ : K ≃ₐ[ℚ] K)
    (hσa : σ a = -a) (hσb : σ b = b) (hτa : τ a = a) (hτb : τ b = -b) :
    LinearIndependent ℚ (biquadraticCoefficients (φ a) (φ b)) ∧
    ∃ D : Module.Basis (Fin 3) ℂ (LinearMap.ker (biquadraticForm (φ a) (φ b))),
      ∀ j i, (D j : Fin 4 → ℂ) i =
        φ ((![![1, a, b, a * b], (fun i => σ (![1, a, b, a * b] i)),
          (fun i => (σ * τ) (![1, a, b, a * b] i))] : Fin 3 → Fin 4 → K) j i) := by
  have hbase : LinearIndependent ℚ (![1, a, b, a * b] : Fin 4 → K) :=
    (funext hv) ▸ v.linearIndependent
  have ha : a ≠ 0 := by simpa using hbase.ne_zero 1
  have hb : b ≠ 0 := by simpa using hbase.ne_zero 2
  have hφa : φ a ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr ha
  have hφb : φ b ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr hb
  refine ⟨biquadraticCoefficients_linearIndependent_map φ.toRatAlgHom hbase,
    biquadraticDirectionBasis hφa hφb, ?_⟩
  intro j i
  rw [coe_biquadraticDirectionBasis]
  fin_cases j <;> fin_cases i <;>
    simp [biquadraticDirections, AlgEquiv.mul_apply, hσa, hσb, hτa, hτb]



theorem actual_biquadratic_rectangle_span
    {K κ : Type*} [Field K] [NumberField K] [Fintype κ]
    (a b : K) (v : Module.Basis (Fin 4) ℚ K)
    (hv : ∀ i, v i = ![1, a, b, a * b] i) (σ τ : K ≃ₐ[ℚ] K)
    (hσa : σ a = -a) (hσb : σ b = b) (hτa : τ a = a) (hτb : τ b = -b)
    (H N : ℕ) (hH : 0 < H) (hHN : H ≤ N)
    (n : κ → Fin 4 → ℕ) (hninj : Function.Injective n) (hn : ∀ j i, n j i < N) :
    let θ := fun j => ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i
    Submodule.span K
      ((fun α : Fin 3 → ℕ => fun j => θ j ^ α 0 * σ (θ j) ^ α 1 *
        (σ * τ) (θ j) ^ α 2) '' {α : Fin 3 → ℕ |
          (α 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
          (α 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
          (α 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)}) = ⊤ := by
  let φ : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
  obtain ⟨hc, D, hD⟩ := source_same_witness_hyperplane a b φ.toRingHom v hv σ τ
    hσa hσb hτa hτb
  have hform : biquadraticForm (φ a) (φ b) =
      dotProductEquiv ℂ (Fin 4) (biquadraticCoefficients (φ a) (φ b)) := by
    ext x
    rfl
  let D' := D.map (LinearEquiv.ofEq _ _ (congrArg LinearMap.ker hform))
  apply Geometry.source_rectangle_span_of_polynomial_zero_test φ.toRingHom
    ![1, a, b, a * b] σ.toRingHom τ.toRingHom H N n hninj hn
  intro F hF hvan
  apply Geometry.uniform_rectangular_multiplicity (Nat.succ_le_iff.mpr hH) hHN
    (biquadraticCoefficients (φ a) (φ b)) hc D' F hF
  intro α hα
  have h₀ := hα 0
  have h₁ := hα 1
  have h₂ := hα 2
  simp [Geometry.rectangleThreshold] at h₀ h₁ h₂
  have hdirs : (fun j => (D' j : Fin 4 → ℂ)) =
      (fun j i => φ (![![1, a, b, a * b],
        (fun i => σ.toRingHom (![1, a, b, a * b] i)),
        (fun i => (σ.toRingHom.comp τ.toRingHom) (![1, a, b, a * b] i))] j i)) := by
    funext j i
    simpa [D'] using hD j i
  rw [hdirs]
  exact hvan α h₀ (by simpa only [neg_div] using h₁) (by simpa only [neg_div] using h₂)

end WeightedTorusJets


end SiegelZeros

end OAI
