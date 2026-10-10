import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.ContourEnergy

namespace OAI

/-! Total crossing energy bounds and Hermitian local Hamiltonian terms. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open scoped BigOperators InnerProductSpace

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy
open Matrix
variable {L q m : ℕ}

lemma propagateConjugation_add (T I : Fin m → Operator L q) (H K : Operator L q) :
    propagateConjugation T I (H+K) = propagateConjugation T I H + propagateConjugation T I K := by
  induction m generalizing H K with
  | zero => rfl
  | succ m ih =>
    simp only [propagateConjugation, Matrix.mul_add, Matrix.add_mul, ih]

lemma propagateConjugation_zero (T I : Fin m → Operator L q) :
    propagateConjugation T I 0 = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [propagateConjugation, Matrix.mul_zero, Matrix.zero_mul, ih]

lemma propagateConjugation_sum {ι : Type*} [Fintype ι]
    (T I : Fin m → Operator L q) (H : ι → Operator L q) :
    propagateConjugation T I (∑ i, H i) = ∑ i, propagateConjugation T I (H i) := by
  let f : Operator L q →+ Operator L q :=
    { toFun := propagateConjugation T I
      map_zero' := propagateConjugation_zero T I
      map_add' := propagateConjugation_add T I }
  exact map_sum f H Finset.univ

def expectation (ψ : State L q) (H : Operator L q) : ℝ := (inner ℂ ψ (asMap H ψ)).re

lemma expectation_add (ψ : State L q) (H K : Operator L q) :
    expectation ψ (H+K) = expectation ψ H + expectation ψ K := by
  simp only [expectation, asMap, map_add, _root_.add_apply, inner_add_right, Complex.add_re]

lemma expectation_sum {ι : Type*} [Fintype ι] (ψ : State L q) (H : ι → Operator L q) :
    expectation ψ (∑ i, H i) = ∑ i, expectation ψ (H i) := by
  simp only [expectation, asMap_sum, inner_sum, Complex.re_sum]

lemma expectation_eigenvalue (ψ : State L q) (hψ : ‖ψ‖ = 1) (H : Operator L q)
    (E : ℝ) (he : asMap H ψ = (E:ℂ) • ψ) : expectation ψ H = E := by
  rw [expectation, he, inner_smul_right, inner_self_eq_norm_sq_to_K, hψ]
  norm_num

def crossingCount (A : Finset (Vertex L)) : ℕ :=
  (Finset.univ.filter (Crosses A)).card

lemma sum_crossings (X : Fin m → Finset (Vertex L)) (a : Fin m → ℝ) :
    (∑ e : Edge L, ∑ j, if Crosses (X j) e then (a j)^2 else 0) =
      ∑ j, (crossingCount (X j):ℝ) * (a j)^2 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, crossingCount]

theorem regularized_energy_bound [NeZero q]
    (X : Fin m → Finset (Vertex L)) (hX : Monotone X)
    (hsep : ∀ e : Edge L, ∀ j k, Crosses (X j) e → Crosses (X k) e → j = k)
    {b : ℝ} (hb : 0 < b) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (ha1 : ∀ j, a j ≤ 1)
    (p : CoordinateFamily q X) (Ω : State L q) (hΩ : Ω ≠ 0)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q)
    (hvs : ∀ v, SupportedOn (hv v) {v})
    (hes : ∀ e, SupportedOn (he e) (EdgeSites e)) (heH : ∀ e, (he e).IsHermitian)
    (J : ℝ) (hen : ∀ e, ‖he e‖ ≤ J) (E : ℝ)
    (hg : asMap (Hamiltonian hv he) Ω = (E:ℂ) • Ω)
    (hc : ∀ j, Commute (regularizedFilters hb.le a p j).matrix
      (reducedDensity (output (regularizedFilters hb.le a p) Ω) (X j)))
    (hclip : ∀ j, let ρ := reducedDensity (output (regularizedFilters hb.le a p) Ω) (X j)
      ρ = Unitary.conjStarAlgAut ℂ _ (p j).1
        (Matrix.diagonal fun i => (marginalDiagonal (p j).1 ρ i : ℂ)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ i, (p j).2.val i+b = max b (marginalDiagonal (p j).1 ρ i/c)) :
    let φ := output (regularizedFilters hb.le a p) Ω
    let ψ := ((‖φ‖⁻¹ : ℝ):ℂ) • φ
    |expectation ψ (Hamiltonian hv he) - E| ≤
      (q:ℝ)^2 * J * ∑ j, (crossingCount (X j):ℝ) * (a j)^2 := by
  classical
  let F := regularizedFilters hb.le a p
  let φ := output F Ω
  let ψ := ((‖φ‖⁻¹ : ℝ):ℂ) • φ
  let T := fun j => liftLocal (X j) (F j).matrix
  let I := fun j => liftLocal (X j) (F j).matrix⁻¹
  have hφ : φ ≠ 0 := regularized_output_ne_zero hb a p hΩ
  have hψ : ‖ψ‖ = 1 := norm_normalized φ hφ
  have hdet (j) : IsUnit (F j).matrix.det := regularizedCoordinateMatrix_invertible hb _ _
  have hI (j) : I j * T j = 1 := by
    dsimp only [I, T]
    rw [← liftLocal_mul, Matrix.nonsing_inv_mul _ (hdet j), liftLocal_one]
  have hc' (j) : Commute (F j).matrix (reducedDensity ψ (X j)) := by
    rw [reducedDensity_real_smul]
    exact (hc j).smul_right _
  have heigen : asMap (propagateConjugation T I (Hamiltonian hv he)) ψ = (E:ℂ) • ψ :=
    transported_ground_equation T I hI (Hamiltonian hv he) Ω E hg _
  have hprop : expectation ψ (propagateConjugation T I (Hamiltonian hv he)) = E :=
    expectation_eigenvalue ψ hψ _ E heigen
  have hsite (v) : expectation ψ (propagateConjugation T I (hv v)) = expectation ψ (hv v) :=
    congrArg Complex.re (propagate_site_expectation ψ X hX F hdet hc' v (hv v) (hvs v))
  have hedge (e) : |expectation ψ (propagateConjugation T I (he e)) - expectation ψ (he e)| ≤
      (q:ℝ)^2 * ‖he e‖ * ∑ j, if Crosses (X j) e then (a j)^2 else 0 :=
    regularized_propagated_edge X hX hb a ha ha1 p φ hφ hc hclip e (hsep e) (he e) (heH e) (hes e)
  change |expectation ψ (Hamiltonian hv he) - E| ≤ _
  have hd : expectation ψ (Hamiltonian hv he) - E =
      ∑ e, (expectation ψ (he e) - expectation ψ (propagateConjugation T I (he e))) := by
    rw [← hprop]
    simp only [Hamiltonian, propagateConjugation_add, propagateConjugation_sum,
      expectation_add, expectation_sum, hsite, Finset.sum_sub_distrib]
    ring
  rw [hd]
  calc
    _ ≤ ∑ e, |expectation ψ (he e) - expectation ψ (propagateConjugation T I (he e))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, (q:ℝ)^2 * J * ∑ j, if Crosses (X j) e then (a j)^2 else 0 := by
      apply Finset.sum_le_sum
      intro e _
      rw [abs_sub_comm]
      apply (hedge e).trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hen e) (sq_nonneg _))
        (Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity))
    _ = _ := by rw [← Finset.mul_sum, sum_crossings]

end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy
open Matrix
variable {L q : ℕ}

def hermitianPart (H : Operator L q) : Operator L q := (2⁻¹:ℂ) • (H + star H)

lemma hermitianPart_hermitian (H : Operator L q) : (hermitianPart H).IsHermitian := by
  change star (hermitianPart H) = hermitianPart H
  simp only [hermitianPart, star_smul, star_add, star_star, star_inv₀, star_ofNat]
  rw [add_comm]

lemma hermitianPart_eq {H : Operator L q} (hH : H.IsHermitian) : hermitianPart H = H := by
  change star H = H at hH
  rw [hermitianPart, hH, ← two_smul ℂ H, smul_smul]
  norm_num

lemma hermitianPart_norm_le (H : Operator L q) : ‖hermitianPart H‖ ≤ ‖H‖ := by
  rw [hermitianPart, norm_smul]
  have h := norm_add_le H (star H)
  rw [norm_star] at h
  norm_num at ⊢
  linarith

lemma hermitianPart_supported (H : Operator L q) (A : Finset (Vertex L))
    (hH : SupportedOn H A) : SupportedOn (hermitianPart H) A := by
  obtain ⟨B,rfl⟩ := hH
  refine ⟨(2⁻¹:ℂ) • (B+star B), ?_⟩
  change (2⁻¹:ℂ) • (liftLocalHom A B + star (liftLocalHom A B)) =
    liftLocalHom A ((2⁻¹:ℂ) • (B+star B))
  rw [map_smul, map_add, map_star]

lemma hermitianPart_add (H K : Operator L q) : hermitianPart (H+K) = hermitianPart H + hermitianPart K := by
  simp only [hermitianPart, star_add, smul_add]
  abel

lemma hermitianPart_sum {ι : Type*} [Fintype ι] (H : ι → Operator L q) :
    hermitianPart (∑ i, H i) = ∑ i, hermitianPart (H i) := by
  simp only [hermitianPart, star_sum, ← Finset.sum_add_distrib, Finset.smul_sum]

lemma hermitianPart_hamiltonian (hv : Vertex L → Operator L q) (he : Edge L → Operator L q) :
    Hamiltonian (fun v => hermitianPart (hv v)) (fun e => hermitianPart (he e)) =
      hermitianPart (Hamiltonian hv he) := by
  simp only [Hamiltonian, hermitianPart_add, hermitianPart_sum]

lemma hermitian_terms_of_grid (hv : Vertex L → Operator L q) (he : Edge L → Operator L q)
    (J : ℝ) (h : IsGridHamiltonian J hv he) :
    IsGridHamiltonian J (fun v => hermitianPart (hv v)) (fun e => hermitianPart (he e)) ∧
    Hamiltonian (fun v => hermitianPart (hv v)) (fun e => hermitianPart (he e)) = Hamiltonian hv he ∧
    (∀ v, (hermitianPart (hv v)).IsHermitian) ∧ (∀ e, (hermitianPart (he e)).IsHermitian) := by
  have heq : Hamiltonian (fun v => hermitianPart (hv v)) (fun e => hermitianPart (he e)) = Hamiltonian hv he := by
    rw [hermitianPart_hamiltonian, hermitianPart_eq h.2.2]
  refine ⟨⟨?_,?_,by rw [heq]; exact h.2.2⟩, heq, fun v => hermitianPart_hermitian _, fun e => hermitianPart_hermitian _⟩
  · intro v
    refine ⟨hermitianPart_supported _ _ (h.1 v).1, ?_⟩
    exact (hermitianPart_norm_le _).trans (h.1 v).2
  · intro e
    refine ⟨hermitianPart_supported _ _ (h.2.1 e).1, ?_⟩
    exact (hermitianPart_norm_le _).trans (h.2.1 e).2

end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

end

end OAI
