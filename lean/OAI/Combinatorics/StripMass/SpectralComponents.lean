import Mathlib
import OAI.Combinatorics.StripMass.PolynomialDegrees
import OAI.Combinatorics.StripMass.PfaffianEvaluation

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripComplexification
noncomputable section
open Polynomial
open scoped BigOperators
lemma component_comp (l : ℂ →ₗ[ℝ] ℝ) (p : Polynomial ℂ) (q : Polynomial ℝ) :
    component l (p.comp (q.map Complex.ofRealHom)) = (component l p).comp q := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp only [add_comp, component_add, hp, hr]
  | monomial n c =>
      have hm : (monomial n c : Polynomial ℂ) = C c * X ^ n := C_mul_X_pow_eq_monomial.symm
      rw [hm, mul_comp, C_comp, pow_comp, X_comp]
      rw [mul_comm, ← Polynomial.map_pow, component_real_mul, component_C]
      have hX : (X ^ n : Polynomial ℂ) = (X ^ n : Polynomial ℝ).map Complex.ofRealHom := by simp
      rw [mul_comm (C c), hX, component_real_mul, component_C]
      simp only [mul_comp, pow_comp, X_comp, C_comp]

lemma component_projection (l : ℂ →ₗ[ℝ] ℝ) (P J E : Polynomial ℂ) (h : Polynomial ℝ) :
    component l (P.comp (h.map Complex.ofRealHom) + X * J.comp (h.map Complex.ofRealHom) +
      X ^ 2 * E.comp (h.map Complex.ofRealHom)) =
    (component l P).comp h + X * (component l J).comp h +
      X ^ 2 * (component l E).comp h := by
  rw [component_add, component_add, component_comp]
  have hx : (X : Polynomial ℂ) = (X : Polynomial ℝ).map Complex.ofRealHom := by simp
  have hx2 : (X ^ 2 : Polynomial ℂ) = (X ^ 2 : Polynomial ℝ).map Complex.ofRealHom := by simp
  rw [hx2, component_real_mul, component_comp, hx, component_real_mul, component_comp]

lemma component_degree_le (l : ℂ →ₗ[ℝ] ℝ) (p : Polynomial ℂ) :
    (component l p).degree ≤ p.degree := by
  apply (degree_le_iff_coeff_zero _ _).2
  intro n hn
  simp [coeff_eq_zero_of_degree_lt hn]

lemma component_natDegree_le (l : ℂ →ₗ[ℝ] ℝ) (p : Polynomial ℂ) :
    (component l p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.2
  intro n hn
  simp [coeff_eq_zero_of_natDegree_lt hn]

lemma component_zero_iff (p : Polynomial ℂ)
    (hr : component Complex.reLm p = 0) (hi : component Complex.imLm p = 0) : p = 0 := by
  ext n
  apply Complex.ext
  · simpa using congrArg (fun q : Polynomial ℝ => q.coeff n) hr
  · simpa using congrArg (fun q : Polynomial ℝ => q.coeff n) hi

end
end StripComplexification

namespace StripPfaffian
noncomputable section
open Polynomial Set MeasureTheory Filter Matrix StripComplexification
open scoped Topology BigOperators

lemma map_harmonic : CriticalStrip.harmonicCoordinate.map Complex.ofRealHom = harmonicPoly := by
  simp [CriticalStrip.harmonicCoordinate, harmonicPoly]

lemma map_perturbedRoot {N : ℕ} (a : Fin N → ℝ) :
    (CriticalStrip.perturbedRoot a).map Complex.ofRealHom =
      perturbedRootC (fun i => (a i : ℂ)) := by
  simp [CriticalStrip.perturbedRoot, perturbedRootC, Epoly, Polynomial.map_prod,
    CriticalStrip.C, CriticalStrip.d, CriticalStrip.lambda, flatC, d]

def rootPolynomialC (N : ℕ) : Polynomial ℂ :=
  (CriticalStrip.rootPolynomial N).map Complex.ofRealHom

def homogeneousQC (N : ℕ) (g : Polynomial ℂ) : Polynomial ℂ := rootPolynomialC N * g

def PerturbedMonicProblemC {N : ℕ} (a : Fin N → ℂ) (g : Polynomial ℂ) : Prop :=
  g.Monic ∧ g.natDegree = N ∧ HasProjectionC N (perturbedRootC a * g)

def MonicProblemC (N : ℕ) (g : Polynomial ℂ) : Prop :=
  g.Monic ∧ g.natDegree = N ∧ HasProjectionC N (homogeneousQC N g)

lemma perturbedRoot_homogeneous (N : ℕ) : perturbedRootC (fun _ : Fin N => flatC) = rootPolynomialC N := by
  change perturbedRootC (fun _ : Fin N => (CriticalStrip.C : ℂ)) = _
  rw [← map_perturbedRoot, CriticalStrip.perturbedRoot_homogeneous]
  rfl

lemma homogeneous_projection_zero_complex (N : ℕ) (hN : 1 ≤ N) (g P J E : Polynomial ℂ)
    (hg : g.degree < (N : WithBot ℕ))
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.degree < (N : WithBot ℕ))
    (hQ : homogeneousQC N g = P.comp harmonicPoly + X * J.comp harmonicPoly +
      X ^ 2 * E.comp harmonicPoly) :
    P = 0 ∧ J = 0 ∧ E = 0 ∧ g = 0 := by
  have hl (l : ℂ →ₗ[ℝ] ℝ) : component l P = 0 ∧ component l J = 0 ∧
      component l E = 0 ∧ component l g = 0 := by
    apply CriticalStrip.homogeneous_projection_zero N hN
      (component l g) (component l P) (component l J) (component l E)
      ((component_degree_le l g).trans_lt hg)
      ((component_natDegree_le l P).trans hP)
      ((component_natDegree_le l J).trans hJ)
      ((component_degree_le l E).trans_lt hE)
    have he := congrArg (component l) hQ
    rw [homogeneousQC, rootPolynomialC, component_real_mul, ← map_harmonic,
      component_projection] at he
    exact he
  have hr := hl Complex.reLm
  have hi := hl Complex.imLm
  exact ⟨component_zero_iff P hr.1 hi.1,
    component_zero_iff J hr.2.1 hi.2.1,
    component_zero_iff E hr.2.2.1 hi.2.2.1,
    component_zero_iff g hr.2.2.2 hi.2.2.2⟩

theorem harmonic_natDegree : harmonicPoly.natDegree = 4 := by
  unfold harmonicPoly
  compute_degree <;> norm_num

theorem degree_lt_natDegree_le_pred {N : ℕ} {p : Polynomial ℂ}
    (hN : 1 ≤ N) (hp : p.degree < (N : WithBot ℕ)) : p.natDegree ≤ N - 1 := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have h : p.natDegree < N := (natDegree_lt_iff_degree_lt hp0).2 hp
  omega

 
theorem projection_natDegree_le (N : ℕ) (hN : 1 ≤ N) (P J E : Polynomial ℂ)
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.degree < (N : WithBot ℕ)) :
    (P.comp harmonicPoly + X * J.comp harmonicPoly +
      X ^ 2 * E.comp harmonicPoly).natDegree ≤ 4 * N + 1 := by
  have he := degree_lt_natDegree_le_pred hN hE
  have hp' : (P.comp harmonicPoly).natDegree ≤ 4 * N + 1 := by
    rw [natDegree_comp, harmonic_natDegree]
    omega
  have hj' : (X * J.comp harmonicPoly).natDegree ≤ 4 * N + 1 := by
    apply le_trans natDegree_mul_le
    rw [natDegree_X, natDegree_comp, harmonic_natDegree]
    omega
  have he' : (X ^ 2 * E.comp harmonicPoly).natDegree ≤ 4 * N + 1 := by
    apply le_trans natDegree_mul_le
    rw [natDegree_X_pow, natDegree_comp, harmonic_natDegree]
    omega
  exact le_trans (natDegree_add_le _ _) (max_le (le_trans (natDegree_add_le _ _) (max_le hp' hj')) he')

abbrev ProjectionSpace (N : ℕ) :=
  (degreeLT ℂ (N + 1)) × (degreeLT ℂ (N + 1)) × (degreeLT ℂ N)

def projectionMap (N : ℕ) : ProjectionSpace N →ₗ[ℂ] Polynomial ℂ where
  toFun t := t.1.val.comp harmonicPoly + X * t.2.1.val.comp harmonicPoly +
    X ^ 2 * t.2.2.val.comp harmonicPoly
  map_add' t u := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_comp]
    ring
  map_smul' a t := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_comp,
      smul_add, mul_smul_comm, RingHom.id_apply]

theorem natDegree_le_of_mem_degreeLT {N : ℕ} {p : Polynomial ℂ}
    (hp : p ∈ degreeLT ℂ (N + 1)) : p.natDegree ≤ N := by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact Nat.lt_succ_iff.1 ((natDegree_lt_iff_degree_lt hp0).2 (mem_degreeLT.1 hp))

theorem Epoly_natDegree_le (a : ℂ) : (Epoly a).natDegree ≤ 2 := by
  unfold Epoly
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · exact (natDegree_mul_le).trans (by simp only [natDegree_C, natDegree_X]; omega)
  · simp only [natDegree_C]; omega

theorem perturbedRootC_natDegree_le {N : ℕ} (a : Fin N → ℂ) :
    (perturbedRootC a).natDegree ≤ 3*N+1 := by
  have hp (i : Fin N) : ((X - C (a i)) * Epoly (a i)).natDegree ≤ 3 := by
    exact (natDegree_mul_le).trans (by
      rw [natDegree_X_sub_C]
      have := Epoly_natDegree_le (a i)
      omega)
  have hh : (∏ i : Fin N, (X - C (a i)) * Epoly (a i)).natDegree ≤ N*3 := by
    apply (natDegree_prod_le (s := Finset.univ) (f := fun i : Fin N =>
      (X - C (a i)) * Epoly (a i))).trans
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_id] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
  rw [perturbedRootC]
  exact (natDegree_mul_le).trans (by rw [natDegree_X_sub_C]; omega)

abbrev SystemSpace (N : ℕ) := ProjectionSpace N × degreeLT ℂ N
abbrev SystemIndex (N : ℕ) := (Fin (N+1) ⊕ (Fin (N+1) ⊕ Fin N)) ⊕ Fin N
def systemBasis (N : ℕ) : Module.Basis (SystemIndex N) ℂ (SystemSpace N) :=
  ((degreeLT.basis ℂ (N+1)).prod ((degreeLT.basis ℂ (N+1)).prod (degreeLT.basis ℂ N))).prod
    (degreeLT.basis ℂ N)
def systemIndexEquiv (N : ℕ) : SystemIndex N ≃ Fin (4*N+2) :=
  Fintype.equivFinOfCardEq (by simp [SystemIndex]; omega)
def targetBasis (N : ℕ) : Module.Basis (SystemIndex N) ℂ (degreeLT ℂ (4*N+2)) :=
  (degreeLT.basis ℂ (4*N+2)).reindex (systemIndexEquiv N).symm

def perturbedSystem {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℂ) :
    SystemSpace N →ₗ[ℂ] degreeLT ℂ (4*N+2) where
  toFun t := ⟨projectionMap N t.1 - perturbedRootC a*t.2.val, mem_degreeLT.2 (by
    apply (degree_le_natDegree).trans_lt
    apply WithBot.coe_lt_coe.2
    simp only [Nat.cast_id]
    apply lt_of_le_of_lt (natDegree_sub_le _ _)
    apply max_lt
    · have hh := projection_natDegree_le N hN t.1.1.val t.1.2.1.val t.1.2.2.val
        (natDegree_le_of_mem_degreeLT t.1.1.property) (natDegree_le_of_mem_degreeLT t.1.2.1.property)
        (mem_degreeLT.1 t.1.2.2.property)
      exact lt_of_le_of_lt hh (by omega)
    · have hg : t.2.val.natDegree < N := by
        by_cases hz : t.2.val=0
        · simp [hz]; omega
        exact (natDegree_lt_iff_degree_lt hz).2 (mem_degreeLT.1 t.2.property)
      exact lt_of_le_of_lt natDegree_mul_le (by have := perturbedRootC_natDegree_le a; omega))⟩
  map_add' t u := by
    apply Subtype.ext
    simp only [Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add]
    ring
  map_smul' r t := by
    apply Subtype.ext
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Submodule.coe_smul, smul_sub,
      mul_smul_comm, RingHom.id_apply]

theorem homogeneous_system_injective (N : ℕ) (hN : 1 ≤ N) :
    Function.Injective (perturbedSystem hN (fun _ => flatC)) := by
  apply (LinearMap.ker_eq_bot).1
  apply LinearMap.ker_eq_bot'.2
  intro t ht
  have he : homogeneousQC N t.2.val = projectionMap N t.1 := by
    have he := congrArg Subtype.val ht
    change projectionMap N t.1 - perturbedRootC (fun _ => flatC)*t.2.val=0 at he
    rw [perturbedRoot_homogeneous] at he
    exact (sub_eq_zero.mp he).symm
  have hz := homogeneous_projection_zero_complex N hN t.2.val t.1.1.val t.1.2.1.val t.1.2.2.val
    (mem_degreeLT.1 t.2.property) (natDegree_le_of_mem_degreeLT t.1.1.property)
    (natDegree_le_of_mem_degreeLT t.1.2.1.property) (mem_degreeLT.1 t.1.2.2.property) he
  exact Prod.ext (Prod.ext (Subtype.ext hz.1) (Prod.ext (Subtype.ext hz.2.1) (Subtype.ext hz.2.2.1)))
    (Subtype.ext hz.2.2.2)

def CoeffContinuous {A : Type*} [TopologicalSpace A] (p : A → Polynomial ℂ) : Prop :=
  ∀ k, Continuous (fun a => (p a).coeff k)
theorem CoeffContinuous.const {A : Type*} [TopologicalSpace A] (p : Polynomial ℂ) :
    CoeffContinuous (fun _ : A => p) := fun _ => continuous_const
theorem CoeffContinuous.C {A : Type*} [TopologicalSpace A] {f : A → ℂ} (hf : Continuous f) :
    CoeffContinuous (fun a => Polynomial.C (f a)) := by
  intro k
  simp only [coeff_C]
  split_ifs <;> fun_prop
theorem CoeffContinuous.add {A : Type*} [TopologicalSpace A] {p q : A → Polynomial ℂ}
    (hp : CoeffContinuous p) (hq : CoeffContinuous q) : CoeffContinuous (fun a => p a+q a) := by
  intro k
  simp only [coeff_add]
  exact (hp k).add (hq k)
theorem CoeffContinuous.sub {A : Type*} [TopologicalSpace A] {p q : A → Polynomial ℂ}
    (hp : CoeffContinuous p) (hq : CoeffContinuous q) : CoeffContinuous (fun a => p a-q a) := by
  intro k
  simp only [coeff_sub]
  exact (hp k).sub (hq k)
theorem CoeffContinuous.mul {A : Type*} [TopologicalSpace A] {p q : A → Polynomial ℂ}
    (hp : CoeffContinuous p) (hq : CoeffContinuous q) : CoeffContinuous (fun a => p a*q a) := by
  intro k
  simp only [coeff_mul]
  exact continuous_finsetSum _ (fun ij _ => (hp ij.1).mul (hq ij.2))
theorem CoeffContinuous.prod {A I : Type*} [TopologicalSpace A] (s : Finset I)
    {p : I → A → Polynomial ℂ} (hp : ∀ i ∈ s, CoeffContinuous (p i)) :
    CoeffContinuous (fun a => ∏ i ∈ s, p i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CoeffContinuous.const (1 : Polynomial ℂ)
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (hp i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))
theorem perturbedRootC_continuous (N : ℕ) : CoeffContinuous (@perturbedRootC N) := by
  apply (CoeffContinuous.const (X-Polynomial.C flatC)).mul
  apply CoeffContinuous.prod
  intro i _
  apply ((CoeffContinuous.const X).sub (CoeffContinuous.C (continuous_apply i))).mul
  apply CoeffContinuous.add
  · exact (CoeffContinuous.const (X^2)).sub ((CoeffContinuous.C (by fun_prop)).mul (CoeffContinuous.const X))
  · exact CoeffContinuous.C (by fun_prop)

def systemMatrix {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℂ) : Matrix (SystemIndex N) (SystemIndex N) ℂ :=
  LinearMap.toMatrix (systemBasis N) (targetBasis N) (perturbedSystem hN a)
theorem target_repr (N : ℕ) (p : degreeLT ℂ (4*N+2)) (i : SystemIndex N) :
    (targetBasis N).repr p i = p.val.coeff (systemIndexEquiv N i) := by
  simp only [targetBasis, Module.Basis.repr_reindex_apply, Equiv.symm_symm, degreeLT.basis_repr]
theorem systemMatrix_continuous {N : ℕ} (hN : 1 ≤ N) : Continuous (systemMatrix hN) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [systemMatrix, LinearMap.toMatrix_apply, target_repr]
  exact ((CoeffContinuous.const (projectionMap N (systemBasis N j).1)).sub
    ((perturbedRootC_continuous N).mul (CoeffContinuous.const (systemBasis N j).2.val))) _

theorem systemMatrix_homogeneous_unit {N : ℕ} (hN : 1 ≤ N) :
    IsUnit (systemMatrix hN (fun _ => flatC)).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).1
  apply Matrix.mulVec_injective_iff_isUnit.1
  intro v w he
  let b := systemBasis N
  let bv := b.equivFun.symm v
  let bw := b.equivFun.symm w
  have hrepr (x : SystemSpace N) : systemMatrix hN (fun _ => flatC) *ᵥ b.equivFun x =
      (targetBasis N).equivFun (perturbedSystem hN (fun _ => flatC) x) :=
    LinearMap.toMatrix_mulVec_repr _ _ _ _
  have hve : b.equivFun bv = v := b.equivFun.apply_symm_apply v
  have hwe : b.equivFun bw = w := b.equivFun.apply_symm_apply w
  rw [← hve, ← hwe, hrepr, hrepr] at he
  have heq := (homogeneous_system_injective N hN) ((targetBasis N).equivFun.injective he)
  exact hve.symm.trans ((congrArg b.equivFun heq).trans hwe)

def systemRHS {N : ℕ} (a : Fin N → ℂ) : degreeLT ℂ (4*N+2) :=
  ⟨perturbedRootC a * X^N, mem_degreeLT.2 (by
    apply (degree_le_natDegree).trans_lt
    apply WithBot.coe_lt_coe.2
    simp only [Nat.cast_id]
    have hh := natDegree_mul_le (p := perturbedRootC a) (q := (X : Polynomial ℂ)^N)
    have hd := perturbedRootC_natDegree_le a
    simp only [natDegree_X_pow] at hh
    omega)⟩
def rhsVector {N : ℕ} (a : Fin N → ℂ) : SystemIndex N → ℂ :=
  (targetBasis N).equivFun (systemRHS a)
theorem rhsVector_continuous (N : ℕ) : Continuous (@rhsVector N) := by
  apply continuous_pi
  intro i
  simp only [rhsVector, Module.Basis.equivFun_apply, target_repr]
  exact ((perturbedRootC_continuous N).mul (CoeffContinuous.const (X^N))) _
def solutionVector {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℂ) : SystemIndex N → ℂ :=
  (systemMatrix hN a)⁻¹ *ᵥ rhsVector a
def solutionTuple {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℂ) : SystemSpace N :=
  (systemBasis N).equivFun.symm (solutionVector hN a)
def confluentPolynomial {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℂ) : Polynomial ℂ :=
  X^N + (solutionTuple hN a).2.val

theorem solutionVector_continuousAt {N : ℕ} (hN : 1 ≤ N) :
    ContinuousAt (solutionVector hN) (fun _ => flatC) := by
  have hd := isUnit_iff_ne_zero.1 (systemMatrix_homogeneous_unit hN)
  have hi : ContinuousAt (fun a => (systemMatrix hN a)⁻¹) (fun _ => flatC) := by
    apply ContinuousAt.comp ?_ (systemMatrix_continuous hN).continuousAt
    apply continuousAt_matrix_inv
    simpa only [show (Ring.inverse : ℂ → ℂ) = Inv.inv from funext Ring.inverse_eq_inv] using continuousAt_inv₀ hd
  apply continuousAt_pi.2
  intro i
  change ContinuousAt (fun a => ∑ j, (systemMatrix hN a)⁻¹ i j * rhsVector a j) _
  apply tendsto_finsetSum
  intro j _
  exact (((continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hi))).mul
    ((continuous_apply j).continuousAt.comp (rhsVector_continuous N).continuousAt)

theorem confluentPolynomial_continuousAt {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    ContinuousAt (fun a => (confluentPolynomial hN a).coeff k) (fun _ => flatC) := by
  simp only [confluentPolynomial, solutionTuple, Module.Basis.equivFun_symm_apply,
    Prod.snd_sum, Prod.smul_snd, Submodule.coe_sum, Submodule.coe_smul, coeff_add, finsetSum_coeff, coeff_smul, smul_eq_mul]
  apply continuousAt_const.add
  apply tendsto_finsetSum
  intro i _
  exact ((continuous_apply i).continuousAt.comp (solutionVector_continuousAt hN)).mul continuousAt_const

theorem solutionTuple_spec {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℂ)
    (ha : IsUnit (systemMatrix hN a).det) :
    perturbedSystem hN a (solutionTuple hN a) = systemRHS a := by
  apply (targetBasis N).equivFun.injective
  simp only [Module.Basis.equivFun_apply]
  rw [← LinearMap.toMatrix_mulVec_repr (systemBasis N) (targetBasis N) (perturbedSystem hN a)]
  change systemMatrix hN a *ᵥ (systemBasis N).equivFun (solutionTuple hN a) = rhsVector a
  rw [solutionTuple, LinearEquiv.apply_symm_apply]
  rw [solutionVector, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ha, Matrix.one_mulVec]

theorem confluentPolynomial_spec {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℂ)
    (ha : IsUnit (systemMatrix hN a).det) : PerturbedMonicProblemC a (confluentPolynomial hN a) := by
  let t := solutionTuple hN a
  have hlow : t.2.val.degree < (N : WithBot ℕ) := mem_degreeLT.1 t.2.property
  refine ⟨monic_X_pow_add hlow, ?_, ?_⟩
  · apply natDegree_eq_of_degree_eq_some
    simpa only [degree_X_pow, confluentPolynomial, t] using degree_add_eq_left_of_degree_lt (p := (X : Polynomial ℂ)^N) (q := t.2.val)
      (by simpa only [degree_X_pow] using hlow)
  · refine ⟨t.1.1.val, t.1.2.1.val, t.1.2.2.val,
      natDegree_le_of_mem_degreeLT t.1.1.property, natDegree_le_of_mem_degreeLT t.1.2.1.property,
      mem_degreeLT.1 t.1.2.2.property, ?_⟩
    have he := congrArg Subtype.val (solutionTuple_spec hN a ha)
    change projectionMap N t.1-perturbedRootC a*t.2.val=perturbedRootC a*X^N at he
    change perturbedRootC a*(X^N+t.2.val)=projectionMap N t.1
    linear_combination -he

theorem perturbed_unique {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℂ)
    (ha : IsUnit (systemMatrix hN a).det) (p : Polynomial ℂ) (hp : PerturbedMonicProblemC a p) :
    p = confluentPolynomial hN a := by
  obtain ⟨hpmonic, hpN, P,J,E,hP,hJ,hE,hQ⟩ := hp
  have hpdeg : p.degree = (N : WithBot ℕ) := by rw [degree_eq_natDegree hpmonic.ne_zero, hpN]
  have hlow : (p-X^N).degree < (N : WithBot ℕ) := by
    simpa only [hpdeg] using degree_sub_lt_left
      (p := p) (q := (X : Polynomial ℂ)^N) (by simpa only [degree_X_pow] using hpdeg)
      hpmonic.ne_zero (hpmonic.trans (monic_X_pow N).symm)
  let t : SystemSpace N := ((⟨P,mem_degreeLT.2 (degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hP))⟩,
    ⟨J,mem_degreeLT.2 (degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hJ))⟩,
    ⟨E,mem_degreeLT.2 hE⟩), ⟨p-X^N,mem_degreeLT.2 hlow⟩)
  have he : perturbedSystem hN a t = systemRHS a := by
    apply Subtype.ext
    change P.comp harmonicPoly+X*J.comp harmonicPoly+X^2*E.comp harmonicPoly-
      perturbedRootC a*(p-X^N)=perturbedRootC a*X^N
    linear_combination -hQ
  have hinj : Function.Injective (perturbedSystem hN a) := by
    intro x y hxy
    apply (systemBasis N).equivFun.injective
    apply (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 ha))
    change systemMatrix hN a *ᵥ (systemBasis N).repr x = systemMatrix hN a *ᵥ (systemBasis N).repr y
    rw [systemMatrix, LinearMap.toMatrix_mulVec_repr, LinearMap.toMatrix_mulVec_repr, hxy]
  have ht : t=solutionTuple hN a := hinj (he.trans (solutionTuple_spec hN a ha).symm)
  have hlast := congrArg (fun t : SystemSpace N => t.2.val) ht
  change p-X^N=(solutionTuple hN a).2.val at hlast
  rw [confluentPolynomial, ← hlast]
  ring

lemma real_monic_problem_map {N : ℕ} {g : Polynomial ℝ}
    (hg : CriticalStrip.MonicProblem N g) :
    PerturbedMonicProblemC (fun _ : Fin N => flatC) (g.map Complex.ofRealHom) := by
  obtain ⟨hgm,hgn,P,J,E,hP,hJ,hE,hQ⟩ := hg
  refine ⟨hgm.map _, ?_, P.map Complex.ofRealHom, J.map Complex.ofRealHom,
    E.map Complex.ofRealHom, natDegree_map_le.trans hP, natDegree_map_le.trans hJ,
    degree_map_le.trans_lt hE, ?_⟩
  · rw [natDegree_map_of_leadingCoeff_ne_zero _ (by rw [hgm]; simp), hgn]
  · have he := congrArg (Polynomial.map Complex.ofRealHom) hQ
    rw [CriticalStrip.homogeneousQ] at he
    rw [perturbedRoot_homogeneous, rootPolynomialC, CriticalStrip.rootPolynomial]
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, Polynomial.map_add, Polynomial.map_comp,
      map_harmonic] using he

 

end
end StripPfaffian

end OAI
