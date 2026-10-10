import Mathlib
import OAI.Combinatorics.StripMass.Trigonometry

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/

namespace CriticalStrip
noncomputable section
section ProjectionAlgebra
open Polynomial Set MeasureTheory Filter
open scoped Topology BigOperators
theorem natDegree_le_of_mem_degreeLT {N : ℕ} {p : Polynomial ℝ}
    (hp : p ∈ degreeLT ℝ (N + 1)) : p.natDegree ≤ N := by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact Nat.lt_succ_iff.1 ((natDegree_lt_iff_degree_lt hp0).2 (mem_degreeLT.1 hp))

 

theorem homogeneous_exists_degree (N : ℕ) (hN : 1 ≤ N) :
    ∃ g : Polynomial ℝ, g ≠ 0 ∧ g.natDegree = N ∧ HasProjection N (homogeneousQ N g) := by
  have hdim : Module.finrank ℝ (degreeLT ℝ (3 * N + 1)) < Module.finrank ℝ (ProjectionSpace N) := by
    rw [Module.finrank_eq_card_basis (degreeLT.basis ℝ (3 * N + 1)), Fintype.card_fin,
      projectionSpace_finrank]
    omega
  obtain ⟨t, ht, htne⟩ := (Submodule.ne_bot_iff _).1
    (LinearMap.ker_ne_bot_of_finrank_lt (f := projectionRemainder N) hdim)
  have ht0 : projectionMap N t %ₘ rootPolynomial N = 0 := by
    have hv := congrArg Subtype.val (LinearMap.mem_ker.1 ht)
    exact hv
  obtain ⟨g, hg⟩ := (modByMonic_eq_zero_iff_dvd (rootPolynomial_monic N)).1 ht0
  have hP : t.1.val.natDegree ≤ N := natDegree_le_of_mem_degreeLT t.1.property
  have hJ : t.2.1.val.natDegree ≤ N := natDegree_le_of_mem_degreeLT t.2.1.property
  have hE : t.2.2.val.degree < (N : WithBot ℕ) := mem_degreeLT.1 t.2.2.property
  have hQ : homogeneousQ N g = t.1.val.comp harmonicCoordinate + X * t.2.1.val.comp harmonicCoordinate +
      X ^ 2 * t.2.2.val.comp harmonicCoordinate := hg.symm
  have hg0 : g ≠ 0 := by
    intro hzero
    have hz := homogeneous_projection_zero N hN g t.1.val t.2.1.val t.2.2.val
      (by simp [hzero]) hP hJ hE hQ
    apply htne
    apply Prod.ext
    · exact Subtype.ext hz.1
    · exact Prod.ext (Subtype.ext hz.2.1) (Subtype.ext hz.2.2.1)
  have hgn : g.natDegree ≤ N := by
    have hd := projection_natDegree_le N hN t.1.val t.2.1.val t.2.2.val hP hJ hE
    rw [← hQ] at hd
    change (rootPolynomial N * g).natDegree ≤ 4 * N + 1 at hd
    rw [natDegree_mul (rootPolynomial_monic N).ne_zero hg0, rootPolynomial_natDegree] at hd
    omega
  have hgeq : g.natDegree = N := by
    by_contra hne
    have hgl : g.degree < (N : WithBot ℕ) := (natDegree_lt_iff_degree_lt hg0).1 (by omega)
    exact hg0 (homogeneous_projection_zero N hN g t.1.val t.2.1.val t.2.2.val
      hgl hP hJ hE hQ).2.2.2
  exact ⟨g, hg0, hgeq, ⟨t.1.val, t.2.1.val, t.2.2.val, hP, hJ, hE, hQ⟩⟩



 theorem HasProjection.smul {N : ℕ} {Q : Polynomial ℝ} (hQ : HasProjection N Q) (a : ℝ) :
    HasProjection N (a • Q) := by
  obtain ⟨P, J, E, hP, hJ, hE, he⟩ := hQ
  refine ⟨a • P, a • J, a • E, ?_, ?_, (degree_smul_le a E).trans_lt hE, ?_⟩
  · exact (natDegree_smul_le a P).trans hP
  · exact (natDegree_smul_le a J).trans hJ
  · simp only [he, smul_add, smul_comp, mul_smul_comm]

 theorem HasProjection.sub {N : ℕ} {Q R : Polynomial ℝ}
    (hQ : HasProjection N Q) (hR : HasProjection N R) : HasProjection N (Q - R) := by
  obtain ⟨P, J, E, hP, hJ, hE, he⟩ := hQ
  obtain ⟨P', J', E', hP', hJ', hE', he'⟩ := hR
  refine ⟨P-P', J-J', E-E', (natDegree_sub_le _ _).trans (max_le hP hP'),
    (natDegree_sub_le _ _).trans (max_le hJ hJ'),
    (degree_sub_le _ _).trans_lt (max_lt hE hE'), ?_⟩
  simp only [he, he', sub_comp]
  ring

 

theorem homogeneous_monic_unique (N : ℕ) (hN : 1 ≤ N) :
    ∃! g : Polynomial ℝ, MonicProblem N g := by
  obtain ⟨q, hq0, hqn, hqproj⟩ := homogeneous_exists_degree N hN
  let g := q.leadingCoeff⁻¹ • q
  have hgmonic : g.Monic := by
    simpa only [g, smul_eq_C_mul, mul_comm] using monic_mul_leadingCoeff_inv hq0
  have hgdeg : g.natDegree = N := by
    change (q.leadingCoeff⁻¹ • q).natDegree = N
    rw [natDegree_smul q (inv_ne_zero (leadingCoeff_ne_zero.mpr hq0)), hqn]
  have hgproj : HasProjection N (homogeneousQ N g) := by
    convert hqproj.smul q.leadingCoeff⁻¹ using 1
    simp only [g, homogeneousQ, mul_smul_comm]
  have hg : MonicProblem N g := ⟨hgmonic, hgdeg, hgproj⟩
  refine ⟨g, hg, ?_⟩
  intro p hp
  have hd : p.degree = (N : WithBot ℕ) := by rw [degree_eq_natDegree hp.1.ne_zero, hp.2.1]
  have hdg : g.degree = (N : WithBot ℕ) := by rw [degree_eq_natDegree hgmonic.ne_zero, hgdeg]
  have hl : (p - g).degree < (N : WithBot ℕ) := by
    simpa only [hd] using degree_sub_lt_left (hd.trans hdg.symm) hp.1.ne_zero (hp.1.trans hgmonic.symm)
  have hproj : HasProjection N (homogeneousQ N (p - g)) := by
    simpa only [homogeneousQ, mul_sub] using hp.2.2.sub hgproj
  obtain ⟨P, J, E, hP, hJ, hE, hQ⟩ := hproj
  exact sub_eq_zero.mp (homogeneous_projection_zero N hN (p - g) P J E hl hP hJ hE hQ).2.2.2

end ProjectionAlgebra

open Polynomial Set MeasureTheory Filter Matrix
open scoped Topology BigOperators

 

def perturbedRoot {N : ℕ} (a : Fin N → ℝ) : Polynomial ℝ :=
  (X - Polynomial.C C) * ∏ i, ((X - Polynomial.C (a i)) *
    (X^2 - Polynomial.C (2*d*a i)*X + Polynomial.C ((a i)^2-d^2)))
def PerturbedMonicProblem {N : ℕ} (a : Fin N → ℝ) (g : Polynomial ℝ) : Prop :=
  g.Monic ∧ g.natDegree = N ∧ HasProjection N (perturbedRoot a * g)

theorem paired_homogeneous :
    X^2 - Polynomial.C (2*d*C)*X + Polynomial.C (C^2-d^2) =
      (X - Polynomial.C C)*(X-Polynomial.C c) := by
  have ha := Real.cos_add (2*lambda) lambda
  have hs := Real.cos_sub (2*lambda) lambda
  rw [show 2*lambda+lambda=3*Real.pi/8 by unfold lambda; ring] at ha
  rw [show 2*lambda-lambda=lambda by ring] at hs
  change c = d*C - Real.sin (2*lambda)*Real.sin lambda at ha
  change C = d*C + Real.sin (2*lambda)*Real.sin lambda at hs
  have hc : c+C=2*d*C := by linarith
  have hd : d = Real.sqrt 2 / 2 := by
    rw [d, lambda, show 2*(Real.pi/8)=Real.pi/4 by ring, Real.cos_pi_div_four]
  have hd2 : d^2 = 1/2 := by rw [hd]; nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hC2 : C^2=(1+d)/2 := by
    have hh := Real.cos_two_mul lambda
    change d = 2*C^2-1 at hh
    linarith
  have hprod : C^2-d^2=C*c := by
    have hh : c=(2*d-1)*C := by nlinarith [hc]
    rw [hh]
    nlinarith [hC2, hd2, mul_assoc d (C^2) 2]
  rw [← hc, hprod, map_add, map_mul]
  ring

 theorem perturbedRoot_homogeneous (N : ℕ) :
    perturbedRoot (fun _ : Fin N => C) = rootPolynomial N := by
  simp only [perturbedRoot, paired_homogeneous, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [rootPolynomial, mul_pow, mul_pow]
  rw [show 2*N+1=N+N+1 by omega, pow_add, pow_add]
  ring

theorem perturbedRoot_natDegree_le {N : ℕ} (a : Fin N → ℝ) :
    (perturbedRoot a).natDegree ≤ 3*N+1 := by
  have hp : ∀ i, ((X - Polynomial.C (a i)) *
    (X^2 - Polynomial.C (2*d*a i)*X + Polynomial.C ((a i)^2-d^2))).natDegree ≤ 3 := by
    intro i
    apply (natDegree_mul_le).trans
    have hq : (X^2 - Polynomial.C (2*d*a i)*X + Polynomial.C ((a i)^2-d^2)).natDegree ≤ 2 := by
      apply (natDegree_add_le _ _).trans
      apply max_le
      · apply (natDegree_sub_le _ _).trans
        apply max_le
        · simp
        · exact (natDegree_mul_le).trans (by simp only [natDegree_C, natDegree_X]; omega)
      · simp only [natDegree_C]; omega
    simpa only [natDegree_X_sub_C] using Nat.add_le_add_left hq 1
  apply (natDegree_mul_le).trans
  have hprod := natDegree_prod_le (s := Finset.univ) (f := fun i : Fin N =>
    (X - Polynomial.C (a i)) * (X^2 - Polynomial.C (2*d*a i)*X + Polynomial.C ((a i)^2-d^2)))
  have hh : (∏ i : Fin N, (X - Polynomial.C (a i)) *
      (X^2 - Polynomial.C (2*d*a i)*X + Polynomial.C ((a i)^2-d^2))).natDegree ≤ N*3 :=
    hprod.trans (by simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i))
  simpa [perturbedRoot, natDegree_X_sub_C, Nat.mul_comm, Nat.add_comm] using Nat.add_le_add_left hh 1

abbrev SystemSpace (N : ℕ) := ProjectionSpace N × degreeLT ℝ N
abbrev SystemIndex (N : ℕ) := (Fin (N+1) ⊕ (Fin (N+1) ⊕ Fin N)) ⊕ Fin N
def systemBasis (N : ℕ) : Module.Basis (SystemIndex N) ℝ (SystemSpace N) :=
  ((degreeLT.basis ℝ (N+1)).prod ((degreeLT.basis ℝ (N+1)).prod (degreeLT.basis ℝ N))).prod
    (degreeLT.basis ℝ N)
def systemIndexEquiv (N : ℕ) : SystemIndex N ≃ Fin (4*N+2) :=
  Fintype.equivFinOfCardEq (by simp [SystemIndex]; omega)
def targetBasis (N : ℕ) : Module.Basis (SystemIndex N) ℝ (degreeLT ℝ (4*N+2)) :=
  (degreeLT.basis ℝ (4*N+2)).reindex (systemIndexEquiv N).symm

def perturbedSystem {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) :
    SystemSpace N →ₗ[ℝ] degreeLT ℝ (4*N+2) where
  toFun t := ⟨projectionMap N t.1 - perturbedRoot a*t.2.val, mem_degreeLT.2 (by
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
      exact lt_of_le_of_lt natDegree_mul_le (by have := perturbedRoot_natDegree_le a; omega))⟩
  map_add' t u := by
    apply Subtype.ext
    simp only [Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add]
    ring
  map_smul' r t := by
    apply Subtype.ext
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Submodule.coe_smul, smul_sub,
      mul_smul_comm, RingHom.id_apply]

theorem homogeneous_system_injective (N : ℕ) (hN : 1 ≤ N) :
    Function.Injective (perturbedSystem hN (fun _ => C)) := by
  apply (LinearMap.ker_eq_bot).1
  apply LinearMap.ker_eq_bot'.2
  intro t ht
  have he : homogeneousQ N t.2.val = projectionMap N t.1 := by
    have he := congrArg Subtype.val ht
    change projectionMap N t.1 - perturbedRoot (fun _ => C)*t.2.val=0 at he
    rw [perturbedRoot_homogeneous] at he
    exact (sub_eq_zero.mp he).symm
  have hz := homogeneous_projection_zero N hN t.2.val t.1.1.val t.1.2.1.val t.1.2.2.val
    (mem_degreeLT.1 t.2.property) (natDegree_le_of_mem_degreeLT t.1.1.property)
    (natDegree_le_of_mem_degreeLT t.1.2.1.property) (mem_degreeLT.1 t.1.2.2.property) he
  exact Prod.ext (Prod.ext (Subtype.ext hz.1) (Prod.ext (Subtype.ext hz.2.1) (Subtype.ext hz.2.2.1)))
    (Subtype.ext hz.2.2.2)



def CoeffContinuous {A : Type*} [TopologicalSpace A] (p : A → Polynomial ℝ) : Prop :=
  ∀ k, Continuous (fun a => (p a).coeff k)
theorem CoeffContinuous.const {A : Type*} [TopologicalSpace A] (p : Polynomial ℝ) :
    CoeffContinuous (fun _ : A => p) := fun _ => continuous_const
theorem CoeffContinuous.C {A : Type*} [TopologicalSpace A] {f : A → ℝ} (hf : Continuous f) :
    CoeffContinuous (fun a => Polynomial.C (f a)) := by
  intro k
  simp only [coeff_C]
  split_ifs <;> fun_prop
theorem CoeffContinuous.add {A : Type*} [TopologicalSpace A] {p q : A → Polynomial ℝ}
    (hp : CoeffContinuous p) (hq : CoeffContinuous q) : CoeffContinuous (fun a => p a+q a) := by
  intro k
  simp only [coeff_add]
  exact (hp k).add (hq k)
theorem CoeffContinuous.sub {A : Type*} [TopologicalSpace A] {p q : A → Polynomial ℝ}
    (hp : CoeffContinuous p) (hq : CoeffContinuous q) : CoeffContinuous (fun a => p a-q a) := by
  intro k
  simp only [coeff_sub]
  exact (hp k).sub (hq k)
theorem CoeffContinuous.mul {A : Type*} [TopologicalSpace A] {p q : A → Polynomial ℝ}
    (hp : CoeffContinuous p) (hq : CoeffContinuous q) : CoeffContinuous (fun a => p a*q a) := by
  intro k
  simp only [coeff_mul]
  exact continuous_finsetSum _ (fun ij _ => (hp ij.1).mul (hq ij.2))
theorem CoeffContinuous.prod {A I : Type*} [TopologicalSpace A] (s : Finset I)
    {p : I → A → Polynomial ℝ} (hp : ∀ i ∈ s, CoeffContinuous (p i)) :
    CoeffContinuous (fun a => ∏ i ∈ s, p i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CoeffContinuous.const (1 : Polynomial ℝ)
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (hp i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))
theorem perturbedRoot_continuous (N : ℕ) : CoeffContinuous (@perturbedRoot N) := by
  apply (CoeffContinuous.const (X-Polynomial.C C)).mul
  apply CoeffContinuous.prod
  intro i _
  apply ((CoeffContinuous.const X).sub (CoeffContinuous.C (continuous_apply i))).mul
  apply CoeffContinuous.add
  · exact (CoeffContinuous.const (X^2)).sub ((CoeffContinuous.C (by fun_prop)).mul (CoeffContinuous.const X))
  · exact CoeffContinuous.C (by fun_prop)

def systemMatrix {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) : Matrix (SystemIndex N) (SystemIndex N) ℝ :=
  LinearMap.toMatrix (systemBasis N) (targetBasis N) (perturbedSystem hN a)
theorem target_repr (N : ℕ) (p : degreeLT ℝ (4*N+2)) (i : SystemIndex N) :
    (targetBasis N).repr p i = p.val.coeff (systemIndexEquiv N i) := by
  simp only [targetBasis, Module.Basis.repr_reindex_apply, Equiv.symm_symm, degreeLT.basis_repr]
theorem systemMatrix_continuous {N : ℕ} (hN : 1 ≤ N) : Continuous (systemMatrix hN) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [systemMatrix, LinearMap.toMatrix_apply, target_repr]
  exact ((CoeffContinuous.const (projectionMap N (systemBasis N j).1)).sub
    ((perturbedRoot_continuous N).mul (CoeffContinuous.const (systemBasis N j).2.val))) _

theorem systemMatrix_homogeneous_unit {N : ℕ} (hN : 1 ≤ N) :
    IsUnit (systemMatrix hN (fun _ => C)).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).1
  apply Matrix.mulVec_injective_iff_isUnit.1
  intro v w he
  let b := systemBasis N
  let bv := b.equivFun.symm v
  let bw := b.equivFun.symm w
  have hrepr (x : SystemSpace N) : systemMatrix hN (fun _ => C) *ᵥ b.equivFun x =
      (targetBasis N).equivFun (perturbedSystem hN (fun _ => C) x) :=
    LinearMap.toMatrix_mulVec_repr _ _ _ _
  have hve : b.equivFun bv = v := b.equivFun.apply_symm_apply v
  have hwe : b.equivFun bw = w := b.equivFun.apply_symm_apply w
  rw [← hve, ← hwe, hrepr, hrepr] at he
  have heq := (homogeneous_system_injective N hN) ((targetBasis N).equivFun.injective he)
  exact hve.symm.trans ((congrArg b.equivFun heq).trans hwe)

def systemRHS {N : ℕ} (a : Fin N → ℝ) : degreeLT ℝ (4*N+2) :=
  ⟨perturbedRoot a * X^N, mem_degreeLT.2 (by
    apply (degree_le_natDegree).trans_lt
    apply WithBot.coe_lt_coe.2
    simp only [Nat.cast_id]
    have hh := natDegree_mul_le (p := perturbedRoot a) (q := (X : Polynomial ℝ)^N)
    have hd := perturbedRoot_natDegree_le a
    simp only [natDegree_X_pow] at hh
    omega)⟩
def rhsVector {N : ℕ} (a : Fin N → ℝ) : SystemIndex N → ℝ :=
  (targetBasis N).equivFun (systemRHS a)
theorem rhsVector_continuous (N : ℕ) : Continuous (@rhsVector N) := by
  apply continuous_pi
  intro i
  simp only [rhsVector, Module.Basis.equivFun_apply, target_repr]
  exact ((perturbedRoot_continuous N).mul (CoeffContinuous.const (X^N))) _
def solutionVector {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) : SystemIndex N → ℝ :=
  (systemMatrix hN a)⁻¹ *ᵥ rhsVector a
def solutionTuple {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) : SystemSpace N :=
  (systemBasis N).equivFun.symm (solutionVector hN a)
def confluentPolynomial {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) : Polynomial ℝ :=
  X^N + (solutionTuple hN a).2.val

theorem solutionVector_continuousAt {N : ℕ} (hN : 1 ≤ N) :
    ContinuousAt (solutionVector hN) (fun _ => C) := by
  have hd := isUnit_iff_ne_zero.1 (systemMatrix_homogeneous_unit hN)
  have hi : ContinuousAt (fun a => (systemMatrix hN a)⁻¹) (fun _ => C) := by
    apply ContinuousAt.comp ?_ (systemMatrix_continuous hN).continuousAt
    apply continuousAt_matrix_inv
    simpa only [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv] using continuousAt_inv₀ hd
  apply continuousAt_pi.2
  intro i
  change ContinuousAt (fun a => ∑ j, (systemMatrix hN a)⁻¹ i j * rhsVector a j) _
  apply tendsto_finsetSum
  intro j _
  exact (((continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hi))).mul
    ((continuous_apply j).continuousAt.comp (rhsVector_continuous N).continuousAt)

theorem confluentPolynomial_continuousAt {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    ContinuousAt (fun a => (confluentPolynomial hN a).coeff k) (fun _ => C) := by
  simp only [confluentPolynomial, solutionTuple, Module.Basis.equivFun_symm_apply,
    Prod.snd_sum, Prod.smul_snd, Submodule.coe_sum, Submodule.coe_smul, coeff_add, finsetSum_coeff, coeff_smul, smul_eq_mul]
  apply continuousAt_const.add
  apply tendsto_finsetSum
  intro i _
  exact ((continuous_apply i).continuousAt.comp (solutionVector_continuousAt hN)).mul continuousAt_const

theorem solutionTuple_spec {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ)
    (ha : IsUnit (systemMatrix hN a).det) :
    perturbedSystem hN a (solutionTuple hN a) = systemRHS a := by
  apply (targetBasis N).equivFun.injective
  simp only [Module.Basis.equivFun_apply]
  rw [← LinearMap.toMatrix_mulVec_repr (systemBasis N) (targetBasis N) (perturbedSystem hN a)]
  change systemMatrix hN a *ᵥ (systemBasis N).equivFun (solutionTuple hN a) = rhsVector a
  rw [solutionTuple, LinearEquiv.apply_symm_apply]
  rw [solutionVector, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ha, Matrix.one_mulVec]

theorem confluentPolynomial_spec {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ)
    (ha : IsUnit (systemMatrix hN a).det) : PerturbedMonicProblem a (confluentPolynomial hN a) := by
  let t := solutionTuple hN a
  have hlow : t.2.val.degree < (N : WithBot ℕ) := mem_degreeLT.1 t.2.property
  refine ⟨monic_X_pow_add hlow, ?_, ?_⟩
  · apply natDegree_eq_of_degree_eq_some
    simpa only [degree_X_pow, confluentPolynomial, t] using degree_add_eq_left_of_degree_lt (p := (X : Polynomial ℝ)^N) (q := t.2.val)
      (by simpa only [degree_X_pow] using hlow)
  · refine ⟨t.1.1.val, t.1.2.1.val, t.1.2.2.val,
      natDegree_le_of_mem_degreeLT t.1.1.property, natDegree_le_of_mem_degreeLT t.1.2.1.property,
      mem_degreeLT.1 t.1.2.2.property, ?_⟩
    have he := congrArg Subtype.val (solutionTuple_spec hN a ha)
    change projectionMap N t.1-perturbedRoot a*t.2.val=perturbedRoot a*X^N at he
    change perturbedRoot a*(X^N+t.2.val)=projectionMap N t.1
    linear_combination -he

theorem perturbed_unique {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ)
    (ha : IsUnit (systemMatrix hN a).det) (p : Polynomial ℝ) (hp : PerturbedMonicProblem a p) :
    p = confluentPolynomial hN a := by
  obtain ⟨hpmonic, hpN, P,J,E,hP,hJ,hE,hQ⟩ := hp
  have hpdeg : p.degree = (N : WithBot ℕ) := by rw [degree_eq_natDegree hpmonic.ne_zero, hpN]
  have hlow : (p-X^N).degree < (N : WithBot ℕ) := by
    simpa only [hpdeg] using degree_sub_lt_left
      (p := p) (q := (X : Polynomial ℝ)^N) (by simpa only [degree_X_pow] using hpdeg)
      hpmonic.ne_zero (hpmonic.trans (monic_X_pow N).symm)
  let t : SystemSpace N := ((⟨P,mem_degreeLT.2 (degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hP))⟩,
    ⟨J,mem_degreeLT.2 (degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hJ))⟩,
    ⟨E,mem_degreeLT.2 hE⟩), ⟨p-X^N,mem_degreeLT.2 hlow⟩)
  have he : perturbedSystem hN a t = systemRHS a := by
    apply Subtype.ext
    change P.comp harmonicCoordinate+X*J.comp harmonicCoordinate+X^2*E.comp harmonicCoordinate-
      perturbedRoot a*(p-X^N)=perturbedRoot a*X^N
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

 

theorem perturbed_monic_continuity (N : ℕ) (hN : 1 ≤ N) :
    ∃ g : (Fin N → ℝ) → Polynomial ℝ,
      MonicProblem N (g (fun _ => C)) ∧
      (∀ k : ℕ, ContinuousAt (fun a => (g a).coeff k) (fun _ => C)) ∧
      ∀ᶠ a in 𝓝 (fun _ : Fin N => C),
        PerturbedMonicProblem a (g a) ∧
        ∀ p, PerturbedMonicProblem a p → p = g a := by
  refine ⟨confluentPolynomial hN, ?_, confluentPolynomial_continuousAt hN, ?_⟩
  · have hh := confluentPolynomial_spec hN (fun _ => C) (systemMatrix_homogeneous_unit hN)
    simpa only [PerturbedMonicProblem, MonicProblem, perturbedRoot_homogeneous, rootPolynomial, homogeneousQ] using hh
  · have hd := (systemMatrix_continuous hN).matrix_det.continuousAt.eventually_ne
      (isUnit_iff_ne_zero.1 (systemMatrix_homogeneous_unit hN))
    filter_upwards [hd] with a ha
    exact ⟨confluentPolynomial_spec hN a (isUnit_iff_ne_zero.2 ha),
      perturbed_unique hN a (isUnit_iff_ne_zero.2 ha)⟩

end
end CriticalStrip
 

namespace StripPfaffian
end StripPfaffian

end OAI
