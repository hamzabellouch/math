import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicLattices

namespace OAI

noncomputable section
open scoped TensorProduct RestrictedProduct Topology Pointwise
open Matrix Module Filter Set
namespace PrimeDegreePackets.Adelic

def finiteMatrixAt {n : ℕ} (g : GL (Fin n) RationalFiniteAdeles) (p : Nat.Primes) :
    GL (Fin n) (Padic p.val) :=
  GeneralLinearGroup.map (RestrictedProduct.evalRingHom (fun p : Nat.Primes => Padic p.val) p) g

@[simp] lemma finiteMatrixAt_inv {n : ℕ} (g : GL (Fin n) RationalFiniteAdeles)
    (p : Nat.Primes) : finiteMatrixAt (g⁻¹) p = (finiteMatrixAt g p)⁻¹ := by
  unfold finiteMatrixAt
  exact map_inv _ _

def localIntegralRows (n : ℕ) (p : Nat.Primes) :
    Submodule (PadicInt p.val) (Fin n → Padic p.val) where
  carrier := {v | ∀ i, v i ∈ rationalLocalIntegers p}
  zero_mem' := fun _ => (rationalLocalIntegers p).zero_mem
  add_mem' hx hy i := (rationalLocalIntegers p).add_mem (hx i) (hy i)
  smul_mem' a _ hx i := (rationalLocalIntegers p).mul_mem a.property (hx i)

def localMatrixLattice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (g : GL (Fin n) RationalFiniteAdeles) (p : Nat.Primes) :
    Submodule (PadicInt p.val) (LocalAlgebra p.val K) :=
  (localIntegralRows n p).comap
    (((Matrix.vecMulLinear (finiteMatrixAt g p).val).comp
      (b.baseChange (Padic p.val)).equivFun.toLinearMap).restrictScalars (PadicInt p.val))

 
def basisFullLattice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) : FullLattice n K where
  carrier := Submodule.span ℤ (Set.range b)
  basis := b.restrictScalars ℤ
  spans := by rw [Submodule.span_span_of_tower ℤ ℚ,b.span_eq]

@[simp] lemma basisFullLattice_basis {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (i : Fin n) : ((basisFullLattice b).basis i : K) = b i :=
  b.restrictScalars_apply ℤ i

lemma completed_basisFullLattice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (p : Nat.Primes) :
    completedLattice p.val (basisFullLattice b) = localIntegralSpan p.val b := by
  rw [completedLattice_eq_span_basis]
  simp only [basisFullLattice_basis,localIntegralSpan,Basis.baseChange_apply,
    Algebra.TensorProduct.includeRight_apply]

lemma mem_localMatrixLattice_iff {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (g : GL (Fin n) RationalFiniteAdeles) (p : Nat.Primes)
    (x : LocalAlgebra p.val K) :
    x ∈ localMatrixLattice b g p ↔
      ∀ i, ((localAlgebraCoordinates p.val b x) ᵥ* (finiteMatrixAt g p).val) i ∈
        rationalLocalIntegers p := Iff.rfl

lemma finiteGlobalMatrixLattice_local_iff {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (g : GL (Fin n) RationalFiniteAdeles) (x : K) :
    x ∈ finiteGlobalMatrixLattice b g ↔ ∀ p : Nat.Primes,
      Algebra.TensorProduct.includeRight (R := ℚ) (A := Padic p.val) x ∈ localMatrixLattice b g p := by
  change finiteCoefficientRow b x ∈ finiteCompletedMatrixLattice g ↔ _
  rw [mem_finiteCompletedMatrixLattice_iff]
  have he (p : Nat.Primes) (i : Fin n) :
      (finiteCoefficientRow b x ᵥ* g.val) i p =
      (localAlgebraCoordinates p.val b (Algebra.TensorProduct.includeRight x) ᵥ*
        (finiteMatrixAt g p).val) i := by
    change ((RestrictedProduct.evalRingHom (fun p : Nat.Primes => Padic p.val) p)
      ((finiteCoefficientRow b x ᵥ* g.val) i)) = _
    rw [RingHom.map_vecMul]
    have hv : (fun j => (↑(b.repr x j) : Padic p.val)) =
        localAlgebraCoordinates p.val b (Algebra.TensorProduct.includeRight x) := by
      funext j
      change (↑(b.repr x j) : Padic p.val) = (b.baseChange (Padic p.val)).repr (1 ⊗ₜ[ℚ] x) j
      simp [Basis.baseChange_repr_tmul,Algebra.smul_def]
    change ((fun j => (↑(b.repr x j) : Padic p.val)) ᵥ* (finiteMatrixAt g p).val) i = _
    rw [hv]
  simp only [FiniteIntegralRow,he,mem_localMatrixLattice_iff]
  exact forall_comm

lemma localMatrixLattice_open {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (g : GL (Fin n) RationalFiniteAdeles) (p : Nat.Primes) :
    IsOpen (localMatrixLattice b g p : Set (LocalAlgebra p.val K)) := by
  have he : (localMatrixLattice b g p : Set (LocalAlgebra p.val K)) =
      ⋂ i, {x | ((localAlgebraCoordinates p.val b x) ᵥ* (finiteMatrixAt g p).val) i ∈
        rationalLocalIntegers p} := by
    ext x
    simp only [Set.mem_iInter,Set.mem_ofPred_eq,SetLike.mem_coe,mem_localMatrixLattice_iff]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  apply (rationalIntegersOpen.out p).preimage
  exact (continuous_apply i).comp ((IsModuleTopology.continuous_of_linearMap
    (Matrix.vecMulLinear (finiteMatrixAt g p).val)).comp (localAlgebraCoordinates p.val b).continuous)

 

lemma open_submodule_absorbs_fullLattice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : Nat.Primes)
    (N : Submodule (PadicInt p.val) (LocalAlgebra p.val K))
    (hN : IsOpen (N : Set (LocalAlgebra p.val K))) :
    ∃ k : ℕ, ∀ x ∈ completedLattice p.val M, (p.val : PadicInt p.val)^k • x ∈ N := by
  have hpow : Tendsto (fun k : ℕ => (p.val : Padic p.val)^k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
      rw [Padic.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.property.one_lt))
  have hx (x : LocalAlgebra p.val K) : ∀ᶠ k : ℕ in atTop, (p.val : PadicInt p.val)^k • x ∈ N := by
    have H := (hpow.smul tendsto_const_nhds).eventually
      (hN.mem_nhds (show (0 : Padic p.val) • x ∈ N by simp))
    filter_upwards [H] with k hk
    rw [← IsScalarTower.algebraMap_smul (Padic p.val),map_pow,map_natCast]
    exact hk
  have hall : ∀ᶠ k : ℕ in atTop, ∀ i : Fin n,
      (p.val : PadicInt p.val)^k •
        (Algebra.TensorProduct.includeRight (M.basis i) : LocalAlgebra p.val K) ∈ N :=
    Filter.eventually_all.mpr (fun i => hx _)
  obtain ⟨k,hk⟩ := hall.exists
  refine ⟨k,?_⟩
  intro x hx
  rw [completedLattice_eq_span_basis] at hx
  induction hx using Submodule.span_induction with
  | mem x h => obtain ⟨i,rfl⟩ := h; exact hk i
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [smul_add] using N.add_mem ihx ihy
  | smul a x hx ih => simpa only [smul_comm ((p.val : PadicInt p.val)^k) a] using N.smul_mem a ih

theorem patch_open_local_modules {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (M : FullLattice n K)
    (N : (p : Nat.Primes) → Submodule (PadicInt p.val) (LocalAlgebra p.val K))
    (hNopen : ∀ p, IsOpen (N p : Set (LocalAlgebra p.val K)))
    (hNle : ∀ p, N p ≤ completedLattice p.val M)
    (hNeq : ∀ᶠ p : Nat.Primes in cofinite, N p = completedLattice p.val M) :
    ∃ L : FullLattice n K, ∀ p : Nat.Primes, completedLattice p.val L = N p := by
  classical
  let S : Set Nat.Primes := {p | N p ≠ completedLattice p.val M}
  have hS : S.Finite := Filter.eventually_cofinite.mp hNeq
  let : Fintype S := hS.fintype
  choose k hk using fun p : S => open_submodule_absorbs_fullLattice M p.val (N p.val) (hNopen p.val)
  have hp : Function.Injective (fun p : S => p.val.val) := by
    intro p q h
    exact Subtype.ext (Subtype.ext h)
  obtain ⟨L,_,hL,hLoff⟩ := patch_fullLattice_completions M hn (fun p : S => p.val.val)
    hp k (fun p : S => N p.val) (fun p => hNle p.val) hk
  refine ⟨L,fun p => ?_⟩
  by_cases hp : p ∈ S
  · exact hL ⟨p,hp⟩
  · have hnot : p.val ∉ Set.range (fun q : S => q.val.val) := by
      rintro ⟨q,hq⟩
      exact hp ((show q.val = p from Subtype.ext hq) ▸ q.property)
    rw [hLoff p.val p.property hnot]
    exact (not_not.mp hp).symm

lemma finite_family_integral_denominator {ι : Type*} [Fintype ι]
    (x : ι → RationalFiniteAdeles) :
    ∃ q : ℕ, q ≠ 0 ∧ ∀ (p : Nat.Primes) i, (q : Padic p.val) * x i p ∈ rationalLocalIntegers p := by
  classical
  have he : ∀ᶠ p : Nat.Primes in cofinite, ∀ i, x i p ∈ rationalLocalIntegers p :=
    Filter.eventually_all.mpr (fun i => (x i).property)
  let S : Set Nat.Primes := {p | ¬∀ i, x i p ∈ rationalLocalIntegers p}
  have hS : S.Finite := Filter.eventually_cofinite.mp he
  let : Fintype S := hS.fintype
  have habs (p : S) : ∃ k : ℕ, ∀ i,
      (p.val.val : Padic p.val.val)^k * x i p.val ∈ rationalLocalIntegers p.val := by
    have hpow : Tendsto (fun k : ℕ => (p.val.val : Padic p.val.val)^k) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
        rw [Padic.norm_p]
        exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.val.property.one_lt))
    have hi (i : ι) : ∀ᶠ k : ℕ in atTop,
        (p.val.val : Padic p.val.val)^k * x i p.val ∈ rationalLocalIntegers p.val := by
      exact (hpow.mul tendsto_const_nhds).eventually ((rationalIntegersOpen.out p.val).mem_nhds
        (show (0 : Padic p.val.val) * x i p.val ∈ rationalLocalIntegers p.val by simp))
    exact (Filter.eventually_all.mpr hi).exists
  choose k hk using habs
  let q : ℕ := ∏ p : S, p.val.val^(k p)
  refine ⟨q,Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ p.val.property.ne_zero),?_⟩
  intro p i
  by_cases hp : p ∈ S
  · have hd : p.val^(k ⟨p,hp⟩) ∣ q :=
      Finset.dvd_prod_of_mem (fun p : S => p.val.val^(k p)) (Finset.mem_univ (⟨p,hp⟩ : S))
    obtain ⟨a,ha⟩ := hd
    rw [ha,Nat.cast_mul,Nat.cast_pow,mul_right_comm]
    exact (rationalLocalIntegers p).mul_mem (hk ⟨p,hp⟩ i) (natCast_mem _ _)
  · exact (rationalLocalIntegers p).mul_mem (natCast_mem _ _) (not_not.mp hp i)

lemma integral_vecMul {n : ℕ} (p : Nat.Primes)
    (v : Fin n → Padic p.val) (A : Matrix (Fin n) (Fin n) (Padic p.val))
    (hv : ∀ i, v i ∈ rationalLocalIntegers p)
    (hA : ∀ i j, A i j ∈ rationalLocalIntegers p) :
    ∀ j, (v ᵥ* A) j ∈ rationalLocalIntegers p := by
  intro j
  change ∑ i, v i * A i j ∈ rationalLocalIntegers p
  exact sum_mem (fun i _ => (rationalLocalIntegers p).mul_mem (hv i) (hA i j))

lemma localMatrixLattice_eq_of_integral {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (g : GL (Fin n) RationalFiniteAdeles) (p : Nat.Primes)
    (hg : ∀ i j, (finiteMatrixAt g p).val i j ∈ rationalLocalIntegers p)
    (hi : ∀ i j, ((finiteMatrixAt g p)⁻¹).val i j ∈ rationalLocalIntegers p) :
    localMatrixLattice b g p = localIntegralSpan p.val b := by
  ext x
  rw [mem_localMatrixLattice_iff,localIntegralSpan_mem]
  change _ ↔ ∀ i, localAlgebraCoordinates p.val b x i ∈ rationalLocalIntegers p
  constructor
  · intro hx
    have H := integral_vecMul p _ _ hx hi
    simpa only [Matrix.vecMul_vecMul,Units.mul_inv,Matrix.vecMul_one] using H
  · intro hx
    exact integral_vecMul p _ _ hx hg

lemma localMatrixLattice_eventually_eq {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (g : GL (Fin n) RationalFiniteAdeles) :
    ∀ᶠ p : Nat.Primes in cofinite, localMatrixLattice b g p = localIntegralSpan p.val b := by
  have hg : ∀ᶠ p : Nat.Primes in cofinite, ∀ i j, g.val i j p ∈ rationalLocalIntegers p :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j => (g.val i j).property))
  have hi : ∀ᶠ p : Nat.Primes in cofinite, ∀ i j, (g⁻¹).val i j p ∈ rationalLocalIntegers p :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j => ((g⁻¹).val i j).property))
  filter_upwards [hg,hi] with p hp hq
  apply localMatrixLattice_eq_of_integral b g p hp
  rw [← finiteMatrixAt_inv]
  exact hq

lemma localMatrixLattice_mul_denominator {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (g : GL (Fin n) RationalFiniteAdeles) (p : Nat.Primes)
    (q : ℕ) (hi : ∀ i j, (q : Padic p.val) * (g⁻¹).val i j p ∈ rationalLocalIntegers p)
    {x : LocalAlgebra p.val K} (hx : x ∈ localMatrixLattice b g p) :
    (q : Padic p.val) • x ∈ localIntegralSpan p.val b := by
  rw [localIntegralSpan_mem]
  change ∀ i, localAlgebraCoordinates p.val b ((q : Padic p.val) • x) i ∈ rationalLocalIntegers p
  rw [mem_localMatrixLattice_iff] at hx
  have hi' : ∀ i j, ((q : Padic p.val) • ((finiteMatrixAt g p)⁻¹).val) i j ∈ rationalLocalIntegers p := by
    rw [← finiteMatrixAt_inv]
    exact hi
  have H := integral_vecMul p _ _ hx hi'
  simpa only [Matrix.vecMul_smul,Matrix.vecMul_vecMul,Units.mul_inv,Matrix.vecMul_one,
    map_smul] using H

lemma local_integral_scalar_smul_eq {K : Type*} [Field K] [NumberField K]
    (p : Nat.Primes) (N : Submodule (PadicInt p.val) (LocalAlgebra p.val K))
    (c : Padic p.val) (hc : c ≠ 0)
    (hci : c ∈ rationalLocalIntegers p) (hcinv : c⁻¹ ∈ rationalLocalIntegers p) :
    c • N = N := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    exact N.smul_mem (⟨c,hci⟩ : PadicInt p.val) hy
  · intro x hx
    apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
    refine ⟨c⁻¹ • x,N.smul_mem (⟨c⁻¹,hcinv⟩ : PadicInt p.val) hx,?_⟩
    rw [smul_smul,mul_inv_cancel₀ hc,one_smul]

lemma completed_scale_eventually_eq {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a : ℚˣ) :
    ∀ᶠ p : Nat.Primes in cofinite,
      completedLattice p.val (scaleFullLattice M (Units.map (algebraMap ℚ K) a)) = completedLattice p.val M := by
  filter_upwards [rational_eventually_integral (a : ℚ), rational_eventually_integral ((a⁻¹ : ℚˣ) : ℚ)]
    with p hp hq
  rw [completedLattice_scale_rat]
  apply local_integral_scalar_smul_eq p _ _
  · exact (Units.map (algebraMap ℚ (Padic p.val)).toMonoidHom a).ne_zero
  · exact hp
  · simpa only [Units.val_inv_eq_inv_val,Rat.cast_inv,eq_ratCast] using hq

lemma localMatrixLattice_le_scaled_basis {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (g : GL (Fin n) RationalFiniteAdeles) (p : Nat.Primes)
    (q : ℕ) (hq : q ≠ 0)
    (hi : ∀ i j, (q : Padic p.val) * (g⁻¹).val i j p ∈ rationalLocalIntegers p) :
    localMatrixLattice b g p ≤ completedLattice p.val
      (scaleFullLattice (basisFullLattice b) (Units.map (algebraMap ℚ K)
        ((Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr hq))⁻¹))) := by
  rw [completedLattice_scale_rat,completed_basisFullLattice]
  intro x hx
  apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
  refine ⟨(q : Padic p.val) • x,localMatrixLattice_mul_denominator b g p q hi hx,?_⟩
  have hqp : (q : Padic p.val) ≠ 0 := Nat.cast_ne_zero.mpr hq
  change (algebraMap ℚ (Padic p.val) ((q : ℚ)⁻¹)) • ((q : Padic p.val) • x) = x
  rw [map_inv₀,map_natCast,smul_smul,inv_mul_cancel₀ hqp,one_smul]

 

theorem finite_matrix_lattice_full_and_completed {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (g : GL (Fin n) RationalFiniteAdeles) :
    ∃ M : FullLattice n K, (M.carrier : Set K) = finiteGlobalMatrixLattice b g ∧
      ∀ p : Nat.Primes, completedLattice p.val M = localMatrixLattice b g p := by
  classical
  obtain ⟨q,hq,hqM⟩ := finite_family_integral_denominator
    (fun ij : Fin n × Fin n => (g⁻¹).val ij.1 ij.2)
  let a : ℚˣ := (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr hq))⁻¹
  let M₀ := basisFullLattice b
  let M := scaleFullLattice M₀ (Units.map (algebraMap ℚ K) a)
  have hle (p : Nat.Primes) : localMatrixLattice b g p ≤ completedLattice p.val M :=
    localMatrixLattice_le_scaled_basis b g p q hq (fun i j => hqM p (i,j))
  have heq : ∀ᶠ p : Nat.Primes in cofinite,
      localMatrixLattice b g p = completedLattice p.val M := by
    filter_upwards [localMatrixLattice_eventually_eq b g,completed_scale_eventually_eq M₀ a]
      with p hp hq
    rw [hq,completed_basisFullLattice]
    exact hp
  obtain ⟨L,hL⟩ := patch_open_local_modules hn M (localMatrixLattice b g)
    (localMatrixLattice_open b g) hle heq
  refine ⟨L,?_,hL⟩
  ext x
  rw [finiteGlobalMatrixLattice_local_iff]
  constructor
  · intro hx p
    rw [← hL p]
    exact Submodule.subset_span ⟨x,hx,rfl⟩
  · intro hx
    apply (mem_fullLattice_iff_forall_completed L hn x).mpr
    intro p hp
    rw [hL ⟨p,hp⟩]
    exact hx ⟨p,hp⟩

end PrimeDegreePackets.Adelic

end

end OAI
