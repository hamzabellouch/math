import Mathlib
import OAI.Algebra.FiniteTensor.DeformedCycles
import OAI.Algebra.FiniteTensor.FormReindexing

namespace OAI

/-! Three-block cycles, Frobenius residues and nonzero normal pairings. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped TensorProduct BigOperators
open Forms FrobeniusTruncation
universe u
variable (K : Type*) [Field K] (p : ℕ) [CharP K p] [Invertible (2 : K)]
  {n : ℕ} (σ : Fin (n+1) → Type u) [∀ i,Fintype (σ i)] [∀ i,DecidableEq (σ i)]

def sigmaBlock (i : Fin (n+1)) (b : A K (σ i) p) : A K ((i : Fin (n+1)) × σ i) p :=
  rename K (σ i) p (Sigma.mk i) b

def sigmaSelected (b : ∀ i,A K (σ i) p) (s : Finset (Fin (n+1))) :
    A K ((i : Fin (n+1)) × σ i) p :=
  ∏ i∈s, sigmaBlock K p σ i (b i)

omit [CharP K p] [Invertible (2 : K)] in
theorem sigmaPotential_single (i : Fin (n+1)) (b : A K (σ i) p) :
    sigmaPotential K p σ (Pi.single i b)=sigmaBlock K p σ i b := by
  unfold sigmaPotential
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]; rfl
  · intro j _ hji; rw [Pi.single_eq_of_ne hji,map_zero]
  · intro hi; exact (hi (Finset.mem_univ i)).elim

omit [Invertible (2 : K)] in
theorem koszul_sigmaBlock (b : ∀ i,A K (σ i) p) (i : Fin (n+1))
    (v : ⨂[K] i, Space K (σ i) p) :
    koszul K ((i : Fin (n+1)) × σ i) p (sigmaBlock K p σ i (b i))
      (sigmaSeparatedEquiv K p σ v)=
      sigmaSeparatedEquiv K p σ
        (PiTensorProduct.map (oddCoordinate
          (fun j => (parity K (A K (σ j) p) (σ j)).toLinearMap)
          (fun j => koszul K (σ j) p (b j)) i) v) := by
  have h := koszul_sigmaSeparated K p σ (Pi.single i (b i)) v
  rw [sigmaPotential_single] at h
  have hf : (fun j => koszul K (σ j) p ((Pi.single i (b i) : ∀ j,A K (σ j) p) j))=
      Pi.single i (koszul K (σ i) p (b i)) := by
    funext j
    by_cases hji : j=i
    · subst j; rw [Pi.single_eq_same,Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hji,Pi.single_eq_of_ne hji,koszul_zero]
  rw [hf,oddTensor_single (fun j => (parity K (A K (σ j) p) (σ j)).toLinearMap)
    (fun j => koszul K (σ j) p (b j)) i] at h
  exact h

omit [CharP K p] [Invertible (2 : K)] in
theorem sigmaProduct_selected (b : ∀ i,A K (σ i) p) (s : Finset (Fin (n+1))) :
    sigmaProduct K p σ (fun i => if i∈s then b i else 1)=sigmaSelected K p σ b s := by
  classical
  unfold sigmaProduct sigmaSelected sigmaBlock
  simp only [apply_ite,map_one,Finset.prod_ite_mem,Finset.univ_inter]

omit [CharP K p] [Invertible (2 : K)] in
theorem mulScalar_sigmaSelected (b : ∀ i,A K (σ i) p) (s : Finset (Fin (n+1)))
    (v : ⨂[K] i, Space K (σ i) p) :
    mulScalar K ((i : Fin (n+1)) × σ i) p (sigmaSelected K p σ b s)
      (sigmaSeparatedEquiv K p σ v)=
      sigmaSeparatedEquiv K p σ
        (partialTensor (fun i => Space K (σ i) p) (fun i => mulScalar K (σ i) p (b i)) s v) := by
  classical
  have h := mulScalar_sigmaSeparated K p σ (fun i => if i∈s then b i else 1) v
  rw [sigmaProduct_selected] at h
  have hf : (fun i => mulScalar K (σ i) p (if i∈s then b i else 1))=
      (fun i => if i∈s then mulScalar K (σ i) p (b i) else LinearMap.id) := by
    funext i
    split_ifs <;> simp only [mulScalar_one]
  rw [hf] at h
  exact h

end
end PD4Tensor.TruncatedForms

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped TensorProduct BigOperators
open Forms FrobeniusTruncation SuperReduction
universe u
variable (K : Type*) [Field K] (p : ℕ) [CharP K p] [Invertible (2 : K)]
  {n : ℕ} (σ : Fin (n+1) → Type u) [∀ i,Fintype (σ i)] [∀ i,DecidableEq (σ i)]

 

theorem exists_three_tensor_form_cycle
    (S b : ∀ i,A K (σ i) p) (active : Finset (Fin (n+1))) (hA : 5≤active.card)
    (α : Space K ((i : Fin (n+1)) × σ i) p)
    (hαδ : koszul K _ p (sigmaPotential K p σ S) α=0)
    (hαd : D K _ p α=0)
    (htrip : ∀ s : Finset (Fin (n+1)), s.card=3 →
      mulScalar K _ p (sigmaSelected K p σ b s) α ∈
        LinearMap.range (koszul K _ p (sigmaPotential K p σ S)))
    (L : Space K ((i : Fin (n+1)) × σ i) p →ₗ[K] K)
    (hLδ : ∀ v,L (koszul K _ p (sigmaPotential K p σ S) v)=0)
    (hLd : ∀ v,L (D K _ p v)=0) (hLα : L α≠0) :
    ∃ (q : Fin 3 ↪ Fin (n+1)) (κ : T K 3 ⊗[K] (⨂[K] i,Space K (σ i) p)),
      (∀ j,q j∈active) ∧
      deformedTensor (fun i => (parity K (A K (σ i) p) (σ i)).toLinearMap)
        (fun i => koszul K (σ i) p (S i)) (fun i => koszul K (σ i) p (b i))
        (threeParameters (K:=K) q) κ=0 ∧
      L (sigmaSeparatedEquiv K p σ (specializeTensor (augmentationAlg K 3) κ))≠0 := by
  classical
  have hc (i : Fin (n+1)) : ∃ C : SuperReduction K (Space K (σ i) p),
      C.d=koszul K (σ i) p (S i) ∧
      C.g=(parity K (A K (σ i) p) (σ i)).toLinearMap ∧
      ∀ w∈(⊤ : Submodule K (Space K (σ i) p)),C.p w∈(⊤ : Submodule K (Space K (σ i) p)) := by
    apply exists_superReduction _ _ (koszul_sq_zero K (σ i) p (S i))
      (fun v => parity_parity v) (koszul_parity K (σ i) p (S i)) ⊤
    intro v _; trivial
  choose C hCd hCg _ using hc
  let e := sigmaSeparatedEquiv K p σ
  have hδ (v : ⨂[K] i,Space K (σ i) p) :
      e (finiteD C v)=koszul K _ p (sigmaPotential K p σ S) (e v) := by
    change sigmaSeparatedEquiv K p σ (oddTensor (fun i => (C i).g) (fun i => (C i).d) v)=_
    simp only [hCd,hCg]
    exact (koszul_sigmaSeparated K p σ S v).symm
  have hd (v : ⨂[K] i,Space K (σ i) p) :
      e (oddTensor (fun i => (C i).g) (fun i => D K (σ i) p) v)=D K _ p (e v) := by
    simp only [hCg]
    exact (D_sigmaSeparated K p σ v).symm
  obtain ⟨q,κ,hq,hκ,hpair⟩ := exists_three_deformed_cycle C
    (fun i => D K (σ i) p) (fun i => mulScalar K (σ i) p (b i))
    (fun i => D_sq_zero K (σ i) p)
    (by intro i v; rw [hCg]; exact differential_parity _ v)
    (by
      intro i v
      rw [hCd]
      have h := LinearMap.congr_fun (D_koszul K (σ i) p (S i)) v
      change D K (σ i) p (koszul K (σ i) p (S i) v)=
        -koszul K (σ i) p (S i) (D K (σ i) p v) at h
      simpa only [neg_neg] using congrArg Neg.neg h.symm)
    (by
      intro i v
      rw [hCd]
      exact (LinearMap.congr_fun (mulScalar_koszul K (σ i) p (S i) (b i)) v).symm)
    (by intro i v; rw [hCg]; exact mulScalar_parity K (σ i) p (b i) v)
    active hA (e.symm α)
    (by apply e.injective; rw [hδ,e.apply_symm_apply,hαδ]; exact e.map_zero.symm)
    (by apply e.injective; rw [hd,e.apply_symm_apply,hαd]; exact e.map_zero.symm)
    (by
      intro s hs
      obtain ⟨β,hβ⟩ := htrip s hs
      refine ⟨e.symm β,?_⟩
      apply e.injective
      rw [hδ,e.apply_symm_apply]
      change _=sigmaSeparatedEquiv K p σ
        (partialTensor (fun i => Space K (σ i) p)
          (fun i => mulScalar K (σ i) p (b i)) s (e.symm α))
      rw [←mulScalar_sigmaSelected]
      change _=mulScalar K _ p (sigmaSelected K p σ b s) (e (e.symm α))
      rw [e.apply_symm_apply]
      exact hβ)
    (L.comp e.toLinearMap)
    (by intro v; change L (e (finiteD C v))=0; rw [hδ]; exact hLδ _)
    (by intro v; change L (e (oddTensor _ _ v))=0; rw [hd]; exact hLd _)
    (by change L (e (e.symm α))≠0; rw [e.apply_symm_apply]; exact hLα)
  refine ⟨q,κ,hq,?_,hpair⟩
  simpa only [hCg,hCd,D_mulScalar] using hκ

end
end PD4Tensor.TruncatedForms

namespace PD4Tensor
namespace FrobeniusTruncation
noncomputable section

variable (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ] (p : ℕ)

 
 
 
 
variable [CharP K p]

 
 

 
 
variable [Fact p.Prime]

 
 
def socle : Ring K σ p := ∏ i : σ, coord K σ p i ^ (p - 1)

omit [CharP K p] [Fact p.Prime] in
@[simp] theorem residue_socle_product (hp : 0 < p) :
    residue K σ p hp (socle K σ p) = 1 := by
  have he : (∑ i : σ, Finsupp.single i (p - 1)) = socleExponent σ p := by
    ext i
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, socleExponent_apply]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold socle coord
  simp only [← map_pow]
  rw [← map_prod]
  simp only [MvPolynomial.X_pow_eq_monomial]
  rw [← MvPolynomial.monomial_sum_prod]
  rw [he]
  simp only [Finset.prod_const_one, residue_socle]

 
def linearForm (A : Matrix σ σ K) (i : σ) : MvPolynomial σ K :=
  ∑ j : σ, MvPolynomial.C (A i j) * MvPolynomial.X j

omit [DecidableEq σ] in
@[simp] theorem linearForm_constant (A : Matrix σ σ K) (i : σ) :
    MvPolynomial.constantCoeff (linearForm K σ A i) = 0 := by
  simp [linearForm]

 
def linearSubst (A : Matrix σ σ K) : Ring K σ p →ₐ[K] Ring K σ p :=
  Ideal.Quotient.liftₐ (ideal K σ p)
    (MvPolynomial.aeval (fun i => Ideal.Quotient.mk (ideal K σ p) (linearForm K σ A i)))
    (by
      have h : ideal K σ p ≤ RingHom.ker
          (MvPolynomial.aeval (fun i => Ideal.Quotient.mk (ideal K σ p) (linearForm K σ A i))).toRingHom := by
        apply Ideal.span_le.mpr
        rintro _ ⟨i, rfl⟩
        change MvPolynomial.aeval _ ((MvPolynomial.X i : MvPolynomial σ K)^p) = 0
        rw [map_pow, MvPolynomial.aeval_X, frobenius_mk]
        simp [zero_pow (Fact.out : p.Prime).ne_zero]
      exact fun f hf => h hf)

omit [DecidableEq σ] in
@[simp] theorem linearSubst_coord (A : Matrix σ σ K) (i : σ) :
    linearSubst K σ p A (coord K σ p i) = ∑ j : σ, A i j • coord K σ p j := by
  change MvPolynomial.aeval (fun j => Ideal.Quotient.mk (ideal K σ p) (linearForm K σ A j))
    (MvPolynomial.X i) = _
  rw [MvPolynomial.aeval_X]
  simp only [linearForm, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro j hj
  change algebraMap K (Ring K σ p) (A i j) * coord K σ p j = _
  exact (Algebra.smul_def _ _).symm

 
omit [DecidableEq σ] in
theorem linearSubst_mul (A B : Matrix σ σ K) :
    linearSubst K σ p (A * B) = (linearSubst K σ p B).comp (linearSubst K σ p A) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change linearSubst K σ p (A * B) (coord K σ p i) =
    linearSubst K σ p B (linearSubst K σ p A (coord K σ p i))
  simp only [linearSubst_coord, map_sum, map_smul, Finset.smul_sum,
    Matrix.mul_apply, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

@[simp] theorem linearSubst_diagonal_coord (D : σ → K) (i : σ) :
    linearSubst K σ p (Matrix.diagonal D) (coord K σ p i) = D i • coord K σ p i := by
  simp [linearSubst_coord, Matrix.diagonal_apply]

@[simp] theorem linearSubst_transvection_coord (t : Matrix.TransvectionStruct σ K) (a : σ) :
    linearSubst K σ p t.toMatrix (coord K σ p a) =
      coord K σ p a + if a = t.i then t.c • coord K σ p t.j else 0 := by
  rw [linearSubst_coord]
  simp only [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_apply,
    add_smul, Finset.sum_add_distrib, Matrix.one_apply]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  by_cases h : a = t.i
  · subst a
    simp [Matrix.single_apply]
  · simp [h, Ne.symm h]

private theorem add_pow_mul_eq {R : Type*} [CommRing R] (a b c : R) (hbc : b*c=0) (n : ℕ) :
    (a+b)^n*c=a^n*c := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (a+b)^(n+1)*c = a*((a+b)^n*c)+(a+b)^n*(b*c) := by ring
      _ = a*(a^n*c) := by rw [ih, hbc, mul_zero, add_zero]
      _ = a^(n+1)*c := by ring

 
theorem linearSubst_transvection_socle (t : Matrix.TransvectionStruct σ K) :
    linearSubst K σ p t.toMatrix (socle K σ p) = socle K σ p := by
  have hpi : p - 1 + 1 = p := by have := (Fact.out : p.Prime).pos; omega
  have hbc : (t.c • coord K σ p t.j) * coord K σ p t.j ^ (p-1) = 0 := by
    rw [smul_mul_assoc, mul_comm, ← pow_succ, hpi, variable_pow, smul_zero]
  have he : (coord K σ p t.i + t.c • coord K σ p t.j) ^ (p-1) *
      coord K σ p t.j ^ (p-1) = coord K σ p t.i ^ (p-1) * coord K σ p t.j ^ (p-1) :=
    add_pow_mul_eq _ _ _ hbc _
  unfold socle
  simp only [map_prod, map_pow, linearSubst_transvection_coord]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t.i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ t.i)]
  simp only [ite_true]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨t.hij.symm, Finset.mem_univ _⟩),
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨t.hij.symm, Finset.mem_univ _⟩)]
  simp only [t.hij.symm, ite_false, add_zero]
  rw [← mul_assoc, he, mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  have hni : i ≠ t.i := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
  simp [hni]

 

theorem linearSubst_socle (A : Matrix σ σ K) :
    linearSubst K σ p A (socle K σ p) = A.det^(p-1) • socle K σ p := by
  apply Matrix.diagonal_transvection_induction
    (fun A => linearSubst K σ p A (socle K σ p) = A.det^(p-1) • socle K σ p) A
  · intro D hD
    simp only [socle, map_prod, map_pow, linearSubst_diagonal_coord,
      smul_pow, Finset.prod_smul, Matrix.det_diagonal, Finset.prod_pow]
  · intro t
    simp [linearSubst_transvection_socle]
  · intro A B hA hB
    rw [linearSubst_mul, AlgHom.comp_apply, hA, map_smul, hB, smul_smul,
      Matrix.det_mul, mul_pow]

 
omit [CharP K p] [Fact p.Prime] in
theorem high_augmentation_le :
    MvPolynomial.idealOfVars σ K ^ (Fintype.card σ * (p-1) + 1) ≤ ideal K σ p := by
  intro f hf
  rw [MvPolynomial.mem_pow_idealOfVars_iff] at hf
  rw [ideal]
  simp only [MvPolynomial.X_pow_eq_monomial]
  rw [Set.range_comp' (fun exponent : σ →₀ ℕ => MvPolynomial.monomial exponent (1 : K))
    (fun index : σ => Finsupp.single index p), MvPolynomial.mem_ideal_span_monomial_image]
  intro a ha
  have hd := hf a ha
  have hex : ∃ i : σ, p ≤ a i := by
    by_contra hn
    push Not at hn
    have hle : a.degree ≤ Fintype.card σ * (p-1) := by
      rw [Finsupp.degree_eq_sum]
      calc
        ∑ i : σ, a i ≤ ∑ i : σ, (p-1) := Finset.sum_le_sum (fun i hi => by have := hn i; omega)
        _ = _ := by simp
    omega
  obtain ⟨i, hi⟩ := hex
  refine ⟨Finsupp.single i p, ⟨i, rfl⟩, ?_⟩
  intro j
  by_cases hj : j = i
  · subst j; simpa using hi
  · simp [Ne.symm hj]

 
def linearPart (f : MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ i : σ, MvPolynomial.C (f.coeff (Finsupp.single i 1)) * MvPolynomial.X i

@[simp] theorem coeff_linearPart (a : σ →₀ ℕ) (f : MvPolynomial σ K) :
    (linearPart K σ f).coeff a =
      if a.degree = 1 then f.coeff a else 0 := by
  by_cases ha : a.degree = 1
  · obtain ⟨i, rfl⟩ := (Finsupp.sum_eq_one_iff a).mp ha
    simp only [linearPart, MvPolynomial.C_mul_X_eq_monomial, MvPolynomial.coeff_sum,
      MvPolynomial.coeff_monomial, Finsupp.single_left_inj one_ne_zero, Finsupp.degree_single,
      ite_true, Finset.sum_ite_eq', Finset.mem_univ]
  · simp only [linearPart, MvPolynomial.coeff_sum, MvPolynomial.C_mul_X_eq_monomial,
      MvPolynomial.coeff_monomial, ha, ite_false]
    apply Finset.sum_eq_zero
    intro i hi
    have hne : Finsupp.single i 1 ≠ a := by
      intro h
      apply ha
      rw [← h, Finsupp.degree_single]
    simp [hne]

omit [DecidableEq σ] in
@[simp] theorem linearPart_constant (f : MvPolynomial σ K) :
    MvPolynomial.constantCoeff (linearPart K σ f) = 0 := by
  simp [linearPart]

omit [Fintype σ] [DecidableEq σ] in
private theorem mem_augmentation (f : MvPolynomial σ K) (hf : MvPolynomial.constantCoeff f = 0) :
    f ∈ MvPolynomial.idealOfVars σ K := by
  rw [← pow_one (MvPolynomial.idealOfVars σ K), MvPolynomial.mem_pow_idealOfVars_iff']
  intro a ha
  have ha0 : a = 0 := (Finsupp.degree_eq_zero_iff a).mp (by omega)
  subst a
  exact hf

 

theorem sub_linearPart_mem (f : MvPolynomial σ K) (hf : MvPolynomial.constantCoeff f = 0) :
    f - linearPart K σ f ∈ MvPolynomial.idealOfVars σ K ^ 2 := by
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  intro a ha
  rw [MvPolynomial.coeff_sub, coeff_linearPart]
  by_cases ha1 : a.degree = 1
  · simp [ha1]
  · have ha0 : a = 0 := (Finsupp.degree_eq_zero_iff a).mp (by omega)
    subst a
    change f.coeff 0 = 0 at hf
    simpa using hf

private theorem filtered_pow_sub {R : Type*} [CommRing R] (J : Ideal R) (f g : R)
    (hf : f ∈ J) (hg : g ∈ J) (hfg : f-g ∈ J^2) (n : ℕ) :
    f^n-g^n ∈ J^(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : f*(f^n-g^n) ∈ J^(1+(n+1)) := by
      rw [pow_add, pow_one]
      exact Ideal.mul_mem_mul hf ih
    have h2 := Ideal.mul_mem_mul hfg (Ideal.pow_mem_pow hg n)
    rw [← pow_add] at h2
    have he : f^(n+1)-g^(n+1) = f*(f^n-g^n)+(f-g)*g^n := by ring
    rw [he]
    exact (J^(n+1+1)).add_mem
      (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1)
      (by convert h2 using 2; omega)

private theorem filtered_prod_mem {R ι : Type*} [CommRing R] (J : Ideal R)
    (s : Finset ι) (f : ι → R) (n : ℕ) (hf : ∀ i ∈ s, f i ∈ J^n) :
    ∏ i ∈ s, f i ∈ J^(s.card*n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.add_mul,
      one_mul, add_comm, pow_add]
    exact Ideal.mul_mem_mul (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem filtered_prod_sub {R ι : Type*} [CommRing R] (J : Ideal R)
    (s : Finset ι) (f g : ι → R) (n : ℕ)
    (hf : ∀ i ∈ s, f i ∈ J^n) (hg : ∀ i ∈ s, g i ∈ J^n)
    (hfg : ∀ i ∈ s, f i-g i ∈ J^(n+1)) :
    (∏ i ∈ s, f i) - (∏ i ∈ s, g i) ∈ J^(s.card*n+1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have hF := filtered_prod_mem J s f n (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hD := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hg j (Finset.mem_insert_of_mem hj))
      (fun j hj => hfg j (Finset.mem_insert_of_mem hj))
    have h1 := Ideal.mul_mem_mul (hfg i (Finset.mem_insert_self _ _)) hF
    have h2 := Ideal.mul_mem_mul (hg i (Finset.mem_insert_self _ _)) hD
    rw [← pow_add] at h1 h2
    have he : f i * (∏ j ∈ s, f j) - g i * (∏ j ∈ s, g j) =
        (f i-g i)*(∏ j ∈ s, f j)+g i*((∏ j ∈ s, f j)-(∏ j ∈ s, g j)) := by ring
    rw [he]
    apply (J^((s.card+1)*n+1)).add_mem
    · have hn : (s.card+1)*n+1 = n+1+s.card*n := by ring
      rw [hn]
      exact h1
    · have hn : (s.card+1)*n+1 = n+(s.card*n+1) := by ring
      rw [hn]
      exact h2

 
omit [CharP K p] [Fact p.Prime] in
theorem top_product_eq_linear (f : σ → MvPolynomial σ K)
    (hf : ∀ i, MvPolynomial.constantCoeff (f i) = 0) :
    (∏ i : σ, Ideal.Quotient.mk (ideal K σ p) (f i) ^ (p-1)) =
      ∏ i : σ, Ideal.Quotient.mk (ideal K σ p) (linearPart K σ (f i)) ^ (p-1) := by
  simp only [← map_pow, ← map_prod]
  apply sub_eq_zero.mp
  rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  apply high_augmentation_le K σ p
  apply filtered_prod_sub _ _ _ _ (p-1)
  · intro i hi
    exact Ideal.pow_mem_pow (mem_augmentation K σ (f i) (hf i)) _
  · intro i hi
    exact Ideal.pow_mem_pow (mem_augmentation K σ _ (linearPart_constant K σ (f i))) _
  · intro i hi
    exact filtered_pow_sub _ _ _ (mem_augmentation K σ (f i) (hf i))
      (mem_augmentation K σ _ (linearPart_constant K σ (f i)))
      (sub_linearPart_mem K σ (f i) (hf i)) _

 

omit [CharP K p] in
theorem coord_mul_socle (i : σ) : coord K σ p i * socle K σ p = 0 := by
  have hp : 1 + (p-1) = p := by have := (Fact.out : p.Prime).pos; omega
  unfold socle
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← mul_assoc,
    mul_comm (coord K σ p i), ← pow_succ]
  rw [show p-1+1=p by omega, variable_pow, zero_mul]

 
omit [CharP K p] in
theorem mk_mul_socle (f : MvPolynomial σ K) :
    Ideal.Quotient.mk (ideal K σ p) f * socle K σ p =
      MvPolynomial.constantCoeff f • socle K σ p := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.constantCoeff_C]
    exact (Algebra.smul_def c _).symm
  | add f g hf hg => simp only [map_add, add_mul, hf, hg, add_smul]
  | mul_X f i hf =>
    rw [map_mul, mul_assoc]
    change _ * (coord K σ p i * socle K σ p) = _
    rw [coord_mul_socle, mul_zero]
    simp

 
def tangentMatrix (f : σ → MvPolynomial σ K) : Matrix σ σ K :=
  fun i j => (f i).coeff (Finsupp.single j 1)

 

theorem top_product_eq_socle (f : σ → MvPolynomial σ K)
    (hf : ∀ i, MvPolynomial.constantCoeff (f i) = 0) :
    (∏ i : σ, Ideal.Quotient.mk (ideal K σ p) (f i) ^ (p-1)) =
      (tangentMatrix K σ f).det ^ (p-1) • socle K σ p := by
  rw [top_product_eq_linear K σ p f hf]
  have hsub : (∏ i : σ, Ideal.Quotient.mk (ideal K σ p) (linearPart K σ (f i)) ^ (p-1)) =
      linearSubst K σ p (tangentMatrix K σ f) (socle K σ p) := by
    simp only [socle, map_prod, map_pow]
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    change Ideal.Quotient.mk (ideal K σ p) (linearPart K σ (f i)) =
      MvPolynomial.aeval (fun j => Ideal.Quotient.mk (ideal K σ p)
        (linearForm K σ (tangentMatrix K σ f) j)) (MvPolynomial.X i)
    rw [MvPolynomial.aeval_X]
    rfl
  rw [hsub, linearSubst_socle]

 
def jacobianDet (f : σ → MvPolynomial σ K) : MvPolynomial σ K :=
  Matrix.det (fun i j => MvPolynomial.pderiv j (f i))

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem constantCoeff_pderiv (i : σ) (f : MvPolynomial σ K) :
    MvPolynomial.constantCoeff (MvPolynomial.pderiv i f) =
      f.coeff (Finsupp.single i 1) := by
  change (MvPolynomial.pderiv i f).coeff 0 = _
  rw [MvPolynomial.coeff_pderiv]
  simp

@[simp] theorem jacobianDet_constant (f : σ → MvPolynomial σ K) :
    MvPolynomial.constantCoeff (jacobianDet K σ f) = (tangentMatrix K σ f).det := by
  change MvPolynomial.constantCoeff
    (Matrix.det (fun i j => MvPolynomial.pderiv j (f i) : Matrix σ σ (MvPolynomial σ K))) = _
  rw [show MvPolynomial.constantCoeff
      (Matrix.det (fun i j => MvPolynomial.pderiv j (f i) : Matrix σ σ (MvPolynomial σ K))) =
    Matrix.det (Matrix.map (fun i j => MvPolynomial.pderiv j (f i))
      MvPolynomial.constantCoeff) from RingHom.map_det _ _]
  congr 1
  ext i j
  exact constantCoeff_pderiv K σ j (f i)

 

theorem normal_residue (hp : 0 < p) (f : σ → MvPolynomial σ K)
    (hf : ∀ i, MvPolynomial.constantCoeff (f i) = 0) :
    residue K σ p hp ((∏ i : σ, Ideal.Quotient.mk (ideal K σ p) (f i) ^ (p-1)) *
      Ideal.Quotient.mk (ideal K σ p) (jacobianDet K σ f)) =
      (tangentMatrix K σ f).det^p := by
  rw [top_product_eq_socle K σ p f hf, smul_mul_assoc, mul_comm, mk_mul_socle,
    jacobianDet_constant, smul_smul, map_smul, residue_socle_product, smul_eq_mul, mul_one]
  rw [← pow_succ, Nat.sub_add_cancel hp]

 
theorem normal_residue_ne_zero (hp : 0 < p) (f : σ → MvPolynomial σ K)
    (hf : ∀ i, MvPolynomial.constantCoeff (f i) = 0)
    (hdet : (tangentMatrix K σ f).det ≠ 0) :
    residue K σ p hp ((∏ i : σ, Ideal.Quotient.mk (ideal K σ p) (f i) ^ (p-1)) *
      Ideal.Quotient.mk (ideal K σ p) (jacobianDet K σ f)) ≠ 0 := by
  rw [normal_residue K σ p hp f hf]
  exact pow_ne_zero _ hdet

end
end FrobeniusTruncation
end PD4Tensor
end

end OAI
