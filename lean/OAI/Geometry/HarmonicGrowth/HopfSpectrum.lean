import OAI.Geometry.HarmonicGrowth.StreamData
import OAI.Geometry.HarmonicGrowth.Counting

namespace OAI

noncomputable section


namespace HarmonicCounterexample.Certificate
open scoped BigOperators

/-- Convexity of d(d+h), proved by the exact nonnegative-square identity.
This is used to certify a strict mean-exponent bound from rational eigenvalues. -/
theorem mean_root_lt {ι : Type*} (s : Finset ι) (w d : ι → ℝ)
    (h k : ℝ) (hw : ∀ i ∈ s,0 ≤ w i) (hkh : 0 < 2*k+h)
    (hspec : (∑ i ∈ s,w i*(d i*(d i+h))) < k*(k+h)*∑ i ∈ s,w i) :
    (∑ i ∈ s,w i*d i) < k*∑ i ∈ s,w i := by
  have hsq : 0 ≤ ∑ i ∈ s,w i*(d i-k)^2 :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  have he : (∑ i ∈ s,w i*(d i-k)^2) =
      (∑ i ∈ s,w i*(d i*(d i+h)))-(2*k+h)*(∑ i ∈ s,w i*d i)+
        k^2*∑ i ∈ s,w i := by
    simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hsq
  by_contra! hn
  have hm := mul_le_mul_of_nonneg_left hn hkh.le
  nlinarith

/-- The source eigenvalue, with its exact pinned normalization. -/
def eigenvalue (l b : ℕ) : ℝ :=
  100000*(101*(l:ℝ)*(l+14)-(2*b-l)^2)/(101*99853)

def exponent (l b : ℕ) : ℝ := -7+Real.sqrt (49+eigenvalue l b)

lemma eigenvalue_pos {l b : ℕ} (hl : 0 < l) (hb : b ≤ l) :
    0 < eigenvalue l b := by
  have hl' : (0:ℝ) < l := by exact_mod_cast hl
  have hb' : (b:ℝ) ≤ l := by exact_mod_cast hb
  have hb0 : (0:ℝ) ≤ b := Nat.cast_nonneg b
  have hs : (2*(b:ℝ)-l)^2 ≤ (l:ℝ)^2 := by nlinarith
  unfold eigenvalue
  apply div_pos _ (by norm_num)
  apply mul_pos (by norm_num)
  nlinarith

lemma exponent_equation {l b : ℕ} (hl : 0 < l) (hb : b ≤ l) :
    exponent l b*(exponent l b+14) = eigenvalue l b := by
  have hp := eigenvalue_pos hl hb
  have hs := Real.sq_sqrt (show 0 ≤ 49+eigenvalue l b by linarith)
  unfold exponent
  nlinarith

lemma exponent_pos {l b : ℕ} (hl : 0 < l) (hb : b ≤ l) :
    0 < exponent l b := by
  have hp := eigenvalue_pos hl hb
  have hs := Real.sqrt_nonneg (49+eigenvalue l b)
  have he := Real.sq_sqrt (show 0 ≤ 49+eigenvalue l b by linarith)
  unfold exponent
  nlinarith

/-- A paired charge count, as a rational integer-valued polynomial. -/
def pairMultiplicity (l b : ℕ) : ℚ :=
  2*((l:ℚ)+7)/7*(binomRat (b+6) 6*binomRat ((l:ℚ)-b+6) 6)

lemma pairMultiplicity_pos {l b : ℕ} (hb : b ≤ l) : 0 < pairMultiplicity l b := by
  have hb6 : (6:ℕ) ≤ b+6 := by omega
  have hl6 : (6:ℕ) ≤ l-b+6 := by omega
  have hbpos : (0:ℚ) < (b+6).choose 6 := by exact_mod_cast Nat.choose_pos hb6
  have hlpos : (0:ℚ) < (l-b+6).choose 6 := by exact_mod_cast Nat.choose_pos hl6
  unfold pairMultiplicity
  rw [show (b:ℚ)+6=((b+6:ℕ):ℚ) by norm_cast,binomRat_nat,
    show (l:ℚ)-b+6=((l-b+6:ℕ):ℚ) by rw [Nat.cast_add,Nat.cast_sub hb]; rfl,
    binomRat_nat]
  positivity

lemma pairMultiplicity_sum (l b : ℕ) :
    (∑ i ∈ Finset.range (b+1),pairMultiplicity l i) =
      2*((l:ℚ)+7)/7*countPrefix l b := by
  rw [countPrefix_sum,Finset.mul_sum]
  rfl

lemma pairMultiplicity_charge_sum (l b : ℕ) :
    (∑ i ∈ Finset.range (b+1),pairMultiplicity l i*((l:ℚ)-2*i)^2) =
      2*((l:ℚ)+7)/7*chargePrefix l b := by
  rw [chargePrefix_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold pairMultiplicity
  ring

end HarmonicCounterexample.Certificate

end

noncomputable section


namespace HarmonicCounterexample.Certificate
open scoped BigOperators

/-- The exact source Hopf multiplicity, obtained as the bihomogeneous kernel
minus its Laplacian target, not an asymptotic density. -/
def hopfMultiplicity (a b : ℕ) : ℕ :=
  (a+7).choose 7*(b+7).choose 7-(a+6).choose 7*(b+6).choose 7

lemma binomRat_seven_from_six (x : ℚ) :
    binomRat (x+6) 7 = x/7*binomRat (x+6) 6 := by
  have h := binomRat_mul_succ (x+6) 6
  norm_num only at h
  linear_combination (1/7:ℚ)*h

lemma hopfMultiplicity_rat (a b : ℕ) :
    (hopfMultiplicity a b:ℚ) = ((a:ℚ)+b+7)/7*
      (binomRat (a+6) 6*binomRat (b+6) 6) := by
  have ha : (a+6).choose 7 ≤ (a+7).choose 7 := Nat.choose_le_choose 7 (by omega)
  have hb : (b+6).choose 7 ≤ (b+7).choose 7 := Nat.choose_le_choose 7 (by omega)
  rw [hopfMultiplicity,Nat.cast_sub (Nat.mul_le_mul ha hb),Nat.cast_mul,Nat.cast_mul,
    ← binomRat_nat,← binomRat_nat,← binomRat_nat,← binomRat_nat]
  push_cast
  rw [show (a:ℚ)+7=((a:ℚ)+6)+1 by ring,
    show (b:ℚ)+7=((b:ℚ)+6)+1 by ring,binomRat_step,binomRat_step,
    binomRat_seven_from_six,binomRat_seven_from_six]
  ring

lemma pairMultiplicity_eq {l b : ℕ} (hb : b ≤ l) :
    pairMultiplicity l b = 2*(hopfMultiplicity b (l-b):ℚ) := by
  rw [hopfMultiplicity_rat]
  unfold pairMultiplicity
  rw [Nat.cast_sub hb]
  ring

lemma hopfMultiplicity_symm (a b : ℕ) : hopfMultiplicity a b = hopfMultiplicity b a := by
  unfold hopfMultiplicity
  rw [mul_comm ((a+7).choose 7),mul_comm ((a+6).choose 7)]

end HarmonicCounterexample.Certificate

end

noncomputable section


namespace HarmonicCounterexample.Construction
open Module Angular LinearODE Certificate
open scoped BigOperators InnerProductSpace

lemma d0_bounds (l:ℕ) (i:Index l) : -B l≤d0 l i ∧ d0 l i≤0 := by
  have hlo := D_lower l (Berger.ComplexStructure.block 8) (basis l i)
  have hhi := D_nonpos l (Berger.ComplexStructure.block 8) (basis l i)
  change -(B l*‖basis l i‖^2) ≤ inner ℝ (basis l i) (Dround l (basis l i)) at hlo
  change inner ℝ (basis l i) (Dround l (basis l i))≤0 at hhi
  rw [basis_eigen,inner_smul_right,real_inner_self_eq_norm_sq,(basis l).norm_eq_one] at hlo hhi
  norm_num at hlo hhi
  exact ⟨hlo,hhi⟩

lemma d0_sum (l:ℕ) : (∑i:Index l,d0 l i)=-(B l/15)*(Fintype.card (Index l):ℝ) := by
  have h := D_trace l (Berger.ComplexStructure.block 8)
  rw [LinearMap.trace_eq_matrix_trace ℝ (basis l).toBasis] at h
  change (LinearMap.toMatrix (basis l).toBasis (basis l).toBasis (Dround l).toLinearMap).trace=_ at h
  rw [← orthogonalMatrix_toMatrix,Dround_diagonal,Matrix.trace_diagonal] at h
  simpa only [Fintype.card_fin] using h

def lambda (l:ℕ) (i:Index l) : ℝ :=
  beta*(qstar^(1/15:ℝ)*B l+(qstar^(1/15:ℝ)-qstar^((1/15:ℝ)-1))*d0 l i)
def root (l:ℕ) (i:Index l) : ℝ := -7+Real.sqrt (49+lambda l i)

lemma lambda_exact (l:ℕ) (i:Index l) :
    lambda l i=100000/(101*99853)*(101*B l+d0 l i) := by
  rw [lambda,beta,a_square,Real.rpow_sub_one qstar_pos.ne']
  have hq := (Real.rpow_pos_of_pos qstar_pos (1/15:ℝ)).ne'
  unfold qstar at *
  field_simp
  ring

lemma lambda_pos (l:ℕ) (i:Index l) : 0<lambda l i := by
  rw [lambda_exact]
  have h := (d0_bounds l i).1
  have hb := B_pos l
  apply mul_pos (by norm_num)
  linarith

lemma root_pos (l:ℕ) (i:Index l) : 0<root l i := by
  have h := Real.sq_sqrt (show 0≤49+lambda l i by linarith [lambda_pos l i])
  have hn := Real.sqrt_nonneg (49+lambda l i)
  unfold root;nlinarith [lambda_pos l i]
lemma root_eq (l:ℕ) (i:Index l) : root l i*(root l i+14)=lambda l i := by
  have h := Real.sq_sqrt (show 0≤49+lambda l i by linarith [lambda_pos l i])
  unfold root;nlinarith

lemma lambda_of_charge {l p:ℕ} (hp:p≤l+2) {i:Index l}
    (hi:d0 l i= -((p:ℝ)-((l+2-p:ℕ):ℝ))^2) :
    lambda l i=eigenvalue (l+2) p := by
  rw [lambda_exact,hi,Nat.cast_sub hp]
  simp only [B,degree,eigenvalue,Nat.cast_add,Nat.cast_ofNat]
  ring

lemma mean_root_from_lambda {l:ℕ} (s:Finset (Index l))
    (hs:(∑i∈s,lambda l i)<50000*(50000+14)*(s.card:ℝ)) :
    (∑i∈s,root l i)<50000*(s.card:ℝ) := by
  have h := mean_root_lt s (fun _=>(1:ℝ)) (root l) 14 50000
    (fun _ _=>by norm_num) (by norm_num) (by simpa only [one_mul,root_eq,Finset.sum_const,nsmul_eq_mul,mul_one] using hs)
  simpa only [one_mul,Finset.sum_const,nsmul_eq_mul,mul_one] using h

lemma full_mean_root {l:ℕ} (hl:l+2≤49963) :
    (∑i:Index l,root l i)<50000*(Fintype.card (Index l):ℝ) := by
  apply mean_root_from_lambda Finset.univ
  simp only [lambda_exact,Finset.card_univ]
  rw [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,d0_sum]
  simp only [nsmul_eq_mul,Finset.card_univ]
  have hd : 0<(Fintype.card (Index l):ℝ) := by
    exact_mod_cast (show 0<Fintype.card (Index l) by simp only [Fintype.card_fin];have := dim_ge_two l;omega)
  have hb : B l≤(49963:ℝ)*(49963+14) := by
    have hl' : degree l≤49963 := by unfold degree;exact_mod_cast hl
    have h0 := degree_pos l
    unfold B
    nlinarith
  nlinarith

end HarmonicCounterexample.Construction

end

noncomputable section


namespace HarmonicCounterexample.ComplexAngular
open MvPolynomial Finsupp
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def biWeight : ι ⊕ ι → ℕ × ℕ := Sum.elim (fun _ => (1,0)) (fun _ => (0,1))

def biSpace (p q : ℕ) : Submodule ℂ (SplitPolynomial ι) :=
  weightedHomogeneousSubmodule ℂ biWeight (p,q)

omit [DecidableEq ι] in
lemma biWeight_apply (d : (ι ⊕ ι) →₀ ℕ) :
    weight biWeight d = (∑ i : ι,d (Sum.inl i),∑ i : ι,d (Sum.inr i)) := by
  rw [weight_eq_sum,Fintype.sum_sum_type]
  have hf (f : ι → ℕ×ℕ) : (∑ i,f i).1 = ∑ i,(f i).1 :=
    map_sum (AddMonoidHom.fst ℕ ℕ) f Finset.univ
  have hg (f : ι → ℕ×ℕ) : (∑ i,f i).2 = ∑ i,(f i).2 :=
    map_sum (AddMonoidHom.snd ℕ ℕ) f Finset.univ
  apply Prod.ext <;> simp [biWeight,Prod.smul_mk,hf,hg]

abbrev DegreeIndex (ι : Type*) [Fintype ι] [DecidableEq ι] (p : ℕ) :=
  ↥((Finset.univ : Finset ι).finsuppAntidiag p)

lemma degreeIndex_mem (d : ι →₀ ℕ) (p : ℕ) :
    d ∈ (Finset.univ : Finset ι).finsuppAntidiag p ↔ ∑ i : ι,d i = p := by
  simp [Finset.mem_finsuppAntidiag]

/-- The actual monomials of bidegree (p,q) are independently chosen left and
right multisets. This is an equivalence, not an assumed multiplicity. -/
def biIndexEquiv (p q : ℕ) :
    {d : (ι ⊕ ι) →₀ ℕ | weight biWeight d = (p,q)} ≃
      DegreeIndex ι p × DegreeIndex ι q where
  toFun d :=
    (⟨(sumFinsuppEquivProdFinsupp d.1).1, (degreeIndex_mem _ _).2 (by
      simpa only [biWeight_apply,Prod.fst, fst_sumFinsuppEquivProdFinsupp] using congrArg Prod.fst d.property)⟩,
     ⟨(sumFinsuppEquivProdFinsupp d.1).2, (degreeIndex_mem _ _).2 (by
      simpa only [biWeight_apply,Prod.snd, snd_sumFinsuppEquivProdFinsupp] using congrArg Prod.snd d.property)⟩)
  invFun e := ⟨sumFinsuppEquivProdFinsupp.symm (e.1.1,e.2.1),by
    change weight biWeight _ = (p,q)
    rw [biWeight_apply]
    apply Prod.ext
    · simpa only [sumFinsuppEquivProdFinsupp_symm_inl] using (degreeIndex_mem _ _).1 e.1.2
    · simpa only [sumFinsuppEquivProdFinsupp_symm_inr] using (degreeIndex_mem _ _).1 e.2.2⟩
  left_inv d := Subtype.ext (sumFinsuppEquivProdFinsupp.symm_apply_apply d.1)
  right_inv e := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst (sumFinsuppEquivProdFinsupp.apply_symm_apply (e.1.1,e.2.1))
    · exact congrArg Prod.snd (sumFinsuppEquivProdFinsupp.apply_symm_apply (e.1.1,e.2.1))

instance biIndex_fintype (p q : ℕ) :
    Fintype {d : (ι ⊕ ι) →₀ ℕ | weight biWeight d = (p,q)} :=
  Fintype.ofEquiv _ (biIndexEquiv p q).symm

lemma biSpace_finrank (p q : ℕ) :
    Module.finrank ℂ (biSpace (ι := ι) p q) =
      (Fintype.card ι+p-1).choose p * (Fintype.card ι+q-1).choose q := by
  classical
  rw [biSpace,weightedHomogeneousSubmodule_eq_finsupp_supported,
    (AddMonoidAlgebra.supportedEquivFinsupp (R := ℂ) (S := ℂ)
      {d : (ι ⊕ ι) →₀ ℕ | weight biWeight d = (p,q)}).finrank_eq]
  rw [Module.finrank_finsupp_self (R := ℂ) (ι := {d : (ι ⊕ ι) →₀ ℕ | weight biWeight d = (p,q)}),
    Fintype.card_congr (biIndexEquiv p q),Fintype.card_prod]
  simp only [DegreeIndex,Fintype.card_coe,Finset.card_finsuppAntidiag_nat_eq_choose,
    Finset.card_univ]

instance biSpace_finite (p q : ℕ) : FiniteDimensional ℂ (biSpace (ι := ι) p q) := by
  rw [biSpace,weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact Module.Finite.equiv (AddMonoidAlgebra.supportedEquivFinsupp (R := ℂ) (S := ℂ)
    {d : (ι ⊕ ι) →₀ ℕ | weight biWeight d = (p,q)}).symm

end HarmonicCounterexample.ComplexAngular

end

noncomputable section


namespace HarmonicCounterexample.ComplexAngular
open MvPolynomial Finsupp
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma conjugate_mem_biSpace {P : SplitPolynomial ι} {p q : ℕ}
    (hP : P ∈ biSpace p q) : conjugate P ∈ biSpace p q := by
  intro d hd
  apply hP
  intro hz
  exact hd (by rw [coeff_conjugate,hz,star_zero])

omit [DecidableEq ι] in
lemma quadric_bihomogeneous : (quadric ι).IsWeightedHomogeneous biWeight (1,1) := by
  apply IsWeightedHomogeneous.sum
  intro i _
  exact (isWeightedHomogeneous_X ℂ biWeight (Sum.inl i)).mul
    (isWeightedHomogeneous_X ℂ biWeight (Sum.inr i))

def biQuadricMultiply (p q : ℕ) : biSpace (ι := ι) p q →ₗ[ℂ] biSpace (ι := ι) (p+1) (q+1) where
  toFun P := ⟨quadric ι*P, by
    change (quadric ι*(P : SplitPolynomial ι)).IsWeightedHomogeneous biWeight (p+1,q+1)
    have h := quadric_bihomogeneous.mul P.property
    simpa only [Prod.mk_add_mk,Nat.add_comm 1] using h⟩
  map_add' P Q := Subtype.ext (mul_add _ _ _)
  map_smul' c P := Subtype.ext (mul_smul_comm _ _ _)

omit [DecidableEq ι] in
lemma biQuadricMultiply_injective [Nontrivial ι] (p q : ℕ) :
    Function.Injective (biQuadricMultiply (ι := ι) p q) := by
  intro P Q h
  apply Subtype.ext
  exact mul_left_cancel₀ (quadric_irreducible.ne_zero) (congrArg Subtype.val h)

def biLaplacian (p q : ℕ) : biSpace (ι := ι) (p+1) (q+1) →ₗ[ℂ] biSpace (ι := ι) p q where
  toFun P := ⟨mixedLaplacian P,by
    rw [mixedLaplacian_apply]
    apply IsWeightedHomogeneous.sum
    intro i _
    have h : (pderiv (Sum.inr i) (P : SplitPolynomial ι)).IsWeightedHomogeneous biWeight (p+1,q) :=
      P.property.pderiv (by simp [biWeight])
    exact h.pderiv (by simp [biWeight])⟩
  map_add' P Q := Subtype.ext (map_add mixedLaplacian (P : SplitPolynomial ι) (Q : SplitPolynomial ι))
  map_smul' c P := Subtype.ext (map_smul mixedLaplacian c (P : SplitPolynomial ι))

lemma biLaplacian_surjective [Nontrivial ι] (p q : ℕ) :
    Function.Surjective (biLaplacian (ι := ι) p q) := by
  intro Q
  obtain ⟨φ,hφ⟩ := LinearMap.dualMap_surjective_of_injective (biQuadricMultiply_injective p q)
    (subspaceFischer (biSpace p q) Q)
  obtain ⟨P,hP⟩ := subspaceFischer_surjective (biSpace (p+1) (q+1))
    (fun _ h => conjugate_mem_biSpace h) φ
  refine ⟨P,subspaceFischer_injective (biSpace p q) (fun _ h => conjugate_mem_biSpace h) ?_⟩
  ext R
  have h := congrArg (fun f : Module.Dual ℂ (biSpace (ι := ι) p q) => f R) hφ
  rw [← hP] at h
  change fischer (P : SplitPolynomial ι) (quadric ι*R) = fischer (Q : SplitPolynomial ι) R at h
  change fischer (mixedLaplacian (P : SplitPolynomial ι)) R = _
  rw [fischer_symm,← fischer_quadric,fischer_symm]
  exact h

/-- Actual bihomogeneous harmonic polynomials. -/
def biHarmonic (p q : ℕ) : Submodule ℂ (SplitPolynomial ι) :=
  biSpace p q ⊓ LinearMap.ker mixedLaplacian

instance biHarmonic_finite (p q : ℕ) : FiniteDimensional ℂ (biHarmonic (ι := ι) p q) :=
  Module.Finite.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)

def biKernelEquiv (p q : ℕ) : LinearMap.ker (biLaplacian (ι := ι) p q) ≃ₗ[ℂ]
    biHarmonic (ι := ι) (p+1) (q+1) where
  toFun P := ⟨P.val.val,⟨P.val.property,congrArg Subtype.val P.property⟩⟩
  invFun P := ⟨⟨P.val,P.property.1⟩,Subtype.ext P.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma biHarmonic_finrank_add [Nontrivial ι] (p q : ℕ) :
    Module.finrank ℂ (biHarmonic (ι := ι) (p+1) (q+1)) +
      (Fintype.card ι+p-1).choose p * (Fintype.card ι+q-1).choose q =
      (Fintype.card ι+p).choose (p+1) * (Fintype.card ι+q).choose (q+1) := by
  have h := LinearMap.finrank_range_add_finrank_ker (biLaplacian (ι := ι) p q)
  rw [LinearMap.range_eq_top.2 (biLaplacian_surjective p q),finrank_top,
    (biKernelEquiv p q).finrank_eq,biSpace_finrank,biSpace_finrank] at h
  simpa only [show Fintype.card ι+(p+1)-1 = Fintype.card ι+p by omega,
    show Fintype.card ι+(q+1)-1 = Fintype.card ι+q by omega,Nat.add_comm] using h

end HarmonicCounterexample.ComplexAngular

end

noncomputable section


namespace HarmonicCounterexample.ComplexAngular
open MvPolynomial Finsupp
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma biSpace_left_weight {p q : ℕ} {P : SplitPolynomial ι}
    (hP : P ∈ biSpace p q) :
    P.IsWeightedHomogeneous (Sum.elim (fun _ : ι => 1) (fun _ : ι => 0)) p := by
  intro d hd
  have he := congrArg Prod.fst (hP hd)
  rw [biWeight_apply] at he
  simpa [weight_eq_sum,Fintype.sum_sum_type] using he

omit [DecidableEq ι] in
lemma biSpace_right_weight {p q : ℕ} {P : SplitPolynomial ι}
    (hP : P ∈ biSpace p q) :
    P.IsWeightedHomogeneous (Sum.elim (fun _ : ι => 0) (fun _ : ι => 1)) q := by
  intro d hd
  have he := congrArg Prod.snd (hP hd)
  rw [biWeight_apply] at he
  simpa [weight_eq_sum,Fintype.sum_sum_type] using he

omit [DecidableEq ι] in
lemma biSpace_leftEuler {p q : ℕ} {P : SplitPolynomial ι}
    (hP : P ∈ biSpace p q) :
    ∑ i : ι,X (Sum.inl i)*pderiv (Sum.inl i) P=(p:ℂ) • P := by
  simpa only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,one_smul,zero_smul,
    Finset.sum_const_zero,add_zero,Nat.cast_smul_eq_nsmul] using
      (biSpace_left_weight hP).sum_weight_X_mul_pderiv

omit [DecidableEq ι] in
lemma biSpace_rightEuler {p q : ℕ} {P : SplitPolynomial ι}
    (hP : P ∈ biSpace p q) :
    ∑ i : ι,X (Sum.inr i)*pderiv (Sum.inr i) P=(q:ℂ) • P := by
  simpa only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,one_smul,zero_smul,
    Finset.sum_const_zero,zero_add,Nat.cast_smul_eq_nsmul] using
      (biSpace_right_weight hP).sum_weight_X_mul_pderiv

end HarmonicCounterexample.ComplexAngular

end

noncomputable section


namespace HarmonicCounterexample.Control
open Matrix MvPolynomial HarmonicCounterexample.Berger
open HarmonicCounterexample.Berger.ComplexStructure
open HarmonicCounterexample.ComplexAngular
open scoped BigOperators

lemma splitMatrix_block (s : ℕ) : splitMatrix (ComplexStructure.block s)=
    Matrix.diagonal (Sum.elim (fun _ : Fin s => Complex.I) (fun _ : Fin s => -Complex.I)) := by
  ext a b
  rcases a with a|a <;> rcases b with b|b <;> by_cases hab : a=b <;>
    simp [splitMatrix,ComplexStructure.block,coordinateSign,coordinatePlane,
      Matrix.fromBlocks,Matrix.diagonal,hab] <;> ring

/-- The true Hopf vector field on actual bihomogeneous polynomials has its
literal integer charge p-q; it is not postulated as a spectral label. -/
lemma hopf_charge {s p q : ℕ} {P : SplitPolynomial (Fin s)}
    (hP : P ∈ biSpace p q) :
    linearField (splitMatrix (ComplexStructure.block s)) P=
      (Complex.I*((p:ℂ)-(q:ℂ))) • P := by
  rw [splitMatrix_block,linearField_apply]
  simp only [Matrix.diagonal_apply,ite_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr,← Finset.smul_sum,neg_smul,Finset.sum_neg_distrib,
    biSpace_leftEuler hP,biSpace_rightEuler hP,smul_smul]
  rw [← sub_eq_add_neg,← sub_smul,mul_sub]

/-- The actual nonnegative Hopf-square eigenvalue entering the Berger angular
operator, including charge zero and both signs of p-q. -/
lemma hopf_square_eigenvalue {s p q : ℕ} {P : SplitPolynomial (Fin s)}
    (hP : P ∈ biSpace p q) :
    -linearField (splitMatrix (ComplexStructure.block s))
      (linearField (splitMatrix (ComplexStructure.block s)) P)=
      (((p:ℂ)-(q:ℂ))^2) • P := by
  rw [hopf_charge hP,Derivation.map_smul,hopf_charge hP,smul_smul,← neg_smul]
  congr 1
  calc
    -(Complex.I*((p:ℂ)-(q:ℂ))*(Complex.I*((p:ℂ)-(q:ℂ))))=
      -(Complex.I*Complex.I)*((p:ℂ)-(q:ℂ))^2 := by ring
    _=_ := by rw [Complex.I_mul_I,neg_neg,one_mul]

end HarmonicCounterexample.Control

end

noncomputable section


namespace HarmonicCounterexample.RealForm
open ComplexStarModule
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [StarAddMonoid V] [StarModule ℂ V]

lemma realPart_map (T : Module.End ℂ V) (hT : ∀ x,T (star x)=star (T x)) (x : V) :
    realPart (T x)=restrictReal T (realPart x) := by
  have h := congrArg (fun A : Module.End ℂ V => realPart (A x)) (complexify_restrictReal T hT)
  rw [complexify_realPart] at h
  exact h.symm

lemma eigen_realPart_zero (T : Module.End ℂ V) (hT : ∀ x,T (star x)=star (T x))
    {m : ℝ} (hm : m≠0) {x : V} (hx : T x=(Complex.I*(m:ℂ)) • x)
    (hz : realPart x=0) : x=0 := by
  have h := congrArg realPart hx
  rw [realPart_map T hT,hz,map_zero,realPart_smul] at h
  simp only [Complex.mul_re,Complex.I_re,Complex.ofReal_re,zero_mul,Complex.I_im,
    Complex.ofReal_im,mul_zero,sub_self,zero_smul,Complex.mul_im,one_mul,zero_add,
    zero_sub] at h
  have hi : imaginaryPart x=0 := (smul_eq_zero.mp (neg_eq_zero.mp h.symm)).resolve_left hm
  exact ComplexStarModule.ext (hz.trans (map_zero _).symm) (hi.trans (map_zero _).symm)

lemma eigen_square_realPart (T : Module.End ℂ V) (hT : ∀ x,T (star x)=star (T x))
    {m : ℝ} {x : V} (hx : T x=(Complex.I*(m:ℂ)) • x) :
    restrictReal T (restrictReal T (realPart x))=(-(m^2)) • realPart x := by
  rw [← realPart_map T hT,← realPart_map T hT,hx,map_smul,hx,smul_smul]
  have he : Complex.I*(m:ℂ)*(Complex.I*(m:ℂ))=(-(m^2):ℝ) := by
    calc
      _=Complex.I*Complex.I*(m:ℂ)^2 := by ring
      _=_ := by rw [Complex.I_mul_I]; push_cast; ring
  rw [he]
  exact realPart.map_smul _ _
end HarmonicCounterexample.RealForm

end

noncomputable section


namespace HarmonicCounterexample.ComplexAngular
open MvPolynomial Finsupp
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

lemma biSpace_homogeneous {p q : ℕ} {P : SplitPolynomial ι} (hP : P∈biSpace p q) :
    P.IsHomogeneous (p+q) := by
  intro d hd
  have h := hP hd
  rw [biWeight_apply] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  rw [weight_eq_sum,Fintype.sum_sum_type]
  simpa using congrArg₂ (·+·) h1 h2

def biHarmonicInclusion (p q : ℕ) : biHarmonic (ι:=ι) p q →ₗ[ℂ] harmonicSpace ι (p+q) where
  toFun P := ⟨P.val,⟨biSpace_homogeneous P.property.1,P.property.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma biHarmonicInclusion_injective (p q : ℕ) :
    Function.Injective (biHarmonicInclusion (ι:=ι) p q) := by
  intro P Q h
  apply Subtype.ext
  exact congrArg (fun X : harmonicSpace ι (p+q) => X.val) h
end HarmonicCounterexample.ComplexAngular

end

noncomputable section


namespace HarmonicCounterexample.Control
open MvPolynomial ComplexAngular Berger Berger.ComplexStructure ComplexStarModule

def biRealCartesian (p q : ℕ) : biHarmonic (ι:=Fin 8) p q →ₗ[ℝ]
    Angular.harmonicPolynomials 16 (p+q) :=
  (realCartesianHarmonic (p+q)).toLinearMap.comp
    (realPart.comp ((biHarmonicInclusion p q).restrictScalars ℝ))

lemma biHarmonic_charge (p q : ℕ) (P : biHarmonic (ι:=Fin 8) p q) :
    harmonicField (p+q) (ComplexStructure.block 8) (biHarmonicInclusion p q P)=
      (Complex.I*Complex.ofReal ((p:ℝ)-(q:ℝ))) • biHarmonicInclusion p q P := by
  apply Subtype.ext
  change linearField (splitFieldMatrix (ComplexStructure.block 8).matrix) P.val=_
  rw [splitFieldMatrix_complex]
  change linearField (splitMatrix (ComplexStructure.block 8)) P.val=
    (Complex.I*Complex.ofReal ((p:ℝ)-(q:ℝ))) • P.val
  simpa only [Complex.ofReal_sub,Complex.ofReal_natCast] using hopf_charge P.property.1

lemma biRealCartesian_injective {p q : ℕ} (hpq : p≠q) :
    Function.Injective (biRealCartesian p q) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro P hP
  have hz : realPart (biHarmonicInclusion p q P)=0 :=
    (realCartesianHarmonic (p+q)).injective (hP.trans ((realCartesianHarmonic (p+q)).map_zero).symm)
  have h := RealForm.eigen_realPart_zero (harmonicField (p+q) (ComplexStructure.block 8))
    (harmonicField_star _ _) (show (p:ℝ)-(q:ℝ)≠0 by exact sub_ne_zero.mpr (by exact_mod_cast hpq))
    (biHarmonic_charge p q P) hz
  exact biHarmonicInclusion_injective p q (h.trans (map_zero _).symm)

lemma biRealCartesian_square (p q : ℕ) (P : biHarmonic (ι:=Fin 8) p q) :
    Angular.rotation ((ComplexStructure.block 8).reindex finSumFinEquiv.symm) (p+q)
      (Angular.rotation ((ComplexStructure.block 8).reindex finSumFinEquiv.symm) (p+q)
        (biRealCartesian p q P))=
      (-((p:ℝ)-(q:ℝ))^2) • biRealCartesian p q P := by
  have h := RealForm.eigen_square_realPart (harmonicField (p+q) (ComplexStructure.block 8))
    (harmonicField_star _ _) (m:=(p:ℝ)-(q:ℝ)) (biHarmonic_charge p q P)
  unfold biRealCartesian
  simp only [LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,LinearMap.coe_restrictScalars]
  rw [← realCartesian_rotation,← realCartesian_rotation,← map_smul]
  apply congrArg (realCartesianHarmonic (p+q))
  exact h
end HarmonicCounterexample.Control

end

noncomputable section


namespace HarmonicCounterexample.ComplexAngular
open MvPolynomial Finsupp
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma pderiv_left_zero {P : SplitPolynomial ι} {q : ℕ} (hP : P ∈ biSpace 0 q) (i : ι) :
    pderiv (Sum.inl i) P = 0 := by
  ext d
  rw [coeff_pderiv,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
  by_cases hc : P.coeff (d+single (Sum.inl i) 1) = 0
  · rw [hc,zero_mul]
  · have hw := biSpace_left_weight hP hc
    simp only [map_add,weight_single,Sum.elim_inl,one_smul] at hw
    omega

omit [DecidableEq ι] in
lemma pderiv_right_zero {P : SplitPolynomial ι} {p : ℕ} (hP : P ∈ biSpace p 0) (i : ι) :
    pderiv (Sum.inr i) P = 0 := by
  ext d
  rw [coeff_pderiv,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
  by_cases hc : P.coeff (d+single (Sum.inr i) 1) = 0
  · rw [hc,zero_mul]
  · have hw := biSpace_right_weight hP hc
    simp only [map_add,weight_single,Sum.elim_inr,one_smul] at hw
    omega

omit [DecidableEq ι] in
lemma biHarmonic_zero_right (p : ℕ) : biHarmonic (ι := ι) p 0 = biSpace p 0 := by
  apply inf_eq_left.2
  intro P hP
  change mixedLaplacian P = 0
  simp only [mixedLaplacian_apply,pderiv_right_zero hP,map_zero,Finset.sum_const_zero]

lemma biHarmonic_zero_left (q : ℕ) : biHarmonic (ι := ι) 0 q = biSpace 0 q := by
  apply inf_eq_left.2
  intro P hP
  change mixedLaplacian P = 0
  rw [mixedLaplacian_apply]
  apply Finset.sum_eq_zero
  intro i _
  have commutation (R : SplitPolynomial ι) (a b : ι ⊕ ι) :
      pderiv a (pderiv b R) = pderiv b (pderiv a R) := by
    induction R using MvPolynomial.induction_on with
    | C c => simp
    | add P Q hp hq => simp only [map_add,hp,hq]
    | mul_X P k hp =>
      simp only [pderiv_mul,map_add,hp]
      by_cases hi : a = k <;> by_cases hj : b = k
      · subst a; subst b; rfl
      · subst a; simp [Ne.symm hj]
      · subst b; simp [Ne.symm hi]
      · simp [Ne.symm hi,Ne.symm hj]
  rw [commutation,pderiv_left_zero hP,map_zero]

/-- Exact dimension formula including the holomorphic and antiholomorphic
boundary spaces. The subtracted term is absent there, as in the manuscript. -/
lemma biHarmonic_finrank [Nontrivial ι] (p q : ℕ) :
    Module.finrank ℂ (biHarmonic (ι := ι) p q) =
      (Fintype.card ι+p-1).choose p * (Fintype.card ι+q-1).choose q -
      if p = 0 ∨ q = 0 then 0 else
        (Fintype.card ι+p-2).choose (p-1) * (Fintype.card ι+q-2).choose (q-1) := by
  cases p with
  | zero =>
    rw [biHarmonic_zero_left,biSpace_finrank]
    simp
  | succ p =>
    cases q with
    | zero =>
      rw [biHarmonic_zero_right,biSpace_finrank]
      simp
    | succ q =>
      have he := biHarmonic_finrank_add (ι := ι) p q
      simp only [Nat.succ_ne_zero,false_or,ite_false,Nat.succ_sub_one]
      have hp : Fintype.card ι+p.succ-1 = Fintype.card ι+p := by omega
      have hq : Fintype.card ι+q.succ-1 = Fintype.card ι+q := by omega
      have hp' : Fintype.card ι+p.succ-2 = Fintype.card ι+p-1 := by omega
      have hq' : Fintype.card ι+q.succ-2 = Fintype.card ι+q-1 := by omega
      rw [hp,hq,hp',hq']
      omega

end HarmonicCounterexample.ComplexAngular

end

noncomputable section


namespace HarmonicCounterexample
lemma eigen_dimension_lower {V W:Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (f:V→ₗ[ℝ]W) (hf:Function.Injective f) (T:Module.End ℝ W) (v:ℝ)
    (h:∀x,T (f x)=v • f x) : Module.finrank ℝ V≤Module.finrank ℝ (Module.End.eigenspace T v) := by
  let F := f.codRestrict (Module.End.eigenspace T v) (fun x=>Module.End.mem_eigenspace_iff.mpr (h x))
  exact LinearMap.finrank_le_finrank_of_injective (show Function.Injective F from
    fun x y hxy=>hf (congrArg Subtype.val hxy))
end HarmonicCounterexample

end

noncomputable section


namespace HarmonicCounterexample.Construction
open Module Angular Control ComplexAngular Certificate
open scoped BigOperators

lemma biharmonic_dimension (p q:ℕ) :
    Module.finrank ℂ (biHarmonic (ι:=Fin 8) p q)=hopfMultiplicity p q := by
  rw [biHarmonic_finrank,hopfMultiplicity]
  simp only [Fintype.card_fin]
  congr 1
  · rw [show 8+p-1=p+7 by omega,show 8+q-1=q+7 by omega]
    rw [show (p+7).choose p=(p+7).choose 7 by
          rw [← Nat.choose_symm (show p≤p+7 by omega)];congr 1;omega,
        show (q+7).choose q=(q+7).choose 7 by
          rw [← Nat.choose_symm (show q≤q+7 by omega)];congr 1;omega]
  · split_ifs with h
    · rcases h with rfl|rfl <;> simp
    · have hp : 0<p := Nat.pos_of_ne_zero (fun hp=>h (Or.inl hp))
      have hq : 0<q := Nat.pos_of_ne_zero (fun hq=>h (Or.inr hq))
      rw [show 8+p-2=p+6 by omega,show 8+q-2=q+6 by omega]
      rw [show (p+6).choose (p-1)=(p+6).choose 7 by
            rw [← Nat.choose_symm (show p-1≤p+6 by omega)];congr 1;omega,
          show (q+6).choose (q-1)=(q+6).choose 7 by
            rw [← Nat.choose_symm (show q-1≤q+6 by omega)];congr 1;omega]

lemma biharmonic_real_dimension (p q:ℕ) :
    Module.finrank ℝ (biHarmonic (ι:=Fin 8) p q)=2*hopfMultiplicity p q := by
  rw [← Module.finrank_mul_finrank ℝ ℂ,Complex.finrank_real_complex,biharmonic_dimension]

lemma d0_card (l:ℕ) (v:ℝ) :
    ({i:Index l | d0 l i=v}:Finset (Index l)).card=
      Module.finrank ℝ (Module.End.eigenspace (Dround l).toLinearMap v) := by
  classical
  exact (Dround_symmetric l).card_filter_eigenvalues_eq rfl v

lemma bi_eigenspace_dimension (p q:ℕ) (hpq:p≠q) :
    2*hopfMultiplicity p q ≤ Module.finrank ℝ
      (Module.End.eigenspace
        (rotation ((Berger.ComplexStructure.block 8).reindex finSumFinEquiv.symm) (p+q)*
         rotation ((Berger.ComplexStructure.block 8).reindex finSumFinEquiv.symm) (p+q))
        (-((p:ℝ)-(q:ℝ))^2)) := by
  rw [← biharmonic_real_dimension]
  apply eigen_dimension_lower (biRealCartesian p q) (biRealCartesian_injective hpq)
  intro P
  rw [Module.End.mul_apply]
  have square_eq := biRealCartesian_square p q P
  convert square_eq using 1

lemma eigen_multiplicity (l p q:ℕ) (hl:p+q=l+2) (hpq:p≠q) :
    2*hopfMultiplicity p q ≤ ({i:Index l | d0 l i= -((p:ℝ)-(q:ℝ))^2}:Finset (Index l)).card := by
  classical
  rw [d0_card]
  have h := bi_eigenspace_dimension p q hpq
  rw [hl] at h
  exact h

end HarmonicCounterexample.Construction

end

end OAI
