import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators TensorProduct

namespace BoundaryOnly.FormalObstruction
namespace MixedForms

variable {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
  [DecidableEq ι]

abbrev Ext := ExteriorAlgebra k (ι → k)
abbrev Forms := A ⊗[k] Ext (k := k) (ι := ι)

def gen (i : ι) : Ext (k := k) (ι := ι) := ExteriorAlgebra.ι k (Pi.single i 1)

def wedge (i : ι) : Module.End k (Ext (k := k) (ι := ι)) :=
  (Algebra.lmul k _).toLinearMap (gen i)

@[simp] theorem wedge_apply (i : ι) (e : Ext (k := k) (ι := ι)) :
    wedge i e = gen i * e := rfl

theorem gen_anticommute (i j : ι) :
    gen (k := k) i * gen j = -(gen j * gen i) := by
  apply eq_neg_iff_add_eq_zero.mpr
  exact ExteriorAlgebra.ι_add_mul_swap _ _

theorem gen_sq (i : ι) : gen (k := k) i * gen i = 0 :=
  ExteriorAlgebra.ι_sq_zero _

                                                         
omit [DecidableEq ι] in
theorem vector_supercommute (v : ι → k) (e : Ext (k := k) (ι := ι)) :
    ExteriorAlgebra.ι k v * e = CliffordAlgebra.involute e * ExteriorAlgebra.ι k v := by
  induction e using ExteriorAlgebra.induction with
  | algebraMap r =>
      rw [AlgHom.commutes]
      exact (Algebra.commutes r _).symm
  | ι u =>
      rw [CliffordAlgebra.involute_ι, neg_mul]
      exact eq_neg_iff_add_eq_zero.mpr (ExteriorAlgebra.ι_add_mul_swap _ _)
  | mul a b ha hb =>
      rw [map_mul, ← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]
  | add a b ha hb => simp only [map_add, mul_add, add_mul, ha, hb]

theorem gen_supercommute (i : ι) (e : Ext (k := k) (ι := ι)) :
    gen i * e = CliffordAlgebra.involute e * gen i :=
  vector_supercommute (Pi.single i 1) e

def parity : Forms (k := k) (A := A) (ι := ι) →ₐ[k] Forms (k := k) (A := A) (ι := ι) :=
  Algebra.TensorProduct.map (AlgHom.id k A) CliffordAlgebra.involute

omit [DecidableEq ι] in
@[simp] theorem parity_tmul (a : A) (e : Ext (k := k) (ι := ι)) :
    parity (a ⊗ₜ[k] e) = a ⊗ₜ[k] CliffordAlgebra.involute e := rfl

omit [DecidableEq ι] in
theorem parity_sq (x : Forms (k := k) (A := A) (ι := ι)) : parity (parity x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a e => simp [CliffordAlgebra.involute_involute]
  | add x y hx hy => simp [hx, hy]

                                                                            
variable [Fintype ι]

def d (pd : ι → Derivation k A A) : Module.End k (Forms (k := k) (A := A) (ι := ι)) :=
  ∑ i, TensorProduct.map (pd i).toLinearMap (wedge i)

@[simp] theorem d_tmul (pd : ι → Derivation k A A) (a : A)
    (e : Ext (k := k) (ι := ι)) :
    d pd (a ⊗ₜ[k] e) = ∑ i, pd i a ⊗ₜ[k] (gen i * e) := by
  simp [d]

theorem d_mul (pd : ι → Derivation k A A)
    (x y : Forms (k := k) (A := A) (ι := ι)) :
    d pd (x * y) = d pd x * y + parity x * d pd y := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ => simp only [add_mul, map_add, hx₁, hx₂]; abel
  | tmul a e =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ hy₁ hy₂ => simp only [mul_add, map_add, hy₁, hy₂]; abel
      | tmul b f =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul, d_tmul, parity_tmul,
            Derivation.leibniz, smul_eq_mul, TensorProduct.add_tmul,
            Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib]
          rw [add_comm]
          congr 1 <;> apply Finset.sum_congr rfl <;> intro i _
          · rw [mul_comm b, mul_assoc]
          · rw [← mul_assoc, gen_supercommute i e, mul_assoc]

theorem d_parity (pd : ι → Derivation k A A)
    (x : Forms (k := k) (A := A) (ι := ι)) :
    d pd (parity x) = -(parity (d pd x)) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, neg_add_rev]; abel
  | tmul a e =>
      simp only [parity_tmul, d_tmul, map_sum, map_mul,
        gen, CliffordAlgebra.involute_ι, neg_mul, TensorProduct.tmul_neg,
        Finset.sum_neg_distrib, neg_neg]

                                                       
def gradient (pd : ι → Derivation k A A) (F : A) :
    Forms (k := k) (A := A) (ι := ι) := d pd (F ⊗ₜ[k] 1)

def delta (pd : ι → Derivation k A A) (F : A) :
    Module.End k (Forms (k := k) (A := A) (ι := ι)) :=
  (Algebra.lmul k _).toLinearMap (gradient pd F)

@[simp] theorem delta_apply (pd : ι → Derivation k A A) (F : A)
    (x : Forms (k := k) (A := A) (ι := ι)) :
    delta pd F x = gradient pd F * x := rfl

                                                                                 
omit [DecidableEq ι] in
theorem antisymmetric_sum {M : Type*} [AddCommGroup M] (f : ι → ι → M)
    (hd : ∀ i, f i i = 0) (ha : ∀ i j, f i j + f j i = 0) :
    ∑ i, ∑ j, f i j = 0 := by
  rw [← Finset.sum_product']
  apply Finset.sum_involution (fun ij _ => (ij.2, ij.1))
  · intro ij _; exact ha _ _
  · intro ij _ hn he
    have heq : ij.2 = ij.1 := congrArg Prod.fst he
    exact hn (by simpa only [heq] using hd ij.1)
  · intro ij _; simp
  · intro ij _; rfl

                                                                                      
theorem d_sq (pd : ι → Derivation k A A)
    (hcomm : ∀ i j a, pd i (pd j a) = pd j (pd i a))
    (x : Forms (k := k) (A := A) (ι := ι)) : d pd (d pd x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul a e =>
      simp only [d_tmul, map_sum]
      apply antisymmetric_sum
      · intro i
        rw [← mul_assoc, gen_sq, zero_mul, TensorProduct.tmul_zero]
      · intro i j
        rw [hcomm j i, ← mul_assoc, gen_anticommute j i, neg_mul,
          TensorProduct.tmul_neg, ← mul_assoc, neg_add_cancel]

                                                                                    
theorem oneform_sq (v : ι → A) :
    (∑ i, v i ⊗ₜ[k] gen (k := k) i) * (∑ i, v i ⊗ₜ[k] gen (k := k) i) = 0 := by
  simp only [Finset.sum_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul]
  apply antisymmetric_sum
  · intro i; rw [gen_sq, TensorProduct.tmul_zero]
  · intro i j
    rw [mul_comm (v j), gen_anticommute j i, TensorProduct.tmul_neg, neg_add_cancel]

@[simp] theorem gradient_eq (pd : ι → Derivation k A A) (F : A) :
    gradient pd F = ∑ i, pd i F ⊗ₜ[k] gen (k := k) i := by
  simp only [gradient, d_tmul, mul_one]

@[simp] theorem parity_gradient (pd : ι → Derivation k A A) (F : A) :
    parity (gradient pd F) = -gradient pd F := by
  simp only [gradient_eq, map_sum, parity_tmul, gen, CliffordAlgebra.involute_ι,
    TensorProduct.tmul_neg, Finset.sum_neg_distrib]

theorem delta_sq (pd : ι → Derivation k A A) (F : A)
    (x : Forms (k := k) (A := A) (ι := ι)) : delta pd F (delta pd F x) = 0 := by
  simp only [delta_apply, ← mul_assoc, gradient_eq, oneform_sq, zero_mul]

                                                         
theorem d_delta (pd : ι → Derivation k A A)
    (hcomm : ∀ i j a, pd i (pd j a) = pd j (pd i a))
    (F : A) (x : Forms (k := k) (A := A) (ι := ι)) :
    d pd (delta pd F x) + delta pd F (d pd x) = 0 := by
  rw [delta_apply, d_mul, parity_gradient]
  have hz : d pd (gradient pd F) = 0 := d_sq pd hcomm _
  rw [hz, zero_mul, zero_add, neg_mul, delta_apply, neg_add_cancel]

                                                           
omit [Fintype ι] [DecidableEq ι] in
theorem constant_commute (F : A) (x : Forms (k := k) (A := A) (ι := ι)) :
    (F ⊗ₜ[k] (1 : Ext (k := k) (ι := ι))) * x =
      x * (F ⊗ₜ[k] (1 : Ext (k := k) (ι := ι))) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [mul_add, add_mul, hx, hy]
  | tmul a e => simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, mul_comm F a]

                                                             
theorem d_commutator (pd : ι → Derivation k A A) (p : A)
    (x : Forms (k := k) (A := A) (ι := ι)) :
    d pd ((p ⊗ₜ[k] 1) * x) - (p ⊗ₜ[k] 1) * d pd x = delta pd p x := by
  rw [d_mul, parity_tmul, map_one, add_sub_cancel_right]
  rfl

                                                                                   
theorem oneform_supercommute (v : ι → A) (x : Forms (k := k) (A := A) (ι := ι)) :
    (∑ i, v i ⊗ₜ[k] gen (k := k) i) * x =
      parity x * (∑ i, v i ⊗ₜ[k] gen (k := k) i) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [mul_add, map_add, add_mul, hx, hy]
  | tmul a e =>
    simp only [Finset.sum_mul, parity_tmul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm (v i), gen_supercommute]

theorem gradient_supercommute (pd : ι → Derivation k A A) (F : A)
    (x : Forms (k := k) (A := A) (ι := ι)) :
    gradient pd F * x = parity x * gradient pd F := by
  rw [gradient_eq]
  exact oneform_supercommute _ _

theorem gradient_sq (pd : ι → Derivation k A A) (F : A) :
    gradient pd F * gradient pd F = 0 := by
  rw [gradient_eq]
  exact oneform_sq _

                                                                           
def coeff : A →+* Forms (k := k) (A := A) (ι := ι) :=
  Algebra.TensorProduct.includeLeftRingHom

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem coeff_apply (a : A) : coeff (k := k) (ι := ι) a = a ⊗ₜ[k] 1 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem parity_coeff (a : A) : parity (coeff (k := k) (ι := ι) a) = coeff a := by
  simp only [coeff_apply, parity_tmul, map_one]

omit [Fintype ι] [DecidableEq ι] in
theorem coeff_commute (a : A) (x : Forms (k := k) (A := A) (ι := ι)) :
    coeff a * x = x * coeff a := constant_commute a x

@[simp] theorem d_coeff (pd : ι → Derivation k A A) (a : A) :
    d pd (coeff (k := k) (ι := ι) a) = gradient pd a := rfl

                                                                                
def cartier (pd : ι → Derivation k A A) (n : ℕ) (u : A) :
    Forms (k := k) (A := A) (ι := ι) := coeff (u ^ n) * gradient pd u

@[simp] theorem parity_cartier (pd : ι → Derivation k A A) (n : ℕ) (u : A) :
    parity (cartier pd n u) = -cartier pd n u := by
  simp only [cartier, map_mul, parity_coeff, parity_gradient, mul_neg]

theorem gradient_mul_cartier (pd : ι → Derivation k A A) (n : ℕ) (u : A) :
    gradient pd u * cartier pd n u = 0 := by
  rw [cartier, ← mul_assoc, ← coeff_commute, mul_assoc, gradient_sq, mul_zero]

theorem d_cartier (pd : ι → Derivation k A A)
    (hcomm : ∀ i j a, pd i (pd j a) = pd j (pd i a)) (n : ℕ) (u : A) :
    d pd (cartier pd n u) = 0 := by
  induction n with
  | zero =>
      simp only [cartier, pow_zero, map_one, one_mul, gradient]
      exact d_sq pd hcomm _
  | succ n ih =>
      have hs : cartier pd (n+1) u = coeff u * cartier pd n u := by
        simp only [cartier, pow_succ', map_mul, mul_assoc]
      rw [hs, d_mul, d_coeff, gradient_mul_cartier, ih, mul_zero, add_zero]

                                                           
def normal (pd : ι → Derivation k A A) (n : ℕ) (us : List A) :
    Forms (k := k) (A := A) (ι := ι) := (us.map (cartier pd n)).prod

@[simp] theorem normal_nil (pd : ι → Derivation k A A) (n : ℕ) : normal pd n [] = 1 := rfl
@[simp] theorem normal_cons (pd : ι → Derivation k A A) (n : ℕ) (u : A) (us : List A) :
    normal pd n (u :: us) = cartier pd n u * normal pd n us := rfl

theorem d_one (pd : ι → Derivation k A A) :
    d pd (1 : Forms (k := k) (A := A) (ι := ι)) = 0 := by
  change d pd ((1 : A) ⊗ₜ[k] (1 : Ext (k := k) (ι := ι))) = 0
  simp only [d_tmul, Derivation.map_one_eq_zero, TensorProduct.zero_tmul, Finset.sum_const_zero]

theorem d_normal (pd : ι → Derivation k A A)
    (hcomm : ∀ i j a, pd i (pd j a) = pd j (pd i a)) (n : ℕ) (us : List A) :
    d pd (normal pd n us) = 0 := by
  induction us with
  | nil => exact d_one pd
  | cons u us ih => rw [normal_cons, d_mul, d_cartier pd hcomm, ih, zero_mul, mul_zero, add_zero]

theorem coeff_mul_normal (pd : ι → Derivation k A A) (n : ℕ) (us : List A)
    (hpow : ∀ u ∈ us, u^(n+1) = 0) (u : A) (hu : u ∈ us) :
    coeff u * normal pd n us = 0 := by
  induction us with
  | nil => simp at hu
  | cons a us ih =>
    rw [List.mem_cons] at hu
    rcases hu with rfl | hu
    · have hz : coeff u * cartier pd n u = 0 := by
        rw [cartier, ← mul_assoc, ← map_mul, ← pow_succ', hpow u (by simp), map_zero, zero_mul]
      rw [normal_cons, ← mul_assoc, hz, zero_mul]
    · rw [normal_cons, ← mul_assoc, coeff_commute u (cartier pd n a), mul_assoc,
        ih (fun v hv => hpow v (List.mem_cons_of_mem a hv)) hu, mul_zero]

theorem gradient_mul_normal (pd : ι → Derivation k A A) (n : ℕ) (us : List A)
    (u : A) (hu : u ∈ us) : gradient pd u * normal pd n us = 0 := by
  induction us with
  | nil => simp at hu
  | cons a us ih =>
    rw [List.mem_cons] at hu
    rcases hu with rfl | hu
    · rw [normal_cons, ← mul_assoc, gradient_mul_cartier, zero_mul]
    · rw [normal_cons, ← mul_assoc, gradient_supercommute, parity_cartier]
      simp only [neg_mul, mul_assoc, ih hu, mul_zero, neg_zero]

theorem coeff_mul_normal_ideal (pd : ι → Derivation k A A) (n : ℕ) (us : List A)
    (hpow : ∀ u ∈ us, u^(n+1) = 0) (F : A)
    (hF : F ∈ Ideal.span {u | u ∈ us}) : coeff F * normal pd n us = 0 := by
  induction hF using Submodule.span_induction with
  | mem u hu => exact coeff_mul_normal pd n us hpow u hu
  | zero => rw [map_zero, zero_mul]
  | add a b ha hb hga hgb => rw [map_add, add_mul, hga, hgb, add_zero]
  | smul a b hb hgb =>
      change coeff (a*b) * normal pd n us = 0
      rw [map_mul, mul_assoc, hgb, mul_zero]

                                                                                     
theorem delta_normal (pd : ι → Derivation k A A) (n : ℕ) (us : List A)
    (hpow : ∀ u ∈ us, u^(n+1) = 0) (F : A)
    (hF : F ∈ Ideal.span {u | u ∈ us}) : delta pd F (normal pd n us) = 0 := by
  change gradient pd F * normal pd n us = 0
  induction hF using Submodule.span_induction with
  | mem u hu => exact gradient_mul_normal pd n us u hu
  | zero => simp [gradient]
  | add a b ha hb hga hgb =>
      simp only [gradient, map_add, TensorProduct.add_tmul, add_mul] at *
      rw [hga, hgb, add_zero]
  | smul a b hb hgb =>
      change gradient pd (a*b) * normal pd n us = 0
      have hgrad : gradient pd (a*b) =
          gradient pd a * coeff b + coeff a * gradient pd b := by
        change d pd (coeff (k := k) (ι := ι) (a*b)) = _
        rw [map_mul, d_mul, parity_coeff, d_coeff, d_coeff]
      rw [hgrad, add_mul, mul_assoc, coeff_mul_normal_ideal pd n us hpow b hb, mul_zero, mul_assoc, hgb,
        mul_zero, add_zero]

                                                                    
def contract (i : ι) : Module.End k (Forms (k := k) (A := A) (ι := ι)) :=
  TensorProduct.map LinearMap.id (CliffordAlgebra.contractLeft (LinearMap.proj i))

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem contract_tmul (i : ι) (a : A) (e : Ext (k := k) (ι := ι)) :
    contract i (a ⊗ₜ[k] e) = a ⊗ₜ[k] CliffordAlgebra.contractLeft (LinearMap.proj i) e := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem contract_coeff (i : ι) (a : A) (x : Forms (k := k) (A := A) (ι := ι)) :
    contract i (coeff a * x) = coeff a * contract i x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]
  | tmul b e => simp only [coeff_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      contract_tmul]

theorem contraction_identity (pd : ι → Derivation k A A) (F : A) (i : ι)
    (x : Forms (k := k) (A := A) (ι := ι)) :
    delta pd F (contract i x) + contract i (delta pd F x) = coeff (pd i F) * x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, mul_add] at *; rw [add_add_add_comm, hx, hy]
  | tmul a e =>
      simp only [delta_apply, gradient_eq, contract_tmul, Finset.sum_mul,
        Algebra.TensorProduct.tmul_mul_tmul, map_sum, gen,
        CliffordAlgebra.contractLeft_ι_mul, LinearMap.proj_apply,
        TensorProduct.tmul_sub, TensorProduct.tmul_smul]
      simp only [← Finset.sum_add_distrib]
      try simp only [add_sub_cancel_left]
      simp [Pi.single_apply, coeff_apply]

                                                                                 
theorem ambient_primitive (pd : ι → Derivation k A A) (F : A)
    (x : Forms (k := k) (A := A) (ι := ι)) (g : A) (h : ι → A)
    (hcycle : delta pd F x = 0)
    (herror : coeff (g - ∑ i, h i * pd i F) * x = 0) :
    coeff g * x = delta pd F (∑ i, coeff (h i) * contract i x) := by
  have hc (i : ι) : delta pd F (contract i x) = coeff (pd i F) * x := by
    simpa only [hcycle, map_zero, add_zero] using contraction_identity pd F i x
  have hx : coeff g * x = coeff (∑ i, h i * pd i F) * x := by
    apply sub_eq_zero.mp
    simpa only [map_sub, sub_mul] using herror
  rw [hx, map_sum, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, mul_assoc, ← hc i, delta_apply, delta_apply, ← mul_assoc,
    coeff_commute (h i) (gradient pd F), mul_assoc]

                                                                          
                                                
theorem normal_primitive (pd : ι → Derivation k A A) (n : ℕ) (us : List A)
    (hpow : ∀ u ∈ us, u^(n+1) = 0) (F g : A) (h : ι → A)
    (hF : F ∈ Ideal.span {u | u ∈ us})
    (hg : g - ∑ i, h i * pd i F ∈ Ideal.span {u | u ∈ us}) :
    coeff g * normal pd n us =
      delta pd F (∑ i, coeff (h i) * contract i (normal pd n us)) :=
  ambient_primitive pd F _ g h (delta_normal pd n us hpow F hF)
    (coeff_mul_normal_ideal pd n us hpow _ hg)

end MixedForms
end BoundaryOnly.FormalObstruction

end
end

end OAI
