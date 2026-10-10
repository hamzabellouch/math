import Mathlib
import OAI.Algebra.FiniteTensor.ExteriorForms
import OAI.Algebra.FiniteTensor.FrobeniusQuotient
import OAI.Algebra.FiniteTensor.SquarefreeParameters

namespace OAI

/-! First-order Koszul equations and lifting of truncated differential-form cycles. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor
noncomputable section
open scoped TensorProduct

variable {K R V : Type*} [Field K] [CommRing R] [Algebra K R]
variable [AddCommGroup V] [Module K V]

 

def firstOrderKoszul (δ d b : V →ₗ[K] V) (t : R) :
    R ⊗[K] V →ₗ[K] R ⊗[K] V :=
  TensorProduct.map LinearMap.id δ +
    TensorProduct.map (LinearMap.mulLeft K t) (d.comp b - b.comp d)

 

theorem firstOrder_lift (δ d b : V →ₗ[K] V)
    (hdδ : d.comp δ = -(δ.comp d)) (hbδ : b.comp δ = δ.comp b)
    (a β γ : V) (ha : δ a = 0) (hβ : d a = δ β) (hγ : b a = δ γ)
    (t : R) (ht : t * t = 0) :
    firstOrderKoszul δ d b t
      ((1 : R) ⊗ₜ[K] a + t ⊗ₜ[K] (d γ + b β)) = 0 := by
  have hcorr : δ (d γ + b β) + (d (b a) - b (d a)) = 0 := by
    have hd := LinearMap.congr_fun hdδ γ
    have hb := LinearMap.congr_fun hbδ β
    simp only [LinearMap.comp_apply, LinearMap.neg_apply] at hd hb
    rw [hγ, hβ, hd, hb, map_add]
    abel
  simp only [firstOrderKoszul, LinearMap.add_apply, map_add,
    TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, ha, TensorProduct.tmul_zero,
    ht, TensorProduct.zero_tmul, mul_one, zero_add, add_zero]
  rw [← TensorProduct.tmul_add, ← map_add δ, add_comm, hcorr, TensorProduct.tmul_zero]

end
end PD4Tensor

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped TensorProduct BigOperators
open Forms
variable (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ] (p : ℕ)
  [CharP K p] [Invertible (2 : K)]
abbrev A := FrobeniusTruncation.Ring K σ p
abbrev Space := Ω K (A K σ p) σ

def D : Space K σ p →ₗ[K] Space K σ p :=
  differential K (A K σ p) σ (FrobeniusTruncation.derivative K σ p)

def koszul (S : A K σ p) : Space K σ p →ₗ[K] Space K σ p :=
  LinearMap.mulLeft K (D K σ p (scalar K (A K σ p) σ S))

def mulScalar (b : A K σ p) : Space K σ p →ₗ[K] Space K σ p :=
  LinearMap.mulLeft K (scalar K (A K σ p) σ b)

def residueForm (hp : 0<p) (ell : E K σ →ₗ[K] K) : Space K σ p →ₗ[K] K :=
  (TensorProduct.lid K K).toLinearMap.comp
    (TensorProduct.map (FrobeniusTruncation.residue K σ p hp) ell)

omit [DecidableEq σ] [CharP K p] [Invertible (2 : K)] in
@[simp] theorem residueForm_tmul (hp : 0<p) (ell : E K σ →ₗ[K] K)
    (a : A K σ p) (e : E K σ) :
    residueForm K σ p hp ell (a ⊗ₜ[K] e) = FrobeniusTruncation.residue K σ p hp a * ell e := by
  simp [residueForm, smul_eq_mul]

 
omit [Invertible (2 : K)] in
theorem stokes (hp : 0<p) (ell : E K σ →ₗ[K] K) (ω : Space K σ p) :
    residueForm K σ p hp ell (D K σ p ω) = 0 := by
  induction ω using TensorProduct.inductionOn with
  | add a b ha hb => simp [ha, hb]
  | tmul a e =>
    simp [D, differential_tmul, FrobeniusTruncation.residue_derivative]

@[simp] theorem D_sq_zero (ω : Space K σ p) : D K σ p (D K σ p ω) = 0 :=
  differential_sq_zero _ (FrobeniusTruncation.derivative_commute K σ p) ω

omit [Invertible (2 : K)] in
theorem D_mul (ω η : Space K σ p) :
    D K σ p (ω*η) = D K σ p ω * η + parity K (A K σ p) σ ω * D K σ p η :=
  differential_mul _ (FrobeniusTruncation.derivative_mul K σ p) ω η

 
omit [Invertible (2 : K)] in
theorem closed_mul_exact_residue (hp : 0<p) (ell : E K σ →ₗ[K] K)
    (ω η : Space K σ p) (hω : D K σ p ω = 0) :
    residueForm K σ p hp ell (ω * D K σ p η) = 0 := by
  have h := stokes K σ p hp ell (parity K (A K σ p) σ ω * η)
  rw [D_mul, show D K σ p (parity K (A K σ p) σ ω) = 0 by
    rw [D, differential_parity, ← D, hω, map_zero, neg_zero], zero_mul, zero_add,
    parity_parity] at h
  exact h

@[simp] theorem koszul_sq_zero (S : A K σ p) (ω : Space K σ p) :
    koszul K σ p S (koszul K σ p S ω) = 0 := by
  change (D K σ p (scalar K (A K σ p) σ S)) *
    ((D K σ p (scalar K (A K σ p) σ S)) * ω) = 0
  rw [← mul_assoc, D, differential_scalar, oneForm_sq_zero, zero_mul]

 
theorem D_koszul (S : A K σ p) :
    (D K σ p).comp (koszul K σ p S) = -((koszul K σ p S).comp (D K σ p)) := by
  apply LinearMap.ext
  intro ω
  change D K σ p (_*ω) = -(_*D K σ p ω)
  rw [D_mul, D_sq_zero, zero_mul, zero_add, D, differential_scalar,
    parity_oneForm, neg_mul]

omit [Invertible (2 : K)] in
theorem mulScalar_koszul (S b : A K σ p) :
    (mulScalar K σ p b).comp (koszul K σ p S) =
      (koszul K σ p S).comp (mulScalar K σ p b) := by
  apply LinearMap.ext
  intro ω
  change _*(_*ω) = _*(_*ω)
  rw [← mul_assoc, ← mul_assoc, scalar_commute]

 
omit [Invertible (2 : K)] in
theorem D_mulScalar (b : A K σ p) :
    (D K σ p).comp (mulScalar K σ p b) - (mulScalar K σ p b).comp (D K σ p) =
      koszul K σ p b := by
  apply LinearMap.ext
  intro ω
  change D K σ p (_*ω) - _*D K σ p ω = _*ω
  rw [D_mul, parity_scalar, add_sub_cancel_right]

 
theorem lift_cycle {R : Type*} [CommRing R] [Algebra K R]
    (S b : A K σ p) (a β γ : Space K σ p)
    (ha : koszul K σ p S a=0) (hβ : D K σ p a = koszul K σ p S β)
    (hγ : mulScalar K σ p b a = koszul K σ p S γ) (t : R) (ht : t*t=0) :
    (TensorProduct.map (LinearMap.id : R →ₗ[K] R) (koszul K σ p S) +
      TensorProduct.map (LinearMap.mulLeft K t) (koszul K σ p b))
        ((1 : R) ⊗ₜ[K] a + t ⊗ₜ[K] (D K σ p γ + mulScalar K σ p b β)) = 0 := by
  have h := firstOrder_lift (koszul K σ p S) (D K σ p) (mulScalar K σ p b)
    (D_koszul K σ p S) (mulScalar_koszul K σ p S b) a β γ ha hβ hγ t ht
  simpa only [firstOrderKoszul, D_mulScalar] using h

end
end PD4Tensor.TruncatedForms
end

end OAI
