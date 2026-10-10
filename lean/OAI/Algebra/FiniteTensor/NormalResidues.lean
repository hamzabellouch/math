import Mathlib
import OAI.Algebra.FiniteTensor.MovingCoordinates
import OAI.Algebra.FiniteTensor.RelativeDerivatives

namespace OAI

/-! Normal-cycle residues, restricted gradients and nonzero exterior pairings. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Forms
noncomputable section
open scoped TensorProduct BigOperators
variable (K A : Type*) [Field K] [CommRing A] [Algebra K A]
variable (σ : Type*) [Fintype σ] [DecidableEq σ]
variable (der : σ → A →ₗ[K] A) (p : ℕ)

theorem normalCycle_product (cs : List A) :
    normalCycle K A σ der p cs =
      scalar K A σ (cs.map (fun c => c^(p-1))).prod *
        (cs.map (fun c => differential K A σ der (scalar K A σ c))).prod := by
  induction cs with
  | nil => simp [normalCycle]
  | cons c cs ih =>
    change (scalar K A σ (c^(p-1)) * differential K A σ der (scalar K A σ c)) *
      normalCycle K A σ der p cs = _
    rw [ih]
    simp only [List.map_cons, List.prod_cons, scalar_mul]
    rw [mul_assoc, ← mul_assoc (differential K A σ der (scalar K A σ c)),
      ← scalar_commute, mul_assoc, ← mul_assoc]

variable [Invertible (2 : K)]
theorem topCoefficient_normalCycle (N : ℕ) (der : Fin N → A →ₗ[K] A)
    (c : Fin N → A) :
    topCoefficient K A N (normalCycle K A (Fin N) der p (List.ofFn c)) =
      (∏ i, c i^(p-1)) * Matrix.det (fun i j => der j (c i)) := by
  rw [normalCycle_product]
  have hscalar (a : A) (ω : Ω K A (Fin N)) : scalar K A (Fin N) a * ω = a • ω := by
    induction ω using TensorProduct.inductionOn with
    | add x y hx hy => simp [mul_add, smul_add, hx, hy]
    | tmul b e => simp [scalar, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
  rw [hscalar, map_smul, smul_eq_mul]
  simp only [List.map_ofFn, Function.comp_def, List.prod_ofFn, differential_scalar]
  rw [topCoefficient_oneForm_product]

end
end PD4Tensor.Forms

namespace PD4Tensor.FrobeniusTruncation
noncomputable section
open scoped TensorProduct BigOperators
variable (K : Type*) [Field K] (N p : ℕ) [CharP K p] [Fact p.Prime]
  [Invertible (2 : K)]

 

theorem exterior_normal_residue (hp : 0 < p) (f : Fin N → MvPolynomial (Fin N) K)
    (hf : ∀ i, MvPolynomial.constantCoeff (f i)=0) :
    residue K (Fin N) p hp
      (Forms.topCoefficient K (Ring K (Fin N) p) N
        (Forms.normalCycle K (Ring K (Fin N) p) (Fin N) (derivative K (Fin N) p) p
          (List.ofFn (fun i => Ideal.Quotient.mk (ideal K (Fin N) p) (f i))))) =
      (tangentMatrix K (Fin N) f).det^p := by
  rw [Forms.topCoefficient_normalCycle]
  simp only [derivative_mk]
  have hj : Matrix.det (fun i j => Ideal.Quotient.mk (ideal K (Fin N) p)
      (MvPolynomial.pderiv j (f i))) =
      Ideal.Quotient.mk (ideal K (Fin N) p) (jacobianDet K (Fin N) f) :=
    (RingHom.map_det (Ideal.Quotient.mk (ideal K (Fin N) p)) _).symm
  rw [hj]
  exact normal_residue K (Fin N) p hp f hf

 
theorem exterior_normal_residue_ne_zero (hp : 0 < p) (f : Fin N → MvPolynomial (Fin N) K)
    (hf : ∀ i, MvPolynomial.constantCoeff (f i)=0)
    (hdet : (tangentMatrix K (Fin N) f).det ≠ 0) :
    residue K (Fin N) p hp
      (Forms.topCoefficient K (Ring K (Fin N) p) N
        (Forms.normalCycle K (Ring K (Fin N) p) (Fin N) (derivative K (Fin N) p) p
          (List.ofFn (fun i => Ideal.Quotient.mk (ideal K (Fin N) p) (f i))))) ≠ 0 := by
  rw [exterior_normal_residue K N p hp f hf]
  exact pow_ne_zero _ hdet

end
end PD4Tensor.FrobeniusTruncation

namespace PD4Tensor.Forms
noncomputable section
open scoped TensorProduct BigOperators
variable {K A B σ : Type*} [Field K] [CommRing A] [Algebra K A]
  [CommRing B] [Algebra K B] [Fintype σ] [DecidableEq σ]

 

theorem restricted_gradient_boundary (r : A →ₐ[K] B) (hr : Function.Surjective r)
    (v : σ → A) (ω : Ω K A σ) (hω : oneForm K A σ v * ω=0)
    (hann : ∀ a, r a=0 → scalar K A σ a * ω=0)
    (a : A) (ha : r a∈Ideal.span (Set.range (fun i => r (v i)))) :
    scalar K A σ a * ω∈LinearMap.range (LinearMap.mulLeft K (oneForm K A σ v)) := by
  obtain ⟨b,hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp ha
  choose c hc using fun i => hr (b i)
  let a' : A := ∑ i, c i * v i
  have he : r (a-a')=0 := by
    simp only [a',map_sub,map_sum,map_mul,hc]
    rw [hb,sub_self]
  have heq : scalar K A σ a * ω=scalar K A σ a' * ω := by
    have h := hann (a-a') he
    simpa only [map_sub,scalar,TensorProduct.sub_tmul,sub_mul,sub_eq_zero] using h
  rw [heq]
  apply gradient_ideal_boundary v ω hω a'
  exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨c,rfl⟩

end
end PD4Tensor.Forms

namespace PD4Tensor.FrobeniusTruncation
noncomputable section
variable (K : Type*) [Field K] (N p : ℕ) [CharP K p] [Fact p.Prime]
  [Invertible (2 : K)]

 

theorem inverse_normal_residue_ne_zero
    (q : Ring K (Fin N) p ≃ₐ[K] Ring K (Fin N) p) :
    residue K (Fin N) p (Fact.out : p.Prime).pos
      (Forms.topCoefficient K (Ring K (Fin N) p) N
        (Forms.normalCycle K (Ring K (Fin N) p) (Fin N) (derivative K (Fin N) p) p
          (List.ofFn (fun i => q (coord K (Fin N) p i)))))≠0 := by
  choose f hf using fun i => Ideal.Quotient.mk_surjective (q (coord K (Fin N) p i))
  have hh := inverse_representatives K (Fin N) p q f hf
  have hr := exterior_normal_residue_ne_zero K N p (Fact.out : p.Prime).pos f hh.1 hh.2
  simpa only [hf] using hr

end
end PD4Tensor.FrobeniusTruncation

namespace PD4Tensor.Forms
noncomputable section
variable (K A σ : Type*) [Field K] [CommRing A] [Algebra K A] [Fintype σ] [DecidableEq σ]
  (der : σ → A →ₗ[K] A) (p : ℕ)

@[simp] theorem normalCycle_append (cs ds : List A) :
    normalCycle K A σ der p (cs++ds)=normalCycle K A σ der p cs * normalCycle K A σ der p ds := by
  simp [normalCycle,List.prod_append]

end
end PD4Tensor.Forms
end

end OAI
