import OAI.Algebra.AuslanderReiten.Algebras.Radical
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Artinian.Module

namespace OAI

namespace ArExplicit

open TensorProduct

variable {k R S : Type*} [CommRing k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def leftTensorIdeal (I : Ideal R) : Ideal (R ⊗[k] S) :=
  I.map (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S)

theorem mem_leftTensorIdeal_iff (I : Ideal R) (x : R ⊗[k] S) :
    x ∈ leftTensorIdeal (S := S) I ↔
      ∃ z : (I.restrictScalars k) ⊗[k] S,
        LinearMap.rTensor S (I.restrictScalars k).subtype z = x := by
  change x ∈ (leftTensorIdeal I).restrictScalars k ↔ _
  rw [leftTensorIdeal, Ideal.map_includeLeft_eq]
  rfl

theorem tmul_mem_leftTensorIdeal (I : Ideal R) {r : R} (hr : r ∈ I) (s : S) :
    r ⊗ₜ[k] s ∈ leftTensorIdeal (S := S) I := by
  apply (mem_leftTensorIdeal_iff I _).mpr
  exact ⟨⟨r, hr⟩ ⊗ₜ[k] s, rfl⟩

theorem leftTensorIdeal_mul_le (I J : Ideal R) :
    leftTensorIdeal (k := k) (S := S) I * leftTensorIdeal J ≤ leftTensorIdeal (I * J) := by
  apply Ideal.mul_le.mpr
  intro x hx y hy
  obtain ⟨x, rfl⟩ := (mem_leftTensorIdeal_iff I x).mp hx
  obtain ⟨y, rfl⟩ := (mem_leftTensorIdeal_iff J y).mp hy
  clear hx hy
  induction x with
  | add x x' hx hx' => simpa only [map_add, add_mul] using
      (leftTensorIdeal (I * J)).add_mem hx hx'
  | tmul x s =>
      induction y with
      | add y y' hy hy' => simpa only [map_add, mul_add] using
          (leftTensorIdeal (I * J)).add_mem hy hy'
      | tmul y s' =>
          simpa only [LinearMap.rTensor_tmul, Submodule.coe_subtype,
            Algebra.TensorProduct.tmul_mul_tmul] using
            tmul_mem_leftTensorIdeal (I * J) (Ideal.mul_mem_mul x.property y.property) (s * s')

theorem leftTensorIdeal_pow_le (I : Ideal R) (n : ℕ) :
    (leftTensorIdeal (k := k) (S := S) I) ^ n ≤ leftTensorIdeal (I ^ n) := by
  induction n with
  | zero =>
      simp only [Submodule.pow_zero, Ideal.one_eq_top, leftTensorIdeal, Ideal.map_top]
      exact le_rfl
  | succ n hn =>
      rw [Submodule.pow_succ, Submodule.pow_succ]
      exact (Ideal.mul_mono_left hn).trans (leftTensorIdeal_mul_le (I ^ n) I)

theorem leftTensorIdeal_isNilpotent (I : Ideal R) (hI : IsNilpotent I) :
    IsNilpotent (leftTensorIdeal (k := k) (S := S) I) := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  apply le_antisymm _ bot_le
  have h := leftTensorIdeal_pow_le (k := k) (S := S) I n
  simpa only [hn, Ideal.zero_eq_bot, leftTensorIdeal, Ideal.map_bot] using h

def rightTensorIdeal (I : Ideal S) : Ideal (R ⊗[k] S) :=
  I.map (Algebra.TensorProduct.includeRight : S →ₐ[k] R ⊗[k] S)

theorem mem_rightTensorIdeal_iff (I : Ideal S) (x : R ⊗[k] S) :
    x ∈ rightTensorIdeal (R := R) I ↔
      ∃ z : R ⊗[k] (I.restrictScalars k),
        LinearMap.lTensor R (I.restrictScalars k).subtype z = x := by
  change x ∈ (rightTensorIdeal I).restrictScalars k ↔ _
  rw [rightTensorIdeal, Ideal.map_includeRight_eq]
  rfl

theorem tmul_mem_rightTensorIdeal (I : Ideal S) (r : R) {s : S} (hs : s ∈ I) :
    r ⊗ₜ[k] s ∈ rightTensorIdeal (R := R) I := by
  apply (mem_rightTensorIdeal_iff I _).mpr
  exact ⟨r ⊗ₜ[k] ⟨s, hs⟩, rfl⟩

theorem rightTensorIdeal_mul_le (I J : Ideal S) :
    rightTensorIdeal (k := k) (R := R) I * rightTensorIdeal J ≤ rightTensorIdeal (I * J) := by
  apply Ideal.mul_le.mpr
  intro x hx y hy
  obtain ⟨x, rfl⟩ := (mem_rightTensorIdeal_iff I x).mp hx
  obtain ⟨y, rfl⟩ := (mem_rightTensorIdeal_iff J y).mp hy
  clear hx hy
  induction x with
  | add x x' hx hx' => simpa only [map_add, add_mul] using
      (rightTensorIdeal (I * J)).add_mem hx hx'
  | tmul r x =>
      induction y with
      | add y y' hy hy' => simpa only [map_add, mul_add] using
          (rightTensorIdeal (I * J)).add_mem hy hy'
      | tmul r' y =>
          simpa only [LinearMap.lTensor_tmul, Submodule.coe_subtype,
            Algebra.TensorProduct.tmul_mul_tmul] using
            tmul_mem_rightTensorIdeal (I * J) (r * r') (Ideal.mul_mem_mul x.property y.property)

theorem rightTensorIdeal_pow_le (I : Ideal S) (n : ℕ) :
    (rightTensorIdeal (k := k) (R := R) I) ^ n ≤ rightTensorIdeal (I ^ n) := by
  induction n with
  | zero =>
      simp only [Submodule.pow_zero, Ideal.one_eq_top, rightTensorIdeal, Ideal.map_top]
      exact le_rfl
  | succ n hn =>
      rw [Submodule.pow_succ, Submodule.pow_succ]
      exact (Ideal.mul_mono_left hn).trans (rightTensorIdeal_mul_le (I ^ n) I)

theorem rightTensorIdeal_isNilpotent (I : Ideal S) (hI : IsNilpotent I) :
    IsNilpotent (rightTensorIdeal (k := k) (R := R) I) := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  apply le_antisymm _ bot_le
  have h := rightTensorIdeal_pow_le (k := k) (R := R) I n
  simpa only [hn, Ideal.zero_eq_bot, rightTensorIdeal, Ideal.map_bot] using h

theorem finiteAlgebra_radical_isNilpotent [IsArtinianRing k] [Module.Finite k R] :
    IsNilpotent (Ring.jacobson R) := by
  let : IsArtinianRing R := IsArtinianRing.of_finite k R
  exact IsSemiprimaryRing.isNilpotent

variable {R' S' : Type*} [Ring R'] [Ring S'] [Algebra k R'] [Algebra k S']

theorem tensor_radical_eq_kernel (f : R →ₐ[k] R') (g : S →ₐ[k] S')
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hfnil : IsNilpotent (RingHom.ker f)) (hgnil : IsNilpotent (RingHom.ker g))
    (hquot : Ring.jacobson (R' ⊗[k] S') = ⊥) :
    Ring.jacobson (R ⊗[k] S) = RingHom.ker (Algebra.TensorProduct.map f g) := by
  let p : R ⊗[k] S →ₐ[k] R' ⊗[k] S' := Algebra.TensorProduct.map f g
  let : RingHomSurjective p.toRingHom := ⟨Algebra.TensorProduct.map_surjective f g hf hg⟩
  apply le_antisymm
  · intro x hx
    have h := Ring.le_comap_jacobson p.toRingHom hx
    simpa only [hquot, Ideal.mem_comap, Ideal.mem_bot, RingHom.mem_ker, p,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h
  · rw [Algebra.TensorProduct.map_ker f g hf hg]
    exact sup_le
      (nilpotentIdeal_le_jacobson _ (leftTensorIdeal_isNilpotent _ hfnil))
      (nilpotentIdeal_le_jacobson _ (rightTensorIdeal_isNilpotent _ hgnil))

end ArExplicit

end OAI
