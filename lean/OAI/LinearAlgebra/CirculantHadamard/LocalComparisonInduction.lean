import OAI.LinearAlgebra.CirculantHadamard.CyclicProjection
import OAI.LinearAlgebra.CirculantHadamard.CyclicScalarDivision
import OAI.LinearAlgebra.CirculantHadamard.ResidueOneAssociation
import Mathlib.Algebra.Prime.Defs

namespace OAI

universe uA uS

noncomputable section

namespace CirculantHadamard.LocalComparison

open CyclicRing

variable {A : Type uA} {S : Type uS} [CommRing A] [IsDomain A]
  [CommRing S] [domainS : IsDomain S] [IsLocalRing S]

/-- If the product has exactly one prime factor up to a unit, at least one
factor is a unit. This elementary base step does not use a valuation. -/
theorem isUnit_or_isUnit_of_mul_prime_unit {p x y : A} (hp : Prime p)
    (b : Aˣ) (hxy : x * y = p * (b : A)) : IsUnit x ∨ IsUnit y := by
  have hdvd : p ∣ x * y := ⟨(b : A), hxy⟩
  rcases hp.dvd_or_dvd hdvd with hx | hy
  · obtain ⟨z, hz⟩ := hx
    have hzy : z * y = (b : A) := by
      apply mul_left_cancel₀ hp.ne_zero
      calc
        p * (z * y) = (p * z) * y := (mul_assoc _ _ _).symm
        _ = x * y := by rw [← hz]
        _ = p * (b : A) := hxy
    exact Or.inr (isUnit_of_mul_isUnit_right (hzy.symm ▸ b.isUnit))
  · obtain ⟨z, hz⟩ := hy
    have hxz : x * z = (b : A) := by
      apply mul_left_cancel₀ hp.ne_zero
      calc
        p * (x * z) = x * (p * z) := by ac_rfl
        _ = x * y := by rw [← hz]
        _ = p * (b : A) := hxy
    exact Or.inl (isUnit_of_mul_isUnit_left (hxz.symm ▸ b.isUnit))

/-- Both augmentations in the comparison theorem are nonzero. -/
theorem augmentation_ne_zero_of_scalar_product {p : ℕ} {e : ℕ}
    (hp : (p : A) ≠ 0) (b : Aˣ) (F K : Elem A (p ^ e))
    (hFK : F * K = scalar (p ^ e) ((p : A) ^ e * (b : A))) :
    augmentation (p ^ e) F ≠ 0 ∧ augmentation (p ^ e) K ≠ 0 := by
  have haug : augmentation (p ^ e) F * augmentation (p ^ e) K =
      (p : A) ^ e * (b : A) := by
    simpa only [map_mul, augmentation_scalar] using
      congrArg (augmentation (p ^ e)) hFK
  have hne : augmentation (p ^ e) F * augmentation (p ^ e) K ≠ 0 := by
    rw [haug]
    exact mul_ne_zero (pow_ne_zero _ hp) b.ne_zero
  exact mul_ne_zero_iff.mp hne

/-- The exponent-one base case, using the actual residue field of `S`. -/
theorem comparison_base (n p : ℕ) (φ : A →+* S) (hp : Prime (p : A))
    (hpS : φ (p : A) ≠ 0)
    (v : Elem A n →+* S)
    (vscalar : ∀ a : A, v (scalar n a) = φ a)
    (vres : ∀ F : Elem A n,
      IsLocalRing.residue S (v F) =
        IsLocalRing.residue S (φ (augmentation n F)))
    (b : Aˣ) (F K : Elem A n)
    (hFK : F * K = scalar n ((p : A) * (b : A))) :
    ResidueOneAssociated (IsLocalRing.residue S) (v F) (φ (augmentation n F)) ∧
      ResidueOneAssociated (IsLocalRing.residue S) (v K) (φ (augmentation n K)) := by
  have haug : augmentation n F * augmentation n K = (p : A) * (b : A) := by
    simpa only [map_mul, augmentation_scalar] using congrArg (augmentation n) hFK
  have hv : v F * v K = φ ((p : A) * (b : A)) := by
    simpa only [map_mul, vscalar] using congrArg v hFK
  have hprod : v F * v K = φ (augmentation n F) * φ (augmentation n K) := by
    calc
      v F * v K = φ ((p : A) * (b : A)) := hv
      _ = φ (augmentation n F * augmentation n K) := congrArg φ haug.symm
      _ = φ (augmentation n F) * φ (augmentation n K) := φ.map_mul _ _
  have hne : φ (augmentation n F) * φ (augmentation n K) ≠ 0 := by
    rw [← map_mul, haug, map_mul]
    exact mul_ne_zero hpS (b.isUnit.map φ).ne_zero
  rcases isUnit_or_isUnit_of_mul_prime_unit hp b haug with hF | hK
  · have h := residueOneAssociated_of_isUnit_residue_eq (hF.map φ) (vres F)
    exact ⟨h, h.product_complement hprod hne⟩
  · have h := residueOneAssociated_of_isUnit_residue_eq (hK.map φ) (vres K)
    have hprod' : v K * v F = φ (augmentation n K) * φ (augmentation n F) := by
      simpa only [mul_comm] using hprod
    have hne' : φ (augmentation n K) * φ (augmentation n F) ≠ 0 := by
      simpa only [mul_comm] using hne
    exact ⟨h.product_complement hprod' hne', h⟩

omit domainS in
/-- Induction step when the first projected factor is divisible by `p`.
The other factor is left intact. The two output associations are both
transported, so the next step may divide either factor. -/
theorem comparison_step_left [IsDomain S] (p e : ℕ) (φ : A →+* S)
    (hp : (p : A) ≠ 0)
    (v : Elem A (p ^ (e + 1)) →+* S)
    (v' : Elem A (p ^ (e + 2)) →+* S)
    (vscalar : ∀ a : A, v (scalar (p ^ (e + 1)) a) = φ a)
    (vq : ∀ F : Elem A (p ^ (e + 2)),
      v (cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F) = v' F)
    (b : Aˣ) (F K : Elem A (p ^ (e + 2)))
    (hFK : F * K = scalar (p ^ (e + 2)) ((p : A) ^ (e + 2) * (b : A)))
    (F' : Elem A (p ^ (e + 1)))
    (hF : cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F =
      scalar (p ^ (e + 1)) (p : A) * F')
    (ih : ∀ U V : Elem A (p ^ (e + 1)),
      U * V = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A)) →
        ResidueOneAssociated (IsLocalRing.residue S) (v U)
          (φ (augmentation (p ^ (e + 1)) U)) ∧
        ResidueOneAssociated (IsLocalRing.residue S) (v V)
          (φ (augmentation (p ^ (e + 1)) V))) :
    ResidueOneAssociated (IsLocalRing.residue S) (v' F)
      (φ (augmentation (p ^ (e + 2)) F)) ∧
    ResidueOneAssociated (IsLocalRing.residue S) (v' K)
      (φ (augmentation (p ^ (e + 2)) K)) := by
  let q := cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1)))
  have hdiv : F' * q K = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A)) :=
    quotient_scalar_norm_division q (fun a => cyclicProjection_single_zero _ a)
      (p : A) hp (e + 1) (b : A) F K F' hFK hF
  obtain ⟨hiF, hiK⟩ := ih F' (q K) hdiv
  have heval : v' F = φ (p : A) * v F' := by
    rw [← vq F, hF, map_mul, vscalar]
  have haug : augmentation (p ^ (e + 2)) F =
      (p : A) * augmentation (p ^ (e + 1)) F' := by
    rw [← augmentation_cyclicProjection (pow_dvd_pow p (Nat.le_succ (e + 1))) F,
      hF, map_mul, augmentation_scalar]
  constructor
  · rw [heval, haug, map_mul]
    exact hiF.mul_left (φ (p : A))
  · simpa only [q, vq, augmentation_cyclicProjection] using hiK

/-- The integral induction with its projection-divisibility input exposed.
The concrete cyclotomic theorem discharges `hdivide`; it is not a definition
of the comparison conclusion. -/
theorem comparison_induction (p : ℕ) (φ : A →+* S)
    (hp : Prime (p : A)) (hpS : φ (p : A) ≠ 0)
    (v : (e : ℕ) → Elem A (p ^ (e + 1)) →+* S)
    (vscalar : ∀ e a, v e (scalar (p ^ (e + 1)) a) = φ a)
    (vres : ∀ F : Elem A (p ^ 1),
      IsLocalRing.residue S (v 0 F) =
        IsLocalRing.residue S (φ (augmentation (p ^ 1) F)))
    (vq : ∀ e F,
      v e (cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F) = v (e + 1) F)
    (hdivide : ∀ e (b : Aˣ) (F K : Elem A (p ^ (e + 2))),
      F * K = scalar (p ^ (e + 2)) ((p : A) ^ (e + 2) * (b : A)) →
      (∃ F', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F =
        scalar (p ^ (e + 1)) (p : A) * F') ∨
      (∃ K', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) K =
        scalar (p ^ (e + 1)) (p : A) * K')) :
    ∀ e (b : Aˣ) (F K : Elem A (p ^ (e + 1))),
      F * K = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A)) →
      ResidueOneAssociated (IsLocalRing.residue S) (v e F)
        (φ (augmentation (p ^ (e + 1)) F)) ∧
      ResidueOneAssociated (IsLocalRing.residue S) (v e K)
        (φ (augmentation (p ^ (e + 1)) K)) := by
  intro e
  induction e with
  | zero =>
      intro b F K hFK
      exact comparison_base (p ^ (0 + 1)) p φ hp hpS (v 0) (vscalar 0) vres
        b F K (by simpa only [Nat.zero_add, pow_one] using hFK)
  | succ e ih =>
      intro b F K hFK
      rcases hdivide e b F K hFK with ⟨F', hF⟩ | ⟨K', hK⟩
      · exact comparison_step_left p e φ hp.ne_zero (v e) (v (e + 1))
          (vscalar e) (vq e) b F K hFK F' hF (ih b)
      · have hKF : K * F = scalar (p ^ (e + 2))
            ((p : A) ^ (e + 2) * (b : A)) := by
          simpa only [mul_comm] using hFK
        exact (comparison_step_left p e φ hp.ne_zero (v e) (v (e + 1))
          (vscalar e) (vq e) b K F hKF K' hK (ih b)).symm

end CirculantHadamard.LocalComparison

end

end OAI
