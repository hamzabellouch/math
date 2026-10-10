import OAI.Analysis.KadisonKastler.ConjugateVectorSupport
import OAI.Analysis.KadisonKastler.TypeIIIProjectionComparison

namespace OAI

/-! # Moving a supported vector back to the original representation

Isometries onto its left and right supports turn a vector into a separating
and cyclic vector on the original Hilbert space. Only the concrete support
identities enter the proof.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem support_transfer_separating (M : VonNeumannAlgebra H) (ξ : H)
    (v : Algebra M) (w : Algebra M.commutant)
    (hv : star v * v = 1)
    (hvp : v.val * star v.val = (vectorSupportProjection M ξ).val.val)
    (hwξ : (w.val * star w.val) ξ = ξ) :
    ∀ a : Algebra M, a.val (star (v.val * w.val) ξ) = 0 → a = 0 := by
  intro a ha
  have hwa : a.val * w.val = w.val * a.val :=
    VonNeumannAlgebra.mem_commutant_iff.mp w.property a.val a.property
  have hwv : star v.val * (w.val * star w.val) =
      (w.val * star w.val) * star v.val :=
    VonNeumannAlgebra.mem_commutant_iff.mp
      (M.commutant.mul_mem w.property (M.commutant.star_mem' w.property))
      (star v.val) (M.star_mem' v.property)
  have he : v.val * w.val * a.val * star (v.val * w.val) =
      (v.val * a.val * star v.val) * (w.val * star w.val) := by
    rw [star_mul]
    calc
      v.val * w.val * a.val * (star w.val * star v.val) =
          v.val * a.val * ((w.val * star w.val) * star v.val) := by
        rw [mul_assoc v.val w.val a.val, ← hwa]
        simp only [mul_assoc]
      _ = (v.val * a.val * star v.val) * (w.val * star w.val) := by
        rw [← hwv]
        simp only [mul_assoc]
  have hbξ : (v.val * a.val * star v.val) ξ = 0 := by
    have hzero : (v.val * w.val * a.val * star (v.val * w.val)) ξ = 0 := by
      change v.val (w.val (a.val (star (v.val * w.val) ξ))) = 0
      rw [ha,map_zero,map_zero]
    rw [he,mul_apply_eq_comp,hwξ] at hzero
    exact hzero
  have hv' : star v.val * v.val = 1 := congrArg Subtype.val hv
  have hb : v * a * star v = 0 := by
    apply vectorSupport_faithful_corner M ξ (v * a * star v) _ hbξ
    change (v.val * a.val * star v.val) * (vectorSupportProjection M ξ).val.val = _
    rw [← hvp]
    calc
      (v.val * a.val * star v.val) * (v.val * star v.val) =
          v.val * a.val * (star v.val * v.val) * star v.val := by simp only [mul_assoc]
      _ = v.val * a.val * star v.val := by rw [hv',mul_one]
  have h := congrArg (fun b : Algebra M => star v * b * v) hb
  simpa only [mul_assoc, ← mul_assoc (star v) v, hv, one_mul,
    mul_one, mul_zero, zero_mul] using h

theorem support_transfer_cyclic (M : VonNeumannAlgebra H) (ξ : H)
    (v : Algebra M) (w : Algebra M.commutant)
    (hw : star w * w = 1)
    (hwq : w.val * star w.val = (vectorSupportProjection M.commutant ξ).val.val)
    (hvξ : (v.val * star v.val) ξ = ξ) :
    DenseRange (algebraVectorMap M (star (v.val * w.val) ξ)) := by
  have hswap : v.val * w.val = w.val * v.val :=
    VonNeumannAlgebra.mem_commutant_iff.mp w.property v.val v.property
  let v' : Algebra M.commutant.commutant :=
    ⟨v.val, by simpa only [M.commutant_commutant] using v.property⟩
  have hs := support_transfer_separating M.commutant ξ w v' hw hwq hvξ
  rw [← hswap] at hs
  have hd := commutant_orbit_dense M.commutant (star (v.val * w.val) ξ) hs
  change Dense (Set.range (fun a : Algebra M.commutant.commutant =>
    a.val (star (v.val * w.val) ξ))) at hd
  rw [VonNeumannAlgebra.commutant_commutant] at hd
  change Dense (Set.range (fun a : Algebra M => a.val (star (v.val * w.val) ξ)))
  exact hd

end

end KadisonKastler

end OAI
