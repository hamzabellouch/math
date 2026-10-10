import Mathlib.MeasureTheory.Group.Integral
import OAI.Geometry.NodalSets.Elliptic.RealCompactMultiplierLemmas

namespace OAI

namespace Yau
open MeasureTheory
noncomputable section

abbrev RealEuclideanL2 (n : ℕ) := Lp ℝ 2 (volume : Measure (Fin n → ℝ))

def realL2Translate {n : ℕ} (v : Fin n → ℝ) (f : RealEuclideanL2 n) : RealEuclideanL2 n :=
  Lp.compMeasurePreserving (fun x ↦ x+v) (measurePreserving_add_right volume v) f

theorem realL2Translate_ae {n : ℕ} (v : Fin n → ℝ) (f : RealEuclideanL2 n) :
    (realL2Translate v f : (Fin n → ℝ) → ℝ) =ᵐ[volume] (fun x ↦ f (x+v)) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume v)

theorem realL2Translate_norm {n : ℕ} (v : Fin n → ℝ) (f : RealEuclideanL2 n) :
    ‖realL2Translate v f‖=‖f‖ := Lp.norm_compMeasurePreserving f _

def realDifferenceQuotient {n : ℕ} (i : Fin n) (h : ℝ) (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ := h⁻¹*(u (x+(Pi.single i h : Fin n → ℝ))-u x)

def realL2DifferenceQuotient {n : ℕ} (i : Fin n) (h : ℝ) (f : RealEuclideanL2 n) :
    RealEuclideanL2 n := h⁻¹ • (realL2Translate ((Pi.single i h : Fin n → ℝ)) f-f)

theorem realL2DifferenceQuotient_ae {n : ℕ} (i : Fin n) (h : ℝ) (f : RealEuclideanL2 n) :
    (realL2DifferenceQuotient i h f : (Fin n → ℝ) → ℝ) =ᵐ[volume] realDifferenceQuotient i h f := by
  filter_upwards [Lp.coeFn_smul h⁻¹ (realL2Translate ((Pi.single i h : Fin n → ℝ)) f-f),
    Lp.coeFn_sub (realL2Translate ((Pi.single i h : Fin n → ℝ)) f) f,
    realL2Translate_ae ((Pi.single i h : Fin n → ℝ)) f] with x h1 h2 h3
  change (h⁻¹ • (realL2Translate ((Pi.single i h : Fin n → ℝ)) f-f)) x = _
  rw [h1]
  change h⁻¹*((realL2Translate ((Pi.single i h : Fin n → ℝ)) f-f) x) = _
  rw [h2]
  change h⁻¹*((realL2Translate ((Pi.single i h : Fin n → ℝ)) f) x-f x) = _
  rw [h3]
  rfl

theorem realDifferenceQuotient_memLp {n : ℕ} (i : Fin n) (h : ℝ)
    (u : (Fin n → ℝ) → ℝ) (hu : MemLp u 2 (volume : Measure (Fin n → ℝ))) :
    MemLp (realDifferenceQuotient i h u) 2 (volume : Measure (Fin n → ℝ)) := by
  have hs : MeasurePreserving (fun x : Fin n → ℝ ↦ x+(Pi.single i h : Fin n → ℝ)) volume volume :=
    measurePreserving_add_right (G := Fin n → ℝ) volume ((Pi.single i h : Fin n → ℝ))
  have ht : MemLp (fun x ↦ u (x+(Pi.single i h : Fin n → ℝ))) 2 volume := hu.comp_measurePreserving (f := fun x : Fin n → ℝ ↦ x+(Pi.single i h : Fin n → ℝ)) hs
  exact (ht.sub hu).const_mul h⁻¹

theorem realL2DifferenceQuotient_norm {n : ℕ} (i : Fin n) (h : ℝ) (f : RealEuclideanL2 n) :
    ‖realL2DifferenceQuotient i h f‖ ≤ (2*|h⁻¹|)*‖f‖ := by
  rw [realL2DifferenceQuotient,norm_smul,Real.norm_eq_abs]
  have hn := norm_sub_le (realL2Translate ((Pi.single i h : Fin n → ℝ)) f) f
  rw [realL2Translate_norm] at hn
  calc
    _ ≤ |h⁻¹| *(‖f‖+‖f‖) := mul_le_mul_of_nonneg_left hn (abs_nonneg _)
    _ = _ := by ring

theorem real_integral_translate_pairing {n : ℕ} (v : Fin n → ℝ)
    (u phi : (Fin n → ℝ) → ℝ) :
    (∫ x, u (x+v)*phi x) = ∫ x, u x*phi (x-v) := by
  have h := integral_add_right_eq_self (fun x ↦ u x*phi (x-v)) v (μ := volume)
  simpa only [add_sub_cancel_right] using h

theorem real_differenceQuotient_pairing {n : ℕ} (i : Fin n) (h : ℝ)
    (u phi : (Fin n → ℝ) → ℝ)
    (hu : MemLp u 2 (volume : Measure (Fin n → ℝ)))
    (hp : MemLp phi 2 (volume : Measure (Fin n → ℝ))) :
    Integrable (fun x ↦ realDifferenceQuotient i h u x*phi x) ∧
    Integrable (fun x ↦ u x*realDifferenceQuotient i (-h) phi x) ∧
    (∫ x, realDifferenceQuotient i h u x*phi x) =
      -(∫ x, u x*realDifferenceQuotient i (-h) phi x) := by
  have h1 := (realDifferenceQuotient_memLp i h u hu).integrable_mul hp
  have h2 := hu.integrable_mul (realDifferenceQuotient_memLp i (-h) phi hp)
  have hs : MeasurePreserving (fun x : Fin n → ℝ ↦ x+(Pi.single i h : Fin n → ℝ)) volume volume :=
    measurePreserving_add_right (G := Fin n → ℝ) volume ((Pi.single i h : Fin n → ℝ))
  have hs' : MeasurePreserving (fun x : Fin n → ℝ ↦ x+(Pi.single i (-h) : Fin n → ℝ)) volume volume :=
    measurePreserving_add_right (G := Fin n → ℝ) volume ((Pi.single i (-h) : Fin n → ℝ))
  have hut : MemLp (fun x ↦ u (x+(Pi.single i h : Fin n → ℝ))) 2 volume := hu.comp_measurePreserving (f := fun x : Fin n → ℝ ↦ x+(Pi.single i h : Fin n → ℝ)) hs
  have hpt : MemLp (fun x ↦ phi (x+(Pi.single i (-h) : Fin n → ℝ))) 2 volume := hp.comp_measurePreserving (f := fun x : Fin n → ℝ ↦ x+(Pi.single i (-h) : Fin n → ℝ)) hs'
  have h3 : Integrable (fun x ↦ u (x+(Pi.single i h : Fin n → ℝ))*phi x) := hut.integrable_mul hp
  have h4 : Integrable (fun x ↦ u x*phi x) := hu.integrable_mul hp
  have h5 : Integrable (fun x ↦ u x*phi (x+(Pi.single i (-h) : Fin n → ℝ))) := hu.integrable_mul hpt
  have he1 : (fun x ↦ realDifferenceQuotient i h u x*phi x) =
      fun x ↦ h⁻¹*(u (x+(Pi.single i h : Fin n → ℝ))*phi x-u x*phi x) := by
    funext x
    unfold realDifferenceQuotient
    ring
  have he2 : (fun x ↦ u x*realDifferenceQuotient i (-h) phi x) =
      fun x ↦ -(h⁻¹*(u x*phi (x+(Pi.single i (-h) : Fin n → ℝ))-u x*phi x)) := by
    funext x
    simp only [realDifferenceQuotient,inv_neg]
    ring
  refine ⟨h1,h2,?_⟩
  rw [he1,he2,integral_neg,neg_neg,integral_const_mul,integral_const_mul,
    integral_sub h3 h4,integral_sub h5 h4,real_integral_translate_pairing]
  simp only [Pi.single_neg,sub_eq_add_neg]

end
end Yau

end OAI
