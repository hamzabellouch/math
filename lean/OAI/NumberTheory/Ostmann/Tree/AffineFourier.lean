import OAI.NumberTheory.Ostmann.Tree.AffineEnergy
import OAI.NumberTheory.Ostmann.Tree.Parseval

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]

theorem fourier_sum {ι : Type*} (S : Finset ι) (f : ι → ZMod p → ℂ) (a : ZMod p) :
    fourier (fun x => ∑ i ∈ S, f i x) a = ∑ i ∈ S, fourier (f i) a := by
  have hf : (fun x => ∑ i ∈ S, f i x) = ∑ i ∈ S, f i := by ext; simp
  rw [hf]
  simp only [fourier, map_sum, Finset.sum_apply, Finset.mul_sum]

theorem fourier_const_mul (f : ZMod p → ℂ) (c : ℂ) (a : ZMod p) :
    fourier (fun x => c*f x) a = c*fourier f a := by
  rw [fourier, ZMod.dft_const_mul]
  dsimp [fourier]
  ring

theorem fourier_unitMul (f : ZMod p → ℂ) (u : (ZMod p)ˣ) (a : ZMod p) :
    fourier (fun x => f ((u:ZMod p)*x)) a = fourier f ((u⁻¹: (ZMod p)ˣ)*a) := by
  simp only [fourier, ZMod.dft_comp_unitMul]

theorem fourier_translate (f : ZMod p → ℂ) (b a : ZMod p) :
    fourier (fun x => f (x+b)) a = ZMod.stdAddChar (a*b)*fourier f a := by
  have hs := (Equiv.addRight b).bijective.sum_comp
    (fun y : ZMod p => f y * ZMod.stdAddChar (-(a*(y-b))))
  change (∑ y : ZMod p, f (y+b) * ZMod.stdAddChar (-(a*((y+b)-b)))) =
    ∑ y : ZMod p, f y * ZMod.stdAddChar (-(a*(y-b))) at hs
  simp only [add_sub_cancel_right] at hs
  rw [fourier_apply, hs, fourier_apply]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  have he : -(a*(y-b)) = a*b + -(a*y) := by ring
  rw [he, AddChar.map_add_eq_mul]
  ring

theorem fourier_affine (f : ZMod p → ℂ) (u : (ZMod p)ˣ) (b a : ZMod p) :
    fourier (fun x => f ((u:ZMod p)*x+b)) a =
      ZMod.stdAddChar (((u⁻¹:(ZMod p)ˣ):ZMod p)*a*b) *
        fourier f (((u⁻¹:(ZMod p)ˣ):ZMod p)*a) := by
  rw [fourier_unitMul (fun x => f (x+b)), fourier_translate]

def affineAction (c : (ZMod p)ˣ → ZMod p → ℂ) (f : ZMod p → ℂ) (t : ZMod p) : ℂ :=
  ∑ u, ∑ b, c u b * f ((u:ZMod p)*t+b)

theorem fourier_affineAction (c : (ZMod p)ˣ → ZMod p → ℂ) (f : ZMod p → ℂ)
    (a : ZMod p) :
    fourier (affineAction c f) a = ∑ u : (ZMod p)ˣ,
      (∑ b, c u b * ZMod.stdAddChar (((u⁻¹:(ZMod p)ˣ):ZMod p)*a*b)) *
        fourier f (((u⁻¹:(ZMod p)ˣ):ZMod p)*a) := by
  unfold affineAction
  rw [fourier_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [fourier_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [fourier_const_mul, fourier_affine]
  ring

end
end Ostmann.FiniteField

end OAI
