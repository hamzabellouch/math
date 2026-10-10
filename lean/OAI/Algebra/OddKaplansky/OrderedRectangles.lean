import OAI.Algebra.OddKaplansky.OrderedOrbits

namespace OAI

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5 portUniverse6 portUniverse7 portUniverse8

section
namespace OddKaplansky.OrderedSectorOrbit
noncomputable section
open scoped Classical BigOperators Matrix
open WreathFourier
variable {K : Type portUniverse1} {H : Type portUniverse2} [Field K] [Group H] [Fintype H] [LinearOrder H]
local instance orderedSectorRectangularDecidableEq : DecidableEq H := Classical.decEq H
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
variable (hm : (Fintype.card (Fourier.C M) : K) ≠ 0)
def matrixPack {W : Type portUniverse3} {N : Type portUniverse4} (F : (r : Rep (H := H) M) → Matrix W N (Block (K := K) M r)) :
    Matrix W N (MonoidAlgebra K (Wreath (H := H) M)) := fun w n => pack M hζ (fun r => F r w n)
include hc in
lemma matrixPack_mul {W : Type portUniverse5} {N : Type portUniverse6} {V : Type portUniverse7} [Fintype N]
    (F : (r : Rep (H := H) M) → Matrix W N (Block (K := K) M r))
    (G : (r : Rep (H := H) M) → Matrix N V (Block (K := K) M r)) :
    matrixPack M hζ F * matrixPack M hζ G = matrixPack M hζ (fun r => F r*G r) := by
  funext w v
  simp only [Matrix.mul_apply,matrixPack,pack_mul M hζ hc]
  rw [← map_sum]
  congr 1
  funext r
  simp only [Finset.sum_apply,]
include hc hm in
lemma matrixPack_one {N : Type portUniverse8} [DecidableEq N] :
    matrixPack (H := H) M hζ (fun _ => (1 : Matrix N N _)) = Matrix.diagonal (fun _ : N => SectorFourier.f M hζ) := by
  funext n n'
  simp only [matrixPack,Matrix.one_apply,Matrix.diagonal_apply]
  by_cases h : n=n'
  · simp only [h,ite_true,pack_one M hζ hc hm]
  · simp only [ite_eq_right h]
    exact map_zero _
include hc hm in
lemma pack_left_sector (F : (r : Rep (H := H) M) → Block (K := K) M r) :
    SectorFourier.f M hζ * pack M hζ F = pack M hζ F := by
  rw [← pack_one M hζ hc hm,pack_mul M hζ hc]
  simp only [one_mul]
end
end OddKaplansky.OrderedSectorOrbit

end

end OAI
