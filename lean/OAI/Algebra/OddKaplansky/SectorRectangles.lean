import OAI.Algebra.OddKaplansky.CosetRectangles

namespace OAI

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5 portUniverse6 portUniverse7 portUniverse8 portUniverse9 portUniverse10

section
namespace OddKaplansky.SectorOrbit
noncomputable section
open scoped Classical BigOperators Matrix
open WreathFourier
variable {K : Type portUniverse1} {H : Type portUniverse2} [Field K] [Group H] [Fintype H]
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
include hc hm in
lemma rectangular (p : ℕ) [Fact p.Prime] [CharP K p]
    (hcomm : ∀ r : Rep (H := H) M, ∀ s t : T M r, s*t=t*s)
    (hexp : ∀ r : Rep (H := H) M, ∀ t : T M r, t^p=1)
    (e : MonoidAlgebra K H) (he : e*e=e)
    {W : Type portUniverse9} {N : Type portUniverse10} [Fintype W] [Fintype N]
    (hw : Fintype.card W = Fintype.card H)
    (hn : Fintype.card N = Module.finrank K (LinearMap.range (Algebra.lmul K (MonoidAlgebra K H) e))) :
    ∃ (J : Matrix W N (MonoidAlgebra K (Wreath (H := H) M)))
      (Y : Matrix N W (MonoidAlgebra K (Wreath (H := H) M))),
      Y*J=Matrix.diagonal (fun _ => SectorFourier.f M hζ) ∧
      J*Y=Matrix.diagonal (fun _ => SectorFourier.f M hζ * MonoidAlgebra.mapDomainAlgHom K K (top M) e) ∧
      (∀ w n, SectorFourier.f M hζ * J w n=J w n) ∧
      (∀ n w, SectorFourier.f M hζ * Y n w=Y n w) := by
  have hall (r : Rep (H := H) M) : ∃ (J : Matrix W N (Block (K := K) M r)) (Y : Matrix N W (Block (K := K) M r)),
      Y*J=1 ∧ J*Y=Matrix.diagonal (fun _ => CosetMatrix.representation (T M r) e) := by
    let : IsMulCommutative (T M r) := ⟨⟨hcomm r⟩⟩
    exact CosetMatrix.representation_rectangular (T M r) p (hexp r) e he hw hn
  choose J Y hYJ hJY using hall
  refine ⟨matrixPack M hζ J,matrixPack M hζ Y,?_,?_,?_,?_⟩
  · rw [matrixPack_mul M hζ hc]
    simp only [hYJ]
    exact matrixPack_one M hζ hc hm
  · rw [matrixPack_mul M hζ hc]
    simp only [hJY]
    funext w w'
    simp only [matrixPack,Matrix.diagonal_apply]
    by_cases h : w=w'
    · simp only [h,ite_true,pack_representation M hζ hc e hm]
    · simp only [ite_eq_right h]
      exact map_zero _
  · intro w n
    exact pack_left_sector M hζ hc hm _
  · intro n w
    exact pack_left_sector M hζ hc hm _
end
end OddKaplansky.SectorOrbit

end

end OAI
