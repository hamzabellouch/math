import OAI.Algebra.OddKaplansky.CosetGreedy

namespace OAI

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4

section
namespace OddKaplansky.OrderedSectorOrbit
noncomputable section
open scoped Classical BigOperators Matrix
open WreathFourier
variable {K : Type portUniverse1} {H : Type portUniverse2} [Field K] [Group H] [Fintype H] [LinearOrder H]
local instance orderedSectorGreedyDecidableEq : DecidableEq H := Classical.decEq H
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable (hcomm : ∀ r : Rep (H := H) M, ∀ s t : T M r, s*t=t*s)
variable (hexp : ∀ r : Rep (H := H) M, ∀ t : T M r, t^p=1)
variable (e : MonoidAlgebra K H) (he : e*e=e)
variable {W : Type portUniverse3} {N : Type portUniverse4} [Fintype W] [LinearOrder W] [Fintype N] [LinearOrder N]
variable (hw : Fintype.card W = Fintype.card H)
variable (hn : Fintype.card N = Module.finrank K (LinearMap.range (Algebra.lmul K (MonoidAlgebra K H) e)))
def blockJ (r : Rep (H := H) M) : Matrix W N (Block (K := K) M r) := by
  letI : IsMulCommutative (T M r) := ⟨⟨hcomm r⟩⟩
  exact OrderedCosetMatrix.explicitJ (T M r) p (hexp r) e he hw hn
def blockY (r : Rep (H := H) M) : Matrix N W (Block (K := K) M r) := by
  letI : IsMulCommutative (T M r) := ⟨⟨hcomm r⟩⟩
  exact OrderedCosetMatrix.explicitY (T M r) p (hexp r) e he hw hn
lemma block_products (r : Rep (H := H) M) :
    blockY M p hcomm hexp e he hw hn r*blockJ M p hcomm hexp e he hw hn r=1 ∧
    blockJ M p hcomm hexp e he hw hn r*blockY M p hcomm hexp e he hw hn r=Matrix.diagonal (fun _ : W => OrderedCosetMatrix.representation (T M r) e) := by
  let : IsMulCommutative (T M r) := ⟨⟨hcomm r⟩⟩
  have hs := OrderedCosetMatrix.explicit_products (T M r) p (hexp r) e he hw hn
  constructor
  · convert hs.1 using 1 <;> congr ; exact Subsingleton.elim _ _
  · exact hs.2
def explicitJ : Matrix W N (MonoidAlgebra K (Wreath (H := H) M)) := matrixPack M hζ (blockJ M p hcomm hexp e he hw hn)
def explicitY : Matrix N W (MonoidAlgebra K (Wreath (H := H) M)) := matrixPack M hζ (blockY M p hcomm hexp e he hw hn)
variable (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
variable (hm : (Fintype.card (Fourier.C M) : K) ≠ 0)
include hc hm in
lemma explicit_properties :
    explicitY M hζ p hcomm hexp e he hw hn*explicitJ M hζ p hcomm hexp e he hw hn=Matrix.diagonal (fun _ => SectorFourier.f M hζ) ∧
    explicitJ M hζ p hcomm hexp e he hw hn*explicitY M hζ p hcomm hexp e he hw hn=Matrix.diagonal (fun _ => SectorFourier.f M hζ * MonoidAlgebra.mapDomainAlgHom K K (top M) e) ∧
    (∀ w n, SectorFourier.f M hζ * explicitJ M hζ p hcomm hexp e he hw hn w n=explicitJ M hζ p hcomm hexp e he hw hn w n) ∧
    (∀ n w, SectorFourier.f M hζ * explicitY M hζ p hcomm hexp e he hw hn n w=explicitY M hζ p hcomm hexp e he hw hn n w) := by
  have hYJ (r : Rep (H := H) M) := (block_products M p hcomm hexp e he hw hn r).1
  have hJY (r : Rep (H := H) M) := (block_products M p hcomm hexp e he hw hn r).2
  refine ⟨?_,?_,?_,?_⟩
  · rw [explicitY,explicitJ,matrixPack_mul M hζ hc]
    simp only [hYJ]
    convert matrixPack_one M hζ hc hm using 1
  · rw [explicitJ,explicitY,matrixPack_mul M hζ hc]
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
end OddKaplansky.OrderedSectorOrbit

end

end OAI
