import OAI.Algebra.OddKaplansky.SectorGreedy

namespace OAI

universe portUniverse1 portUniverse2 portUniverse3

section
namespace OddKaplansky.OrderedSourceSector
noncomputable section
local instance orderedSourceDecidableEq (α : Type portUniverse1) : DecidableEq α := Classical.decEq α
open scoped Classical BigOperators Matrix
open WreathFourier OrderedSectorOrbit
variable {K : Type} [Field K] (M p : ℕ) [NeZero M] [Fact p.Prime] [CharP K p]
local instance : DecidableEq (SectorStabilizer.H M p) := Classical.decEq _
variable {ζ : K} (hζ : IsPrimitiveRoot ζ M)
lemma stabilizer_comm (r : Rep (H := SectorStabilizer.H M p) M) : ∀ s t : T M r, s*t=t*s := by
  rw [T_leftFixed]
  exact SectorStabilizer.commutative M p (fun x => (lmb M r x).toAdd) (lmb_weight M r)
lemma stabilizer_exp (r : Rep (H := SectorStabilizer.H M p) M) : ∀ t : T M r, t^p=1 := by
  rw [T_leftFixed]
  exact SectorStabilizer.exponent M p (fun x => (lmb M r x).toAdd) (lmb_weight M r)
variable (e : MonoidAlgebra K (SectorStabilizer.H M p)) (he : e*e=e)
variable {W : Type portUniverse2} {N : Type portUniverse3} [Fintype W] [LinearOrder W] [Fintype N] [LinearOrder N]
variable (hw : Fintype.card W=Fintype.card (SectorStabilizer.H M p))
variable (hn : Fintype.card N=Module.finrank K (LinearMap.range (Algebra.lmul K _ e)))
def explicitJ := OrderedSectorOrbit.explicitJ M hζ p (stabilizer_comm M p) (stabilizer_exp M p) e he hw hn
def explicitY := OrderedSectorOrbit.explicitY M hζ p (stabilizer_comm M p) (stabilizer_exp M p) e he hw hn
lemma explicit_properties (hc : (Fintype.card (Base (H := SectorStabilizer.H M p) M) : K) ≠ 0)
    (hm : (Fintype.card (Fourier.C M) : K) ≠ 0) :
    explicitY M p hζ e he hw hn*explicitJ M p hζ e he hw hn=Matrix.diagonal (fun _ => SectorFourier.f M hζ) ∧
    explicitJ M p hζ e he hw hn*explicitY M p hζ e he hw hn=Matrix.diagonal (fun _ => SectorFourier.f M hζ * MonoidAlgebra.mapDomainAlgHom K K (top M) e) ∧
    (∀ w n, SectorFourier.f M hζ * explicitJ M p hζ e he hw hn w n=explicitJ M p hζ e he hw hn w n) ∧
    (∀ n w, SectorFourier.f M hζ * explicitY M p hζ e he hw hn n w=explicitY M p hζ e he hw hn n w) :=
  OrderedSectorOrbit.explicit_properties M hζ p (stabilizer_comm M p) (stabilizer_exp M p) e he hw hn hc hm
end
end OddKaplansky.OrderedSourceSector

end

end OAI
