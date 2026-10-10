import OAI.Algebra.OddKaplansky.SectorStabilizer

namespace OAI

universe portUniverse1 portUniverse2 portUniverse3

section
namespace OddKaplansky.SourceSector
noncomputable section
open scoped Classical BigOperators Matrix
open WreathFourier SectorOrbit
lemma T_leftFixed {H : Type portUniverse1} [Group H] [Fintype H] (M : ℕ) [NeZero M] (r : Rep (H := H) M) :
    T M r = SectorStabilizer.stabilizer M (fun x => (lmb M r x).toAdd) := by
  ext g
  rw [mem_T]
  constructor
  · intro he x
    have hh := congrArg (fun a : Base (H := H) M => (a (g*x)).toAdd) he
    simpa only [shift_apply,inv_mul_cancel_left] using hh.symm
  · intro hg
    funext x
    apply Multiplicative.toAdd.injective
    have hh := hg (g⁻¹*x)
    simpa only [shift_apply,mul_inv_cancel_left] using hh.symm
variable {K : Type} [Field K] (M p : ℕ) [NeZero M] [Fact p.Prime] [CharP K p]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ M)
include hζ in
lemma rectangular (hc : (Fintype.card (Base (H := SectorStabilizer.H M p) M) : K) ≠ 0)
    (hm : (Fintype.card (Fourier.C M) : K) ≠ 0)
    (e : MonoidAlgebra K (SectorStabilizer.H M p)) (he : e*e=e)
    {W : Type portUniverse2} {N : Type portUniverse3} [Fintype W] [Fintype N]
    (hw : Fintype.card W = Fintype.card (SectorStabilizer.H M p))
    (hn : Fintype.card N = Module.finrank K (LinearMap.range (Algebra.lmul K _ e))) :
    ∃ (J : Matrix W N (MonoidAlgebra K (Wreath (H := SectorStabilizer.H M p) M)))
      (Y : Matrix N W (MonoidAlgebra K (Wreath (H := SectorStabilizer.H M p) M))),
      Y*J=Matrix.diagonal (fun _ => SectorFourier.f M hζ) ∧
      J*Y=Matrix.diagonal (fun _ => SectorFourier.f M hζ * MonoidAlgebra.mapDomainAlgHom K K (top M) e) ∧
      (∀ w n, SectorFourier.f M hζ * J w n=J w n) ∧
      (∀ n w, SectorFourier.f M hζ * Y n w=Y n w) := by
  apply SectorOrbit.rectangular M hζ hc hm p _ _ e he hw hn
  · intro r
    rw [T_leftFixed]
    exact SectorStabilizer.commutative M p (fun x => (lmb M r x).toAdd) (lmb_weight M r)
  · intro r
    rw [T_leftFixed]
    exact SectorStabilizer.exponent M p (fun x => (lmb M r x).toAdd) (lmb_weight M r)
end
end OddKaplansky.SourceSector

end

end OAI
