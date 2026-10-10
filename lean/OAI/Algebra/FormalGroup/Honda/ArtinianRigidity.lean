import OAI.Algebra.FormalGroup.Honda.NilpotentTower
import OAI.Algebra.FormalGroup.Honda.Transport

namespace OAI

noncomputable section

universe uK uR

namespace HeightThree.ArtinianRigidity
open HondaTarget DeformationRigidity CoordinateTransport NilpotentTower

lemma automorphism_rigid {K : Type uK} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (n : ℕ) (R : Type uR) [CommRing R] [Algebra K R] (ρ : R →ₐ[K] K)
    (hn : (RingHom.ker ρ)^(n+1)=⊥) (F : FormalGroup R) (e : CoordinateIso F F)
    (he : e.series.map ρ.toRingHom=PowerSeries.X)
    (hF : (multiplicationSeries F p).map ρ.toRingHom=PowerSeries.X^(p^3)) :
    e.series=PowerSeries.X := by
  induction n generalizing R with
  | zero =>
    have hi : Function.Injective ρ.toRingHom := (RingHom.injective_iff_ker_eq_bot ρ).mpr (by simpa using hn)
    apply PowerSeries.map_injective ρ.toRingHom hi
    rw [he,PowerSeries.map_X]
  | succ n ih =>
    let S := quotient ρ n
    let π : R →ₐ[K] S := projection ρ n
    let σ : S →ₐ[K] K := augmentation ρ n
    have fac : σ.toRingHom.comp π.toRingHom=ρ.toRingHom := rfl
    have : Nontrivial R := ρ.toRingHom.domain_nontrivial
    have : CharP R p := (Algebra.charP_iff K R p).mp inferInstance
    have hsmall : SmallExtension.IsSmall π.toRingHom ρ.toRingHom :=
      ⟨projection_ker_le ρ n,projection_annihilate ρ n hn⟩
    let d := CoordinateTransport.CoordinateIso.map e π.toRingHom
    have hd : d.series.map σ.toRingHom=PowerSeries.X := by
      change (e.series.map π.toRingHom).map σ.toRingHom=PowerSeries.X
      rw [unimap_comp,fac,he]
    have hF' : (multiplicationSeries (F.map π.toRingHom) p).map σ.toRingHom=PowerSeries.X^(p^3) := by
      rw [multiplication_map,unimap_comp,fac,hF]
    have hd' := ih S σ (augmentation_nilpotent ρ n) (F.map π.toRingHom) d hd hF'
    exact SmallExtension.small_automorphism_rigid p π.toRingHom ρ.toRingHom hsmall F e hd' hF

end HeightThree.ArtinianRigidity

end

end OAI
