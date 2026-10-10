import Mathlib
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.PointIdealGenerators

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.PointCoordinates
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
variable {K : Type} [Field K] {X : Scheme} [IsAffine X]

def affinePointMorphism (p : Γ(X, ⊤) →+* K) : Spec (CommRingCat.of K) ⟶ X :=
  Spec.map (CommRingCat.ofHom p) ≫ X.isoSpec.inv

def affineCenter (p : Γ(X, ⊤) →+* K) : X :=
  X.isoSpec.inv ⟨RingHom.ker p, RingHom.ker_isPrime p⟩

lemma affineCenter_eq_rational (p : Γ(X, ⊤) →+* K) :
    affineCenter p = affinePointMorphism p (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) := rfl

lemma isoSpec_affineCenter (p : Γ(X, ⊤) →+* K) :
    X.isoSpec.hom (affineCenter p) = ⟨RingHom.ker p, RingHom.ker_isPrime p⟩ := by
  change (X.isoSpec.inv ≫ X.isoSpec.hom) _ = _
  rw [Iso.inv_hom_id]
  rfl

theorem affine_center_cutout [Algebra K Γ(X, ⊤)] {ι : Type}
    (a : ι → Γ(X, ⊤)) (ha : Function.Surjective (MvPolynomial.aeval (R := K) a))
    (p : Γ(X, ⊤) →ₐ[K] K) (x : X) :
    (x ∉ (⨆ i, X.basicOpen (a i - algebraMap K Γ(X, ⊤) (p (a i))) : X.Opens)) ↔
      x = affineCenter p.toRingHom := by
  have hker := ker_eq_span_centered a ha p
  have hm : (RingHom.ker p.toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective p (fun c => ⟨algebraMap K Γ(X, ⊤) c, p.commutes c⟩)
  constructor
  · intro hx
    have hle : RingHom.ker p.toRingHom ≤ (X.isoSpec.hom x).asIdeal := by
      rw [hker]
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hh : x ∉ X.basicOpen (a i - algebraMap K Γ(X, ⊤) (p (a i))) :=
        fun hi => hx (Opens.mem_iSup.mpr ⟨i, hi⟩)
      rw [← X.map_PrimeSpectrum_basicOpen_of_affine] at hh
      exact not_not.mp hh
    have hp : X.isoSpec.hom x = (⟨RingHom.ker p.toRingHom, RingHom.ker_isPrime p⟩ : PrimeSpectrum Γ(X, ⊤)) :=
      PrimeSpectrum.ext (hm.eq_of_le (X.isoSpec.hom x).isPrime.ne_top hle).symm
    have he := congrArg (fun z => X.isoSpec.inv z) hp
    change (X.isoSpec.hom ≫ X.isoSpec.inv) x = affineCenter p.toRingHom at he
    rwa [Iso.hom_inv_id] at he
  · rintro rfl hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    rw [← X.map_PrimeSpectrum_basicOpen_of_affine] at hi
    change a i - algebraMap K Γ(X, ⊤) (p (a i)) ∉
      (X.isoSpec.hom (affineCenter p.toRingHom)).asIdeal at hi
    rw [isoSpec_affineCenter] at hi
    exact hi (by simp)

end
end MaximalSeshadri.PointCoordinates
end


end
end

end OAI
