import OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification

namespace OAI

noncomputable section

namespace PiExponent

section

open AlgebraicGeometry TopologicalSpace
open scoped HomogeneousIdeal

variable {A T : Type*} [CommRing A] [IsDomain A] [SetLike T A] [AddSubgroupClass T A]
  (𝒜 : ℕ → T) [GradedRing 𝒜]

def projectiveGenericPoint {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (hd : 0 < d) (hne : s ≠ 0) :
    ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := ⊥
  isPrime := by
    simpa only [HomogeneousIdeal.toIdeal_bot] using (inferInstance : (⊥ : Ideal A).IsPrime)
  not_irrelevant_le h := by
    have hm := h (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd hs)
    change s ∈ (⊥ : Ideal A) at hm
    exact hne (Ideal.mem_bot.mp hm)

theorem projective_basicOpen_dense {s : A} {d : ℕ} (hs : s ∈ 𝒜 d)
    (hd : 0 < d) (hne : s ≠ 0) : Dense (Proj.basicOpen 𝒜 s : Set (Proj 𝒜)) := by
  let p := projectiveGenericPoint 𝒜 hs hd hne
  have hp : p ∈ Proj.basicOpen 𝒜 s := by
    change s ∉ (⊥ : Ideal A)
    exact fun h => hne (Ideal.mem_bot.mp h)
  intro x
  apply closure_mono (Set.singleton_subset_iff.mpr hp)
  exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 p x).mp
    (show (⊥ : HomogeneousIdeal 𝒜) ≤ x.asHomogeneousIdeal from bot_le)

end

namespace WeightedCompactification

open MvPolynomial AlgebraicGeometry

variable {R ι σ : Type*} [CommRing R] [IsDomain R]

theorem imageCoordinate_zero_exponent_ne_zero (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0) :
    imageCoordinate (R := R) a z ≠ 0 := by
  intro h
  have hc := congrArg (fun x : monomialImage (R := R) a => x.1) h
  simp [homogeneousMonomialMap, hz] at hc

theorem constantChart_dense (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0) :
    Dense (Proj.basicOpen (imageGrade (R := R) a) (imageCoordinate a z) :
      Set (Proj (imageGrade (R := R) a))) :=
  projective_basicOpen_dense _ (imageCoordinate_mem a z) (by decide)
    (imageCoordinate_zero_exponent_ne_zero a z hz)

end WeightedCompactification

end PiExponent

end

end OAI
