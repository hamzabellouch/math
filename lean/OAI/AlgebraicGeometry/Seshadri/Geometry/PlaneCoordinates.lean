import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionChart

namespace OAI


                                          
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {σ : Type} {X : Scheme.{0}} {M : X.Modules}

def ratioOn (s : σ → (O X ⟶ M)) (i j : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) : Γ(U.toScheme,⊤) :=
  coefficient (sectionFrameOn (s i) U hi) (restrictSection U.ι (s j))

@[simp] lemma ratioOn_full (s : σ → (O X ⟶ M)) (i j : σ) :
    ratioOn s i j (SectionOpens.isoOpen (s i)) le_rfl =
      coefficient (sectionFrame (s i)) (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)) := by
  rw [ratioOn, sectionFrameOn_coefficient, Scheme.homOfLE_rfl]
  rfl

@[simp] lemma ratioOn_self (s : σ → (O X ⟶ M)) (i : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) : ratioOn s i i U hi = 1 :=
  sectionFrameOn_normalized (s i) U hi

def ratioUnitOn (s : σ → (O X ⟶ M)) (i j : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) (hj : U ≤ SectionOpens.isoOpen (s j)) :
    Γ(U.toScheme,⊤)ˣ :=
  frameChange (sectionFrameOn (s j) U hj) (sectionFrameOn (s i) U hi)

@[simp] lemma ratioUnitOn_val (s : σ → (O X ⟶ M)) (i j : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) (hj : U ≤ SectionOpens.isoOpen (s j)) :
    (ratioUnitOn s i j U hi hj : Γ(U.toScheme,⊤)) = ratioOn s i j U hi := by
  have h := coefficient_change (sectionFrameOn (s j) U hj)
    (sectionFrameOn (s i) U hi) (restrictSection U.ι (s j))
  dsimp only [ratioUnitOn, ratioOn]
  simpa only [sectionFrameOn_normalized, mul_one] using h.symm

lemma ratioOn_restrict (s : σ → (O X ⟶ M)) (i j : σ) {U W : X.Opens}
    (hi : U ≤ SectionOpens.isoOpen (s i)) (h : W ≤ U) :
    (X.homOfLE h).appTop (ratioOn s i j U hi) = ratioOn s i j W (h.trans hi) := by
  dsimp only [ratioOn]
  rw [sectionFrameOn_coefficient, sectionFrameOn_coefficient]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Scheme.homOfLE_homOfLE]

lemma ratioUnitOn_restrict (s : σ → (O X ⟶ M)) (i j : σ) {U W : X.Opens}
    (hi : U ≤ SectionOpens.isoOpen (s i)) (hj : U ≤ SectionOpens.isoOpen (s j))
    (h : W ≤ U) :
    Units.map (X.homOfLE h).appTop.hom (ratioUnitOn s i j U hi hj) =
      ratioUnitOn s i j W (h.trans hi) (h.trans hj) := by
  apply Units.ext
  simp only [Units.coe_map, ratioUnitOn_val]
  exact ratioOn_restrict s i j hi h

lemma ratioOn_cocycle (s : σ → (O X ⟶ M)) (i j l : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) (hj : U ≤ SectionOpens.isoOpen (s j)) :
    ratioOn s i l U hi = ratioOn s i j U hi * ratioOn s j l U hj := by
  have h := coefficient_change (sectionFrameOn (s j) U hj)
    (sectionFrameOn (s i) U hi) (restrictSection U.ι (s l))
  rw [← ratioUnitOn_val s i j U hi hj]
  exact h

lemma ratioUnitOn_cocycle (s : σ → (O X ⟶ M)) (i j l : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) (hj : U ≤ SectionOpens.isoOpen (s j))
    (hl : U ≤ SectionOpens.isoOpen (s l)) :
    ratioUnitOn s i l U hi hl = ratioUnitOn s i j U hi hj * ratioUnitOn s j l U hj hl := by
  apply Units.ext
  simp only [Units.val_mul, ratioUnitOn_val]
  exact ratioOn_cocycle s i j l U hi hj

lemma ratioUnitOn_symm (s : σ → (O X ⟶ M)) (i j : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) (hj : U ≤ SectionOpens.isoOpen (s j)) :
    ratioUnitOn s j i U hj hi = (ratioUnitOn s i j U hi hj)⁻¹ := by
  change frameChange _ _ = (frameChange _ _)⁻¹
  rfl

lemma ratioOn_basicOpen (s : σ → (O X ⟶ M)) (i j : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) :
    U.ι ⁻¹ᵁ SectionOpens.isoOpen (s j) = U.toScheme.basicOpen (ratioOn s i j U hi) :=
  preimage_isoOpen (s j) U.ι (sectionFrameOn (s i) U hi)

end
end MaximalSeshadri.Projective

end



end OAI
