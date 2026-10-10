import OAI.NumberTheory.PiExponent.Approximation.FrameSubopens
import OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme} {M : X.Modules}

def normalizedPowerFrame (U : X.Opens) (s : structureSheaf X ⟶ M)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)] (n : ℕ) :
    (modulePow X M n).restrict U.ι ≅ structureSheaf U.toScheme := by
  letI := powerSection_restrict_isIso U s n
  exact (asIso ((Scheme.Modules.restrictFunctor U.ι).map (powerSection s n))).symm ≪≫
    Scheme.Modules.restrictUnitIso U.ι

lemma normalizedPowerFrame_normalized (U : X.Opens) (s : structureSheaf X ⟶ M)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)] (n : ℕ) :
    coefficient (normalizedPowerFrame U s n) (restrictSection U.ι (powerSection s n)) = 1 := by
  change coefficient (normalizedPowerFrame U s n) (normalizedPowerFrame U s n).inv = 1
  exact coefficient_frame _

lemma normalizedPowerFrame_coefficient (U : X.Opens) (si sj : structureSheaf X ⟶ M)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map si)]
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (hi : coefficient e (restrictSection U.ι si) = 1) (n : ℕ) :
    coefficient (normalizedPowerFrame U si n) (restrictSection U.ι (powerSection sj n)) =
      coefficient e (restrictSection U.ι sj) ^ n := by
  have hc := coefficient_change (localPowerFrame U e n) (normalizedPowerFrame U si n)
    (restrictSection U.ι (powerSection sj n))
  have hbase := coefficient_change (localPowerFrame U e n) (normalizedPowerFrame U si n)
    (restrictSection U.ι (powerSection si n))
  rw [normalizedPowerFrame_normalized, local_powerSection_coefficient, hi,
    one_pow, mul_one] at hbase
  rw [local_powerSection_coefficient, ← mul_assoc, ← hbase, one_mul] at hc
  exact hc

def coordinatePowerFrame (s : structureSheaf X ⟶ M) (n : ℕ) :
    (modulePow X M n).restrict (SectionOpens.isoOpen s).ι ≅
      structureSheaf (SectionOpens.isoOpen s).toScheme := by
  letI := SectionOpens.isIso_restrict_isoOpen s
  exact normalizedPowerFrame _ s n

lemma coordinatePowerFrame_coefficient (si sj : structureSheaf X ⟶ M) (n : ℕ) :
    coefficient (coordinatePowerFrame si n)
      (restrictSection (SectionOpens.isoOpen si).ι (powerSection sj n)) =
    coefficient (PiExponentSeshadri.Projective.sectionFrame si)
      (restrictSection (SectionOpens.isoOpen si).ι sj) ^ n := by
  exact @normalizedPowerFrame_coefficient X M _ si sj
    (SectionOpens.isIso_restrict_isoOpen si) (PiExponentSeshadri.Projective.sectionFrame si)
    (PiExponentSeshadri.Projective.sectionFrame_normalized si) n

@[simp] lemma coordinatePowerFrame_normalized (s : structureSheaf X ⟶ M) (n : ℕ) :
    coefficient (coordinatePowerFrame s n)
      (restrictSection (SectionOpens.isoOpen s).ι (powerSection s n)) = 1 := by
  erw [coordinatePowerFrame_coefficient, PiExponentSeshadri.Projective.sectionFrame_normalized, one_pow]
  rfl

lemma coordinatePowerFrame_overlap {W : Scheme}
    (si sj : structureSheaf X ⟶ M) (n : ℕ)
    (a : W ⟶ (SectionOpens.isoOpen si).toScheme)
    (b : W ⟶ (SectionOpens.isoOpen sj).toScheme)
    [IsOpenImmersion a] [IsOpenImmersion b]
    (h : a ≫ (SectionOpens.isoOpen si).ι = b ≫ (SectionOpens.isoOpen sj).ι) :
    ∃ c : Γ(W,⊤)ˣ,
      (c : Γ(W,⊤)) =
        b.appTop (coefficient (PiExponentSeshadri.Projective.sectionFrame sj)
          (restrictSection (SectionOpens.isoOpen sj).ι si)) ^ n ∧
      ∀ t : structureSheaf X ⟶ modulePow X M n,
        b.appTop (coefficient (coordinatePowerFrame sj n)
          (restrictSection (SectionOpens.isoOpen sj).ι t)) =
        (c : Γ(W,⊤)) * a.appTop (coefficient (coordinatePowerFrame si n)
          (restrictSection (SectionOpens.isoOpen si).ι t)) := by
  obtain ⟨c, hc, ht⟩ := normalized_overlap_coefficients
    (SectionOpens.isoOpen si).ι (SectionOpens.isoOpen sj).ι a b h
    (coordinatePowerFrame si n) (coordinatePowerFrame sj n)
    (powerSection si n) (coordinatePowerFrame_normalized si n)
  refine ⟨c, ?_, ht⟩
  erw [coordinatePowerFrame_coefficient, map_pow] at hc
  exact hc

lemma coordinatePowerFrame_frameChange (si sj : structureSheaf X ⟶ M) (n : ℕ)
    {W : X.Opens} (hi : W ≤ SectionOpens.isoOpen si) (hj : W ≤ SectionOpens.isoOpen sj) :
    (frameChange (restrictOpenFrame hi (coordinatePowerFrame si n))
      (restrictOpenFrame hj (coordinatePowerFrame sj n)) : Γ(W.toScheme,⊤)) =
      (X.homOfLE hj).appTop
        (coefficient (PiExponentSeshadri.Projective.sectionFrame sj)
          (restrictSection (SectionOpens.isoOpen sj).ι si)) ^ n := by
  erw [frameChange_restrictOpenFrame hi hj _ _ (powerSection si n)
    (coordinatePowerFrame_normalized si n), coordinatePowerFrame_coefficient, map_pow]
  rfl

lemma coordinatePowerFrame_change (si sj : structureSheaf X ⟶ M) (n : ℕ)
    {W : X.Opens} (hi : W ≤ SectionOpens.isoOpen si) (hj : W ≤ SectionOpens.isoOpen sj)
    (t : O W.toScheme ⟶ (modulePow X M n).restrict W.ι) :
    coefficient (restrictOpenFrame hj (coordinatePowerFrame sj n)) t =
      (X.homOfLE hj).appTop
        (coefficient (PiExponentSeshadri.Projective.sectionFrame sj)
          (restrictSection (SectionOpens.isoOpen sj).ι si)) ^ n *
      coefficient (restrictOpenFrame hi (coordinatePowerFrame si n)) t := by
  erw [coefficient_change (restrictOpenFrame hi (coordinatePowerFrame si n)),
    coordinatePowerFrame_frameChange]

end
end PiExponentSeshadri.Geometry

end OAI
