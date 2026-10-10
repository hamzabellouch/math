import OAI.Algebra.Finitistic.Bimodule.BimoduleAugmentationEpi
import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalShortExact
import OAI.Algebra.Finitistic.Bimodule.BimoduleFiniteRowsAcyclic
import Mathlib.Algebra.Homology.HomologySequenceLemmas

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

/-- An acyclic kernel in an actual short exact sequence makes the quotient map
an isomorphism on homology. -/
theorem shortExact_quasiIso_g (S : ShortComplex (CochainComplex (ModuleCat.{u} B) ℤ))
    (hS : S.ShortExact) (hK : S.X₁.Acyclic) : QuasiIso S.g := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hz (a : ℤ) : IsZero (S.X₁.homology a) :=
    (exactAt_iff_isZero_homology _ _).mp (hK a)
  have : Mono (homologyMap S.g n) := (hS.homology_exact₂ n).mono_g_iff.mpr
    ((hz n).eq_of_src _ _)
  have : Epi (homologyMap S.g n) := (hS.homology_exact₃ n (n+1) rfl).epi_f_iff.mpr
    ((hz (n+1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

variable {P : BiComplex k B} {X : ModuleCat.{u} (Enveloping k B)}
variable (res : AugmentedProjective k B P X)

/-- The actual bimodule augmentation is an epimorphism of complexes. -/
theorem augmentation_epi : Epi res.augmentation := by
  let : ∀ n, Epi (res.augmentation.f n) := augmentation_epi_f res
  constructor
  intro Y f g h
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_epi (res.augmentation.f n)).mp
  exact congrArg (fun φ => φ.f n) h

/-- Tensoring the actual bounded resolution augmentation with a complex of
projective left modules gives a quasi-isomorphism of B-module complexes. -/
theorem augmentation_total_quasiIso (Z : CochainComplex (ModuleCat.{u} B) ℤ)
    [∀ q, Projective (Z.X q)] :
    QuasiIso (leftTotalMap res.augmentation Z res.data.degrees
      (intervalDegrees_strictMono res.data.lower res.data.upper)) := by
  let := augmentation_epi res
  let K := kernel res.augmentation
  let S : ShortComplex (BiComplex k B) :=
    ShortComplex.mk (kernel.ι res.augmentation) res.augmentation (kernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel res.augmentation }
  have hK : K.Acyclic := hS.acyclic_X₁ res.quasiIso
  have hb (a : ℤ) (ha : ∀ i, res.data.degrees i ≠ a) : IsZero (K.X a) := by
    have hz : IsZero (P.X a) := outside_interval_isZero k B P
      res.data.lower res.data.upper res.data.bounded a ha
    have : Subsingleton (P.X a) := ModuleCat.isZero_iff_subsingleton.mp hz
    have hinj := (ModuleCat.mono_iff_injective ((kernel.ι res.augmentation).f a)).mp inferInstance
    have : Subsingleton (K.X a) := ⟨fun x y => hinj (Subsingleton.elim _ _)⟩
    exact ModuleCat.isZero_of_subsingleton _
  have htK : (total k B K res.data.degrees
      (intervalDegrees_strictMono res.data.lower res.data.upper) Z).Acyclic := by
    apply total_acyclic_of_rows k B K Z res.data.degrees
      (intervalDegrees_strictMono res.data.lower res.data.upper) hb hK
      res.data.lower (res.data.lower + (res.data.upper-res.data.lower).toNat)
    · intro i
      dsimp [BoundedProjective.degrees,intervalDegrees]
      omega
    · intro i
      have := i.isLt
      dsimp [BoundedProjective.degrees,intervalDegrees]
      omega
  exact shortExact_quasiIso_g _
    (leftTotal_shortExact k B Z res.data.degrees
      (intervalDegrees_strictMono res.data.lower res.data.upper) S hS) htK
end LittleFinitistic.BimoduleTotal

end

end OAI
