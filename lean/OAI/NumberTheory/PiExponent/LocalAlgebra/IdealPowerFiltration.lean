import OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent
import OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels
import OAI.NumberTheory.PiExponent.Approximation.FullSupportNilpotence
import OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent
import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X : Scheme.{0}}

instance closedInclusion_mono (I : X.IdealSheafData) : Mono (closedInclusion I) :=
  inferInstanceAs (Mono (inclusion I.subschemeι))

lemma closedInclusion_structureMap_eq_zero {I J : X.IdealSheafData} (h : I ≤ J) :
    closedInclusion I ≫ structureMap J.subschemeι = 0 := by
  ext U x
  change J.subschemeι.app U ((closedInclusion I).app U x) = 0
  have hi : I.subschemeι.app U ((closedInclusion I).app U x) = 0 :=
    congrArg (fun f => f.app U x) (kernel.condition (structureMap I.subschemeι))
  rw [Scheme.Hom.congr_app (Scheme.IdealSheafData.inclusion_subschemeι h).symm U,
    Scheme.Hom.comp_app]
  change J.subscheme.presheaf.map _
    ((Scheme.IdealSheafData.inclusion h).app _
      (I.subschemeι.app U ((closedInclusion I).app U x))) = 0
  rw [hi, map_zero, map_zero]

def closedMap {I J : X.IdealSheafData} (h : I ≤ J) : closedModule I ⟶ closedModule J :=
  kernel.lift (structureMap J.subschemeι) (closedInclusion I)
    (closedInclusion_structureMap_eq_zero h)

@[reassoc (attr := simp)] lemma closedMap_inclusion {I J : X.IdealSheafData} (h : I ≤ J) :
    closedMap h ≫ closedInclusion J = closedInclusion I := kernel.lift_ι _ _ _

instance closedMap_mono {I J : X.IdealSheafData} (h : I ≤ J) : Mono (closedMap h) := by
  have : Mono (closedMap h ≫ closedInclusion J) := by rw [closedMap_inclusion]; infer_instance
  exact mono_of_mono (closedMap h) (closedInclusion J)

@[simp] lemma closedMap_refl (I : X.IdealSheafData) : closedMap (le_refl I) = 𝟙 _ := by
  apply (cancel_mono (closedInclusion I)).mp
  simp

@[reassoc (attr := simp)] lemma closedMap_comp {I J K : X.IdealSheafData}
    (hIJ : I ≤ J) (hJK : J ≤ K) : closedMap hIJ ≫ closedMap hJK = closedMap (hIJ.trans hJK) := by
  apply (cancel_mono (closedInclusion K)).mp
  simp

def powerMap (I : X.IdealSheafData) (n : ℕ) : closedModule (I^(n+1)) ⟶ closedModule (I^n) :=
  closedMap (fun _U => Ideal.pow_le_pow_right (Nat.le_succ n))

instance powerMap_mono (I : X.IdealSheafData) (n : ℕ) : Mono (powerMap I n) :=
  closedMap_mono _

def powerLayer (I : X.IdealSheafData) (n : ℕ) : X.Modules := cokernel (powerMap I n)

def powerSequence (I : X.IdealSheafData) (n : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (powerMap I n) (cokernel.π (powerMap I n)) (cokernel.condition _)

theorem powerSequence_shortExact (I : X.IdealSheafData) (n : ℕ) :
    (powerSequence I n).ShortExact := by
  change (ShortComplex.mk (powerMap I n) (cokernel.π (powerMap I n)) _).ShortExact
  exact { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (powerMap I n)) }

theorem closedModule_bot_isZero : IsZero (closedModule (⊥ : X.IdealSheafData)) := by
  have hmono : Mono (structureMap (Scheme.IdealSheafData.subschemeι (⊥ : X.IdealSheafData))) := by
    let F := Scheme.Modules.toPresheafOfModules X
    apply F.mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro U
    exact (ConcreteCategory.bijective_of_isIso
      ((⊥ : X.IdealSheafData).subschemeι.app U.unop)).injective
  exact isZero_kernel_of_mono _

theorem closedModule_isFinitePresentation [IsLocallyNoetherian X] (I : X.IdealSheafData) :
    (closedModule I).IsFinitePresentation := by
  have : (unit X).IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  have : (unit I.subscheme).IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  let : ((Scheme.Modules.pushforward I.subschemeι).obj (unit I.subscheme)).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward I.subschemeι).obj (unit I.subscheme))).choose.isQuasicoherent
  exact PiExponent.FiniteGlobalPresentation.kernel_isFinitePresentation (structureMap I.subschemeι)

theorem powerLayer_isFinitePresentation [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (n : ℕ) : (powerLayer I n).IsFinitePresentation := by
  have := closedModule_isFinitePresentation (I^n)
  have := closedModule_isFinitePresentation (I^(n+1))
  let : (closedModule (I^(n+1))).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (closedModule (I^(n+1)))).choose.isQuasicoherent
  exact PiExponent.CoherentCokernels.cokernel_isFinitePresentation (powerMap I n)

theorem powerModule_eventually_isZero [IsNoetherian X] (I : X.IdealSheafData)
    (hI : I.support = ⊤) : ∃ n : ℕ, 0 < n ∧ IsZero (closedModule (I^n)) := by
  obtain ⟨n, hn, he⟩ := Geometry.exists_pos_pow_eq_bot_of_fullSupport I hI
  exact ⟨n,hn,he ▸ closedModule_bot_isZero⟩

end
end PiExponentSeshadri.IdealModule

end OAI
