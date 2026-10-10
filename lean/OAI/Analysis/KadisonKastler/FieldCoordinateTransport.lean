import OAI.Analysis.KadisonKastler.L2CoordinateEquiv
import OAI.Analysis.KadisonKastler.DirectIntegralConjugacy
import OAI.Analysis.KadisonKastler.CanonicalAmplification

namespace OAI

/-! # Transporting a field decomposition through constant fiber coordinates -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X H K : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (μ : Measure X) (e : H ≃ₗᵢ[ℂ] K)

theorem representsOperatorField_coordinate_transport
    (F : X → H →L[ℂ] H) (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : RepresentsOperatorField μ F T) :
    RepresentsOperatorField μ (fun x => e.conjStarAlgEquiv (F x))
      ((l2CoordinateEquiv μ e).conjStarAlgEquiv T) := by
  intro f
  let E := l2CoordinateEquiv μ e
  let g := E.symm f
  filter_upwards [l2CoordinateEquiv_ae μ e (T g), hT g,
    l2CoordinateEquiv_ae μ e g] with x het ht heg
  have hg : g x = e.symm (f x) := by
    apply e.injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    simpa only [g, E, LinearIsometryEquiv.apply_symm_apply] using heg.symm
  change (E (T g)) x = e (F x (e.symm (f x)))
  rw [het, ht, hg]

theorem operatorFieldDecomposition_coordinate_transport
    (M : X → VonNeumannAlgebra H) (A : VonNeumannAlgebra (Lp H 2 μ))
    (hA : OperatorFieldDecomposition μ M A) :
    OperatorFieldDecomposition μ (fun x => spatialTransportAlgebra e (M x))
      (spatialTransportAlgebra (l2CoordinateEquiv μ e) A) := by
  constructor
  · rintro _ ⟨T, hT, rfl⟩
    obtain ⟨F, hm, hn, hF, ha⟩ := hA.decompose T hT
    refine ⟨fun x => e.conjStarAlgEquiv (F x), ?_, ?_, ?_,
      representsOperatorField_coordinate_transport μ e F T ha⟩
    · intro v
      exact e.continuous.comp_aestronglyMeasurable (hm (e.symm v))
    · change ∀ᵐ x ∂μ, ‖e.conjStarAlgEquiv (F x)‖ ≤
        ‖(l2CoordinateEquiv μ e).conjStarAlgEquiv T‖
      simpa only [norm_spatialConjugate] using hn
    · exact hF.mono fun x hx => ⟨F x, hx, rfl⟩
  · intro G C hC hm hn hG
    let F := fun x => e.conjStarAlgEquiv.symm (G x)
    have hFm (v : H) : AEStronglyMeasurable (fun x => F x v) μ :=
      e.symm.continuous.comp_aestronglyMeasurable (hm (e v))
    have hFn : ∀ᵐ x ∂μ, ‖F x‖ ≤ C := by
      simpa only [F, LinearIsometryEquiv.symm_conjStarAlgEquiv, norm_spatialConjugate] using hn
    have hFM : ∀ᵐ x ∂μ, F x ∈ M x :=
      hG.mono fun x hx => (mem_spatialTransportAlgebra e (M x) (G x)).mp hx
    obtain ⟨T, hT, ha⟩ := hA.reconstruct F C hC hFm hFn hFM
    refine ⟨(l2CoordinateEquiv μ e).conjStarAlgEquiv T, ⟨T, hT, rfl⟩, ?_⟩
    simpa only [F, StarAlgEquiv.apply_symm_apply] using
      representsOperatorField_coordinate_transport μ e F T ha

end

end KadisonKastler

end OAI
