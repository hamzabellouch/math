import Mathlib
import OAI.Analysis.Conductivity.Variational.LocalSymmetricPiola

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def localPiolaSource (X : OpenPartialHomeomorph E E) (r : E → ℝ) (y : E) : ℝ := by
  classical
  exact if y∈X.target then |(fderiv ℝ X (X.symm y)).det|⁻¹*r (X.symm y) else 0

lemma localPiolaSource_pairing (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E) (hX : DifferentiableOn ℝ X X.source)
    (hdet : ∀ x∈X.source,(fderiv ℝ X x).det≠0)
    (r : E → ℝ) (hs : Function.support r⊆X.source) (φ : E → ℝ) :
    (∫ y,φ y*localPiolaSource X r y ∂μ)=(∫ x,φ (X x)*r x ∂μ) := by
  rw [integral_eq_setIntegral_of_zero_off μ X.target _ (by
    intro y hy; simp [localPiolaSource,hy])]
  rw [←X.image_source_eq_target,integral_image_eq_integral_abs_det_fderiv_smul μ
    X.open_source.measurableSet
    (fun x hx => ((hX x hx).differentiableAt (X.open_source.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt)
    X.injOn]
  rw [integral_eq_setIntegral_of_zero_off μ X.source (fun x => φ (X x)*r x) (by
    intro x hx
    rw [Function.notMem_support.mp (notMem_subset hs hx),mul_zero])]
  apply setIntegral_congr_fun X.open_source.measurableSet
  intro x hx
  simp only [localPiolaSource,ite_eq_left (X.map_source hx),X.left_inv hx,smul_eq_mul]
  have hn := abs_ne_zero.mpr (hdet x hx)
  field_simp

omit [BorelSpace E] in
lemma compactFlux_local_source (μ : Measure E) {U : Set E} (hU : IsOpen U)
    (F : E → E) (r : E → ℝ) (hcF : HasCompactSupport F) (hcr : HasCompactSupport r)
    (hsF : tsupport F⊆U) (hsr : tsupport r⊆U)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
      (∫ x,fderiv ℝ φ x (F x) ∂μ)=-(∫ x,φ x*r x ∂μ))
    (ψ : E → ℝ) (hψ : ContDiffOn ℝ (↑(⊤ : ℕ∞)) ψ U) :
    (∫ x,fderiv ℝ ψ x (F x) ∂μ)=-(∫ x,ψ x*r x ∂μ) := by
  obtain ⟨g,hg,he⟩ := exists_smooth_extension_near_compact hU (hcF.union hcr)
    (union_subset hsF hsr) ψ hψ
  calc
    _ = ∫ x,fderiv ℝ g x (F x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x∈tsupport F
      · rw [(he x (mem_union_left _ hx)).fderiv_eq]
      · rw [image_eq_zero_of_notMem_tsupport hx,map_zero,map_zero]
    _ = -(∫ x,g x*r x ∂μ) := hweak g hg
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x∈tsupport r
      · rw [(he x (mem_union_right _ hx)).eq_of_nhds]
      · rw [image_eq_zero_of_notMem_tsupport hx,mul_zero,mul_zero]

theorem localPiolaFlux_weak_source (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E)
    (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    (F : E → E) (r : E → ℝ) (hcF : HasCompactSupport F) (hcr : HasCompactSupport r)
    (hsF : tsupport F⊆X.source) (hsr : tsupport r⊆X.source)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
      (∫ x,fderiv ℝ φ x (F x) ∂μ)=-(∫ x,φ x*r x ∂μ))
    (ψ : E → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) :
    (∫ y,fderiv ℝ ψ y (localPiolaFlux X F y) ∂μ)=
      -(∫ y,ψ y*localPiolaSource X r y ∂μ) := by
  have hd := hX.differentiableOn (by simp)
  have hdi := hXi.differentiableOn (by simp)
  have hdet : ∀ x∈X.source,(fderiv ℝ X x).det≠0 :=
    fun _ hx => local_fderiv_det_ne_zero X hd hdi hx
  rw [localPiolaFlux_pairing μ X hd hdet F (subset_closure.trans hsF) ψ (hψ.differentiable (by simp)),
    localPiolaSource_pairing μ X hd hdet r (subset_closure.trans hsr) ψ]
  exact compactFlux_local_source μ X.open_source F r hcF hcr hsF hsr hweak _
    (hψ.comp_contDiffOn hX)

end ScalarConductivity



namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma tensorColumn_tsupport (B : Coord3 → Mat3) (D : Coord3 → Matrix (Fin 3) (Fin 2) ℝ) (j : Fin 2) :
    tsupport (fun x => (B x*D x).col j)⊆tsupport B := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  apply subset_closure
  intro hz
  apply hx
  simp only [hz,Matrix.zero_mul]
  rfl

theorem local_symmetric_source_transport
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    (B : Coord3 → Mat3) (hB : ContDiff ℝ (↑(⊤ : ℕ∞)) B)
    (hcB : HasCompactSupport B) (hsB : tsupport B⊆X.source)
    (hsy : ∀ x,(B x).IsSymm)
    (u : Coord3 → Fin 2 → ℝ) (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞)) u X.source)
    (r : Fin 2 → Coord3 → ℝ) (hcr : ∀ j,HasCompactSupport (r j))
    (hsr : ∀ j,tsupport (r j)⊆X.source)
    (hweak : ∀ j (φ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
      (∫ x,fderiv ℝ φ x ((B x*gradientColumns (fderiv ℝ u x)).col j))=
        -(∫ x,φ x*r j x)) :
    ∃ H : Coord3 → Mat3,
      ContDiff ℝ (↑(⊤ : ℕ∞)) H ∧ HasCompactSupport H ∧ tsupport H⊆X.target ∧
      (∀ y,(H y).IsSymm) ∧
      ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
        (∫ y,fderiv ℝ ψ y ((H y*gradientColumns (fderiv ℝ (u∘X.symm) y)).col j))=
          -(∫ y,ψ y*localPiolaSource X (r j) y) := by
  refine ⟨localPiolaTensor X B,localPiolaTensor_smooth X hX hXi B hB hcB hsB,
    (localPiolaTensor_compact X B hcB hsB).1,(localPiolaTensor_compact X B hcB hsB).2,
    localPiolaTensor_isSymm X B hsy,?_⟩
  intro j ψ hψ
  simp_rw [localPiolaTensor_columns X (hX.differentiableOn (by simp))
    (hXi.differentiableOn (by simp)) B u (hu.differentiableOn (by simp))]
  have ht := tensorColumn_tsupport B (fun x => gradientColumns (fderiv ℝ u x)) j
  exact localPiolaFlux_weak_source volume X hX hXi _ _
    (hcB.of_isClosed_subset isClosed_closure ht) (hcr j) (ht.trans hsB) (hsr j) (hweak j) ψ hψ

end ScalarConductivity

end

end OAI
