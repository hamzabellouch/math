import Mathlib
import OAI.Analysis.Conductivity.Branching.LinearFiniteEndTransport

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma continuousLinearEquiv_det_ne_zero (P : Coord3 ≃L[ℝ] Coord3) :
    (P : Coord3 →L[ℝ] Coord3).det≠0 := by
  have hd : (fderiv ℝ (P : Coord3 → Coord3) 0).det≠0 :=
    fderiv_equiv_det_ne_zero P.toEquiv P.differentiable P.symm.differentiable 0
  simpa only [ContinuousLinearEquiv.fderiv] using hd

lemma continuousLinearEquiv_quasiMeasurePreserving (P : Coord3 ≃L[ℝ] Coord3) :
    Measure.QuasiMeasurePreserving P volume volume :=
  Measure.ContinuousLinearMap.quasiMeasurePreserving volume (P : Coord3 →L[ℝ] Coord3)
    (continuousLinearEquiv_det_ne_zero P)

lemma pi_clm_apply_sum {n : ℕ} (D : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    D v=∑ i,v i*D (Pi.single i 1) := by
  have he : v=∑ i,v i • Pi.single i 1 := by
    simpa only [←Pi.single_smul,smul_eq_mul,mul_one] using
      (Finset.univ_sum_single v).symm
  calc
    D v=D (∑ i,v i • Pi.single i 1) := congrArg D he
    _ = _ := by simp only [map_sum,map_smul,smul_eq_mul]

lemma coordinate_flux_pairing (F : Coord3 → Coord3) (ψ : SmoothScalar Coord3) (x : Coord3) :
    fderiv ℝ ψ.val x (F x)=∑ i,F x i*(smoothDirection (Pi.single i 1) ψ).val x :=
  pi_clm_apply_sum _ _

def linearFluxPullback (P : Coord3 ≃L[ℝ] Coord3) (F : Coord3 → Coord3) (x : Coord3) : Coord3 :=
  P.symm (F (P x))

lemma linearFluxPullback_weak (P : Coord3 ≃L[ℝ] Coord3)
    {F : Coord3 → Coord3} {U : Set Coord3}
    (hF : ∀ ψ : SmoothScalar Coord3,HasCompactSupport ψ.val → tsupport ψ.val⊆U →
      (∫ x,fderiv ℝ ψ.val x (F x))=0)
    (ψ : SmoothScalar Coord3) (hc : HasCompactSupport ψ.val)
    (hs : tsupport ψ.val⊆P ⁻¹' U) :
    (∫ x,fderiv ℝ ψ.val x (linearFluxPullback P F x))=0 := by
  let φ : SmoothScalar Coord3 := ⟨ψ.val ∘ P.symm,(smoothScalar_contDiff ψ).comp P.symm.contDiff⟩
  have hφc : HasCompactSupport φ.val := hc.comp_homeomorph P.symm.toHomeomorph
  have hφs : tsupport φ.val⊆U := by
    intro y hy
    have hh : P.symm y∈tsupport ψ.val := tsupport_comp_subset_preimage ψ.val P.symm.continuous hy
    simpa only [mem_preimage,P.apply_symm_apply] using hs hh
  have he := piolaFlux_pairing volume P.symm.toEquiv P.symm.differentiable
    (fderiv_equiv_det_ne_zero P.symm.toEquiv P.symm.differentiable P.differentiable)
    F ψ.val ((smoothScalar_contDiff ψ).differentiable (by simp))
  have he' : (∫ x,|(P.symm : Coord3 →L[ℝ] Coord3).det|⁻¹ *
      fderiv ℝ ψ.val x (linearFluxPullback P F x))=(0 : ℝ) := by
    calc
      _=(∫ x,fderiv ℝ ψ.val x (piolaFlux P.symm.toEquiv F x)) := by
        congr 1
        funext x
        have hd : fderiv ℝ P.symm.toEquiv (P.symm.toEquiv.symm x)=
            (P.symm : Coord3 →L[ℝ] Coord3) := P.symm.fderiv
        simp only [piolaFlux,hd,map_smul,smul_eq_mul]
        rfl
      _ = _ := he.trans (hF φ hφc hφs)
  rw [integral_const_mul] at he'
  exact (mul_eq_zero.mp he').resolve_left (inv_ne_zero (abs_ne_zero.mpr
    (continuousLinearEquiv_det_ne_zero P.symm)))

lemma continuous_flux_compact_test_integrable {F : Coord3 → Coord3} (hF : Continuous F)
    (ψ : SmoothScalar Coord3) (hc : HasCompactSupport ψ.val) :
    Integrable (fun x => fderiv ℝ ψ.val x (F x)) := by
  simp_rw [coordinate_flux_pairing]
  apply integrable_finsetSum
  intro i _
  exact (((continuous_apply i).comp hF).mul
    (smoothScalar_contDiff (smoothDirection (Pi.single i 1) ψ)).continuous).integrable_of_hasCompactSupport
      (compactSupport_smoothDirection (Pi.single i 1) hc).mul_left

lemma linearFluxPullback_C1 (P : Coord3 ≃L[ℝ] Coord3) {F : Coord3 → Coord3}
    (hF : ContDiff ℝ 1 F) : ContDiff ℝ 1 (linearFluxPullback P F) :=
  P.symm.contDiff.comp (hF.comp P.contDiff)

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma matrix_mul_transpose_col_sum {n : ℕ} (M : Matrix (Fin 3) (Fin n) ℝ)
    (N : Matrix (Fin 2) (Fin n) ℝ) (j : Fin 2) :
    (M*Nᵀ).col j=∑ k,N j k • M.col k := by
  ext i
  simp only [Matrix.col_apply,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul,mul_comm]

def linearColumnsPullback (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ))
    (G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ) (x : Coord3) : Matrix (Fin 3) (Fin 2) ℝ :=
  operatorMatrix (P.symm : Coord3 →L[ℝ] Coord3)*G (P x)*
    (operatorMatrix (Q : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)))ᵀ

lemma linearColumnsPullback_col (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ))
    (G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ) (x : Coord3) (j : Fin 2) :
    (linearColumnsPullback P Q G x).col j=
      ∑ k,operatorMatrix (Q : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) j k •
        linearFluxPullback P (fun y => (G y).col k) x := by
  rw [linearColumnsPullback,matrix_mul_transpose_col_sum]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  exact operatorMatrix_mulVec (P.symm : Coord3 →L[ℝ] Coord3) ((G (P x)).col k)

lemma linearColumnsPullback_C1 (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ))
    {G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ} (hG : ContDiff ℝ 1 G) :
    ContDiff ℝ 1 (linearColumnsPullback P Q G) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact contDiffAt_matrix_mul (contDiffAt_matrix_mul contDiffAt_const
    ((hG.comp P.contDiff).contDiffAt)) contDiffAt_const

lemma linearColumnsPullback_weak (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ))
    {G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ} (hGc : Continuous G) {U : Set Coord3}
    (hG : ∀ (j : Fin 2) (ψ : SmoothScalar Coord3),HasCompactSupport ψ.val → tsupport ψ.val⊆U →
      (∫ x,fderiv ℝ ψ.val x ((G x).col j))=0)
    (j : Fin 2) (ψ : SmoothScalar Coord3) (hc : HasCompactSupport ψ.val)
    (hs : tsupport ψ.val⊆P ⁻¹' U) :
    Integrable (fun x => fderiv ℝ ψ.val x ((linearColumnsPullback P Q G x).col j)) ∧
      (∫ x,fderiv ℝ ψ.val x ((linearColumnsPullback P Q G x).col j))=0 := by
  have hcont (k : Fin 2) : Continuous (linearFluxPullback P (fun y => (G y).col k)) := by
    have hgk : Continuous (fun y => (G y).col k) :=
      continuous_pi fun i => (continuous_apply k).comp ((continuous_apply i).comp hGc)
    exact P.symm.continuous.comp (hgk.comp P.continuous)
  have hI (k : Fin 2) := continuous_flux_compact_test_integrable (hcont k) ψ hc
  have hw (k : Fin 2) := linearFluxPullback_weak P (hG k) ψ hc hs
  have he (x : Coord3) : fderiv ℝ ψ.val x ((linearColumnsPullback P Q G x).col j)=
      ∑ k,operatorMatrix (Q : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) j k *
        fderiv ℝ ψ.val x (linearFluxPullback P (fun y => (G y).col k) x) := by
    rw [linearColumnsPullback_col,map_sum]
    simp only [map_smul,smul_eq_mul]
  simp_rw [he]
  constructor
  · exact integrable_finsetSum _ (fun k _ => (hI k).const_mul _)
  · rw [integral_finsetSum _ (fun k _ => (hI k).const_mul _)]
    simp only [integral_const_mul,hw,mul_zero,Finset.sum_const_zero]

lemma linearTensorPullback_C1_representative (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ))
    {u : Coord3 → Fin 2 → ℝ} (hu : Differentiable ℝ u) {A : Coord3 → Mat3}
    {G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ}
    (hG : ∀ᵐ x : Coord3,A x*gradientColumns (fderiv ℝ u x)=G x) :
    ∀ᵐ x : Coord3,linearTensorPullback P A x*
      gradientColumns (fderiv ℝ (fun y => Q (u (P y))) x)=linearColumnsPullback P Q G x := by
  filter_upwards [(continuousLinearEquiv_quasiMeasurePreserving P).ae hG] with x hx
  rw [linearTensorPullback_columns P Q A (hu _),hx]
  rfl

end ScalarConductivity

end

end OAI
