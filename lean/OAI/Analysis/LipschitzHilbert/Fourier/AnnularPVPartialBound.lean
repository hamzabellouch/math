import OAI.Analysis.LipschitzHilbert.Fourier.AnnularPVCommutatorSquare
import OAI.Analysis.LipschitzHilbert.Fourier.AnnularBoundedSynthesis
import OAI.Analysis.LipschitzHilbert.Fourier.AnnularPVFromNarrow
import OAI.Analysis.LipschitzHilbert.Fourier.AnnularPVReconstruction

namespace OAI

/-! The finite annular output has a uniform L2 bound, derived directly
from the annular input estimates and actual signed PV commutators. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

def annularPVBoundConstant (D : ℝ) : ℝ :=
  Real.sqrt 12*Real.sqrt (2*(signedPVCommutatorConstant^2+12*D^2))

theorem annularPVComm_eq (N : ℕ) (i : Fin (2*N+1)) (u : (ℝ×ℝ) → ℝ)
    (R : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    annularPVComm N u R f i=
      annularBoundedComponent N (productSlopePrincipalValue u R f) i-
      productSlopePrincipalValue u R
        (schwartzVerticalProjection reassemblyDifferenceSchwartz (reassemblyScale N i) 0 f) := by
  unfold annularPVComm annularProfile principalValueProfileCommutator
  rw [verticalMultiplier_dilate _ _ 1 (reassemblyScale_pos N i) (by norm_num),
    schwartzVerticalProjection_dilate,mul_one]
  rfl

theorem annularPVPartial_bound (N : ℕ) (field : Plane → ℝ) (hf : LipschitzWith 1 field)
    (hfb : ∀ z, |field z|≤1/4) (R : ℝ) (hR : 0<R) (hRs : R≤1/4)
    (D : ℝ) (hD : 0≤D)
    (hband : ∀ W : ℝ, 0<W → ∀ g : SchwartzMap (ℝ×ℝ) ℂ,
      (∀ omega, planarFourier g omega≠0 → W*omega.2∈fixedAnnulus) →
      MemLp (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R g) 2 planeMeasure ∧
      eLpNorm (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R g) 2 planeMeasure≤
        ENNReal.ofReal (D*‖g.toLp 2 planeMeasure‖))
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (annularPVPartial N (fun z => field (planeCoordinates z)) R f) 2 planeMeasure ∧
      eLpNorm (annularPVPartial N (fun z => field (planeCoordinates z)) R f) 2 planeMeasure≤
        ENNReal.ofReal (annularPVBoundConstant D*‖f.toLp 2 planeMeasure‖) := by
  let u := fun z => field (planeCoordinates z)
  let p := fun i : Fin (2*N+1) =>
    schwartzVerticalProjection reassemblyDifferenceSchwartz (reassemblyScale N i) 0 f
  let V := fun i : Fin (2*N+1) => productSlopePrincipalValue u R (p i)
  let G := annularBoundedComponent N (productSlopePrincipalValue u R f)
  obtain ⟨hc,hcBound⟩ := annularPVComm_square N field hf hfb R hR hRs f
  have hv (i : Fin (2*N+1)) : MemLp (V i) 2 planeMeasure ∧
      eLpNorm (V i) 2 planeMeasure≤ENNReal.ofReal (D*‖(p i).toLp 2 planeMeasure‖) :=
    hband _ (reassemblyScale_pos N i) (p i)
      (annularProjection_fourier_support reassemblyDifferenceSchwartz reassemblyDifference_fixedAnnulus
        (reassemblyScale N i) f)
  have hGid (i : Fin (2*N+1)) : G i=annularPVComm N u R f i+V i := by
    rw [annularPVComm_eq]
    exact (sub_add_cancel _ _).symm
  have hG (i : Fin (2*N+1)) : MemLp (G i) 2 planeMeasure := by
    rw [hGid]
    exact (hc i).add (hv i).1
  have hGlp (i : Fin (2*N+1)) : (hG i).toLp (G i)=
      (hc i).toLp (annularPVComm N u R f i)+(hv i).1.toLp (V i) := by
    apply Lp.ext
    filter_upwards [(hG i).coeFn_toLp,(hc i).coeFn_toLp,(hv i).1.coeFn_toLp,
      Lp.coeFn_add ((hc i).toLp _) ((hv i).1.toLp _)] with z hg he hb ha
    rw [hg,ha]
    simp only [Pi.add_apply]
    rw [he,hb]
    exact congrFun (hGid i) z
  have hvNorm (i : Fin (2*N+1)) : ‖(hv i).1.toLp (V i)‖≤D*‖(p i).toLp 2 planeMeasure‖ := by
    rw [Lp.norm_toLp]
    have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hv i).2
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hD (norm_nonneg _))] using he
  have hpSquare : (∑ i : Fin (2*N+1), ‖(p i).toLp 2 planeMeasure‖^2)≤
      12*‖f.toLp 2 planeMeasure‖^2 := by
    have hh := annular_upper_frame N (f.toLp 2 planeMeasure)
    simp only [verticalL2Projection_onSchwartz _ _ (reassemblyScale_pos N _)] at hh
    rw [Fin.sum_univ_eq_sum_range (fun n =>
      ‖(schwartzVerticalProjection reassemblyDifferenceSchwartz (reassemblyScale N n) 0 f).toLp 2 planeMeasure‖^2)]
    exact hh
  have hvSquare : (∑ i, ‖(hv i).1.toLp (V i)‖^2)≤12*D^2*‖f.toLp 2 planeMeasure‖^2 := by
    calc
      _ ≤ ∑ i : Fin (2*N+1), (D*‖(p i).toLp 2 planeMeasure‖)^2 :=
        Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hvNorm i) 2)
      _ = D^2*(∑ i : Fin (2*N+1), ‖(p i).toLp 2 planeMeasure‖^2) := by
        simp only [mul_pow,Finset.mul_sum]
      _ ≤ D^2*(12*‖f.toLp 2 planeMeasure‖^2) :=
        mul_le_mul_of_nonneg_left hpSquare (sq_nonneg D)
      _ = _ := by ring
  have hcSquare : (∑ i, ‖(hc i).toLp (annularPVComm N u R f i)‖^2)≤
      signedPVCommutatorConstant^2*‖f.toLp 2 planeMeasure‖^2 := by
    apply hcBound.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply pow_le_pow_left₀ (mul_nonneg signedPVCommutatorConstant_nonneg hR.le) _ 2
    exact mul_le_of_le_one_right signedPVCommutatorConstant_nonneg (by linarith)
  have hgSquare : (∑ i, ‖(hG i).toLp (G i)‖^2)≤
      (2*(signedPVCommutatorConstant^2+12*D^2))*‖f.toLp 2 planeMeasure‖^2 := by
    have hpoint (i : Fin (2*N+1)) : ‖(hG i).toLp (G i)‖^2≤
        2*‖(hc i).toLp (annularPVComm N u R f i)‖^2+2*‖(hv i).1.toLp (V i)‖^2 := by
      rw [hGlp]
      have ht := norm_add_le ((hc i).toLp (annularPVComm N u R f i)) ((hv i).1.toLp (V i))
      have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
      nlinarith [sq_nonneg (‖(hc i).toLp (annularPVComm N u R f i)‖-‖(hv i).1.toLp (V i)‖)]
    have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hpoint i)
    simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
    nlinarith only [hh,hcSquare,hvSquare]
  have hsum := annularBounded_synthesis N (productSlopePrincipalValue u R f)
    (productSlopePrincipalValue_measurable u (hf.continuous.measurable.comp planeCoordinates.measurable)
      f f.differentiable R hR hRs) (2*((_root_.OAI.SchwartzMap.globalLipschitzConstant f):ℝ)*R)
    (fun z => productSchwartzPV_pointwise_bound u z ((hfb _).trans (by norm_num)) f R hR) hG
  have hn : ‖(finiteFunctionSum_memLp G hG).toLp (fun z => ∑ i, G i z)‖≤
      annularPVBoundConstant D*‖f.toLp 2 planeMeasure‖ := by
    apply hsum.trans
    apply (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hgSquare) (Real.sqrt_nonneg 12)).trans_eq
    rw [Real.sqrt_mul (by positivity : 0≤2*(signedPVCommutatorConstant^2+12*D^2)),
      Real.sqrt_sq (norm_nonneg (f.toLp 2 planeMeasure))]
    dsimp only [annularPVBoundConstant]
    ring
  have hid : (fun z => ∑ i, G i z)=annularPVPartial N u R f := by
    funext z
    simpa only [G,annularBoundedComponent,annularPVPartial,Finset.sum_apply] using
      Fin.sum_univ_eq_sum_range (fun n => verticalConvolution
      (verticalProfileKernel reassemblyDifferenceSchwartz (reassemblyScale N n) 0)
      (productSlopePrincipalValue u R f) z) (2*N+1)
  have hm : MemLp (annularPVPartial N u R f) 2 planeMeasure := by
    rw [←hid]
    exact finiteFunctionSum_memLp G hG
  refine ⟨hm,?_⟩
  rw [←hid,←Lp.enorm_toLp (finiteFunctionSum_memLp G hG),←ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hn

end LipschitzHilbert.PacketRepresentation

end

end OAI
