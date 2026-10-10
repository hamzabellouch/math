import Mathlib
import OAI.Analysis.Conductivity.Flux.FlatBackgroundTensor
import OAI.Analysis.Conductivity.Flux.AxialFluxBlend

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

def endingJoinCutoff (t : ℝ) : ℝ := smoothTransition (t-6)

lemma endingJoinCutoff_smooth : ContDiff ℝ (↑(⊤:ℕ∞)) endingJoinCutoff :=
  smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

lemma endingJoinCutoff_bounds (t : ℝ) : 0≤endingJoinCutoff t ∧ endingJoinCutoff t≤1 :=
  ⟨smoothTransition.nonneg _,smoothTransition.le_one _⟩

lemma endingJoinCutoff_left {t : ℝ} (ht : t≤6) : endingJoinCutoff t=0 :=
  smoothTransition.zero_of_nonpos (by linarith)

lemma endingJoinCutoff_right {t : ℝ} (ht : 7≤t) : endingJoinCutoff t=1 :=
  smoothTransition.one_of_one_le (by linarith)

lemma endingJoinCutoff_deriv_zero {t : ℝ} (ht : t∉Icc (6:ℝ) 7) : deriv endingJoinCutoff t=0 := by
  have he : t<6 ∨ 7<t := by simpa only [mem_Icc,not_and_or,not_le] using ht
  rcases he with he|he
  · have hh : endingJoinCutoff=ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds he] with y hy
      exact endingJoinCutoff_left hy.le
    rw [hh.deriv_eq,deriv_const]
  · have hh : endingJoinCutoff=ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds he] with y hy
      exact endingJoinCutoff_right hy.le
    rw [hh.deriv_eq,deriv_const]

def endingJoinTensor (D : Coord3 → Mat3) (lam k J L K : ℝ) (x : Coord3) : Mat3 :=
  (1-endingJoinCutoff (x 0)) • D x+endingJoinCutoff (x 0) • delayedEndingTensor lam k J L K 7 x

lemma endingJoinTensor_left (D : Coord3 → Mat3) (lam k J L K : ℝ) (x : Coord3) (hx : x 0≤6) :
    endingJoinTensor D lam k J L K x=D x := by
  simp [endingJoinTensor,endingJoinCutoff_left hx]

lemma endingJoinTensor_right (D : Coord3 → Mat3) (lam k J L K : ℝ) (x : Coord3) (hx : 7≤x 0) :
    endingJoinTensor D lam k J L K x=delayedEndingTensor lam k J L K 7 x := by
  simp [endingJoinTensor,endingJoinCutoff_right hx]

lemma normal_flux_of_symm {A : Mat3} (hA : A.IsSymm) (hn : A*ᵥPi.single 0 1=Pi.single 0 1) (v : Coord3) :
    (A*ᵥv) 0=v 0 := by
  have h (i : Fin 3) : A i 0=if i=0 then 1 else 0 := by
    have hh := congrFun hn i
    simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_three,Pi.single_apply] using hh
  have hs (i : Fin 3) : A 0 i=A i 0 := congrFun (congrFun hA i) 0
  simp [Matrix.mulVec,dotProduct,hs,h]

lemma flatBackgroundTensor_normal (s : Fin 3 → ℝ) :
    flatBackgroundTensor s*ᵥPi.single 0 1=Pi.single 0 1 := by
  ext i
  fin_cases i <;> simp [flatBackgroundTensor,Matrix.mulVec,dotProduct,Pi.single_apply]

end ScalarConductivity

end
end

end OAI
