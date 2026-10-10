import Mathlib
import OAI.Analysis.Conductivity.Variational.SynchronizedChartWaves

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def coordinateDivergence (F : Coord3 → Coord3) (x : Coord3) : ℝ :=
  ∑ i : Fin 3,fderiv ℝ (fun y => F y i) x (Pi.single i 1)

lemma coordinate_fderiv_expansion (ψ : Coord3 → ℝ) (x v : Coord3) :
    fderiv ℝ ψ x v=∑ i : Fin 3,v i*fderiv ℝ ψ x (Pi.single i 1) := by
  have he : v=∑ i : Fin 3,v i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [he]
  simp

lemma coordinateDivergence_smooth {F : Coord3 → Coord3}
    (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (coordinateDivergence F) := by
  apply ContDiff.sum; intro i _
  exact (((contDiff_pi.mp hF) i).fderiv_right (by simp)).clm_apply contDiff_const

lemma coordinateDivergence_compact {F : Coord3 → Coord3}
    (hs : HasCompactSupport F) : HasCompactSupport (coordinateDivergence F) := by
  have hc (i : Fin 3) : HasCompactSupport (fun x => fderiv ℝ (fun y => F y i) x (Pi.single i 1)) := by
    have hci : HasCompactSupport (fun x => F x i) := hs.comp_left (g := fun v : Coord3 => v i) rfl
    exact hci.fderiv_apply ℝ _
  have he : coordinateDivergence F = fun x =>
      (fderiv ℝ (fun y => F y 0) x (Pi.single 0 1)+
       fderiv ℝ (fun y => F y 1) x (Pi.single 1 1))+
       fderiv ℝ (fun y => F y 2) x (Pi.single 2 1) := by
    funext x
    simp [coordinateDivergence,Fin.sum_univ_three]
  rw [he]
  exact ((hc 0).add (hc 1)).add (hc 2)

theorem coordinateDivergence_weak {F : Coord3 → Coord3}
    (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) (hs : HasCompactSupport F)
    (ψ : Coord3 → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) :
    (∫ x,fderiv ℝ ψ x (F x))= -(∫ x,ψ x*coordinateDivergence F x) := by
  have hc (i : Fin 3) : HasCompactSupport (fun x => F x i) :=
    hs.comp_left (g := fun v : Coord3 => v i) rfl
  have hFi (i : Fin 3) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => F x i) :=
    contDiff_pi.mp hF i
  have hdψ (i : Fin 3) : Continuous (fun x => fderiv ℝ ψ x (Pi.single i 1)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdF (i : Fin 3) : Continuous (fun x => fderiv ℝ (fun y => F y i) x (Pi.single i 1)) :=
    ((hFi i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hi₁ (i : Fin 3) : Integrable (fun x => F x i*fderiv ℝ ψ x (Pi.single i 1)) :=
    ((hFi i).continuous.mul (hdψ i)).integrable_of_hasCompactSupport (hc i).mul_right
  have hi₂ (i : Fin 3) : Integrable (fun x => ψ x*fderiv ℝ (fun y => F y i) x (Pi.single i 1)) :=
    (hψ.continuous.mul (hdF i)).integrable_of_hasCompactSupport ((hc i).fderiv_apply ℝ _).mul_left
  have he (i : Fin 3) : (∫ x,F x i*fderiv ℝ ψ x (Pi.single i 1))=
      -(∫ x,ψ x*fderiv ℝ (fun y => F y i) x (Pi.single i 1)) := by
    have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure Coord3))
      (f := ψ) (g := fun x => F x i) (v := Pi.single i 1)
      (by simpa only [mul_comm] using hi₁ i) (hi₂ i)
      ((hψ.continuous.mul (hFi i).continuous).integrable_of_hasCompactSupport (hc i).mul_left)
      (fun x _ => hψ.differentiable (by simp) x)
      (fun x _ => (hFi i).differentiable (by simp) x)
    have hh' : (∫ x,fderiv ℝ ψ x (Pi.single i 1)*F x i)=
        (∫ x,F x i*fderiv ℝ ψ x (Pi.single i 1)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => mul_comm _ _)
    rw [hh'] at hh
    linarith
  have hex : (fun x => fderiv ℝ ψ x (F x))=
      (fun x => ∑ i : Fin 3,F x i*fderiv ℝ ψ x (Pi.single i 1)) := by
    funext x
    exact coordinate_fderiv_expansion ψ x (F x)
  rw [hex]
  simp only [coordinateDivergence,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hi₁ i),integral_finsetSum _ (fun i _ => hi₂ i)]
  simp_rw [he]
  simp only [Finset.sum_neg_distrib]

end ScalarConductivity

end

end OAI
