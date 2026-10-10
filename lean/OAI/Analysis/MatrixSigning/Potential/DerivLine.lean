import Mathlib
import OAI.Analysis.MatrixSigning.Calculus.NormSmulRightId

namespace OAI

open Matrix

namespace CurrentKS.Difference

section
open Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma deriv_line {f : E → ℝ} {x h : E} {t : ℝ}
    (hf : DifferentiableAt ℝ f (x+t • h)) :
    deriv (fun s : ℝ => f (x+s • h)) t = fderiv ℝ f (x+t • h) h := by
  have hh : HasDerivAt (fun s : ℝ => x+s • h) h t := by
    have hh := ((hasDerivAt_id t).smul_const h).const_add x
    simp only [one_smul] at hh
    exact hh
  exact (hf.hasFDerivAt.comp_hasDerivAt t hh).deriv

lemma deriv_line_eventually {f : E → ℝ} {x h : E} {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (x+t • h)) :
    deriv (fun s : ℝ => f (x+s • h)) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ f (x+s • h) h) := by
  have hh : HasDerivAt (fun s : ℝ => x+s • h) h t := by
    have hh := ((hasDerivAt_id t).smul_const h).const_add x
    simp only [one_smul] at hh
    exact hh
  have he : ∀ᶠ s in 𝓝 t, ContDiffAt ℝ 2 f (x+s • h) :=
    (hf.eventually (by norm_num)).filter_mono hh.continuousAt
  filter_upwards [he] with s hs
  exact deriv_line (hs.differentiableAt (by norm_num))

lemma deriv_fderiv_line {f : E → ℝ} {x h : E} {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (x+t • h)) :
    deriv (fun s : ℝ => fderiv ℝ f (x+s • h) h) t =
      fderiv ℝ (fderiv ℝ f) (x+t • h) h h := by
  have hh : HasDerivAt (fun s : ℝ => x+s • h) h t := by
    have hh := ((hasDerivAt_id t).smul_const h).const_add x
    simp only [one_smul] at hh
    exact hh
  have hfdc : ContDiffAt ℝ 1 (fderiv ℝ f) (x+t • h) :=
    hf.fderiv_right (by norm_num)
  have hfd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (x+t • h)) (x+t • h) :=
    (hfdc.differentiableAt (by norm_num)).hasFDerivAt
  have hc : HasDerivAt (fun s : ℝ => fderiv ℝ f (x+s • h))
      (fderiv ℝ (fderiv ℝ f) (x+t • h) h) t := hfd.comp_hasDerivAt t hh
  have hd : HasDerivAt (fun s : ℝ => fderiv ℝ f (x+s • h) h)
      (fderiv ℝ (fderiv ℝ f) (x+t • h) h h+fderiv ℝ f (x+t • h) 0) t :=
    hc.clm_apply (hasDerivAt_const t h)
  simpa only [map_zero,add_zero] using hd.deriv

lemma second_deriv_line {f : E → ℝ} {x h : E} {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (x+t • h)) :
    deriv (deriv (fun s : ℝ => f (x+s • h))) t =
      fderiv ℝ (fderiv ℝ f) (x+t • h) h h := by
  exact (deriv_line_eventually hf).deriv_eq.trans (deriv_fderiv_line hf)

end

open scoped BigOperators

variable {N : ℕ}

lemma coordinate_expansion (x : Fin N → ℝ) : x = ∑ i, x i • (Pi.single i (1:ℝ) : Fin N → ℝ) := by
  classical
  ext j
  simp [Pi.single_apply,Finset.sum_apply]

lemma linear_coordinates (L : (Fin N → ℝ) →L[ℝ] ℝ) (x : Fin N → ℝ) :
    L x = ∑ i,x i*L (Pi.single i (1:ℝ)) := by
  conv_lhs => rw [coordinate_expansion x]
  simp only [map_sum,map_smul,smul_eq_mul]

lemma bilinear_coordinates (B : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ)
    (x y : Fin N → ℝ) :
    B x y = ∑ i,∑ j,(B (Pi.single i (1:ℝ)) (Pi.single j (1:ℝ)))*x i*y j := by
  conv_lhs => rw [coordinate_expansion x,coordinate_expansion y]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,
    smul_eq_mul,Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma linear_coordinate_bound (L : (Fin N → ℝ) →L[ℝ] ℝ) (x : Fin N → ℝ)
    {a C : ℝ} (_ha : 0 ≤ a) (hC : 0 ≤ C) (hx : ∀ i,|x i| ≤ C)
    (hL : ∀ i,|L (Pi.single i (1:ℝ))| ≤ a) : |L x| ≤ (N:ℝ)*a*C := by
  rw [linear_coordinates]
  calc
    _ ≤ ∑ i,|x i*L (Pi.single i (1:ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin N,C*a := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (hx i) (hL i) (abs_nonneg _) hC
    _ = (N:ℝ)*a*C := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

end CurrentKS.Difference

end OAI
