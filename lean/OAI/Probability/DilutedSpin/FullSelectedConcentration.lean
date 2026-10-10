import OAI.Probability.DilutedSpin.ActualRootVariance
import OAI.Probability.DilutedSpin.FullSelectedRegularity

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

/-- Concentration of the actual selected corrected score under the full common
reservoir law. The variance estimate is produced from replacement controls,
not a premise. All unselected types keep their original factors and priors. -/
theorem full_selected_corrected_concentration
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (hbmeas : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    {B C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ h k x y, |base h k x y| ≤ B+C*k)
    (hf : ∀ i x y, |Real.log (fixed i x y)| ≤ 1)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (hrep : ∀ h k (j : Fin k) x z y,
      |base h k x y-base h k (replaceRoot k x j z) y| ≤ 2*C)
    (hadd : ∀ h k z x y, |base h (k+1) (z,x) y-base h k x y| ≤ C)
    (fieldBound : Fin M → ℝ)
    (hfield : ∀ j h z k x y, |base h k x y-base (replaceRoot M h j z) k x y| ≤ fieldBound j)
    {t a b ρ : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hρ : 0 < ρ)
    (hJ : Icc (a-ρ) (b+ρ) ⊆ Ioo (-(1:ℝ)/4) (1/4)) :
    let G := fullSelectedScore T Q m base sel fixed D E t
    (∫ u in a..b, (∫ z, |G z u-∫ w, G w u ∂fullRootLaw ξ μ ν r s| ∂fullRootLaw ξ μ ν r s))/(b-a) ≤
      4*Real.sqrt (3*C^2*(r:ℝ)+4*(s:ℝ)+∑ j, (fieldBound j)^2/2)/ρ+12*ρ*(s:ℝ)/(b-a) := by
  let F := fullSelectedLog T Q m base sel fixed D E t
  let G := fullSelectedScore T Q m base sel fixed D E t
  have hFeq (z : FullRootState Y X I M) : F z =
      KernelTower.correctedPerturbLog (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m
        (otherLog (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) sel fixed)
        (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel D)
        (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel E) t :=
    funext (fun u => fullSelectedLog_eq T Q m base sel fixed D E t z u)
  have hu (u : ℝ) (h : u ∈ Ioo (-(1:ℝ)/4) (1/4)) : |u| ≤ 1/4 :=
    abs_le.mpr ⟨by linarith [h.1],h.2.le⟩
  have hbsel (u : ℝ) (h : u ∈ Ioo (-(1:ℝ)/4) (1/4)) :=
    selectedFactor_log_bound sel fixed D E hf hD hE ht (hu u h)
  have hFm (u : ℝ) : Measurable (fun z => F z u) :=
    measurable_fullSelectedLog T Q m base sel fixed D E t hbmeas u
  have hGm : Measurable (fun z : FullRootState Y X I M × ℝ => G z.1 z.2) :=
    measurable_fullSelectedScore T Q m base sel fixed D E t hbmeas
  have hfc (z : FullRootState Y X I M) : ConvexOn ℝ (Ioo (-(1:ℝ)/4) (1/4)) (F z) := by
    have hh := (KernelTower.correctedPerturbLog_convex
      (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m hm
      (otherLog (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) sel fixed)
      (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel D)
      (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel E)
      (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht).subset
      Ioo_subset_Icc_self (convex_Ioo _ _)
    rw [hFeq]
    exact hh
  have hLp (u : ℝ) (h : u ∈ Ioo (-(1:ℝ)/4) (1/4)) :
      MemLp (fun z => F z u) 2 (fullRootLaw ξ μ ν r s) := by
    refine fullRoot_memLp_linear ξ μ ν r s
      (F := fun h k x n y => root T Q m (base h k x) (rootArray n y)
        (selectedFactor sel fixed D E t u)+(2*u^2)*n)
      (B := B) (C := C) (D := 1+|2*u^2|) ?_ ?_
    · intro k n
      exact (measurable_root_base T Q m (fun z : RootPath Y M × RootPath X k => base z.1 k z.2)
        (hbmeas k) (selectedFactor sel fixed D E t u) n).add measurable_const
    · intro h' k x n y
      have hh := root_uniform_bound T Q m hm (base h' k x) (rootArray n y)
        (selectedFactor sel fixed D E t u) (hb h' k x) (hbsel u h)
      calc
        _ ≤ |root T Q m (base h' k x) (rootArray n y) (selectedFactor sel fixed D E t u)|+|(2*u^2)*(n:ℝ)| := abs_add_le _ _
        _ ≤ B+C*k+1*n+|2*u^2| *n := by
          rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
          exact add_le_add hh le_rfl
        _ = _ := by ring
  have hbound (z : FullRootState Y X I M) (u : ℝ) (h : u ∈ Ioo (-(1:ℝ)/4) (1/4)) :
      |G z u| ≤ 3*(z.2.2.1:ℝ) := by
    rw [show G z u = _ from fullSelectedScore_eq T Q m base sel fixed D E t z u]
    exact KernelTower.correctedPerturbScore_bound _ _ _ _ _
      (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht (hu u h)
  have hd (z : FullRootState Y X I M) (u : ℝ) (h : u ∈ Ioo (-(1:ℝ)/4) (1/4)) :
      HasDerivAt (F z) (G z u) u := by
    have hp (q : Fin z.2.2.1) (y : FinitePath (Ω × Row (A := A) (rootArray z.2.2.1 z.2.2.2)) L) :
        0 < 1+t*selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel D q y+
          u*selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel E q y := by
      have hh := KernelTower.perturb_factor_lower _ _
        (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht (hu u h) q y
      linarith
    rw [hFeq,show G z u = _ from fullSelectedScore_eq T Q m base sel fixed D E t z u]
    exact KernelTower.hasDerivAt_correctedPerturbLog (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m (fun j => ne_of_gt (hm j))
        (otherLog (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) sel fixed) _ _ t u hp
  have hv (u : ℝ) (h : u ∈ Icc (a-ρ) (b+ρ)) :
      variance (fun z => F z u) (fullRootLaw ξ μ ν r s) ≤
        3*C^2*(r:ℝ)+4*(s:ℝ)+∑ j, (fieldBound j)^2/2 := by
    have hh := variance_actual_root μ ν ξ r s T Q m hm base hbmeas
      (selectedFactor sel fixed D E t u) hC (by norm_num : (0:ℝ) ≤ 1) hb (hbsel u (hJ h))
      hrep hadd fieldBound hfield (2*u^2)
    have hsq := mul_self_le_mul_self (abs_nonneg u) (hu u (hJ h))
    simp only [← pow_two,sq_abs] at hsq
    have hc : |2*u^2| ≤ 1/8 := by
      rw [abs_of_nonneg (by positivity)]
      nlinarith
    have hcc := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ 1+|2*u^2|)
      (show 1+|2*u^2| ≤ 9/8 by linarith)
    have hcoef : 3*(1+|2*u^2|)^2 ≤ 4 := by nlinarith
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hcoef s.coe_nonneg])
  have hh := root_derivative_integral_bound (fullRootLaw ξ μ ν r s)
    isOpen_Ioo (convex_Ioo _ _) hFm hGm hfc hLp
    (((fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)).const_mul 3) hbound hd hab hρ hJ hv
  rw [integral_const_mul,fullRoot_count_mean] at hh
  convert hh using 1; ring

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
