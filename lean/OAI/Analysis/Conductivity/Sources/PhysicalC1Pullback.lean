import Mathlib
import OAI.Analysis.Conductivity.Variational.UniformC1Bounds
import OAI.Analysis.Conductivity.Sources.LocalPhysicalCorrection

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

def inverseSourceWeight (X : OpenPartialHomeomorph Coord3 Coord3) (x : Coord3) : ℝ :=
  |(fderiv ℝ X.symm (X x)).det|⁻¹

lemma inverseSourceWeight_smooth
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤:ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤:ℕ∞)) X.symm X.target) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (inverseSourceWeight X) X.source := by
  apply X.open_source.contDiffOn_iff.mpr
  intro x hx
  have hxs := hX.contDiffAt (X.open_source.mem_nhds hx)
  have hxis := hXi.contDiffAt (X.open_target.mem_nhds (X.map_source hx))
  have hd : ContDiffAt ℝ (↑(⊤:ℕ∞)) (fun y => fderiv ℝ X.symm (X y)) x :=
    (hxis.fderiv_right (by trivial)).comp x hxs
  have hd0 := local_fderiv_det_ne_zero X.symm (hXi.differentiableOn (by simp))
    (hX.differentiableOn (by simp)) (X.map_source hx)
  exact ((((contDiff_clm_det (E := Coord3) (↑(⊤:ℕ∞))).contDiffAt.comp x hd).abs hd0).inv
    (abs_ne_zero.mpr hd0))

lemma compact_smooth_C1_bound {f : Coord3 → ℝ} {U K : Set Coord3}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f U)
    (hK : IsCompact K) (hKU : K⊆U) :
    ∃ M : ℝ,0<M ∧ ∀ x∈K,|f x|≤M ∧ ‖fderiv ℝ f x‖≤M := by
  have hd : ContinuousOn (fderiv ℝ f) U := by
    intro x hx
    exact ((hf.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 0) (by simp)).continuousAt.continuousWithinAt
  obtain ⟨A,hA⟩ := (hK.image_of_continuousOn (hf.continuousOn.mono hKU)).isBounded.exists_norm_le
  obtain ⟨B,hB⟩ := (hK.image_of_continuousOn (hd.mono hKU)).isBounded.exists_norm_le
  refine ⟨|A|+|B|+1,by positivity,fun x hx => ⟨?_,?_⟩⟩
  · exact (hA _ (mem_image_of_mem _ hx)).trans (by linarith [le_abs_self A,abs_nonneg B])
  · exact (hB _ (mem_image_of_mem _ hx)).trans (by linarith [le_abs_self B,abs_nonneg A])

theorem localPiolaSource_inverse_C1
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤:ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤:ℕ∞)) X.symm X.target)
    {K : Set Coord3} (hK : IsCompact K) (hKs : K⊆X.source) :
    ∃ L : ℝ,0<L ∧ ∀ (r : Coord3 → ℝ),ContDiff ℝ (↑(⊤:ℕ∞)) r →
      HasCompactSupport r → tsupport r⊆X '' K → ∀ M : ℝ,0≤M →
      UniformC1Bound r M → UniformC1Bound (localPiolaSource X.symm r) (L*M) := by
  let w := inverseSourceWeight X
  have hw := inverseSourceWeight_smooth X hX hXi
  obtain ⟨B,hB,hwb⟩ := compact_smooth_C1_bound X.open_source hw hK hKs
  have hdX : ContinuousOn (fderiv ℝ X) X.source := by
    intro x hx
    exact ((hX.contDiffAt (X.open_source.mem_nhds hx)).fderiv_right (m := 0) (by simp)).continuousAt.continuousWithinAt
  obtain ⟨D,hD⟩ := (hK.image_of_continuousOn (hdX.mono hKs)).isBounded.exists_norm_le
  have hDX (x) (hx : x∈K) : ‖fderiv ℝ X x‖≤|D|+1 :=
    (hD _ (mem_image_of_mem _ hx)).trans (by linarith [le_abs_self D])
  refine ⟨B*(|D|+2),by positivity,fun r hr hc hs M hM hb => ?_⟩
  let p := localPiolaSource X.symm r
  have hps : tsupport p⊆K := localPiolaSource_inverse_support X r hc hKs hs
  intro x
  change |p x| ≤ B*(|D|+2)*M ∧ ‖fderiv ℝ p x‖ ≤ B*(|D|+2)*M
  by_cases hx : x∈K
  · have hxs := hX.contDiffAt (X.open_source.mem_nhds (hKs hx))
    have hws := hw.contDiffAt (X.open_source.mem_nhds (hKs hx))
    have he : p=ᶠ[𝓝 x] (fun y => w y*r (X y)) := by
      filter_upwards [X.open_source.mem_nhds (hKs hx)] with y hy
      simp [p,localPiolaSource,hy,w,inverseSourceWeight]
    have hrc : DifferentiableAt ℝ (fun y => r (X y)) x :=
      (hr.differentiable (by simp) (X x)).comp x (hxs.differentiableAt (by simp))
    refine ⟨?_,?_⟩
    · rw [he.eq_of_nhds,abs_mul]
      exact (mul_le_mul (hwb x hx).1 (hb (X x)).1 (abs_nonneg _) hB.le).trans
        (by nlinarith [mul_nonneg hB.le hM,abs_nonneg D])
    · rw [he.fderiv_eq,fderiv_fun_mul (hws.differentiableAt (by simp)) hrc]
      have hchain := ((hr.differentiable (by simp) (X x)).hasFDerivAt.comp x
        (hxs.differentiableAt (by simp)).hasFDerivAt).fderiv
      have hcomp : ‖fderiv ℝ (fun y => r (X y)) x‖≤M*(|D|+1) := by
        change ‖fderiv ℝ (r ∘ X) x‖ ≤ _
        rw [hchain]
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (hb (X x)).2 (hDX x hx) (norm_nonneg _) hM)
      calc
        _ ≤ ‖w x • fderiv ℝ (fun y => r (X y)) x‖+‖r (X x) • fderiv ℝ w x‖ := norm_add_le _ _
        _ = |w x| *‖fderiv ℝ (fun y => r (X y)) x‖+|r (X x)| *‖fderiv ℝ w x‖ := by
          simp only [norm_smul,Real.norm_eq_abs]
        _ ≤ B*(M*(|D|+1))+M*B := add_le_add
          (mul_le_mul (hwb x hx).1 hcomp (norm_nonneg _) hB.le)
          (mul_le_mul (hb (X x)).1 (hwb x hx).2 (norm_nonneg _) hM)
        _ = _ := by ring
  · have hn : x∉tsupport p := fun h => hx (hps h)
    rw [image_eq_zero_of_notMem_tsupport hn,fderiv_of_notMem_tsupport ℝ hn,abs_zero,norm_zero]
    exact ⟨by positivity,by positivity⟩

end ScalarConductivity

end

end OAI
