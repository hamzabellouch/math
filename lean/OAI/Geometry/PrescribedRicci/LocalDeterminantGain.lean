import Mathlib
import OAI.Geometry.PrescribedRicci.LocalDeterminantBound

namespace OAI

/-! Local Determinant Gain. -/

section

 

noncomputable section
open Set Filter Topology Matrix _root_.MeasureTheory _root_.OAI.MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap Classical Matrix.Norms.Elementwise BoundedContinuousFunction ENNReal
open scoped ComplexOrder MatrixOrder
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {Z : Type*}
lemma UniformSobolev.neg {s : ℝ} {F : Z → 𝓢(E,ℂ)} (hF : UniformSobolev s F) :
    UniformSobolev s (fun z => -F z) := by
  obtain ⟨C,hC,hc⟩ := hF
  refine ⟨C,hC,fun z => ?_⟩
  have he : schwartzCoord s (-F z) = -schwartzCoord s (F z) := by
    simpa only [neg_one_smul] using schwartzCoord_smul s (-1) (F z)
  change ‖schwartzCoord s (-F z)‖ ≤ C
  rw [he,norm_neg]
  exact hc z

lemma UniformSobolev.sub {s : ℝ} {F G : Z → 𝓢(E,ℂ)}
    (hF : UniformSobolev s F) (hG : UniformSobolev s G) :
    UniformSobolev s (fun z => F z-G z) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg
end SobolevChart
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart FrozenPoisson MetricLocalization TameInterpolation
variable {d : ℕ} [Nonempty (Fin d)] {Z : Type*}

lemma uniform_determinant_word_differential
    {ι : Type*} [Fintype ι] [Nonempty ι] (e : ι → EC d) (ws : List ι) (hw : ws ≠ [])
    (κ : 𝓢(EC d,ℂ)) (f ρ : Z → 𝓢(EC d,ℂ)) (G H : Z → Fin d → Fin d → 𝓢(EC d,ℂ))
    (c : Z → BasisIndex d → BasisIndex d → EC d →ᵇ ℂ)
    (hc : ∀ z i j, (c z i j : EC d → ℂ).HasTemperateGrowth)
    (hec : ∀ z y, y ∈ tsupport (κ : EC d → ℂ) → ∀ i j,
      c z i j y = (traceBilin (fun k l => H z k l y)
        (rankTwo (stdOrthonormalBasis ℝ (EC d) i) (stdOrthonormalBasis ℝ (EC d) j)) : ℂ))
    (hr : ∀ z y, (SchwartzMap.smulLeftCLM ℂ κ (schwartzWord (ws.map e) (f z)) y).im = 0)
    (he : ∀ z y, y ∈ tsupport (κ : EC d → ℂ) → ∀ i j,
      (H z i j : EC d → ℂ) =ᶠ[𝓝 y] (fun x => G z i j x+hessianEntrySchwartz i j (f z) x))
    (heρ : ∀ z y, y ∈ tsupport (κ : EC d → ℂ) →
      (fun x => (show Matrix (Fin d) (Fin d) ℂ from fun i j => H z i j x).det) =ᶠ[𝓝 y] ρ z)
    (hinv : ∀ z y, y ∈ tsupport (κ : EC d → ℂ) →
      IsUnit (show Matrix (Fin d) (Fin d) ℂ from fun i j => H z i j y).det)
    {B J : ℝ} (hB : 0 ≤ B) (hJ : 0 ≤ J)
    (hb : ∀ z y, y ∈ tsupport (κ : EC d → ℂ) → ∀ i j,
      ‖(show Matrix (Fin d) (Fin d) ℂ from fun i j => H z i j y)⁻¹ i j‖ ≤ B)
    (hj : ∀ z y, y ∈ tsupport (κ : EC d → ℂ) →
      ‖(show Matrix (Fin d) (Fin d) ℂ from fun i j => H z i j y).det⁻¹‖ ≤ J)
    (hF : UniformSobolev ((ws.length:ℝ)+1) f)
    (hρ : UniformSobolev (ws.length:ℝ) ρ)
    (hG : ∀ i j, UniformSobolev (ws.length:ℝ) (fun z => G z i j))
    (hHc : ∀ z i j, HasCompactSupport (H z i j : EC d → ℂ))
    (hH0 : ∀ σ : Equiv.Perm (Fin d), ∃ A : ℝ, 0 ≤ A ∧ ∀ z,
      familyJetNorm e (realComponents (initialJet e (fun i x => H z (σ i) i x))) 0 ∞ ≤ A)
    (hHS : ∀ i j, UniformSobolev ((ws.length:ℝ)-1) (fun z => H z i j)) :
    UniformSobolev 0 (fun z => schwartzDifferential (c z)
      (SchwartzMap.smulLeftCLM ℂ κ (schwartzWord (ws.map e) (f z)))) := by
  let K := ‖κ.toBoundedContinuousFunction‖
  have hK : 0 ≤ K := norm_nonneg _
  have hk (y) : ‖κ y‖ ≤ K := κ.toBoundedContinuousFunction.norm_coe_le_norm y
  let R (z : Z) := detJetRemainder e (fun x i j => H z i j x) ws
  have hR : UniformL2 R := detJetRemainder_uniformL2 e H hHc ws hH0 hHS
  have hp : UniformL2 (fun z x => ‖schwartzWord (ws.map e) (ρ z) x‖) :=
    (hρ.word (ws.map e) (by simp)).uniformL2.norm
  have herr (i j) : UniformL2 (fun z x => ‖wordHessianError κ (ws.map e) i j (f z) x‖) := by
    apply UniformL2.norm
    apply UniformSobolev.uniformL2
    apply hF.of_coreBound
    simpa only [List.length_map] using wordHessianError_bound κ (ws.map e) i j
  have hbg (i j) : UniformL2 (fun z x => K*‖schwartzWord (ws.map e) (G z i j) x‖) := by
    simpa only [smul_eq_mul] using ((hG i j).word (ws.map e) (by simp)).uniformL2.norm.smul K
  have hmajor : UniformL2 (fun z y =>
      K*J*(‖schwartzWord (ws.map e) (ρ z) y‖+‖R z y‖)+
        B*∑ i, ∑ j, (‖wordHessianError κ (ws.map e) j i (f z) y‖+
          K*‖schwartzWord (ws.map e) (G z j i) y‖)) := by
    simpa only [smul_eq_mul] using ((hp.add hR.norm).smul (K*J)).add
      ((UniformL2.sum Finset.univ (fun i => fun z y => ∑ j, (‖wordHessianError κ (ws.map e) j i (f z) y‖+
        K*‖schwartzWord (ws.map e) (G z j i) y‖)) (fun i _ =>
          UniformL2.sum Finset.univ _ (fun j _ => (herr j i).add (hbg j i)))).smul B)
  apply UniformSobolev.zero_of_majorant hmajor
  intro z y
  by_cases hy : y ∈ tsupport (κ : EC d → ℂ)
  · rw [schwartzDifferential_apply _ (hc z)]
    have hsum : (∑ i, ∑ j, c z i j y *
        fderiv ℝ (fderiv ℝ (SchwartzMap.smulLeftCLM ℂ κ (schwartzWord (ws.map e) (f z)))) y
          (stdOrthonormalBasis ℝ (EC d) i) (stdOrthonormalBasis ℝ (EC d) j)) =
        (((show Matrix (Fin d) (Fin d) ℂ from fun i j => H z i j y)⁻¹ *
          (show Matrix (Fin d) (Fin d) ℂ from fun i j => hessianEntrySchwartz i j
            (SchwartzMap.smulLeftCLM ℂ κ (schwartzWord (ws.map e) (f z))) y)).trace.re : ℂ) := by
      simp_rw [hec z y hy]
      exact schwartz_real_trace_expression _ (hinv z y hy) _ (hr z) y
    rw [hsum,Complex.norm_real,Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans
      (determinant_word_cutoff_bound e ws hw κ (f z) (G z) (H z) (ρ z) y
        (he z y hy) (heρ z y hy) (hinv z y hy) hB hJ (hb z y hy) (hj z y hy) (hk y))
  · have hzero : schwartzDifferential (c z) (SchwartzMap.smulLeftCLM ℂ κ (schwartzWord (ws.map e) (f z))) y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hy (((schwartzDifferential_tsupport _ _).trans
        ((SchwartzMap.tsupport_smulLeftCLM_subset _ _).trans inter_subset_right)) ht))
    rw [hzero,norm_zero]
    exact add_nonneg (mul_nonneg (mul_nonneg hK hJ) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
      (mul_nonneg hB (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        add_nonneg (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))))
end GlobalElliptic

end
end

end OAI
