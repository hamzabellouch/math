import Mathlib
import OAI.MathematicalPhysics.BFSS.ClosedProfiles

namespace OAI

/-! Closed weighted moments and basis-independent slice kinetic bounds. -/

namespace BFSSNormalAnalysis
noncomputable section
open MeasureTheory Filter Topology
variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {μ : Measure E}

theorem weighted_moment_closed (f : ℕ → Lp F 2 μ) (u : Lp F 2 μ)
    (w : E → ℝ) (hw : AEStronglyMeasurable w μ) (B : ℝ) (hB : 0 ≤ B)
    (hf : Tendsto f atTop (𝓝 u))
    (hm : ∀ n, MemLp (fun x => w x • f n x) 2 μ)
    (hb : ∀ n, ‖(hm n).toLp (fun x => w x • f n x)‖ ≤ B) :
    ∃ hu : MemLp (fun x => w x • u x) 2 μ,
      ‖hu.toLp (fun x => w x • u x)‖ ≤ B := by
  obtain ⟨σ,_,ha⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  have he : eLpNorm (fun x => w x • u x) 2 μ ≤ ENNReal.ofReal B := by
    apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (f := fun n x => w x • f (σ n) x)
    · exact Filter.Eventually.of_forall fun n => by
        rw [←ENNReal.toReal_le_toReal (hm (σ n)).eLpNorm_ne_top ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal hB]
        simpa only [Lp.norm_toLp] using hb (σ n)
    · exact fun n => (hm (σ n)).aestronglyMeasurable
    · exact hw.smul (Lp.memLp u).aestronglyMeasurable
    · filter_upwards [ha] with x hx
      exact tendsto_const_nhds.smul hx
  have hu : MemLp (fun x => w x • u x) 2 μ :=
    he.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hu,?_⟩
  rw [Lp.norm_toLp]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq (ENNReal.toReal_ofReal hB)
end
end BFSSNormalAnalysis
namespace BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch
noncomputable section
open MeasureTheory Set Filter Topology
variable {N : ℕ} {M : AlgebraData N} {G : M.GaugeData} {q : Boson N}
  (P : G.MeasuredNormalPatch q)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2

lemma profile_moment_mem (h : ℝ) (f : G.invariantCore) :
    MemLp (fun x : M.NormalCoordinates q => ‖x‖ • P.profile h f x) 2 volume := by
  have hc : MemLp (fun x : M.NormalCoordinates q => ‖x‖ •
      M.normalMeasuredCoordinates q h P.density P.cutoff f.val x) 2 volume := (continuous_norm.smul
    (M.normalMeasuredCoordinates_continuous q h P.density P.cutoff f.val
      P.density_continuous P.cutoff_continuous)).memLp_of_hasCompactSupport
        (M.normalMeasuredCoordinates_compactSupport q h P.density P.cutoff f.val).smul_left
  apply MemLp.ae_eq (hf_Lp := hc)
  filter_upwards [P.profile_ae h f] with x hx
  rw [hx]

lemma profile_moment_norm_sq (h : ℝ) (f : G.invariantCore) :
    ‖(P.profile_moment_mem h f).toLp (fun x => ‖x‖ • P.profile h f x)‖^2 =
      ∫ z : M.normalSlice q, ‖z‖^2*‖M.normalMeasuredField q h P.density P.cutoff f.val z‖^2 := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def,←M.normalMeasuredCoordinates_moment_integral]
  apply integral_congr_ae
  filter_upwards [(P.profile_moment_mem h f).coeFn_toLp, P.profile_ae h f] with x hx hf
  rw [hx,real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),mul_pow,hf]

theorem profile_limit_moment (h : ℕ → ℝ) (hh : ∀ n, 0 < h n ∧ h n ≤ 1)
    (f : ℕ → G.invariantCore) (B E : ℝ)
    (hnorm : ∀ n, ‖coreToL2 (f n).val‖ ≤ B)
    (henergy : ∀ n, M.deformedCoreEnergy (h n) 1 (f n).val ≤ E)
    (u : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)))
    (hu : Tendsto (fun n => P.profile (h n) (f n)) atTop (𝓝 u)) :
    ∃ hmem : MemLp (fun x : M.NormalCoordinates q => ‖x‖ • u x) 2 volume,
      P.c/2*‖hmem.toLp (fun x => ‖x‖ • u x)‖^2 ≤ E+P.K*B^2 := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hnorm 0)
  have hm (n : ℕ) := P.moment_bound (h n) (hh n).1 (hh n).2 (f n)
  have he (n : ℕ) : P.c/2*
      ‖(P.profile_moment_mem (h n) (f n)).toLp
        (fun x => ‖x‖ • P.profile (h n) (f n) x)‖^2 ≤ E+P.K*B^2 := by
    rw [P.profile_moment_norm_sq]
    exact (hm n).trans (add_le_add (henergy n)
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hnorm n) 2) P.K_nonneg))
  have hc : 0 < P.c/2 := half_pos P.c_pos
  have hE : 0 ≤ E+P.K*B^2 :=
    (mul_nonneg hc.le (sq_nonneg _)).trans (he 0)
  let C : ℝ := Real.sqrt ((E+P.K*B^2)/(P.c/2))
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hC2 : C^2 = (E+P.K*B^2)/(P.c/2) :=
    Real.sq_sqrt (div_nonneg hE hc.le)
  have hb (n : ℕ) : ‖(P.profile_moment_mem (h n) (f n)).toLp
      (fun x => ‖x‖ • P.profile (h n) (f n) x)‖ ≤ C := by
    apply (sq_le_sq₀ (norm_nonneg _) hC).mp
    rw [hC2]
    exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using he n)
  obtain ⟨hmem,hbound⟩ := BFSSNormalAnalysis.weighted_moment_closed
    (fun n => P.profile (h n) (f n)) u (fun x => ‖x‖)
    continuous_norm.aestronglyMeasurable C hC hu
    (fun n => P.profile_moment_mem (h n) (f n)) hb
  refine ⟨hmem,?_⟩
  have ht := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hbound 2) hc.le
  rw [hC2,mul_div_cancel₀ _ hc.ne'] at ht
  exact ht
end
end BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch
namespace BFSSSliceAnalytic
noncomputable section
open Finset
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma orthonormal_kinetic_le (e : OrthonormalBasis ι ℝ E) (v : κ → E)
    (hv : Orthonormal ℝ v) (L : E →L[ℝ] F) :
    (∑ j, ‖L (v j)‖^2) ≤ ∑ i, ‖L (e i)‖^2 := by
  let b := stdOrthonormalBasis ℝ F
  have h (j : κ) : ‖L (v j)‖^2 = ∑ k, ‖inner ℝ (v j) (L.adjoint (b k))‖^2 := by
    simp_rw [L.adjoint_inner_right]
    exact (b.sum_sq_norm_inner_left _).symm
  have h' (i : ι) : ‖L (e i)‖^2 = ∑ k, ‖inner ℝ (e i) (L.adjoint (b k))‖^2 := by
    simp_rw [L.adjoint_inner_right]
    exact (b.sum_sq_norm_inner_left _).symm
  simp_rw [h,h']
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro k _
  rw [e.sum_sq_norm_inner_right]
  exact hv.sum_inner_products_le _

lemma kinetic_basis_independent (e : OrthonormalBasis ι ℝ E)
    (v : OrthonormalBasis κ ℝ E) (L : E →L[ℝ] F) :
    (∑ j, ‖L (v j)‖^2) = ∑ i, ‖L (e i)‖^2 :=
  le_antisymm (orthonormal_kinetic_le e v v.orthonormal L)
    (orthonormal_kinetic_le v e e.orthonormal L)

lemma slice_kinetic_le (S : Submodule ℝ E) (e : OrthonormalBasis ι ℝ E)
    (b : OrthonormalBasis κ ℝ S) (L : E →L[ℝ] F) :
    (∑ j, ‖L (b j : E)‖^2) ≤ ∑ i, ‖L (e i)‖^2 := by
  exact orthonormal_kinetic_le e _ (S.subtypeₗᵢ.orthonormal_comp_iff.mpr b.orthonormal) L

lemma affine_kinetic_le (S : Submodule ℝ E) (e : OrthonormalBasis ι ℝ E)
    (b : OrthonormalBasis κ ℝ S) (a : E) (c : ℝ) (f : E → F)
    (hf : Differentiable ℝ f) (z : S) :
    (∑ j, ‖fderiv ℝ (fun z : S => c • f (a+(z : E))) z (b j)‖^2) ≤
      c^2 * ∑ i, ‖fderiv ℝ f (a+(z : E)) (e i)‖^2 := by
  rw [affine_fderiv S a c f hf]
  simp only [IsSMulApply.smul_apply,ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (slice_kinetic_le S e b _) (sq_nonneg c)
end
end BFSSSliceAnalytic

end OAI
