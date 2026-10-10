import Mathlib
import OAI.MathematicalPhysics.BFSS.ProfileMoments
import OAI.MathematicalPhysics.BFSS.PotentialLimits

namespace OAI

/-! Moment-controlled quadratic fields and limiting profile energies. -/

namespace BFSSNormalAnalysis
noncomputable section
open MeasureTheory Set Filter Topology
variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [CompleteSpace F]
variable (μ : Measure X)

omit [CompleteSpace F] in
lemma field_memLp_moment (u : Lp F 2 μ) (w : X → ℝ)
    (hm : MemLp (fun x => w x • u x) 2 μ)
    (A : X → F →L[ℝ] F) (hA : AEStronglyMeasurable A μ)
    (C : ℝ) (hC : 0 ≤ C) (hw : ∀ x, 0 ≤ w x)
    (hbound : ∀ x, ‖A x‖ ≤ C*w x) :
    MemLp (fun x => A x (u x)) 2 μ := by
  apply (hm.const_smul C).of_le ((ContinuousLinearMap.apply ℝ F).aestronglyMeasurable_comp₂
    (Lp.memLp u).aestronglyMeasurable hA)
  filter_upwards [] with x
  change ‖A x (u x)‖ ≤ ‖C • (w x • u x)‖
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC,norm_smul,Real.norm_eq_abs,abs_of_nonneg (hw x)]
  exact ((A x).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)).trans_eq (mul_assoc _ _ _))

omit [CompleteSpace F] in
lemma field_moment_norm_le (u : Lp F 2 μ) (w : X → ℝ)
    (hm : MemLp (fun x => w x • u x) 2 μ)
    (A : X → F →L[ℝ] F) (hA : AEStronglyMeasurable A μ)
    (C : ℝ) (hC : 0 ≤ C) (hw : ∀ x, 0 ≤ w x)
    (hbound : ∀ x, ‖A x‖ ≤ C*w x) :
    ‖(field_memLp_moment μ u w hm A hA C hC hw hbound).toLp (fun x => A x (u x))‖ ≤
      C*‖hm.toLp (fun x => w x • u x)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(field_memLp_moment μ u w hm A hA C hC hw hbound).coeFn_toLp,hm.coeFn_toLp] with x hx hy
  rw [hx,hy,norm_smul,Real.norm_eq_abs,abs_of_nonneg (hw x)]
  exact ((A x).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)).trans_eq (mul_assoc _ _ _))

omit [CompleteSpace F] in
lemma field_quadratic_integrable (u : Lp F 2 μ) (A : X → F →L[ℝ] F)
    (ha : MemLp (fun x => A x (u x)) 2 μ) :
    Integrable (fun x => inner ℝ (u x) (A x (u x))) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) u (ha.toLp _)).congr
  filter_upwards [ha.coeFn_toLp] with x hx
  rw [hx]

omit [CompleteSpace F] in
lemma field_quadratic_abs_le (u : Lp F 2 μ) (w : X → ℝ)
    (hm : MemLp (fun x => w x • u x) 2 μ)
    (A : X → F →L[ℝ] F) (hA : AEStronglyMeasurable A μ)
    (C : ℝ) (hC : 0 ≤ C) (hw : ∀ x, 0 ≤ w x)
    (hbound : ∀ x, ‖A x‖ ≤ C*w x) :
    |∫ x, inner ℝ (u x) (A x (u x)) ∂μ| ≤
      ‖u‖*(C*‖hm.toLp (fun x => w x • u x)‖) := by
  let ha := field_memLp_moment μ u w hm A hA C hC hw hbound
  have he : (∫ x, inner ℝ (u x) (A x (u x)) ∂μ) = inner ℝ u (ha.toLp _) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp] with x hx
    rw [hx]
  rw [he]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
    (field_moment_norm_le μ u w hm A hA C hC hw hbound) (norm_nonneg _))

omit [CompleteSpace F] in
lemma constant_quadratic_eq (A : F →L[ℝ] F) (u : Lp F 2 μ) :
    (∫ x, inner ℝ (u x) (A (u x)) ∂μ) = inner ℝ u (A.compLp u) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [A.coeFn_compLp u] with x hx
  rw [hx]

omit [CompleteSpace F] in
lemma constant_quadratic_tendsto (A : F →L[ℝ] F) (f : ℕ → Lp F 2 μ)
    (u : Lp F 2 μ) (hf : Tendsto f atTop (𝓝 u)) :
    Tendsto (fun n => ∫ x, inner ℝ (f n x) (A (f n x)) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (u x) (A (u x)) ∂μ)) := by
  simp_rw [constant_quadratic_eq]
  exact hf.inner ((A.compLpL 2 μ).continuous.tendsto u |>.comp hf)

omit [CompleteSpace F] in
theorem affine_quadratic_tendsto (A₀ : F →L[ℝ] F) (A₁ : X → F →L[ℝ] F)
    (hA₁ : AEStronglyMeasurable A₁ μ) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (C B D : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) (_hD : 0 ≤ D)
    (hA : ∀ x, ‖A₁ x‖ ≤ C*w x) (h : ℕ → ℝ) (hzero : Tendsto h atTop (𝓝 0))
    (f : ℕ → Lp F 2 μ) (u : Lp F 2 μ) (hf : Tendsto f atTop (𝓝 u))
    (hnorm : ∀ n, ‖f n‖ ≤ B)
    (hm : ∀ n, MemLp (fun x => w x • f n x) 2 μ)
    (hmoment : ∀ n, ‖(hm n).toLp (fun x => w x • f n x)‖ ≤ D) :
    Tendsto (fun n => ∫ x, inner ℝ (f n x) ((A₀+h n • A₁ x) (f n x)) ∂μ)
      atTop (𝓝 (∫ x, inner ℝ (u x) (A₀ (u x)) ∂μ)) := by
  let I := fun n => ∫ x, inner ℝ (f n x) (A₁ x (f n x)) ∂μ
  have hI (n : ℕ) : |I n| ≤ B*(C*D) := by
    exact (field_quadratic_abs_le μ (f n) w (hm n) A₁ hA₁ C hC hw hA).trans
      (mul_le_mul (hnorm n) (mul_le_mul_of_nonneg_left (hmoment n) hC)
        (mul_nonneg hC (norm_nonneg _)) hB)
  have herr : Tendsto (fun n => h n*I n) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n => |h n| *(B*(C*D)))
    · intro n
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left (hI n) (abs_nonneg _)
    · simpa only [abs_zero,zero_mul] using hzero.abs.mul_const (B*(C*D))
  have he (n : ℕ) :
      (∫ x, inner ℝ (f n x) ((A₀+h n • A₁ x) (f n x)) ∂μ) =
      (∫ x, inner ℝ (f n x) (A₀ (f n x)) ∂μ)+h n*I n := by
    have hi := field_quadratic_integrable μ (f n) A₁
      (field_memLp_moment μ (f n) w (hm n) A₁ hA₁ C hC hw hA)
    have hc := field_quadratic_integrable μ (f n) (fun _ => A₀) (A₀.comp_memLp (f n))
    simp only [_root_.add_apply,_root_.smul_apply,inner_add_right,
      inner_smul_right]
    rw [integral_add hc (hi.const_mul _),integral_const_mul]
  simp_rw [he]
  simpa only [add_zero] using (constant_quadratic_tendsto μ A₀ f u hf).add herr
end
end BFSSNormalAnalysis
namespace BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal
variable {N : ℕ} {M : AlgebraData N} {G : M.GaugeData} {q : Boson N}
variable (P : G.MeasuredNormalPatch q)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2
local instance energyLimitsFermionInnerProductSpace : InnerProductSpace ℝ (Fermion N) := inferInstance
local instance energyLimitsFermionCompleteSpace : CompleteSpace (Fermion N) := inferInstance

lemma profile_moment_norm_le {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) (f : G.invariantCore)
    (E : ℝ≥0) (hnorm : ‖coreToL2 f.val‖^2 ≤ E)
    (henergy : M.deformedCoreEnergy h 1 f.val ≤ E) :
    ‖(P.profile_moment_mem h f).toLp (fun x => ‖x‖ • P.profile h f x)‖ ≤
      Real.sqrt (2*((E : ℝ)+P.K*E)/P.c) := by
  have hb := P.moment_bound h hh h1 f
  rw [←P.profile_moment_norm_sq] at hb
  have he : P.c/2 * ‖(P.profile_moment_mem h f).toLp (fun x => ‖x‖ • P.profile h f x)‖^2 ≤
      (E : ℝ)+P.K*E := hb.trans (add_le_add henergy (mul_le_mul_of_nonneg_left hnorm P.K_nonneg))
  have hK := P.K_nonneg
  have hc := P.c_pos
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
  apply (le_div_iff₀ P.c_pos).mpr
  nlinarith only [he]

theorem profile_fermion_energy_tendsto (h : ℕ → ℝ)
    (hh : ∀ n, 0 < h n ∧ h n ≤ 1) (hzero : Tendsto h atTop (𝓝 0))
    (f : ℕ → G.invariantCore) (E : ℝ≥0)
    (hnorm : ∀ n, ‖coreToL2 (f n).val‖^2 ≤ E)
    (henergy : ∀ n, M.deformedCoreEnergy (h n) 1 (f n).val ≤ E)
    (u : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)))
    (hu : Tendsto (fun n => P.profile (h n) (f n)) atTop (𝓝 u)) :
    Tendsto (fun n => ∫ x : M.NormalCoordinates q,
      inner ℝ (P.profile (h n) (f n) x)
        (M.deformedFermionField (h n) 1 ((h n)⁻¹ • q+(M.normalCoordinateIsometry q x : Boson N))
          (P.profile (h n) (f n) x))) atTop
      (𝓝 (∫ x : M.NormalCoordinates q,
        inner ℝ (u x) (M.deformedFermionField 1 1 q (u x)))) := by
  have hA : Continuous (fun x : M.NormalCoordinates q =>
      M.deformedFermionField 1 0 (M.normalCoordinateIsometry q x : Boson N)) :=
    (M.deformedFermionField_continuous 1 0).comp
      (continuous_subtype_val.comp (M.normalCoordinateIsometry q).continuous)
  have hAb (x : M.NormalCoordinates q) :
      ‖M.deformedFermionField 1 0 (M.normalCoordinateIsometry q x : Boson N)‖ ≤
        M.fermionGrowthConstant*‖x‖ := by
    simpa only [abs_one,one_mul,abs_zero,add_zero,Submodule.norm_coe,LinearIsometryEquiv.norm_map] using
      M.deformedFermionField_growth 1 0 (M.normalCoordinateIsometry q x : Boson N)
  have hn (n : ℕ) : ‖P.profile (h n) (f n)‖ ≤ Real.sqrt E := by
    apply (P.profile_norm_le (hh n).1 (hh n).2 (f n)).trans
    exact (Real.le_sqrt (norm_nonneg _) E.property).mpr (hnorm n)
  have ht := BFSSNormalAnalysis.affine_quadratic_tendsto volume
    (M.deformedFermionField 1 1 q)
    (fun x : M.NormalCoordinates q => M.deformedFermionField 1 0 (M.normalCoordinateIsometry q x : Boson N))
    hA.aestronglyMeasurable (fun x : M.NormalCoordinates q => ‖x‖) (fun x => norm_nonneg x)
    M.fermionGrowthConstant (Real.sqrt E) (Real.sqrt (2*((E : ℝ)+P.K*E)/P.c))
    M.fermionGrowthConstant_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hAb h hzero
    (fun n => P.profile (h n) (f n)) u hu hn
    (fun n => P.profile_moment_mem (h n) (f n))
    (fun n => P.profile_moment_norm_le (hh n).1 (hh n).2 (f n) E (hnorm n) (henergy n))
  have he (n : ℕ) (x : M.NormalCoordinates q) :=
    M.deformedFermionField_normal_affine q (M.normalCoordinateIsometry q x : Boson N) (hh n).1.ne'
  simpa only [he] using ht
end
end BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch
namespace BFSSNormalAnalysis
noncomputable section
open MeasureTheory Filter Topology
variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [CompleteSpace F]
variable (μ : Measure X)

omit [CompleteSpace F] in
theorem varying_weight_norm_sq_le_limit (f : ℕ → Lp F 2 μ) (u : Lp F 2 μ)
    (hf : Tendsto f atTop (𝓝 u)) (w : ℕ → X → ℝ) (w₀ : X → ℝ)
    (hw₀ : AEStronglyMeasurable w₀ μ) (hwlim : ∀ x, Tendsto (fun n => w n x) atTop (𝓝 (w₀ x)))
    (hm : ∀ n, MemLp (fun x => w n x • f n x) 2 μ)
    (b : ℕ → ℝ) (b₀ : ℝ) (hb : Tendsto b atTop (𝓝 b₀))
    (hbound : ∀ n, ‖(hm n).toLp (fun x => w n x • f n x)‖^2 ≤ b n) :
    ∃ hu : MemLp (fun x => w₀ x • u x) 2 μ,
      ‖hu.toLp (fun x => w₀ x • u x)‖^2 ≤ b₀ := by
  obtain ⟨σ,hσ,ha⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  have hbN (n : ℕ) : 0 ≤ b n := (sq_nonneg _).trans (hbound n)
  have hb₀ : 0 ≤ b₀ := ge_of_tendsto hb (Eventually.of_forall hbN)
  have hpt : ∀ᵐ x ∂μ, Tendsto (fun n => w (σ n) x • f (σ n) x) atTop (𝓝 (w₀ x • u x)) := by
    filter_upwards [ha] with x hx
    exact ((hwlim x).comp hσ.tendsto_atTop).smul hx
  have hle : eLpNorm (fun x => w₀ x • u x) 2 μ ≤ ENNReal.ofReal (Real.sqrt b₀) := by
    have hfat := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2) (fun n => (hm (σ n)).aestronglyMeasurable)
      (fun x => w₀ x • u x) (hw₀.smul (Lp.memLp u).aestronglyMeasurable) hpt
    apply hfat.trans
    have hupper (n : ℕ) : eLpNorm (fun x => w (σ n) x • f (σ n) x) 2 μ ≤
        ENNReal.ofReal (Real.sqrt (b (σ n))) := by
      rw [←ENNReal.toReal_le_toReal (hm (σ n)).eLpNorm_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (Real.sqrt_nonneg _),←Lp.norm_toLp _ (hm (σ n))]
      exact (Real.le_sqrt (norm_nonneg _) (hbN (σ n))).mpr (hbound (σ n))
    have hlim := (ENNReal.continuous_ofReal.tendsto (Real.sqrt b₀)).comp
      (((hb.comp hσ.tendsto_atTop).sqrt))
    exact (Filter.liminf_le_liminf (Eventually.of_forall hupper)).trans_eq hlim.liminf_eq
  have hmem : MemLp (fun x => w₀ x • u x) 2 μ :=
    hle.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hmem,?_⟩
  have hn : ‖hmem.toLp (fun x => w₀ x • u x)‖ ≤ Real.sqrt b₀ := by
    rw [Lp.norm_toLp]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans_eq
      (ENNReal.toReal_ofReal (Real.sqrt_nonneg _))
  exact (Real.le_sqrt (norm_nonneg _) hb₀).mp hn
end
end BFSSNormalAnalysis
namespace BFSSQuantum.AlgebraData
noncomputable section
open Finset
variable {N : ℕ} (M : AlgebraData N)
lemma normalEffectivePotential_nonneg (q : Boson N) (h : ℝ) (z : Boson N) :
    0 ≤ M.normalEffectivePotential q h z := by
  unfold normalEffectivePotential
  positivity
end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch
noncomputable section
open MeasureTheory Set Filter Topology
variable {N : ℕ} {M : AlgebraData N} {G : M.GaugeData} {q : Boson N}
variable (P : G.MeasuredNormalPatch q)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2
local instance energyLimitsPotentialInnerProductSpace : InnerProductSpace ℝ (Fermion N) := inferInstance
local instance energyLimitsPotentialCompleteSpace : CompleteSpace (Fermion N) := inferInstance

lemma profile_potential_mem (h : ℝ) (f : G.invariantCore) :
    MemLp (fun x : M.NormalCoordinates q =>
      Real.sqrt (M.normalEffectivePotential q h (M.normalCoordinateIsometry q x : Boson N)) •
        P.profile h f x) 2 volume := by
  have hw : Continuous (fun x : M.NormalCoordinates q =>
      Real.sqrt (M.normalEffectivePotential q h (M.normalCoordinateIsometry q x : Boson N))) :=
    ((M.normalEffectivePotential_continuous q).comp (continuous_const.prodMk
      (continuous_subtype_val.comp (M.normalCoordinateIsometry q).continuous))).sqrt
  have hc : MemLp (fun x : M.NormalCoordinates q =>
      Real.sqrt (M.normalEffectivePotential q h (M.normalCoordinateIsometry q x : Boson N)) •
        M.normalMeasuredCoordinates q h P.density P.cutoff f.val x) 2 volume :=
    (hw.smul (M.normalMeasuredCoordinates_continuous q h P.density P.cutoff f.val
      P.density_continuous P.cutoff_continuous)).memLp_of_hasCompactSupport
        (M.normalMeasuredCoordinates_compactSupport q h P.density P.cutoff f.val).smul_left
  apply MemLp.ae_eq (hf_Lp := hc)
  filter_upwards [P.profile_ae h f] with x hx
  rw [hx]

lemma profile_potential_norm_sq (h : ℝ) (f : G.invariantCore) :
    ‖(P.profile_potential_mem h f).toLp (fun x =>
      Real.sqrt (M.normalEffectivePotential q h (M.normalCoordinateIsometry q x : Boson N)) •
        P.profile h f x)‖^2 = ∫ x : M.NormalCoordinates q,
      M.normalEffectivePotential q h (M.normalCoordinateIsometry q x : Boson N)*‖P.profile h f x‖^2 := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(P.profile_potential_mem h f).coeFn_toLp] with x hx
  rw [hx,real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    Real.sq_sqrt (M.normalEffectivePotential_nonneg q h _)]

theorem profile_bosonic_energy_le_limit (h : ℕ → ℝ)
    (hzero : Tendsto h atTop (𝓝 0)) (f : ℕ → G.invariantCore)
    (u : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)))
    (hu : Tendsto (fun n => P.profile (h n) (f n)) atTop (𝓝 u))
    (b₀ : ℝ) (hb : Tendsto (fun n => ∫ x : M.NormalCoordinates q,
      M.normalEffectivePotential q (h n) (M.normalCoordinateIsometry q x : Boson N)*
        ‖P.profile (h n) (f n) x‖^2) atTop (𝓝 b₀)) :
    ∃ hm : MemLp (fun x : M.NormalCoordinates q =>
      Real.sqrt (M.normalQuadratic q (M.normalCoordinateIsometry q x : Boson N)) • u x) 2 volume,
      ‖hm.toLp (fun x => Real.sqrt (M.normalQuadratic q (M.normalCoordinateIsometry q x : Boson N)) • u x)‖^2 ≤ b₀ := by
  have hwlim (x : M.NormalCoordinates q) : Tendsto (fun n =>
      Real.sqrt (M.normalEffectivePotential q (h n) (M.normalCoordinateIsometry q x : Boson N)))
      atTop (𝓝 (Real.sqrt (M.normalQuadratic q (M.normalCoordinateIsometry q x : Boson N)))) := by
    have ht := ((M.normalEffectivePotential_continuous q).tendsto
      (0,(M.normalCoordinateIsometry q x : Boson N))).comp (hzero.prodMk_nhds tendsto_const_nhds)
    simpa only [Function.comp_apply,M.normalEffectivePotential_zero] using ht.sqrt
  have hw₀ : Continuous (fun x : M.NormalCoordinates q =>
      Real.sqrt (M.normalQuadratic q (M.normalCoordinateIsometry q x : Boson N))) := by
    simp_rw [←M.normalEffectivePotential_zero]
    exact ((M.normalEffectivePotential_continuous q).comp (continuous_const.prodMk
      (continuous_subtype_val.comp (M.normalCoordinateIsometry q).continuous))).sqrt
  exact BFSSNormalAnalysis.varying_weight_norm_sq_le_limit volume
    (fun n => P.profile (h n) (f n)) u hu
    (fun n x => Real.sqrt (M.normalEffectivePotential q (h n) (M.normalCoordinateIsometry q x : Boson N)))
    (fun x => Real.sqrt (M.normalQuadratic q (M.normalCoordinateIsometry q x : Boson N)))
    hw₀.aestronglyMeasurable hwlim (fun n => P.profile_potential_mem (h n) (f n))
    _ b₀ hb (fun n => (P.profile_potential_norm_sq (h n) (f n)).le)
end
end BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch

namespace BFSSSliceAnalytic
noncomputable section
open Finset
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma contraction_basis_independent (e : OrthonormalBasis ι ℝ E)
    (b : OrthonormalBasis κ ℝ E) (K : E →ₗ[ℝ] (F →L[ℝ] F)) (D : E →ₗ[ℝ] F) :
    (∑ j, K (b j) (D (b j))) = ∑ i, K (e i) (D (e i)) := by
  have hx (j : κ) : K (b j) = ∑ i, (inner ℝ (e i) (b j)) • K (e i) := by
    simpa only [map_sum, map_smul] using congrArg K (e.sum_repr' (b j)).symm
  simp_rw [hx, _root_.sum_apply, _root_.smul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [← map_smul, ← map_sum]
  congr 2
  simpa only [real_inner_comm] using b.sum_repr' (e i)
end
end BFSSSliceAnalytic

end OAI
