import Mathlib
import OAI.Analysis.HardSphere.Geometry.PositiveTimeSeqTendsto
import OAI.Analysis.HardSphere.Operators.SemigroupLaplaceDerivWithin

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology

lemma IsGroundVector.killed_eigenvector {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) {t : ℝ} (ht : 0 ≤ t) :
    killedTransition N L a t u.1=(Real.exp (-t*energy u):ℂ) • u.1 := by
  have hE : 0 ≤ energy u := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have he : semigroupLaplace (killedTransition N L a) u.1=((1+energy u)⁻¹:ℝ) • u.1 := by
    change killedLaplace N L a u.1=_
    rw [killedLaplace_eq_formResolvent]
    rw [← IsScalarTower.algebraMap_smul ℂ ((1+energy u)⁻¹:ℝ) u.1]
    change formResolvent N L a u.1=(((1+energy u)⁻¹:ℝ):ℂ) • u.1
    simpa only [Complex.ofReal_inv,Complex.ofReal_add,Complex.ofReal_one] using hu.resolvent_eigenvector
  have hh := semigroupLaplace_eigenvector (killedTransition N L a)
    (killedTransition_add_nonneg N L a) (killedTransition_clamped_continuous N L a)
    (fun t _ ↦ killedTransition_apply_contraction N L a t) u.1 (by positivity) he ht
  simp only [inv_inv] at hh
  rw [show (1-(1+energy u))*t= -t*energy u by ring] at hh
  exact hh.trans (IsScalarTower.algebraMap_smul ℂ _ _).symm

end HardSphere

namespace HardSphere
open Filter Set ContinuousLinearMap
open scoped Topology
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Nontrivial F]
local instance : Algebra ℝ (F →L[ℂ] F) := Algebra.restrictScalars ℝ ℂ _

def regularHeat (R : F →L[ℂ] F) (t : ℝ) : F →L[ℂ] F :=
  if 0<t then cfc (p := IsSelfAdjoint) (heatScalar t) R else 1

omit [Nontrivial F] in
lemma regularHeat_zero (R : F →L[ℂ] F) : regularHeat R 0=1 := by simp [regularHeat]

omit [Nontrivial F] in
lemma regularHeat_pos (R : F →L[ℂ] F) {t : ℝ} (ht : 0<t) :
    regularHeat R t=cfc (p := IsSelfAdjoint) (heatScalar t) R := ite_eq_left ht

omit [Nontrivial F] in
lemma regularHeat_add (R : F →L[ℂ] F) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    regularHeat R (s+t)=regularHeat R s*regularHeat R t := by
  rcases eq_or_lt_of_le hs with rfl | hs'
  · simp [regularHeat_zero]
  rcases eq_or_lt_of_le ht with rfl | ht'
  · simp [regularHeat_zero]
  rw [regularHeat_pos R hs',regularHeat_pos R ht',regularHeat_pos R (add_pos hs' ht'),
    show heatScalar (s+t)=(fun x ↦ heatScalar s x*heatScalar t x) from funext (heatScalar_add hs' ht')]
  exact cfc_mul _ _ _ (heatScalar_smooth s).continuous.continuousOn (heatScalar_smooth t).continuous.continuousOn

omit [Nontrivial F] in
lemma regularHeat_commute (R : F →L[ℂ] F) (t : ℝ) : Commute (regularHeat R t) R := by
  by_cases ht : 0<t
  · rw [regularHeat_pos R ht]
    exact (Commute.refl R).cfc_real _
  · simp only [regularHeat,ite_eq_right ht]
    exact Commute.one_left _

lemma regularHeat_contract {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1) (t : ℝ) :
    ‖regularHeat R t‖≤1 := by
  by_cases ht : 0<t
  · rw [regularHeat_pos R ht]
    apply norm_cfc_le zero_le_one
    intro x hx
    have hs := positive_contraction_spectrum hRp hRn hx
    rw [Real.norm_eq_abs,abs_of_nonneg (heatScalar_nonneg t x)]
    rcases eq_or_lt_of_le hs.1 with rfl | hx0
    · simp only [heatScalar_zero,zero_le_one]
    · rw [heatScalar_eq_exp ht hx0]
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le) (sub_nonneg.mpr ((one_le_inv₀ hx0).mpr hs.2))
  · simp only [regularHeat,ite_eq_right ht,norm_one,le_refl]

lemma regularHeat_apply_contract {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1)
    (t : ℝ) (f : F) : ‖regularHeat R t f‖≤‖f‖ :=
  (le_opNorm _ _).trans (by simpa using mul_le_mul_of_nonneg_right (regularHeat_contract hRp hRn t) (norm_nonneg f))

omit [Nontrivial F] in
lemma regularHeat_generator {R : F →L[ℂ] F} (hRp : R.IsPositive) {t : ℝ} (ht : 0<t) (f : F) :
    R f-regularHeat R t (R f)=t • generatorOperator R t f := by
  rw [generatorOperator_eq hRp,regularHeat_pos R ht]
  simp only [smul_apply,mul_apply_eq_comp,sub_apply,one_apply_eq_self,smul_smul,
    mul_inv_cancel₀ ht.ne',one_smul]

lemma regularHeat_range_bound {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1)
    {t : ℝ} (ht : 0 ≤ t) (f : F) : ‖R f-regularHeat R t (R f)‖≤t*‖f‖ := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · simp [regularHeat_zero]
  rw [regularHeat_generator hRp ht',norm_smul,Real.norm_eq_abs,abs_of_pos ht']
  apply mul_le_mul_of_nonneg_left _ ht'.le
  exact (le_opNorm _ _).trans (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
      (generatorOperator_norm_le hRp hRn ht') (norm_nonneg f)))

lemma regularHeat_range_lipschitz {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1)
    (f : F) : LipschitzOnWith ‖f‖₊ (fun t : ℝ ↦ regularHeat R t (R f)) (Ici 0) := by
  apply LipschitzOnWith.of_dist_le_mul
  have step : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t →
      ‖regularHeat R t (R f)-regularHeat R s (R f)‖≤(t-s)*‖f‖ := by
    intro s t hs hst
    have he : regularHeat R t (R f)-regularHeat R s (R f)=
        regularHeat R s (regularHeat R (t-s) (R f)-R f) := by
      rw [map_sub,← mul_apply_eq_comp (regularHeat R s) (regularHeat R (t-s)),
        ← regularHeat_add R hs (sub_nonneg.mpr hst),add_sub_cancel]
    rw [he]
    exact (regularHeat_apply_contract hRp hRn _ _).trans (by
      rw [norm_sub_rev]; exact regularHeat_range_bound hRp hRn (sub_nonneg.mpr hst) f)
  intro s hs t ht
  simp only [dist_eq_norm,Real.norm_eq_abs,coe_nnnorm]
  rcases le_total s t with hst | hts
  · rw [norm_sub_rev,abs_of_nonpos (sub_nonpos.mpr hst)]
    convert step hs hst using 1
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr hts)]
    convert step ht hts using 1
    ring

lemma regularHeat_range_continuousOn {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1)
    (f : F) : ContinuousOn (fun t : ℝ ↦ regularHeat R t (R f)) (Ici 0) :=
  (regularHeat_range_lipschitz hRp hRn f).continuousOn

lemma hasDerivWithinAt_Ici_of_slope_right {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : ℝ → G} {a : ℝ} {v : G}
    (h : Tendsto (fun h : ℝ ↦ h⁻¹ • (f (a+h)-f a)) (𝓝[>] 0) (𝓝 v)) :
    HasDerivWithinAt f v (Ici a) a := by
  rw [hasDerivWithinAt_iff_tendsto_slope,Ici_sdiff_left]
  have hs : Tendsto (fun s : ℝ ↦ s-a) (𝓝[>] a) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun s : ℝ ↦ s-a) a := by fun_prop
      have hh : Tendsto (fun s : ℝ ↦ s-a) (𝓝 a) (𝓝 (a-a)) := hc.tendsto
      rw [sub_self] at hh
      exact hh.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_pos.mpr (show a<s from hs)
  change Tendsto (fun s : ℝ ↦ (s-a)⁻¹ • (f s-f a)) (𝓝[>] a) (𝓝 v)
  simpa only [Function.comp_def,add_sub_cancel] using h.comp hs

lemma regularHeat_range_generator_tendsto {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1)
    (f : F) : Tendsto (fun h : ℝ ↦ generatorOperator R h (R f)) (𝓝[>] 0) (𝓝 ((1-R) (R f))) := by
  rw [← tendsto_sub_nhds_zero_iff,tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (g := fun h : ℝ ↦ h*‖f‖) (Eventually.of_forall (fun _ ↦ norm_nonneg _)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    change ‖((generatorOperator R h-(1-R))*R) f‖≤_
    exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (generatorOperator_range_error hRp hRn hh) (norm_nonneg f))
  · simpa only [id_eq,zero_mul] using ((tendsto_id : Tendsto (fun h : ℝ ↦ h) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds).mul_const ‖f‖

lemma regularHeat_range_hasDerivWithinAt {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1)
    (f : F) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ ↦ regularHeat R s (R (R f)))
      (regularHeat R t (R (R f)-R f)) (Ici t) t := by
  have hg := ((regularHeat_range_generator_tendsto hRp hRn f).neg)
  simp only [sub_apply,one_apply_eq_self,neg_sub] at hg
  have hh := (regularHeat R t).continuous.tendsto (R (R f)-R f) |>.comp hg
  apply hasDerivWithinAt_Ici_of_slope_right
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh0
  change 0<h at hh0
  dsimp only [Function.comp_def]
  rw [regularHeat_add R ht hh0.le,mul_apply_eq_comp,← map_sub,← map_smul_of_tower]
  rw [← neg_sub (R (R f)),regularHeat_generator hRp hh0 (R f),smul_neg,smul_smul,
    inv_mul_cancel₀ hh0.ne',one_smul]

end HardSphere

end
end
end
end
end
end

end OAI
