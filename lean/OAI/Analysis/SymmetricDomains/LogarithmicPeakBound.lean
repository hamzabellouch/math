import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Module

def conormalRestriction {E : Type*} [AddCommGroup E] [Module ℝ E]
    (V : Submodule ℝ E) (T : Submodule ℝ V) :
    (T.map V.subtype).dualAnnihilator →ₗ[ℝ] T.dualAnnihilator where
  toFun f := ⟨f.val.comp V.subtype,by
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro x hx
    exact (Submodule.mem_dualAnnihilator _).mp f.property x.val ⟨x,hx,rfl⟩⟩
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' c f := by apply Subtype.ext; rfl

theorem conormalRestriction_surjective {E : Type*} [AddCommGroup E] [Module ℝ E]
    (V : Submodule ℝ E) (T : Submodule ℝ V) :
    Function.Surjective (conormalRestriction V T) := by
  intro f
  obtain ⟨g,hg⟩ := f.val.exists_extend
  have hgT : g ∈ (T.map V.subtype).dualAnnihilator := by
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hx
    change (g.comp V.subtype) y = 0
    rw [hg]
    exact (Submodule.mem_dualAnnihilator _).mp f.property y hy
  refine ⟨⟨g,hgT⟩,?_⟩
  apply Subtype.ext
  exact hg

theorem critical_parameter_affine_fiber {E : Type*} [AddCommGroup E] [Module ℝ E]
    (T : Submodule ℝ E) (ell : Module.Dual ℝ E) (a : Module.Dual ℝ E) :
    (∀ x ∈ T, ell x + a x = 0) ↔ ∃ b : T.dualAnnihilator, a = b.val-ell := by
  constructor
  · intro h
    refine ⟨⟨ell+a,?_⟩,?_⟩
    · exact (Submodule.mem_dualAnnihilator _).mpr h
    · simp
  · rintro ⟨b,rfl⟩ x hx
    have h := (Submodule.mem_dualAnnihilator _).mp b.property x hx
    simpa using h

end

open Set Complex

theorem normalized_log_peak_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {p : E} {L : E →L[ℂ] ℂ}
    (hf : HasFDerivAt f L p) (hfp : f p = 1) (a : E →L[ℂ] ℂ) :
    HasFDerivAt (fun q => Complex.log (f q * Complex.exp (a (q-p)))) (L+a) p := by
  have ha : HasFDerivAt (fun q => a (q-p)) a p := by
    simpa only [map_sub] using a.hasFDerivAt.sub_const (a p)
  have hae : HasFDerivAt (fun q => Complex.exp (a (q-p))) a p := by
    simpa only [sub_self,map_zero,Complex.exp_zero,one_smul] using ha.cexp
  have hg : HasFDerivAt (fun q => f q*Complex.exp (a (q-p))) (L+a) p := by
    convert hf.mul hae using 1
    first | rfl | simp [hfp, add_comm]
  have hgp : f p*Complex.exp (a (p-p)) = 1 := by simp [hfp]
  simpa only [hgp,inv_one,one_smul] using hg.clog (hgp ▸ Complex.one_mem_slitPlane)

theorem normalized_log_peak_analytic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {p : E} (hf : AnalyticAt ℂ f p) (hfp : f p = 1)
    (a : E →L[ℂ] ℂ) :
    AnalyticAt ℂ (fun q => Complex.log (f q*Complex.exp (a (q-p)))) p ∧
      Complex.log (f p*Complex.exp (a (p-p))) = 0 := by
  have ha : AnalyticAt ℂ (fun q => a (q-p)) p := by
    convert (a.analyticAt p).sub (analyticAt_const (v := a p)) using 1
    ext q
    simp [map_sub]
  have hg : AnalyticAt ℂ (fun q => f q*Complex.exp (a (q-p))) p := by
    convert hf.mul ha.cexp using 1
    rfl
  exact ⟨hg.clog (by simp [hfp]),by simp [hfp]⟩

theorem logarithmic_peak_bound {X : Type*} (h : X → ℂ) (E : X → ℝ)
    {q : X} (hq : h q ≠ 0) (hb : ‖h q‖ ≤ Real.exp (-E q)) :
    (Complex.log (h q)).re ≤ -E q := by
  rw [Complex.log_re]
  apply Real.log_le_iff_le_exp (norm_pos_iff.mpr hq) |>.mpr
  exact hb

end Release061

end

end OAI
