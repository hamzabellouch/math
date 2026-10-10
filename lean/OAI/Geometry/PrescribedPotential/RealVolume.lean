import Mathlib
import OAI.Geometry.PrescribedPotential.RealSmoothOperator
import OAI.Geometry.PrescribedPotential.CompletedVolume
import OAI.Geometry.PrescribedPotential.RealPoisson

namespace OAI

/-! Real Volume. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical BoundedContinuousFunction ComplexOrder
namespace RealClosedDerivative
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma subtype_iff (S : Submodule ℝ F) (f : E → S) (L : E →L[ℝ] S) (x : E) :
    HasStrictFDerivAt f L x ↔
      HasStrictFDerivAt (fun y => (f y).val) (S.subtypeL ∘L L) x := by
  simp only [hasStrictFDerivAt_iff_isLittleO]
  conv_lhs => rw [← Asymptotics.isLittleO_norm_left]
  conv_rhs => rw [← Asymptotics.isLittleO_norm_left]
  rfl
end RealClosedDerivative

namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

local instance (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

def realVolume (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (u : D.localizers.RealSobolev ((k : ℝ)+2)) : D.localizers.RealSobolev (k : ℝ) :=
  ⟨D.completedVolume k hk u.val, D.completedVolume_real k hk u.val u.property⟩

lemma realVolume_continuous (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) :
    Continuous (D.realVolume k hk) :=
  ((D.completedVolume_contDiff k hk).continuous.comp continuous_subtype_val).subtype_mk _

lemma realVolume_ambient_contDiff (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) :
    ContDiff ℝ ∞ (fun u : D.localizers.RealSobolev ((k : ℝ)+2) => (D.realVolume k hk u).val) :=
  (D.completedVolume_contDiff k hk).comp (D.localizers.realCompletion ((k : ℝ)+2)).subtypeL.contDiff

lemma completedVolume_real_directional (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (f : RealSmooth A) (x : X) :
    HasDerivAt (fun t : ℝ => D.localizers.strong (k : ℝ)
      (D.completedVolume k hk (t • D.localizers.embed ((k : ℝ)+2) f.val)) x)
      (complexL g f.val x) 0 := by
  have hs : (Module.finrank ℝ (EC d) : ℝ) < 2*(k : ℝ) := by
    have hh : (Module.finrank ℝ (EC d) : ℝ) < (k : ℝ) := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have he (t : ℝ) : t • D.localizers.embed ((k : ℝ)+2) f.val =
      D.localizers.embed ((k : ℝ)+2) (Smooth.ofReal (f.source.realSMul t)) := by
    rw [← map_smul, ← f.ofReal_source]
    congr 1
    ext y
    simp [SmoothRealFunction.realSMul, Complex.real_smul]
  have hd := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0
    (g.potentialDensity_directional f.source x)
  have hl : complexL g f.val x = ((g.laplacian f.source).value x : ℂ) := by
    rw [← f.ofReal_source, complexL_ofReal]
    rfl
  rw [hl]
  apply hd.congr_of_eventuallyEq
  filter_upwards [] with t
  rw [he, D.completedVolume_embed, D.localizers.strong_embed _ hs]
  rfl

lemma realVolume_hasStrictFDerivAt_zero (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) :
    HasStrictFDerivAt (D.realVolume k hk) (D.realLOrder k) 0 := by
  let F := fun u : D.localizers.RealSobolev ((k : ℝ)+2) => (D.realVolume k hk u).val
  let J := fderiv ℝ F 0
  have hJ : HasStrictFDerivAt F J 0 := (D.realVolume_ambient_contDiff k hk).hasStrictFDerivAt (by simp)
  have hs : (Module.finrank ℝ (EC d) : ℝ) < 2*(k : ℝ) := by
    have hh : (Module.finrank ℝ (EC d) : ℝ) < (k : ℝ) := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hj : J = (D.localizers.realCompletion (k : ℝ)).subtypeL ∘L D.realLOrder k := by
    apply DFunLike.coe_injective
    apply (D.localizers.realEmbed_dense ((k : ℝ)+2)).equalizer J.continuous (by fun_prop)
    funext f
    apply D.localizers.strong_injective (k : ℝ) hs
    ext x
    let v := D.localizers.realEmbed ((k : ℝ)+2) f
    have hc : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    have hF : HasFDerivAt F J ((0 : ℝ) • v) := by simpa using hJ.hasFDerivAt
    have hv := hF.comp_hasDerivAt 0 hc
    have he := (D.pointEvaluation (k : ℝ) x).hasFDerivAt.comp_hasDerivAt 0 hv
    have hdr := D.completedVolume_real_directional k hk f x
    have heq := he.unique hdr
    change D.localizers.strong (k : ℝ) (J v) x = complexL g f.val x at heq
    change D.localizers.strong (k : ℝ) (J v) x = _
    rw [heq]
    change complexL g f.val x = D.localizers.strong (k : ℝ)
      (D.completedLOrder k (D.localizers.embed ((k : ℝ)+2) f.val)) x
    rw [D.completedLOrder_embed, D.localizers.strong_embed _ hs]
    rfl
  apply (RealClosedDerivative.subtype_iff (D.localizers.realCompletion (k : ℝ)) _ _ _).mpr
  rw [← hj]
  exact hJ

lemma realVolume_zero (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) :
    D.realVolume k hk 0 = D.realConstants (k : ℝ) 1 := by
  have h₀ : Smooth.ofReal (SmoothRealFunction.constant (A := A) 0) = 0 := by
    ext x
    change (↑(0 : ℝ) : ℂ) = 0
    exact Complex.ofReal_zero
  have hv := D.completedVolume_embed k hk (SmoothRealFunction.constant (A := A) 0)
  rw [h₀, map_zero] at hv
  apply Subtype.ext
  change D.completedVolume k hk 0 = D.localizers.embed (k : ℝ) (Smooth.const (↑(1 : ℝ)))
  rw [hv]
  congr 1
  ext x
  obtain ⟨i, hi⟩ := A.covers x
  change ((g.potentialDensity (SmoothRealFunction.constant 0)).value x : ℂ) = 1
  rw [g.potentialDensity_complex _ i hi]
  simp only [KaehlerMetric.volumePolynomial, SmoothRealFunction.hessian_constant, add_zero]
  exact div_self (ne_of_gt (g.positive i _ ((A.chart i).mapsTo hi)).det_pos)

end GluingData
end GlobalElliptic

end
end

end OAI
