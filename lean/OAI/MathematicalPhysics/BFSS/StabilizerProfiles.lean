import Mathlib
import OAI.MathematicalPhysics.BFSS.ClosedProfiles

namespace OAI

/-! Stabilizer-equivariant normal profile spaces and limits. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Set
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] normalSlice gaugeAction coreToL2 normalCoreField normalMeasuredField

def stabilizerCoordinateIsometry (q : Boson N) (U : M.gaugeStabilizer q) :
    M.NormalCoordinates q ≃ₗᵢ[ℝ] M.NormalCoordinates q :=
  (M.normalCoordinateIsometry q).trans
    ((M.stabilizerNormalIsometry q U).trans (M.normalCoordinateIsometry q).symm)

lemma normalCoordinate_stabilizer (q : Boson N) (U : M.gaugeStabilizer q)
    (x : M.NormalCoordinates q) :
    M.normalCoordinateIsometry q (M.stabilizerCoordinateIsometry q U x) =
      M.stabilizerNormalIsometry q U (M.normalCoordinateIsometry q x) := by
  simp only [stabilizerCoordinateIsometry,LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]

namespace GaugeData
variable {M} (G : M.GaugeData)

def stabilizerOfGauge (q : Boson N) (g : GaugeGroup N) (hg : G.boson g q = q) :
    M.gaugeStabilizer q := ⟨⟨g,g.prop.1⟩,by
      change M.gaugeAction ⟨g,g.prop.1⟩ q = q
      rw [←G.boson_eq_gaugeAction]; exact hg⟩

lemma fermion_real_smul (g : GaugeGroup N) (r : ℝ) (x : Fermion N) :
    G.fermion g (r • x) = r • G.fermion g x :=
  ((G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).map_smul r x

lemma normalCoreField_equivariant (q : Boson N) (h : ℝ) (f : G.invariantCore)
    (g : GaugeGroup N) (hg : G.boson g q = q) (z : M.normalSlice q) :
    M.normalCoreField q h f.val (M.stabilizerNormalIsometry q (G.stabilizerOfGauge q g hg) z) =
      G.fermion g (M.normalCoreField q h f.val z) := by
  have he : ((M.stabilizerNormalIsometry q (G.stabilizerOfGauge q g hg) z) : Boson N) =
      G.boson g (z : Boson N) := (G.boson_eq_gaugeAction g z).symm
  have ha : G.boson g (h⁻¹ • q+(z : Boson N)) = h⁻¹ • q+G.boson g (z : Boson N) := by
    rw [map_add,map_smul,hg]
  unfold AlgebraData.normalCoreField
  rw [he,←ha,G.invariantCore_equivariant,G.fermion_real_smul]

namespace MeasuredNormalPatch
variable {G} {q : Boson N} (P : G.MeasuredNormalPatch q)

lemma normalMeasuredField_equivariant (h : ℝ) (f : G.invariantCore)
    (g : GaugeGroup N) (hg : G.boson g q = q) (z : M.normalSlice q) :
    M.normalMeasuredField q h P.density P.cutoff f.val
      (M.stabilizerNormalIsometry q (G.stabilizerOfGauge q g hg) z) =
      G.fermion g (M.normalMeasuredField q h P.density P.cutoff f.val z) := by
  let U := G.stabilizerOfGauge q g hg
  have hq : M.gaugeAction U q = q := U.prop
  have hc : q+h • ((M.stabilizerNormalIsometry q U z : M.normalSlice q) : Boson N) =
      M.gaugeAction U (q+h • (z : Boson N)) := by
    rw [M.gaugeAction_add,M.gaugeAction_smul,hq]
    rfl
  unfold AlgebraData.normalMeasuredField
  rw [←map_smul, P.density_invariant,hc,P.cutoff_invariant]
  rw [G.normalCoreField_equivariant q h f g hg z,G.fermion_real_smul]

lemma normalMeasuredCoordinates_equivariant (h : ℝ) (f : G.invariantCore)
    (g : GaugeGroup N) (hg : G.boson g q = q) (x : M.NormalCoordinates q) :
    M.normalMeasuredCoordinates q h P.density P.cutoff f.val
      (M.stabilizerCoordinateIsometry q (G.stabilizerOfGauge q g hg) x) =
      G.fermion g (M.normalMeasuredCoordinates q h P.density P.cutoff f.val x) := by
  simp only [M.normalMeasuredCoordinates_eq,M.normalCoordinate_stabilizer]
  exact P.normalMeasuredField_equivariant h f g hg _
end MeasuredNormalPatch
end GaugeData
end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData.GaugeData
noncomputable section
open MeasureTheory Set Filter
variable {N : ℕ} {M : AlgebraData N} (G : M.GaugeData)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2

def normalBosonPullback (q : Boson N) (g : GaugeGroup N) (hg : G.boson g q = q) :
    Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)) →ₗ[ℂ]
      Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)) :=
  Lp.compMeasurePreservingₗ ℂ (M.stabilizerCoordinateIsometry q (G.stabilizerOfGauge q g hg))
    (M.stabilizerCoordinateIsometry q (G.stabilizerOfGauge q g hg)).measurePreserving

def normalFiberAction (q : Boson N) (g : GaugeGroup N) :
    Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)) →ₗ[ℂ]
      Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)) :=
  ContinuousLinearMap.compLpₗ 2 volume (G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap

def normalEquivariantSpace (q : Boson N) :
    Submodule ℂ (Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q))) :=
  ⨅ g : {g : GaugeGroup N // G.boson g q = q},
    LinearMap.ker (G.normalBosonPullback q g.val g.prop - G.normalFiberAction q g.val)

lemma normalEquivariantSpace_closed (q : Boson N) :
    IsClosed (G.normalEquivariantSpace q : Set (Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)))) := by
  have hb (g : GaugeGroup N) (hg : G.boson g q = q) : Continuous (G.normalBosonPullback q g hg) :=
    (Lp.compMeasurePreservingₗᵢ ℂ (M.stabilizerCoordinateIsometry q (G.stabilizerOfGauge q g hg))
      (M.stabilizerCoordinateIsometry q (G.stabilizerOfGauge q g hg)).measurePreserving).continuous
  have hf (g : GaugeGroup N) : Continuous (G.normalFiberAction q g) :=
    ((G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 volume).continuous
  rw [normalEquivariantSpace,Submodule.coe_iInf]
  change IsClosed (⋂ g : {g : GaugeGroup N // G.boson g q = q},
    {x | (G.normalBosonPullback q g.val g.prop - G.normalFiberAction q g.val) x = 0})
  exact isClosed_iInter fun g => isClosed_eq ((hb g.val g.prop).sub (hf g.val)) continuous_const

namespace MeasuredNormalPatch
variable {G} {q : Boson N} (P : G.MeasuredNormalPatch q)
attribute [local irreducible] closedProfile

lemma profile_mem_equivariantSpace (h : ℝ) (f : G.invariantCore) :
    P.profile h f ∈ G.normalEquivariantSpace q := by
  apply (Submodule.mem_iInf _).2
  intro g
  change G.normalBosonPullback q g.val g.prop (P.profile h f) -
    G.normalFiberAction q g.val (P.profile h f) = 0
  apply sub_eq_zero.mpr
  apply Lp.ext
  let e := M.stabilizerCoordinateIsometry q (G.stabilizerOfGauge q g.val g.prop)
  have hb := Lp.coeFn_compMeasurePreserving (P.profile h f) e.measurePreserving
  have hf := ContinuousLinearMap.coeFn_compLp
    (G.fermion g.val).toContinuousLinearEquiv.toContinuousLinearMap (P.profile h f)
  have hp := (P.profile_ae h f).comp_tendsto e.measurePreserving.quasiMeasurePreserving.tendsto_ae
  filter_upwards [hb,hf,hp,P.profile_ae h f] with x hxb hxf hxp hxx
  calc
    _ = P.profile h f (e x) := hxb
    _ = M.normalMeasuredCoordinates q h P.density P.cutoff f.val (e x) := hxp
    _ = G.fermion g.val (M.normalMeasuredCoordinates q h P.density P.cutoff f.val x) :=
      P.normalMeasuredCoordinates_equivariant h f g.val g.prop x
    _ = G.fermion g.val (P.profile h f x) := congrArg (G.fermion g.val) hxx.symm
    _ = _ := hxf.symm

lemma closedProfile_mem_equivariantSpace {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) (x : G.coreNormClosure) :
    P.closedProfile h x ∈ G.normalEquivariantSpace q := by
  have hc : IsClosed {x : G.coreNormClosure | P.closedProfile h x ∈ G.normalEquivariantSpace q} :=
    (G.normalEquivariantSpace_closed q).preimage (P.closedProfile h).continuous
  apply closure_minimal (s := range G.coreNormEmbedding) _ hc (G.coreNormEmbedding_dense x)
  rintro _ ⟨f,rfl⟩
  change P.closedProfile h (G.coreNormEmbedding f) ∈ G.normalEquivariantSpace q
  rw [P.closedProfile_core hh h1]
  exact P.profile_mem_equivariantSpace h f

lemma limit_mem_equivariantSpace
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n ∧ h n ≤ 1) (x : ℕ → G.coreNormClosure)
    {v : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q))}
    (hv : Tendsto (fun n => P.closedProfile (h n) (x n)) atTop (nhds v)) :
    v ∈ G.normalEquivariantSpace q :=
  (G.normalEquivariantSpace_closed q).mem_of_tendsto hv
    (Filter.Eventually.of_forall fun n => P.closedProfile_mem_equivariantSpace (hh n).1 (hh n).2 (x n))
end MeasuredNormalPatch
end
end BFSSQuantum.AlgebraData.GaugeData

end OAI
