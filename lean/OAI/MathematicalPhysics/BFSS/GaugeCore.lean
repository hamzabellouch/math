import Mathlib
import OAI.MathematicalPhysics.BFSS.GaugeOrbits

namespace OAI

/-! Gauge actions on the physical Hilbert space and invariant smooth core. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)

def adjointCoefficient (g : GaugeGroup N) (A B : ColorIndex N) : ℝ :=
  (Matrix.trace (M.color B * ((g : ColorMatrix N) * M.color A *
    (g : ColorMatrix N).conjTranspose))).re

structure GaugeData where
  boson : GaugeGroup N →* (Boson N ≃ₗᵢ[ℝ] Boson N)
  fermion : GaugeGroup N →* (Fermion N ≃ₗᵢ[ℂ] Fermion N)
  boson_adjoint : ∀ g x i, M.matrixCoordinate (boson g x) i =
    (g : ColorMatrix N) * M.matrixCoordinate x i * (g : ColorMatrix N).conjTranspose
  fermion_adjoint : ∀ g α A f, fermion g (M.theta α A f) =
    ∑ B : ColorIndex N, (M.adjointCoefficient g A B : ℂ) •
      M.theta α B (fermion g f)
  boson_continuous : Continuous (fun z : GaugeGroup N × Boson N => boson z.1 z.2)
  fermion_continuous : Continuous (fun z : GaugeGroup N × Fermion N => fermion z.1 z.2)

namespace GaugeData
variable {M} (G : M.GaugeData)

def bosonPullback (g : GaugeGroup N) : FullL2 N →ₗ[ℂ] FullL2 N :=
  Lp.compMeasurePreservingₗ ℂ (G.boson g) (G.boson g).measurePreserving

def fiberAction (g : GaugeGroup N) : FullL2 N →ₗ[ℂ] FullL2 N :=
  ContinuousLinearMap.compLpₗ 2 (volume : Measure (Boson N))
    (G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap

def physicalSpace : Submodule ℂ (FullL2 N) :=
  ⨅ g : GaugeGroup N, LinearMap.ker (G.bosonPullback g - G.fiberAction g)

lemma physicalSpace_closed : IsClosed (G.physicalSpace : Set (FullL2 N)) := by
  have hb (g : GaugeGroup N) : Continuous (G.bosonPullback g) :=
    (Lp.compMeasurePreservingₗᵢ ℂ (G.boson g) (G.boson g).measurePreserving).continuous
  have hf (g : GaugeGroup N) : Continuous (G.fiberAction g) :=
    ((G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 volume).continuous
  rw [physicalSpace, Submodule.coe_iInf]
  change IsClosed (⋂ g : GaugeGroup N,
    {x : FullL2 N | (G.bosonPullback g - G.fiberAction g) x = 0})
  exact isClosed_iInter fun g => isClosed_eq ((hb g).sub (hf g)) continuous_const

def invariantCore : Submodule ℂ (SmoothCore N) :=
  G.physicalSpace.comap coreToL2

lemma invariantCore_equivariant (f : G.invariantCore) (g : GaugeGroup N) (x : Boson N) :
    f.val (G.boson g x) = G.fermion g (f.val x) := by
  have hmem : coreToL2 f.val ∈ G.physicalSpace := f.prop
  have he : G.bosonPullback g (coreToL2 f.val) = G.fiberAction g (coreToL2 f.val) := by
    have hh := (Submodule.mem_iInf _).mp hmem g
    exact sub_eq_zero.mp hh
  have hb := Lp.coeFn_compMeasurePreserving (coreToL2 f.val) (G.boson g).measurePreserving
  have hf := ContinuousLinearMap.coeFn_compLp
    (G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap (coreToL2 f.val)
  have ha := (coreToL2_ae f.val).comp_tendsto
    (G.boson g).measurePreserving.quasiMeasurePreserving.tendsto_ae
  have hEq : (fun x => f.val (G.boson g x)) =ᵐ[volume] (fun x => G.fermion g (f.val x)) := by
    have he' := Lp.ext_iff.mp he
    filter_upwards [hb,hf,ha,coreToL2_ae f.val,he'] with y hyb hyf hya hy hye
    exact hya.symm.trans (hyb.symm.trans (hye.trans (hyf.trans (congrArg (G.fermion g) hy))))
  have hp := (Continuous.ae_eq_iff_eq volume
    (f.val.continuous.comp (G.boson g).continuous)
    ((G.fermion g).continuous.comp f.val.continuous)).mp hEq
  exact congrFun hp x

lemma invariantCore_norm_gauge (f : G.invariantCore) (g : GaugeGroup N) (x : Boson N) :
    ‖f.val (G.boson g x)‖ = ‖f.val x‖ := by
  rw [G.invariantCore_equivariant]
  exact (G.fermion g).norm_map _

end GaugeData
end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)

lemma exists_specialUnitary_same_conjugation (hN : 2 ≤ N)
    (U : unitary (ColorMatrix N)) :
    ∃ g : GaugeGroup N, ∀ X : ColorMatrix N,
      (g : ColorMatrix N)*X*(g : ColorMatrix N)ᴴ =
      (U : ColorMatrix N)*X*(U : ColorMatrix N)ᴴ := by
  obtain ⟨c,hc⟩ := IsAlgClosed.exists_pow_nat_eq ((U : ColorMatrix N).det)⁻¹
    (show 0 < N by omega)
  have hd : ‖(U : ColorMatrix N).det‖ = 1 :=
    CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary U.prop)
  have hcn : ‖c‖ = 1 := by
    apply (pow_left_inj₀ (norm_nonneg c) zero_le_one (by omega : N ≠ 0)).mp
    rw [←norm_pow,hc,norm_inv,hd,inv_one,one_pow]
  have hcc : c * star c = 1 := by
    change c * (starRingEnd ℂ) c = 1
    rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hcn,one_pow,Complex.ofReal_one]
  have hcu : c ∈ unitary ℂ := Unitary.mem_iff.mpr ⟨by rw [mul_comm]; exact hcc,hcc⟩
  have hunit : c • (U : ColorMatrix N) ∈ unitary (ColorMatrix N) :=
    Unitary.smul_mem (⟨c,hcu⟩ : unitary ℂ) U.prop
  have hdet : (c • (U : ColorMatrix N)).det = 1 := by
    rw [Matrix.det_smul,Fintype.card_fin,hc]
    exact inv_mul_cancel₀ (by intro hz; simp [hz] at hd)
  refine ⟨⟨c • (U : ColorMatrix N),hunit,hdet⟩,?_⟩
  intro X
  change (c • (U : ColorMatrix N))*X*(c • (U : ColorMatrix N))ᴴ = _
  rw [Matrix.conjTranspose_smul,smul_mul_assoc,mul_smul_comm,smul_mul_assoc,smul_smul,
    mul_comm (star c) c,hcc,one_smul]

namespace GaugeData
variable {M} (G : M.GaugeData)

lemma boson_eq_gaugeAction (g : GaugeGroup N) (x : Boson N) :
    G.boson g x = M.gaugeAction ⟨g,g.prop.1⟩ x := by
  have hp (i : SpaceIndex) : spatialColor (G.boson g x) i =
      spatialColor (M.gaugeAction ⟨g,g.prop.1⟩ x) i := by
    apply M.colorEmbed_injective
    change M.matrixCoordinate (G.boson g x) i =
      M.colorEmbed (M.colorConjugate g (spatialColor x i))
    rw [M.colorEmbed_conjugate g g.prop.1]
    exact G.boson_adjoint g x i
  ext p
  exact congrArg (fun a : ColorVector N => a p.2) (hp p.1)

lemma unitary_boson_exists (hN : 2 ≤ N) (U : unitary (ColorMatrix N)) :
    ∃ g : GaugeGroup N, ∀ x : Boson N, G.boson g x = M.gaugeAction U x := by
  obtain ⟨g,hg⟩ := exists_specialUnitary_same_conjugation hN U
  refine ⟨g,?_⟩
  intro x
  rw [G.boson_eq_gaugeAction]
  ext p
  change M.colorExtract ((g : ColorMatrix N)*M.colorEmbed (spatialColor x p.1)*
    (g : ColorMatrix N)ᴴ) p.2 = M.colorExtract ((U : ColorMatrix N)*
      M.colorEmbed (spatialColor x p.1)*(U : ColorMatrix N)ᴴ) p.2
  rw [hg]

lemma invariantCore_norm_unitary (hN : 2 ≤ N) (f : G.invariantCore)
    (U : unitary (ColorMatrix N)) (x : Boson N) :
    ‖f.val (M.gaugeAction U x)‖ = ‖f.val x‖ := by
  obtain ⟨g,hg⟩ := G.unitary_boson_exists hN U
  rw [←hg x]
  exact G.invariantCore_norm_gauge f g x

end GaugeData
end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData.GaugeData
noncomputable section
open MeasureTheory
variable {N : ℕ} {M : AlgebraData N} (G : M.GaugeData)

lemma invariantCore_fderiv (f : G.invariantCore) (g : GaugeGroup N) (x v : Boson N) :
    fderiv ℝ (f.val : Boson N → Fermion N) (G.boson g x) (G.boson g v) =
      G.fermion g (fderiv ℝ (f.val : Boson N → Fermion N) x v) := by
  let B : Fermion N →L[ℝ] Fermion N :=
    (G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have hf : Differentiable ℝ (f.val : Boson N → Fermion N) :=
    f.val.contDiff.differentiable (by norm_num)
  have hl := (hf (G.boson g x)).hasFDerivAt.comp x (G.boson g).hasFDerivAt
  have hr := B.hasFDerivAt.comp x (hf x).hasFDerivAt
  have he : ((f.val : Boson N → Fermion N) ∘ G.boson g) = B ∘ f.val := by
    funext y
    exact G.invariantCore_equivariant f g y
  rw [he] at hl
  have hd := hl.unique hr
  exact congrArg (fun L : Boson N →L[ℝ] Fermion N => L v) hd

lemma invariantCore_fderiv_norm (f : G.invariantCore) (g : GaugeGroup N) (x : Boson N) :
    ‖fderiv ℝ (f.val : Boson N → Fermion N) (G.boson g x)‖ =
      ‖fderiv ℝ (f.val : Boson N → Fermion N) x‖ := by
  have hp (k : GaugeGroup N) (y : Boson N) :
      ‖fderiv ℝ (f.val : Boson N → Fermion N) (G.boson k y)‖ ≤
        ‖fderiv ℝ (f.val : Boson N → Fermion N) y‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    obtain ⟨w,rfl⟩ := (G.boson k).surjective v
    rw [G.invariantCore_fderiv,(G.fermion k).norm_map,(G.boson k).norm_map]
    exact (fderiv ℝ (f.val : Boson N → Fermion N) y).le_opNorm w
  apply le_antisymm (hp g x)
  have hh := hp g⁻¹ (G.boson g x)
  simpa using hh

lemma invariantCore_fderiv_norm_unitary (hN : 2 ≤ N) (f : G.invariantCore)
    (U : unitary (ColorMatrix N)) (x : Boson N) :
    ‖fderiv ℝ (f.val : Boson N → Fermion N) (M.gaugeAction U x)‖ =
      ‖fderiv ℝ (f.val : Boson N → Fermion N) x‖ := by
  obtain ⟨g,hg⟩ := G.unitary_boson_exists hN U
  rw [←hg x]
  exact G.invariantCore_fderiv_norm f g x

end
end BFSSQuantum.AlgebraData.GaugeData

end OAI
