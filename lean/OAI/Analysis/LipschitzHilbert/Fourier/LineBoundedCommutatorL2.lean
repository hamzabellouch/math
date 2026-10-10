import OAI.Analysis.LipschitzHilbert.Fourier.LineCommutatorLinearity

namespace OAI

/-! For a fixed bounded Schwartz coefficient the undifferentiated
commutator is an actual bounded L2 map. This identifies the limits of
the differentiated frequency approximations. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def lineProductLM (b : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ →ₗ[ℂ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.smulLeftCLM ℂ b).toLinearMap

theorem lineProductLM_apply (b f : SchwartzMap ℝ ℂ) :
    lineProductLM b f=lineSchwartzProduct b f := by
  ext x
  simp only [lineProductLM,ContinuousLinearMap.coe_coe,
    SchwartzMap.smulLeftCLM_apply_apply b.hasTemperateGrowth,smul_eq_mul,lineSchwartzProduct_apply]

def lineCommutatorLM (m b : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ →ₗ[ℂ] SchwartzMap ℝ ℂ :=
  (lineProductLM b).comp (lineSchwartzProjectionLM m 1 (by norm_num))-
    (lineSchwartzProjectionLM m 1 (by norm_num)).comp (lineProductLM b)

theorem lineCommutatorLM_apply (m b f : SchwartzMap ℝ ℂ) :
    lineCommutatorLM m b f=lineSchwartzCommutator m b f := by
  simp only [lineCommutatorLM,LinearMap.sub_apply,LinearMap.comp_apply,lineProductLM_apply,
    lineSchwartzCommutator]
  rfl

def lineCommutatorToL2 (m b : SchwartzMap ℝ ℂ) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap.comp (lineCommutatorLM m b)

theorem lineCommutatorToL2_bound (m b f : SchwartzMap ℝ ℂ) (A B : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hm : ∀ eta, ‖m eta‖≤A) (hb : ∀ x, ‖b x‖≤B) :
    ‖lineCommutatorToL2 m b f‖≤(2*A*B)*‖f.toLp 2 volume‖ := by
  have hh := lineSchwartzCommutator_bounded_energy m b f A B hm hb
  have ho := memLp_toL2_norm_sq volume _ ((lineSchwartzCommutator m b f).memLp 2 volume)
  have hf := memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  change ‖(lineSchwartzCommutator m b f).toLp 2 volume‖^2=_ at ho
  change ‖f.toLp 2 volume‖^2=_ at hf
  rw [←ho,←hf] at hh
  have he : lineCommutatorToL2 m b f=(lineSchwartzCommutator m b f).toLp 2 volume := by
    change (lineCommutatorLM m b f).toLp 2 volume=_
    rw [lineCommutatorLM_apply]
  rw [he]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith only [hh]

def lineCommutatorL2 (m b : SchwartzMap ℝ ℂ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (lineCommutatorToL2 m b).extendOfNorm (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap

theorem lineCommutatorL2_onSchwartz (m b f : SchwartzMap ℝ ℂ) :
    lineCommutatorL2 m b (f.toLp 2 volume)=(lineSchwartzCommutator m b f).toLp 2 volume := by
  have he : lineCommutatorL2 m b (f.toLp 2 volume)=lineCommutatorToL2 m b f := by
    apply LinearMap.extendOfNorm_eq
    · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
    · refine ⟨2*(SchwartzMap.seminorm ℝ 0 0 m)*(SchwartzMap.seminorm ℝ 0 0 b),fun g => ?_⟩
      exact lineCommutatorToL2_bound m b g _ _ (apply_nonneg _ _) (apply_nonneg _ _)
        (fun eta => m.norm_le_seminorm ℝ eta) (fun x => b.norm_le_seminorm ℝ x)
  rw [he]
  change (lineCommutatorLM m b f).toLp 2 volume=_
  rw [lineCommutatorLM_apply]

end LipschitzHilbert.PacketRepresentation

end

end OAI
