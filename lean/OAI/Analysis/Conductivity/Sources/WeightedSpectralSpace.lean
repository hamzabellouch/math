import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology
open scoped ENNReal

abbrev SpectralL2 (ι : Type*) := lp (fun _ : ι => ℂ) 2
abbrev SpectralJet (ι : Type*) := PiLp 2 (fun _ : Fin 2 => SpectralL2 ι)

def spectralTraceGraph {ι : Type*} (w : ι → ℝ) : Submodule ℂ (SpectralJet ι) where
  carrier := {z | ∀ i, (z 1) i=(Real.sqrt (w i):ℂ)*(z 0) i}
  zero_mem' := by intro i; simp
  add_mem' := by
    intro x y hx hy i
    change (x 1) i+(y 1) i=(Real.sqrt (w i):ℂ)*((x 0) i+(y 0) i)
    rw [hx i,hy i,mul_add]
  smul_mem' := by
    intro c x hx i
    change c*((x 1) i)=(Real.sqrt (w i):ℂ)*(c*((x 0) i))
    rw [hx i]; ring

lemma spectralTraceGraph_closed {ι : Type*} (w : ι → ℝ) :
    IsClosed (spectralTraceGraph w : Set (SpectralJet ι)) := by
  change IsClosed {z : SpectralJet ι | ∀ i, (z 1) i=(Real.sqrt (w i):ℂ)*(z 0) i}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_eq ((lp.evalCLM ℂ (fun _ : ι => ℂ) 2 i).continuous.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 => SpectralL2 ι) 1))
    (continuous_const.mul ((lp.evalCLM ℂ (fun _ : ι => ℂ) 2 i).continuous.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 => SpectralL2 ι) 0)))

instance spectralTraceGraph_complete {ι : Type*} (w : ι → ℝ) :
    CompleteSpace (spectralTraceGraph w) := (spectralTraceGraph_closed w).completeSpace_coe

lemma spectralTraceGraph_fst_injective {ι : Type*} (w : ι → ℝ) :
    Function.Injective (fun z : spectralTraceGraph w => z.val 0) := by
  intro x y h
  apply Subtype.ext
  apply PiLp.ext
  intro j
  fin_cases j
  · exact h
  · ext i
    exact (x.property i).trans ((congrArg (fun f : SpectralL2 ι =>
      (Real.sqrt (w i):ℂ)*f i) h).trans (y.property i).symm)

lemma sqrt_weight_norm_sq {ι : Type*} {w : ι → ℝ} (hw : ∀ i,0≤w i)
    (f : SpectralL2 ι) (i : ι) :
    ‖(Real.sqrt (w i):ℂ)*f i‖^2=w i*‖f i‖^2 := by
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (hw i)]

lemma spectralTraceGraph_exists_iff {ι : Type*} {w : ι → ℝ} (hw : ∀ i,0≤w i)
    (f : SpectralL2 ι) :
    (∃ z : spectralTraceGraph w, z.val 0=f) ↔ Summable (fun i => w i*‖f i‖^2) := by
  constructor
  · rintro ⟨z,hz⟩
    have hh := (lp.memℓp (z.val 1)).summable (by norm_num : 0<(2:ℝ≥0∞).toReal)
    simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hh
    have he (i : ι) : ‖(z.val 1) i‖^2=w i*‖f i‖^2 := by
      rw [z.property i,hz]
      exact sqrt_weight_norm_sq hw f i
    simpa only [he] using hh
  · intro hs
    have hm : Memℓp (fun i => (Real.sqrt (w i):ℂ)*f i) 2 := by
      apply (memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).mpr
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two,sqrt_weight_norm_sq hw f] using hs
    let g : SpectralL2 ι := ⟨_,hm⟩
    refine ⟨⟨WithLp.toLp 2 ![f,g],?_⟩,?_⟩
    · intro i; rfl
    · rfl

end ScalarConductivity

end

end OAI
