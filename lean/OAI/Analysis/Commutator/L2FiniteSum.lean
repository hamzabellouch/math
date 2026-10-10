import Mathlib
import OAI.Analysis.Commutator.DecomposableNorm

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma memLp_vector (f : PiLp 2 (fun _ : ι => Lp H 2 μ)) :
    MemLp (fun a => WithLp.toLp 2 (fun i => f i a)) 2 μ := by
  have hm : MemLp (fun a i => f i a) 2 μ := memLp_pi_iff.mpr (fun i => Lp.memLp (f i))
  exact hm.continuousLinearMap_comp (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap

def assemble (f : PiLp 2 (fun _ : ι => Lp H 2 μ)) : Lp (PiLp 2 (fun _ : ι => H)) 2 μ :=
  (memLp_vector μ f).toLp _

omit [CompleteSpace H] in
lemma assemble_ae (f : PiLp 2 (fun _ : ι => Lp H 2 μ)) :
    assemble μ f =ᵐ[μ] fun a => WithLp.toLp 2 (fun i => f i a) := MemLp.coeFn_toLp _

omit [CompleteSpace H] in
lemma assemble_add (f g : PiLp 2 (fun _ : ι => Lp H 2 μ)) :
    assemble μ (f+g)=assemble μ f+assemble μ g := by
  apply Lp.ext
  have hv : ∀ᵐ a ∂μ,∀ i,(f i+g i) a=f i a+g i a := ae_all_iff.mpr (fun i => Lp.coeFn_add (f i) (g i))
  filter_upwards [assemble_ae μ (f+g),assemble_ae μ f,assemble_ae μ g,
    Lp.coeFn_add (assemble μ f) (assemble μ g),hv] with a h1 h2 h3 h4 ha
  rw [h1,h4]
  change _=assemble μ f a+assemble μ g a
  rw [h2,h3]
  ext i
  exact ha i

omit [CompleteSpace H] in
lemma assemble_smul (c : ℂ) (f : PiLp 2 (fun _ : ι => Lp H 2 μ)) :
    assemble μ (c • f)=c • assemble μ f := by
  apply Lp.ext
  have hv : ∀ᵐ a ∂μ,∀ i,(c • f i) a=c • (f i a) := ae_all_iff.mpr (fun i => Lp.coeFn_smul c (f i))
  filter_upwards [assemble_ae μ (c • f),assemble_ae μ f,Lp.coeFn_smul c (assemble μ f),hv]
    with a h1 h2 h3 ha
  rw [h1,h3]
  change _=c • (assemble μ f a)
  rw [h2]
  ext i
  exact ha i

omit [CompleteSpace H] in
lemma assemble_norm (f : PiLp 2 (fun _ : ι => Lp H 2 μ)) : ‖assemble μ f‖=‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [l2_norm_sq,PiLp.norm_sq_eq_of_L2]
  calc
    _=(∫ a,∑ i,‖f i a‖^2 ∂μ) := by
      apply integral_congr_ae
      filter_upwards [assemble_ae μ f] with a ha
      rw [ha,PiLp.norm_sq_eq_of_L2]
    _=∑ i,∫ a,‖f i a‖^2 ∂μ := integral_finsetSum _ (fun i _ =>
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (f i))).mp (Lp.memLp (f i)))
    _=_ := by congr 1; ext i; exact (l2_norm_sq μ (f i)).symm

def assembleIsometry : PiLp 2 (fun _ : ι => Lp H 2 μ) →ₗᵢ[ℂ] Lp (PiLp 2 (fun _ : ι => H)) 2 μ where
  toFun := assemble μ
  map_add' := assemble_add μ
  map_smul' := assemble_smul μ
  norm_map' := assemble_norm μ

omit [CompleteSpace H] in
lemma assemble_surjective : Function.Surjective (assembleIsometry (H:=H) (ι:=ι) μ) := by
  intro f
  let g : PiLp 2 (fun _ : ι => Lp H 2 μ) :=
    WithLp.toLp 2 (fun i => (PiLp.proj 2 (fun _ : ι => H) i : PiLp 2 (fun _ : ι => H) →L[ℂ] H).compLp f)
  refine ⟨g,?_⟩
  apply Lp.ext
  have hg : ∀ᵐ a ∂μ,∀ i,g i a=f a i := ae_all_iff.mpr (fun i => ContinuousLinearMap.coeFn_compLp _ _)
  filter_upwards [assemble_ae μ g,hg] with a ha hb
  change assemble μ g a=f a
  rw [ha]
  ext i
  exact hb i

def finiteSumEquiv : PiLp 2 (fun _ : ι => Lp H 2 μ) ≃ₗᵢ[ℂ] Lp (PiLp 2 (fun _ : ι => H)) 2 μ :=
  LinearIsometryEquiv.ofSurjective (assembleIsometry μ) (assemble_surjective μ)

end Kadison.Decomposable

end

end
end

end OAI
