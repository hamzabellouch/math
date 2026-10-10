import OAI.Analysis.LipschitzHilbert.Trees.SourceRestrictedGram

namespace OAI

/-! Exact L2 Gram identities for the finite physical packet sums. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem memLp_inner_integral (mu : Measure X) (f g : X → E)
    (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    inner ℂ (hf.toLp f) (hg.toLp g)=∫ x, inner ℂ (f x) (g x) ∂mu := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hfx hgx
  rw [hfx,hgx]

theorem memLp_toL2_norm_sq (mu : Measure X) (f : X → E) (hf : MemLp f 2 mu) :
    ‖hf.toLp f‖^2=∫ x, ‖f x‖^2 ∂mu := by
  have h := memLp_inner_integral mu f f hf hf
  simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow] at h
  change ((‖hf.toLp f‖^2 : ℝ) : ℂ)=(∫ x, ((‖f x‖^2 : ℝ) : ℂ) ∂mu) at h
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

theorem finite_integral_gram (mu : Measure X) {ι : Type*} (S : Finset ι)
    (f : ι → X → E) (hf : ∀ i∈S, MemLp (f i) 2 mu) :
    (∫ x, ‖∑ i∈S, f i x‖^2 ∂mu)=
      (∑ i∈S, ∑ j∈S, ∫ x, inner ℂ (f i x) (f j x) ∂mu).re := by
  have hi (i : ι) (hi : i∈S) (j : ι) (hj : j∈S) :
      Integrable (fun x => inner ℂ (f i x) (f j x)) mu :=
    ((hf i hi).norm.integrable_mul (hf j hj).norm).mono'
      ((hf i hi).aestronglyMeasurable.inner (hf j hj).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => norm_inner_le_norm (𝕜 := ℂ) _ _)
  have hp (x : X) : ‖∑ i∈S, f i x‖^2=(∑ i∈S, ∑ j∈S, inner ℂ (f i x) (f j x)).re := by
    change ‖∑ i∈S, f i x‖^2=RCLike.re (∑ i∈S, ∑ j∈S, inner ℂ (f i x) (f j x))
    rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ E]
    simp only [sum_inner,inner_sum,map_sum]
    exact Finset.sum_comm
  simp_rw [hp]
  have hI : Integrable (fun x => ∑ i∈S, ∑ j∈S, inner ℂ (f i x) (f j x)) mu :=
    integrable_finsetSum S (fun i hiS => integrable_finsetSum S (fun j hjS => hi i hiS j hjS))
  change (∫ x, RCLike.re (∑ i∈S, ∑ j∈S, inner ℂ (f i x) (f j x)) ∂mu)=_
  rw [integral_re hI]
  change RCLike.re (∫ x, ∑ i∈S, ∑ j∈S, inner ℂ (f i x) (f j x) ∂mu)=
    RCLike.re (∑ i∈S, ∑ j∈S, ∫ x, inner ℂ (f i x) (f j x) ∂mu)
  congr 1
  rw [integral_finsetSum _ (fun i hiS => integrable_finsetSum _ (fun j hjS => hi i hiS j hjS))]
  apply Finset.sum_congr rfl
  intro i hiS
  exact integral_finsetSum _ (fun j hjS => hi i hiS j hjS)

end LipschitzHilbert

end

end OAI
