import Mathlib
import OAI.Geometry.PrescribedRicci.TameStability

namespace OAI

/-! Tame Approximation. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ContDiff Classical ComplexOrder MatrixOrder
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]

lemma schwartzCoord_sub (s : ℝ) (f g : 𝓢(E,ℂ)) :
    schwartzCoord s (f-g) = schwartzCoord s f-schwartzCoord s g := by
  apply realize_injective s
  simp only [map_sub,realize_schwartzCoord]

lemma continuous_multiply : Continuous (fun p : (E →ᵇ ℂ) × L2 E => multiply p.1 p.2) := by
  change Continuous (fun p : (E →ᵇ ℂ) × L2 E =>
    (ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2 (boundedToLinf p.1) p.2)
  fun_prop

omit [Fintype ι] in
lemma continuous_perturbation_entry (v : ι → E) (i j : ι) :
    Continuous (fun p : (ι → ι → E →ᵇ ℂ) × L2 E =>
      multiply (p.1 i j) (secondH2 (v i) (v j) p.2)) := by
  have ha : Continuous (fun p : (ι → ι → E →ᵇ ℂ) × L2 E => p.1 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)
  have hu : Continuous (fun p : (ι → ι → E →ᵇ ℂ) × L2 E =>
      secondH2 (v i) (v j) p.2) :=
    (secondH2 (v i) (v j)).continuous.comp continuous_snd
  change Continuous (fun p : (ι → ι → E →ᵇ ℂ) × L2 E =>
    (ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2
      (boundedToLinf (p.1 i j)) (secondH2 (v i) (v j) p.2))
  exact (((ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2).continuous.comp
    (boundedToLinf.continuous.comp ha)).clm_apply hu

lemma perturbation_apply_identity (v : ι → E) (a : ι → ι → E →ᵇ ℂ) (u : L2 E) :
    perturbation v a u = ∑ i, ∑ j, multiply (a i j) (secondH2 (v i) (v j) u) := by
  simp only [perturbation,_root_.sum_apply,ContinuousLinearMap.comp_apply]

lemma continuous_perturbation (v : ι → E) :
    Continuous (fun p : (ι → ι → E →ᵇ ℂ) × L2 E => perturbation v p.1 p.2) := by
  simp only [perturbation_apply_identity]
  exact continuous_finsetSum Finset.univ (fun i _ =>
    continuous_finsetSum Finset.univ (fun j _ => continuous_perturbation_entry v i j))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
lemma continuous_perturbationBound (v : ι → E) :
    Continuous (perturbationBound v) := by
  unfold perturbationBound
  fun_prop

end SobolevChart
namespace FrozenPoisson.ParameterRegularity
open SobolevChart EllipticKernel
variable {n : ℕ} {ι : Type*} [Fintype ι]

lemma tame_high_cauchy (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (k : ℕ)
    (hk : Module.finrank ℝ (EC n)+1 < k) (M : ℝ) (hM : 0 ≤ M)
    (θ : ℝ) (hθ : θ < 1) (x : ℕ → TameData H t v k M θ (ellipticBound H hH))
    (hf : CauchySeq (fun l => schwartzCoord (k:ℝ) (x l).f))
    (ha : ∀ i j, CauchySeq (fun l => schwartzCoord (k:ℝ) ((x l).a i j))) :
    CauchySeq (fun l => schwartzCoord ((k:ℝ)+2) (x l).u) := by
  obtain ⟨J,hJ,hj⟩ := tame_solution_bound H hH t ht v k hk M hM θ hθ
  obtain ⟨R,hR,hfR⟩ := hf.isBounded_range.exists_pos_norm_le
  have hu (l : ℕ) : ‖schwartzCoord ((k:ℝ)+2) (x l).u‖ ≤ J*R :=
    (hj (x l)).trans (mul_le_mul_of_nonneg_left (hfR _ (mem_range_self l)) hJ)
  obtain ⟨C,B,hC,hB,hcb⟩ := tame_stability H hH t ht v k hk M hM θ hθ
  obtain ⟨bf,hbf,hbf',htf⟩ := cauchySeq_iff_le_tendsto_0.mp hf
  choose ba hba hba' hta using fun i j => cauchySeq_iff_le_tendsto_0.mp (ha i j)
  apply cauchySeq_of_le_tendsto_0 (fun N => C*(bf N+B*(∑ i, ∑ j, ba i j N)*(J*R)))
  · intro l m N hl hm
    have h0 := hcb (x l) (x m)
    simp only [schwartzCoord_sub] at h0
    rw [dist_eq_norm]
    apply h0.trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply add_le_add
    · simpa only [dist_eq_norm] using hbf' l m N hl hm
    · have ha' : (∑ i, ∑ j, ‖schwartzCoord (k:ℝ) ((x l).a i j)-
          schwartzCoord (k:ℝ) ((x m).a i j)‖) ≤ ∑ i, ∑ j, ba i j N := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        simpa only [dist_eq_norm] using hba' i j l m N hl hm
      exact mul_le_mul (mul_le_mul_of_nonneg_left ha' hB) (hu m) (norm_nonneg _)
        (mul_nonneg hB (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hba i j N))))
  · have ha0 : Tendsto (fun N => ∑ i, ∑ j, ba i j N) atTop (nhds (0:ℝ)) := by
      simpa using tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ => hta i j))
    simpa using (htf.add ((ha0.const_mul B).mul_const (J*R))).const_mul C

lemma tame_data_low_equation (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (k : ℕ) (M θ : ℝ)
    (x : TameData H t v k M θ (ellipticBound H hH)) :
    schwartzCoord 2 x.u = parameterHilbert H hH t ht
      (schwartzCoord 0 x.f + perturbation v (coefficientBCF x.a) (schwartzCoord 2 x.u)) := by
  have hh := congrArg (schwartzCoord 2) x.equation
  have hr := schwartzCoord_resolvent H hH t ht 0 (x.f+smoothPerturbation v x.a x.u)
  norm_num only [zero_add] at hr
  rw [hr,schwartzCoord_add,schwartzCoord_perturbation] at hh
  exact hh

end FrozenPoisson.ParameterRegularity

end
end

end OAI
