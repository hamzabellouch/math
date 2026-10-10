import Mathlib
import OAI.Geometry.PrescribedRicci.TameLimit

namespace OAI

/-! Tame Rough Inverse. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ContDiff Classical ComplexOrder MatrixOrder
namespace FrozenPoisson.ParameterRegularity
open SobolevChart EllipticKernel
variable {n : ℕ} {ι : Type*} [Fintype ι]

lemma exists_tame_approximants (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (k : ℕ)
    (hs : (Module.finrank ℝ (EC n):ℝ) < 2*(k:ℝ))
    (a : ι → ι → L2 (EC n)) (f : L2 (EC n))
    (hsmall : perturbationBound v (fun i j => strongEmbedding (k:ℝ) hs (a i j))*ellipticBound H hH < 1) :
    ∃ (M θ : ℝ) (_ : 0 ≤ M) (_ : θ < 1)
      (x : ℕ → TameData H t v k M θ (ellipticBound H hH)),
      (∀ i j, Tendsto (fun l => schwartzCoord (k:ℝ) ((x l).a i j)) atTop (nhds (a i j))) ∧
      Tendsto (fun l => schwartzCoord (k:ℝ) (x l).f) atTop (nhds f) := by
  choose aa haa using fun i j => exists_schwartz_approx (k:ℝ) (a i j)
  obtain ⟨ff,hff⟩ := exists_schwartz_approx (k:ℝ) f
  let asq : ℕ → SmoothCoefficients ι (EC n) := fun l i j => aa i j l
  let p := perturbationBound v (fun i j => strongEmbedding (k:ℝ) hs (a i j))*ellipticBound H hH
  let θ := (p+1)/2
  have hθp : p < θ := by dsimp [θ,p]; linarith
  have hθ : θ < 1 := by dsimp [θ,p]; linarith
  have ha0 := coefficientBCF_tendsto (k:ℝ) hs asq a haa
  have hp : Tendsto (fun l => perturbationBound v (coefficientBCF (asq l))*ellipticBound H hH)
      atTop (nhds p) := ((continuous_perturbationBound v).tendsto _ |>.comp ha0).mul_const _
  have hsm : ∀ᶠ l in atTop, perturbationBound v (coefficientBCF (asq l))*ellipticBound H hH ≤ θ :=
    (hp.eventually (gt_mem_nhds hθp)).mono (fun _ h => h.le)
  let M := (∑ i, ∑ j, ‖a i j‖)+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMa (i j : ι) : ‖a i j‖+1 ≤ M := by
    have hij : ‖a i j‖ ≤ ∑ i, ∑ j, ‖a i j‖ :=
      (Finset.single_le_sum (fun l _ => norm_nonneg (a i l)) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun m _ => norm_nonneg (a l m))) (Finset.mem_univ i))
    exact add_le_add hij le_rfl
  have hbd : ∀ᶠ l in atTop, ∀ i j, ‖schwartzCoord (k:ℝ) (asq l i j)‖ ≤ M := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    have hh := (haa i j).norm.eventually (gt_mem_nhds (show ‖a i j‖ < ‖a i j‖+1 by linarith))
    exact hh.mono (fun _ hl => hl.le.trans (hMa i j))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hbd.and hsm)
  have hn (l : ℕ) := hN (l+N) (Nat.le_add_left N l)
  let x (l : ℕ) : TameData H t v k M θ (ellipticBound H hH) :=
    ⟨asq (l+N),ff (l+N),schwartzLocal H hH t ht v (asq (l+N)) ((hn l).2.trans_lt hθ) (ff (l+N)),
      (hn l).1,(hn l).2,
      schwartzLocal_fixed H hH t ht v (asq (l+N)) ((hn l).2.trans_lt hθ) (ff (l+N))⟩
  refine ⟨M,θ,hM,hθ,x,fun i j => ?_,?_⟩
  · exact (haa i j).comp (tendsto_add_atTop_nat N)
  · exact hff.comp (tendsto_add_atTop_nat N)

 

theorem rough_local_memSobolev (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (k : ℕ)
    (hk : Module.finrank ℝ (EC n)+1 < k)
    (hs : (Module.finrank ℝ (EC n):ℝ) < 2*(k:ℝ))
    (a : ι → ι → L2 (EC n)) (f : L2 (EC n))
    (hsmall : perturbationBound v (fun i j => strongEmbedding (k:ℝ) hs (a i j))*ellipticBound H hH < 1) :
    MemSobolev ((k:ℝ)+2) 2 (realize 2 (parameterLocal H hH t ht v
      (fun i j => strongEmbedding (k:ℝ) hs (a i j)) hsmall (lowerCoord (k:ℝ) 0 (Nat.cast_nonneg k) f))) := by
  obtain ⟨M,θ,hM,hθ,x,ha,hf⟩ := exists_tame_approximants H hH t ht v k hs a f hsmall
  exact tame_limit_representation H hH t ht v k hk hs M hM θ hθ x a f ha hf hsmall

end FrozenPoisson.ParameterRegularity

end
end

end OAI
