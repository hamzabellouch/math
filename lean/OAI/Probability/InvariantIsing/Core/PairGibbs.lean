import OAI.Probability.InvariantIsing.Arrays.ReplicaContractions

namespace OAI

/-! Two-replica Gibbs calculus used by the off-diagonal Ward equation. -/

noncomputable section

open IsingPerceptron MeasureTheory
open scoped BigOperators

namespace InvariantIsing

variable {S : Type*} [Fintype S]

omit [Fintype S] in
lemma GibbsReference_pair {w : S → ℝ} (hw : GibbsReference w) :
    GibbsReference (fun x : S × S => w x.1 * w x.2) := by
  refine ⟨fun x => mul_nonneg (hw.1 x.1) (hw.1 x.2), ?_⟩
  obtain ⟨σ, hσ⟩ := hw.2
  exact ⟨(σ, σ), mul_pos hσ hσ⟩

lemma finitePartition_pair (w H : S → ℝ) :
    finitePartition (fun x : S × S => w x.1 * w x.2)
      (fun x => H x.1 + H x.2) = finitePartition w H * finitePartition w H := by
  simp only [finitePartition, Fintype.sum_prod_type, Real.exp_add, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  ring

lemma finiteGibbs_pair (w H : S → ℝ) (x : S × S) :
    finiteGibbs (fun x : S × S => w x.1 * w x.2) (fun x => H x.1 + H x.2) x =
      finiteGibbs w H x.1 * finiteGibbs w H x.2 := by
  simp only [finiteGibbs, finitePartition_pair, Real.exp_add, div_eq_mul_inv, mul_inv_rev]
  ring

lemma gibbsAverage_pair (w H : S → ℝ) (A : S → S → ℝ) :
    gibbsAverage (fun x : S × S => w x.1 * w x.2) (fun x => H x.1 + H x.2)
      (fun x => A x.1 x.2) = gibbsPairAverage w H A := by
  simp only [gibbsAverage, Fintype.sum_prod_type, finiteGibbs_pair, gibbsPairAverage]

lemma gibbsPairAverage_add (w H : S → ℝ) (A B : S → S → ℝ) :
    gibbsPairAverage w H (fun σ τ => A σ τ + B σ τ) =
      gibbsPairAverage w H A + gibbsPairAverage w H B := by
  simp only [gibbsPairAverage, mul_add, Finset.sum_add_distrib]

lemma gibbsPairAverage_fst {w : S → ℝ} (hw : GibbsReference w) (H A : S → ℝ) :
    gibbsPairAverage w H (fun σ _ => A σ) = gibbsAverage w H A := by
  calc
    _ = ∑ σ, finiteGibbs w H σ * A σ * ∑ τ, finiteGibbs w H τ := by
      simp only [gibbsPairAverage, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro τ _
      ring
    _ = _ := by simp only [finiteGibbs_sum hw H, mul_one, gibbsAverage]

lemma gibbsPairAverage_swap (w H : S → ℝ) (A : S → S → ℝ) :
    gibbsPairAverage w H (fun σ τ => A τ σ) = gibbsPairAverage w H A := by
  unfold gibbsPairAverage
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  ring

lemma gibbsPairAverage_snd {w : S → ℝ} (hw : GibbsReference w) (H A : S → ℝ) :
    gibbsPairAverage w H (fun _ τ => A τ) = gibbsAverage w H A := by
  rw [← gibbsPairAverage_fst hw H A]
  exact gibbsPairAverage_swap w H (fun σ _ => A σ)

lemma gibbsAverage_pair_sum {w : S → ℝ} (hw : GibbsReference w) (H A : S → ℝ) :
    gibbsAverage (fun x : S × S => w x.1 * w x.2) (fun x => H x.1 + H x.2)
      (fun x => A x.1 + A x.2) = 2 * gibbsAverage w H A := by
  rw [gibbsAverage_pair w H (fun σ τ => A σ + A τ), gibbsPairAverage_add,
    gibbsPairAverage_fst hw, gibbsPairAverage_snd hw]
  ring

/-- The two-replica derivative has one Hamiltonian insertion in each existing
replica and two Gibbs normalization subtractions. -/
lemma hasDerivAt_gibbsPairAverage {w : S → ℝ} (hw : GibbsReference w)
    {H : ℝ → S → ℝ} {A : ℝ → S → S → ℝ}
    {dH : S → ℝ} {dA : S → S → ℝ} {t : ℝ}
    (hH : ∀ σ, HasDerivAt (fun s => H s σ) (dH σ) t)
    (hA : ∀ σ τ, HasDerivAt (fun s => A s σ τ) (dA σ τ) t) :
    HasDerivAt (fun s => gibbsPairAverage w (H s) (A s))
      (gibbsPairAverage w (H t) dA +
        gibbsPairAverage w (H t) (fun σ τ => A t σ τ * (dH σ + dH τ)) -
        2 * gibbsPairAverage w (H t) (A t) * gibbsAverage w (H t) dH) t := by
  have hd := hasDerivAt_gibbsAverage (GibbsReference_pair hw)
    (fun x : S × S => (hH x.1).add (hH x.2)) (fun x : S × S => hA x.1 x.2)
  simp only [Pi.add_apply, gibbsAverage_pair] at hd
  rw [gibbsAverage_pair w (H t) (fun σ τ => A t σ τ * (dH σ + dH τ)),
    gibbsAverage_pair w (H t) (fun σ τ => dH σ + dH τ)] at hd
  rw [gibbsPairAverage_add, gibbsPairAverage_fst hw, gibbsPairAverage_snd hw] at hd
  convert hd using 1
  ring

end InvariantIsing

end

end OAI
