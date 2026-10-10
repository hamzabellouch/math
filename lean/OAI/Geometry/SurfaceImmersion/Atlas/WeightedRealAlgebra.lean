import OAI.Geometry.SurfaceImmersion.Atlas.WeightedReciprocal

namespace OAI

/-! Real scalar and vector products used in the quantitative normal formula. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma WeightedBound.mul_real {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f g : E → ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2^m*C*D) (fun x => f x*g x) := by
  intro j hj x hx
  calc
    _ ≤ s^j*(∑ i ∈ Finset.range (j+1), (j.choose i : ℝ)*
        ‖iteratedFDerivWithin ℝ i f U x‖*‖iteratedFDerivWithin ℝ (j-i) g U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_mul_le (n := j) (N := ∞) hf hg hU hx
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ ≤ 2^j*C*D := weighted_binomial_bound hs hC hD j _ _
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun i hi => hbf i (hi.trans hj) x hx) (fun i hi => hbg i (hi.trans hj) x hx)
    _ ≤ _ := by gcongr; norm_num

lemma contDiffOn_dot_real {ι : Type*} [Fintype ι] {U : Set E} {f g : E → ι → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (fun x => dotProduct (f x) (g x)) U :=
  ContDiffOn.sum (fun i _ => (contDiffOn_pi.mp hf i).mul (contDiffOn_pi.mp hg i))

lemma WeightedBound.dot_real {ι : Type*} [Fintype ι] {U : Set E}
    (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ} {f g : E → ι → ℝ}
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m ((Fintype.card ι : ℝ)*(2^m*C*D))
      (fun x => dotProduct (f x) (g x)) := by
  have hh := WeightedBound.finset_sum hU hs Finset.univ (fun _ : ι => 2^m*C*D)
    (fun i x => f x i*g x i)
    (fun i _ => (contDiffOn_pi.mp hf i).mul (contDiffOn_pi.mp hg i))
    (fun i _ => (hbf.component hU hs hC hf i).mul_real hU hs hC hD
      (contDiffOn_pi.mp hf i) (contDiffOn_pi.mp hg i) (hbg.component hU hs hD hg i))
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,dotProduct] using hh

lemma WeightedBound.smul_real_pi {ι : Type*} [Fintype ι] {U : Set E}
    (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ} {f : E → ℝ} {g : E → ι → ℝ}
    (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2^m*C*D) (fun x => f x • g x) := by
  apply WeightedBound.pi hU hs (by positivity)
  · intro i
    exact hf.mul (contDiffOn_pi.mp hg i)
  · intro i
    exact hbf.mul_real hU hs.le hC hD hf (contDiffOn_pi.mp hg i)
      (hbg.component hU hs.le hD hg i)

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
