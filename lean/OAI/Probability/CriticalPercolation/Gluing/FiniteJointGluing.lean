import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.HitValue
import OAI.Probability.CriticalPercolation.Gluing.FiniteJointGluingStrict
import OAI.Probability.CriticalPercolation.ProductMeasure.ContinuousExpectWeights

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma finite_joint_gluing (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (o : V) (A T : Set V) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ expect w
      (fun ω => hitValue T (component (G.openGraph ω) v))) :
    expect w (fun ω => hitValue A (component (G.openGraph ω) o)) * a ≤
      expect w (fun ω => jointHitValue A T (component (G.openGraph ω) o)) := by
  classical
  let w' : ℝ → E → Prop → ℝ := fun t e b => (1-t) * w e b + if b then 0 else t
  have hzero : w' 0 = w := by funext e b; simp [w']
  have hcont : Continuous w' := by
    apply continuous_pi
    intro e
    apply continuous_pi
    intro b
    dsimp only [w']
    split_ifs <;> fun_prop
  let err : ℝ → ℝ := fun t => ∑ v : V,
    |expect (w' t) (fun ω => hitValue T (component (G.openGraph ω) v)) -
      expect w (fun ω => hitValue T (component (G.openGraph ω) v))|
  have herr : Continuous err := by
    apply continuous_finsetSum
    intro v _
    exact (((continuous_expect_weights _).comp hcont).sub continuous_const).abs
  have herr0 : err 0 = 0 := by simp [err, hzero]
  have hbound (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
      expect (w' t) (fun ω => hitValue A (component (G.openGraph ω) o)) * (a-err t) ≤
        expect (w' t) (fun ω => jointHitValue A T (component (G.openGraph ω) o)) := by
    apply G.finite_joint_gluing_strict
    · intro e
      have hs := hw e
      simp only [Fintype.sum_Prop] at hs ⊢
      dsimp only [w']
      rw [ite_eq_left True.intro, ite_eq_right (by trivial : ¬ False)]
      nlinarith
    · intro e b
      have hm := mul_nonneg (sub_nonneg.mpr ht1) (hpos e b)
      dsimp only [w']
      apply add_nonneg hm
      split_ifs <;> linarith
    · intro e
      have hm := mul_nonneg (sub_nonneg.mpr ht1) (hpos e False)
      dsimp only [w']
      rw [ite_eq_right (by trivial : ¬ False)]
      exact add_pos_of_nonneg_of_pos hm ht
    · intro v hv
      have hsingle :
          |expect (w' t) (fun ω => hitValue T (component (G.openGraph ω) v)) -
            expect w (fun ω => hitValue T (component (G.openGraph ω) v))| ≤ err t := by
        dsimp only [err]
        exact Finset.single_le_sum (f := fun u : V =>
          |expect (w' t) (fun ω => hitValue T (component (G.openGraph ω) u)) -
            expect w (fun ω => hitValue T (component (G.openGraph ω) u))|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ v)
      have hneg := (abs_le.mp hsingle).1
      linarith [ha v hv]
  have ht : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ)+1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hL := ((((continuous_expect_weights
    (fun ω => hitValue A (component (G.openGraph ω) o))).comp hcont).mul
      ((continuous_const (y := a)).sub herr)).tendsto 0).comp ht
  have hR := (((continuous_expect_weights
    (fun ω => jointHitValue A T (component (G.openGraph ω) o))).comp hcont).tendsto 0).comp ht
  have hh := le_of_tendsto_of_tendsto hL hR (Filter.Eventually.of_forall (fun n : ℕ =>
    hbound (1/((n : ℝ)+1)) (by positivity) (by
      apply (div_le_one (by positivity : (0 : ℝ) < n+1)).mpr
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith)))
  simpa only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply, hzero, herr0, sub_zero] using hh

end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

end
end

end OAI
