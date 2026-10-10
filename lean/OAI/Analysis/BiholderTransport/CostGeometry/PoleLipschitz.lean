import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ManifoldLipschitz
import OAI.Analysis.BiholderTransport.Coordinates.PoleCoordinates

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.uniform_hopfPole_lipschitz (hmtw : WeakMTW (n := n) (M := M)) (a : M) :
    ∃ C>0, ∃ r>0,
      ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀ t : ℝ, 1/2≤t → t<1 → ∀ u v : M → ℝ, Continuous u → Continuous v →
        IsCostDualPair u v →
        LipschitzOnWith (Real.toNNReal (C/(1-t)))
          (fun z => hopfPole (n := n) t u ((extChartAt 𝓘(ℝ,Model n) a).symm z))
          (ball (extChartAt 𝓘(ℝ,Model n) a a) r) := by
  let : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨B,hB,r₁,hr₁,hT₁,H⟩ := hmtw.uniform_hopfLax_C11 a
  let D : ℝ≥0 := Real.toNNReal (Metric.diam (univ : Set M))
  have hD : ∀ x y : M, dist x y≤D := by
    intro x y
    rw [Real.coe_toNNReal _ Metric.diam_nonneg]
    exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)
  obtain ⟨L,r₂,hr₂,hT₂,hL⟩ := exists_lipschitzOn_inverse_chart (E := Model n) a
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let r := min (r₁/8) (r₂/2)
  have hr : 0<r := lt_min (by positivity) (by positivity)
  have hr₁' : r<r₁/4 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr₂' : r<r₂ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hT : closedBall (χ a) r ⊆ χ.target := fun z hz =>
    hT₁ ((closedBall_subset_ball (by linarith : r<r₁)) hz)
  let K : Set (ℝ × Model n × (Model n →L[ℝ] ℝ)) :=
    Icc (1/2) 1 ×ˢ (closedBall (χ a) r ×ˢ closedBall 0 (2*(D:ℝ)*L))
  have hK : IsCompact K := isCompact_Icc.prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  obtain ⟨A,hA⟩ := contMDiffOn_exists_lipschitzOn_compact hK
    (f := coordinateBackward (n := n) a)
    (fun q hq => (coordinateBackward_contMDiffAt (hT hq.2.1)).of_le (by simp))
  let C : ℝ := (A:ℝ)*(1+12*B)+1
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,r,hr,fun z hz => hT (ball_subset_closedBall hz),?_⟩
  intro t ht ht1 u v hu hv hdual
  have ht0 : 0<t := by linarith
  have hs : 0<1-t := sub_pos.mpr ht1
  let f : Model n → ℝ := fun z => hopfLax t u (χ.symm z)
  have hf := (hopfLax_lipschitz hu hD ht0).comp_lipschitzOnWith hL
  have hd_bound : ∀ z∈ball (χ a) r, ‖fderiv ℝ f z‖≤2*(D:ℝ)*L := by
    intro z hz
    have hz₂ : z∈ball (χ a) r₂ := ball_subset_ball hr₂'.le hz
    have hn := norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hz₂) hf
    have hdiv : (D:ℝ)/t≤2*D := (div_le_iff₀ ht0).mpr (by nlinarith [D.coe_nonneg])
    calc
      _≤↑((D/Real.toNNReal t)*L : ℝ≥0) := hn
      _=(D:ℝ)/t*L := by rw [NNReal.coe_mul,NNReal.coe_div,Real.coe_toNNReal _ ht0.le]
      _≤_ := mul_le_mul_of_nonneg_right hdiv L.coe_nonneg
  have hd_lip := (H t ht0 ht1 u v hu hv hdual).2
  have hcoef : 6*(B/t+B/(1-t)) ≤ (12*B)/(1-t) := by
    have hdualT : B/t≤B/(1-t) := div_le_div_of_nonneg_left hB.le hs (by linarith)
    calc
      _ ≤ 6*(B/(1-t)+B/(1-t)) := by linarith
      _ = _ := by ring
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro z hz w hw
  have hzK : (t,z,fderiv ℝ f z)∈K :=
    ⟨⟨ht,ht1.le⟩,ball_subset_closedBall hz,by simpa only [mem_closedBall,dist_zero_right] using hd_bound z hz⟩
  have hwK : (t,w,fderiv ℝ f w)∈K :=
    ⟨⟨ht,ht1.le⟩,ball_subset_closedBall hw,by simpa only [mem_closedBall,dist_zero_right] using hd_bound w hw⟩
  have Hz := hmtw.coordinateBackward_eq_pole hu hv hdual ht0 ht1 (hT (ball_subset_closedBall hz))
  have Hw := hmtw.coordinateBackward_eq_pole hu hv hdual ht0 ht1 (hT (ball_subset_closedBall hw))
  change dist (hopfPole (n := n) t u (χ.symm z)) (hopfPole (n := n) t u (χ.symm w))≤_
  rw [←Hz,←Hw]
  have hder := hd_lip.dist_le_mul z (ball_subset_ball hr₁'.le hz)
    w (ball_subset_ball hr₁'.le hw)
  rw [Real.coe_toNNReal _ (by positivity)] at hder
  have hd : dist (t,z,fderiv ℝ f z) (t,w,fderiv ℝ f w)≤
      ((1+12*B)/(1-t))*dist z w := by
    rw [Prod.dist_eq,dist_self,Prod.dist_eq,max_eq_right (le_max_of_le_left dist_nonneg)]
    apply max_le
    · have h1 : 1≤(1+12*B)/(1-t) := (le_div_iff₀ hs).mpr (by nlinarith)
      simpa using mul_le_mul_of_nonneg_right h1 (dist_nonneg (x := z) (y := w))
    · calc
        _≤6*(B/t+B/(1-t))*dist z w := hder
        _≤((12*B)/(1-t))*dist z w := mul_le_mul_of_nonneg_right hcoef dist_nonneg
        _≤((1+12*B)/(1-t))*dist z w := mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (by linarith) hs.le) dist_nonneg
  calc
    _≤(A:ℝ)*dist (t,z,fderiv ℝ f z) (t,w,fderiv ℝ f w) := hA.dist_le_mul _ hzK _ hwK
    _≤(A:ℝ)*(((1+12*B)/(1-t))*dist z w) := mul_le_mul_of_nonneg_left hd A.coe_nonneg
    _≤(C/(1-t))*dist z w := by
      have hc : (A:ℝ)*((1+12*B)/(1-t))≤C/(1-t) := by
        rw [←mul_div_assoc]
        apply div_le_div_of_nonneg_right _ hs.le
        dsimp [C]; linarith
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc (dist_nonneg (x := z) (y := w))
    _=_ := by rw [Real.coe_toNNReal _ (div_nonneg hC.le hs.le)]
end WeakMTWTransport

end

end OAI
