import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SpatialDTranslate
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailDifferentiability

namespace OAI

noncomputable section
namespace VelocityDetection.Cylinder
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty

theorem D_lift {f : Coord 2 → ℝ} (hf : Differentiable ℝ f) (i : Fin 3) (x : Space) :
    D i (fun y : Space => f y.1) x = fderiv ℝ f x.1 (frame i).1 := by
  have hh := ((hf x.1).hasFDerivAt.comp x (hasFDerivAt_fst (p := x))).fderiv
  change fderiv ℝ (fun y : Space => f y.1) x = _ at hh
  simp only [D, hh, ContinuousLinearMap.comp_apply]
  rfl

def horizontalD (i : Fin 3) (f : ScalarField 2) : ScalarField 2 :=
  fun t X => (![spatialD 0 f t X, spatialD 1 f t X, 0] : Fin 3 → ℝ) i

theorem D_lift_eq {f : ScalarField 2} {t : ℝ}
    (hf : Differentiable ℝ (f t)) (i : Fin 3) (x : Space) :
    D i (fun y : Space => f t y.1) x = horizontalD i f t x.1 := by
  rw [D_lift hf]
  fin_cases i
  · change fderiv ℝ (f t) x.1 (frame 0).1 = spatialD 0 f t x.1
    rw [spatialD_eq_fderiv 0 t x.1 (hf x.1)]
    congr 1
    ext j
    fin_cases j <;> simp [frame]
  · change fderiv ℝ (f t) x.1 (frame 1).1 = spatialD 1 f t x.1
    rw [spatialD_eq_fderiv 1 t x.1 (hf x.1)]
    congr 1
    ext j
    fin_cases j <;> simp [frame]
  · simp [frame, horizontalD]

@[fun_prop] theorem contDiff_horizontalD {f : ScalarField 2}
    (hf : ContDiff ℝ ∞ (uncurry f)) (i : Fin 3) :
    ContDiff ℝ ∞ (uncurry (horizontalD i f)) := by
  fin_cases i
  · change ContDiff ℝ ∞ (uncurry (spatialD 0 f))
    have hh : uncurry (spatialD 0 f) = JointCalculus.dAlong (0, Pi.single 0 1) (uncurry f) :=
      funext fun q => JointCalculus.spatialD_eq hf 0 q.1 q.2
    rw [hh]
    exact JointCalculus.contDiff_dAlong (0, Pi.single 0 1) hf
  · change ContDiff ℝ ∞ (uncurry (spatialD 1 f))
    have hh : uncurry (spatialD 1 f) = JointCalculus.dAlong (0, Pi.single 1 1) (uncurry f) :=
      funext fun q => JointCalculus.spatialD_eq hf 1 q.1 q.2
    rw [hh]
    exact JointCalculus.contDiff_dAlong (0, Pi.single 1 1) hf
  · exact contDiff_const

theorem slice_smooth {f : ScalarField 2} (hf : ContDiff ℝ ∞ (uncurry f)) (t : ℝ) :
    ContDiff ℝ ∞ (f t) :=
  hf.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun X : Coord 2 => (t, X)))

theorem second_D_lift_eq {f : ScalarField 2}
    (hf : ContDiff ℝ ∞ (uncurry f)) (i k : Fin 3) (t : ℝ) (x : Space) :
    D k (D i (fun y : Space => f t y.1)) x = horizontalD k (horizontalD i f) t x.1 := by
  have hh : D i (fun y : Space => f t y.1) = fun y => horizontalD i f t y.1 :=
    funext (D_lift_eq ((slice_smooth hf t).differentiable (by simp)) i)
  rw [hh]
  exact D_lift_eq ((slice_smooth (contDiff_horizontalD hf i) t).differentiable (by simp)) k x

theorem horizontalD_tails {f : ScalarField 2}
    (hf : ∀ i, TailSpace.ContinuousTails (spatialD i f)) (i : Fin 3) :
    TailSpace.ContinuousTails (horizontalD i f) := by
  fin_cases i
  · exact hf 0
  · exact hf 1
  · exact TailSpace.continuousTails_zero

theorem second_horizontalD_tails {f : ScalarField 2}
    (hf : ∀ i k, TailSpace.ContinuousTails (spatialD k (spatialD i f))) (i k : Fin 3) :
    TailSpace.ContinuousTails (horizontalD k (horizontalD i f)) := by
  fin_cases i
  · exact horizontalD_tails (hf 0) k
  · exact horizontalD_tails (hf 1) k
  · have hh : horizontalD k (horizontalD 2 f) = fun _ _ => 0 := by
      funext t X
      fin_cases k <;> simp [horizontalD, spatialD]
    change TailSpace.ContinuousTails (horizontalD k (horizontalD (2 : Fin 3) f))
    rw [hh]
    exact TailSpace.continuousTails_zero

theorem comparisonClass_lift_of_tails (v : ℝ → Coord 2 → Vect)
    (hs : ∀ i, ContDiff ℝ ∞ (uncurry (fun t X => v t X i)))
    (hv : ∀ i, TailSpace.C1Tails (fun t X => v t X i))
    (hD : ∀ i k, TailSpace.ContinuousTails (spatialD k (fun t X => v t X i)))
    (hDD : ∀ i k l, TailSpace.ContinuousTails (spatialD l (spatialD k (fun t X => v t X i)))) :
    ComparisonClass (fun t x => v t x.1) (fun _ _ => 0) := by
  have hs' (t : ℝ) (i : Fin 3) : Differentiable ℝ (fun X => v t X i) :=
    (slice_smooth (hs i) t).differentiable (by simp)
  have hd (i k : Fin 3) := horizontalD_tails (hD i) k
  have hdd (i k l : Fin 3) := second_horizontalD_tails (hDD i) k l
  have Df (i k : Fin 3) (t : ℝ) : D k (fun x : Space => v t x.1 i) =
      fun x => horizontalD k (fun t X => v t X i) t x.1 :=
    funext (D_lift_eq (f := fun t X => v t X i) (hs' t i) k)
  have DDf (i k l : Fin 3) (t : ℝ) : D l (D k (fun x : Space => v t x.1 i)) =
      fun x => horizontalD l (horizontalD k (fun t X => v t X i)) t x.1 :=
    funext (second_D_lift_eq (hs i) k l t)
  have Dz (k : Fin 3) : D k (fun _ : Space => (0 : ℝ)) = fun _ => 0 := by
    funext x
    simp [D, fderiv_const_apply]
  have pull : Continuous (fun q : ℝ × Space => (q.1, q.2.1)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hT
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i
        have hi : ContDiff ℝ 2 (fun X => v t X i) := (slice_smooth (hs i) t).of_le (by decide)
        exact hi.comp contDiff_fst
      · intro i X z
        rfl
      · intro i
        exact memLp_lift ((hv i).continuous.memLp t)
      · intro i k
        simpa only [Df i k t] using memLp_lift ((hd i k).memLp t)
      · intro i k l
        simpa only [DDf] using memLp_lift ((hdd i k l).memLp t)
    · intro i
      exact (hv i).continuous.cylinderL2 T
    · intro i k
      simpa only [Df] using (hd i k).cylinderL2 T
    · intro i k l
      simpa only [DDf] using (hdd i k l).cylinderL2 T
  · intro T hT
    choose G dG hc hdc hr hdr hder using fun i => (hv i).cylinderC1 T
    refine ⟨fun t i => G i t, fun t i => dG i t, hc, hdc, ?_, ?_, ?_⟩
    · intro t ht i
      exact hr i t ht
    · intro t ht i
      exact hdr i t ht
    · intro t ht i
      exact hder i t ht
  · intro T hT
    have hz : continuousL2On (fun _ _ => 0) T :=
      ⟨fun _ => 0, continuousOn_const, fun t ht => Lp.coeFn_zero ..⟩
    refine ⟨?_, hz, ?_⟩
    · intro t ht
      refine ⟨contDiff_const, fun _ _ => rfl, MemLp.zero, ?_⟩
      intro k
      rw [Dz]
      exact MemLp.zero
    · intro i
      simpa only [Dz] using hz
  · intro t ht x i
    have hh : Differentiable ℝ (fun s => v s x.1 i) :=
      ((hs i).comp (contDiff_id.prodMk contDiff_const :
        ContDiff ℝ ∞ (fun s : ℝ => (s, x.1)))).differentiable (by simp)
    exact (hh t).differentiableWithinAt.hasDerivWithinAt
  · intro T hT i
    exact ((hs i).continuous.comp pull).continuousOn
  · intro T hT i
    apply ((JointCalculus.contDiff_dAlong (1, 0) (hs i)).continuous.comp pull).continuousOn.congr
    intro q hq
    exact JointCalculus.timeD_eq (hs i) hq.1.1 q.2.1
  · intro T hT i k
    have hh := ((contDiff_horizontalD (hs i) k).continuous.comp pull).continuousOn (s := Icc 0 T ×ˢ univ)
    apply hh.congr
    intro q hq
    exact congrFun (Df i k q.1) q.2
  · intro T hT i k l
    have hh := ((contDiff_horizontalD (contDiff_horizontalD (hs i) k) l).continuous.comp pull).continuousOn (s := Icc 0 T ×ˢ univ)
    apply hh.congr
    intro q hq
    exact second_D_lift_eq (hs i) k l q.1 q.2
  · intro T hT
    exact continuousOn_const
  · intro T hT i
    simpa only [Dz] using
      (continuousOn_const : ContinuousOn (fun _ : ℝ × Space => (0 : ℝ)) (Icc 0 T ×ˢ univ))
  · intro T hT
    choose B hB hb using fun i => (hv i).continuous.bounded hT.le
    choose C hC hc using fun i k => (hd i k).bounded hT.le
    have hc0 (i : Fin 3) : 0 ≤ ∑ k, C i k := Finset.sum_nonneg fun k _ => hC i k
    have htotal (i : Fin 3) : B i + ∑ k, C i k ≤ ∑ j, (B j + ∑ k, C j k) :=
      Finset.single_le_sum (fun j _ => add_nonneg (hB j) (hc0 j)) (Finset.mem_univ i)
    refine ⟨∑ i, (B i + ∑ k, C i k),
      Finset.sum_nonneg (fun i _ => add_nonneg (hB i) (hc0 i)), ?_, ?_⟩
    · intro t ht x i
      exact (hb i t ht x.1).trans ((le_add_of_nonneg_right (hc0 i)).trans (htotal i))
    · intro t ht x i k
      rw [Df i k t]
      have hk : C i k ≤ ∑ j, C i j := Finset.single_le_sum (fun j _ => hC i j) (Finset.mem_univ k)
      exact (hc i k t ht x.1).trans (hk.trans ((le_add_of_nonneg_left (hB i)).trans (htotal i)))

end VelocityDetection.Cylinder
end

end OAI
