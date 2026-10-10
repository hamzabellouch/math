import OAI.NumberTheory.DukePrimeDegree.Geometry.CountableCutNeighborhoods
import OAI.NumberTheory.DukePrimeDegree.Geometry.ExponentialCutFamily
import OAI.NumberTheory.DukePrimeDegree.Entropy.UpperRootCutItineraries

namespace OAI

/-! # Controlled countable observations with upper-root future neighborhoods

The chosen distance cuts have exponentially controlled cardinalities and
boundary constants. Their countable height-selected observation has
small lifts and is constant on an upper-root neighborhood in almost
every whole-future fiber.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_controlled_root_future_observation (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (B : ℝ) (hB : 0 < B) (H : X (d+1) → ℕ) (hH : Measurable H)
    (t : ℕ → ℝ)
    (ht : ∀ m, t m ≤ 2*B*(m:ℝ)+B)
    (hlevel : ∀ x m, H x ≤ m ↔
      quotientLogDistance (Quotient.mk _ (1 : G (d+1))) x ≤ t m)
    (hstep : ∀ x, H (rightAction x (diagonalOneParameter ell hell (-1))) ≤ H x+1)
    (hnull : ∀ m, μ {x | quotientLogDistance (Quotient.mk _ (1 : G (d+1))) x=t m}=0)
    {D₀ : ℝ} (hD₀ : 0 ≤ D₀)
    (hbound : ∀ m k, μ (realBoundaryStrip
      (quotientLogDistance (Quotient.mk _ (1 : G (d+1)))) (t m) ((1/4:ℝ)^k)) ≤
        ENNReal.ofReal (D₀*(1/2:ℝ)^k))
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1) :
    ∃ Q : X (d+1) → ℕ, Measurable Q ∧
      (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
      (∀ x y, Q y=Q x → H y=H x ∧
        ∃ g ∈ matrixBall (d+1) (r₀*Real.exp (-(4*B)*(H x:ℝ))), rightAction x g=y) ∧
      ∀ᵐ x ∂μ, ∀ᶠ s in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
        Q ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k]
          (rightAction x ((completeRootChain (d+1)).word s))) =
        Q ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k] x) := by
  classical
  let T : X (d+1) → X (d+1) := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    change μ.map (fun x => rightAction x (diagonalOneParameter ell hell (-1)))=μ
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  let r := fun m : ℕ => r₀*Real.exp (-(4*B)*(m:ℝ))
  let τ := fun m => Real.log (1+r m)
  have hτ (m : ℕ) : 0 < τ m := by
    have hr : 0 < r m := by dsimp [r]; positivity
    exact Real.log_pos (by linarith)
  obtain ⟨N,z,c,K,C,hK,hC,hfamily⟩ := exists_exponential_distance_cut_family
    (Nat.succ_pos d) μ (A := 2*B) (B := 4*B) (R₀ := B)
    (by positivity) (by positivity) hB.le hr₀ hr₀1
  let f : ∀ m, Fin (N m) → X (d+1) → ℝ := fun m i => quotientLogDistance (z m i)
  let P := fun m => finiteCutCode (f m) (c m)
  let Q := layeredObservation H P
  have hP (m : ℕ) : Measurable (P m) :=
    finiteCutCode_measurable (fun i => (continuous_quotientLogDistance (d+1) _).measurable) _
  refine ⟨Q,layeredObservation_measurable hH hP,layeredObservation_finite_levels H P,?_,?_⟩
  · intro x y hxy
    have he := layeredObservation_eq H P hxy
    refine ⟨he.1,?_⟩
    have hx : quotientLogDistance (Quotient.mk _ (1 : G (d+1))) x ≤ 2*B*(H x:ℝ)+B :=
      ((hlevel x (H x)).mp le_rfl).trans (ht (H x))
    obtain ⟨i,hi⟩ := (hfamily (H x)).2.2.1 x hx
    have hy := (finiteCutCode_eq_imp_iff (f (H x)) (c (H x)) he.2 i).mpr hi
    exact (hfamily (H x)).2.2.2 i x hi y hy
  · have hneigh := ae_layered_cut_future_neighborhoods (V := UpperRootTime (d+1)) μ hT
      (continuous_rightAction _) H hH hstep
      (quotientLogDistance (Quotient.mk _ (1 : G (d+1))))
      (continuous_quotientLogDistance (d+1) _) t hlevel hnull
      hD₀ hbound N f
      (fun m i => continuous_quotientLogDistance (d+1) _) c
      (fun m i => ((hfamily m).2.1 i).2.2.1)
      (fun m => 48/τ m) (fun m => div_nonneg (by norm_num) (hτ m).le)
      (fun m i k => ((hfamily m).2.1 i).2.2.2 k) hC hK.le (fun m => (hfamily m).1)
    filter_upwards [hneigh] with x hx
    let F : UpperRootTime (d+1) → X (d+1) :=
      fun s => rightAction x ((completeRootChain (d+1)).word s)
    have hbase : F (completeRootChain (d+1)).zeroTime=x := by
      simp only [F,EliminationChain.word_zeroTime,rightAction_one]
    have hF : ContinuousAt F (completeRootChain (d+1)).zeroTime :=
      ((continuous_rightOrbit (d+1) x).comp (upperRootWord_isEmbedding (d+1)).continuous).continuousAt
    let R : ℝ := 1/(6*(d+1:ℝ))
    have hR : 0 < R := by dsimp [R]; positivity
    have hsmall : 3*(d+1:ℝ)*R ≤ 1 := by
      dsimp [R]
      have hn : (d+1:ℝ) ≠ 0 := by positivity
      field_simp
      nlinarith
    have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have he (k : ℕ) : Real.exp (-Real.log 4*(k:ℝ))=(1/4:ℝ)^k := by
      rw [mul_comm (-Real.log 4) (k:ℝ),Real.exp_nat_mul,
        Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<4)]
      simp only [one_div]
    have hc (w : X (d+1)) (k : ℕ) (s : UpperRootTime (d+1))
        (hs : s ∈ (completeRootChain (d+1)).cube R) :
        |quotientLogDistance w (T^[k] (F s))-quotientLogDistance w (T^[k] x)| ≤ (1/4:ℝ)^k := by
      exact (quotientLogDistance_upperRoot_iterate_bound ell hell (Real.log 4)
        hlog hgap hR hsmall w x k hs).trans_eq (he k)
    exact hx F (completeRootChain (d+1)).zeroTime hbase hF _
      (((completeRootChain (d+1)).cube_open R).mem_nhds
        ((completeRootChain (d+1)).zeroTime_mem_cube hR))
      (fun k s hs => hc _ k s hs) (fun k m i s hs => hc _ k s hs)

end DukePrimeDegree

end

end OAI
