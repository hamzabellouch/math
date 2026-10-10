import OAI.NumberTheory.DukePrimeDegree.Geometry.FirstCoverCode
import OAI.NumberTheory.DukePrimeDegree.Geometry.CountableCutNeighborhoods
import OAI.NumberTheory.DukePrimeDegree.Geometry.ExponentialCutFamily
import OAI.NumberTheory.DukePrimeDegree.Entropy.UpperRootCutItineraries
import OAI.NumberTheory.DukePrimeDegree.Geometry.SeparatedCutFamily
import OAI.NumberTheory.DukePrimeDegree.Entropy.LayeredCoverPredecessors
import OAI.NumberTheory.DukePrimeDegree.Entropy.ExponentialPredecessorScales

namespace OAI

/-! # A future observation with uniformly finite predecessor sets

The same distance cuts give future neighborhoods and a finite branching
bound. The chart radius is chosen small enough for uniform local packing.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_branching_cover_future_observation (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (B : ℝ) (hB : 0 < B) (H : X (d+1) → ℕ) (hH : Measurable H)
    (t : ℕ → ℝ)
    (ht : ∀ m, t m ≤ 2*B*(m:ℝ)+B)
    (hlevel : ∀ x m, H x ≤ m ↔
      quotientLogDistance (Quotient.mk _ (1 : G (d+1))) x ≤ t m)
    (hstep : ∀ x, H (rightAction x (diagonalOneParameter ell hell (-1))) ≤ H x+1 ∧
      H x ≤ H (rightAction x (diagonalOneParameter ell hell (-1)))+1)
    (hnull : ∀ m, μ {x | quotientLogDistance (Quotient.mk _ (1 : G (d+1))) x=t m}=0)
    {D₀ : ℝ} (hD₀ : 0 ≤ D₀)
    (hbound : ∀ m k, μ (realBoundaryStrip
      (quotientLogDistance (Quotient.mk _ (1 : G (d+1)))) (t m) ((1/4:ℝ)^k)) ≤
        ENNReal.ofReal (D₀*(1/2:ℝ)^k))
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1)
    (hpack : ((d+1:ℕ):ℝ)*predecessorPackingRadius (d+1)
      (diagonalOneParameter ell hell (-1)) (16*Real.exp (4*B)) 16*r₀ ≤ 4) :
    ∃ Q : X (d+1) → ℕ, Measurable Q ∧
      (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
      (∀ x y, Q y=Q x → H y=H x ∧
        ∃ g ∈ matrixBall (d+1) (r₀*Real.exp (-(4*B)*(H x:ℝ))), rightAction x g=y) ∧
      (∀ᵐ x ∂μ, ∀ᶠ s in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
        Q ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k]
          (rightAction x ((completeRootChain (d+1)).word s))) =
        Q ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k] x)) ∧
      UniformFinitePredecessors
        (fun x => rightAction x (diagonalOneParameter ell hell (-1))) Q ∧
      ∃ (J : ℕ → ℕ) (K C : ℝ), 0 < K ∧ 0 ≤ C ∧
        (∀ m, (J m : ℝ) ≤ K*Real.exp (C*(m:ℝ))) ∧
        ∀ m, Q '' {x | H x=m} ⊆ (Nat.pair m) '' Set.Iio (J m) := by
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
  obtain ⟨N,z,c,K,C,hK,hC,hfamily⟩ := exists_separated_exponential_cut_family
    (Nat.succ_pos d) μ (A := 2*B) (B := 4*B) (R₀ := B)
    (by positivity) (by positivity) hB.le hr₀ hr₀1
  let f : ∀ m, Fin (N m) → X (d+1) → ℝ := fun m i => quotientLogDistance (z m i)
  let P := fun m => firstCoverCode (f m) (c m)
  let Q := layeredObservation H P
  have hP (m : ℕ) : Measurable (P m) :=
    firstCoverCode_measurable (fun i => (continuous_quotientLogDistance (d+1) _).measurable) _
  refine ⟨Q,layeredObservation_measurable hH hP,layeredObservation_finite_levels H P,?_,?_,?_,?_⟩
  · intro x y hxy
    have he := layeredObservation_eq H P hxy
    refine ⟨he.1,?_⟩
    have hx : quotientLogDistance (Quotient.mk _ (1 : G (d+1))) x ≤ 2*B*(H x:ℝ)+B :=
      ((hlevel x (H x)).mp le_rfl).trans (ht (H x))
    obtain ⟨i,hy,hi⟩ := firstCoverCode_common (f (H x)) (c (H x))
      ((hfamily (H x)).2.2.2.1 x hx) he.2
    exact (hfamily (H x)).2.2.2.2 i x hi y hy
  · have hneigh := ae_layered_cut_future_neighborhoods (V := UpperRootTime (d+1)) μ hT
      (continuous_rightAction _) H hH (fun x => (hstep x).1)
      (quotientLogDistance (Quotient.mk _ (1 : G (d+1))))
      (continuous_quotientLogDistance (d+1) _) t hlevel hnull
      hD₀ hbound N f
      (fun m i => continuous_quotientLogDistance (d+1) _) c
      (fun m i => ((hfamily m).2.2.1 i).2.2.1)
      (fun m => 48/τ m) (fun m => div_nonneg (by norm_num) (hτ m).le)
      (fun m i k => ((hfamily m).2.2.1 i).2.2.2 k) hC hK.le (fun m => (hfamily m).1)
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
    have hn := hx F (completeRootChain (d+1)).zeroTime hbase hF _
      (((completeRootChain (d+1)).cube_open R).mem_nhds
        ((completeRootChain (d+1)).zeroTime_mem_cube hR))
      (fun k s hs => hc _ k s hs) (fun k m i s hs => hc _ k s hs)
    filter_upwards [hn] with s hs
    intro k
    exact layered_firstCover_eq_of_cutCode_eq H f c (hs k)

  · have hsc (m : ℕ) := exponential_cover_scale_bounds hr₀ hr₀1
      (show 0 ≤ 4*B by positivity) m
    have hKP : 0 ≤ predecessorPackingRadius (d+1)
        (diagonalOneParameter ell hell (-1)) (16*Real.exp (4*B)) 16 := by
      dsimp [predecessorPackingRadius]
      positivity
    apply layered_cover_uniform_predecessors (Nat.succ_pos d)
      (diagonalOneParameter ell hell (-1)) H N z c r (fun m => τ m/8)
      (by positivity) (by norm_num) (fun m => (hsc m).2.2.1)
      (fun m => (hsc m).2.2.2.1.trans (by linarith))
      (fun m => exponential_cover_smallness hr₀ hr₀1 (by positivity) hKP hpack m)
      hstep (fun m => (hsc m).2.2.2.2) ?_ ?_ ?_ ?_ ?_
    · intro x
      exact exponential_cover_image_radius hr₀ hr₀1 (by positivity) (hstep x).2
    · intro m i j hij
      exact ((hfamily m).2.1 i j hij).le
    · intro m i
      have hh := ((hfamily m).2.2.1 i).1
      exact lt_trans (by have := hτ m; positivity) hh
    · intro m x hx
      apply (hfamily m).2.2.2.1 x
      have hh := ((hlevel x m).mp (by omega)).trans (ht m)
      exact hh
    · exact fun m => (hfamily m).2.2.2.2
  · refine ⟨fun m => N m+1,K+1,C,by linarith,hC,?_,?_⟩
    · intro m
      have hr : 0 < r m := by dsimp [r]; positivity
      have hrle : r m ≤ 1 := by
        dsimp [r]
        have he : Real.exp (-(4*B)*(m:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by
          nlinarith [mul_nonneg hB.le (Nat.cast_nonneg (α := ℝ) m)])
        exact (mul_le_mul_of_nonneg_left he hr₀.le).trans (by simpa using hr₀1)
      have hlog : τ m ≤ 1 := by
        have hh := Real.log_le_sub_one_of_pos (show 0 < 1+r m by linarith)
        dsimp [τ]
        linarith
      have hfactor : 1 ≤ 48/τ m := (le_div_iff₀ (hτ m)).mpr (by linarith)
      have hb := (hfamily m).1
      change (N m:ℝ≥0∞)*ENNReal.ofReal (48/τ m) ≤
        ENNReal.ofReal (K*Real.exp (C*(m:ℝ))) at hb
      have hraw := ENNReal.toReal_mono (by finiteness) hb
      have hd : 0 ≤ (48/τ m:ℝ) := div_nonneg (by norm_num) (hτ m).le
      have hk : 0 ≤ K*Real.exp (C*(m:ℝ)) := mul_nonneg hK.le (Real.exp_pos _).le
      rw [ENNReal.toReal_mul,ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal hd,ENNReal.toReal_ofReal hk] at hraw
      have hn : (N m:ℝ) ≤ K*Real.exp (C*(m:ℝ)) :=
        (le_mul_of_one_le_right (Nat.cast_nonneg _) hfactor).trans hraw
      have he : 1 ≤ Real.exp (C*(m:ℝ)) :=
        Real.one_le_exp_iff.mpr (mul_nonneg hC (Nat.cast_nonneg _))
      push_cast
      nlinarith
    · intro m q hq
      obtain ⟨x,hx,rfl⟩ := hq
      change H x=m at hx
      refine ⟨(P m x).val,(P m x).isLt,?_⟩
      dsimp [Q,layeredObservation]
      rw [hx]

end DukePrimeDegree

end

end OAI
