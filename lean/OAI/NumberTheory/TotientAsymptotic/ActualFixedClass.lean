import OAI.NumberTheory.TotientAsymptotic.CollisionKernelDomain
import OAI.NumberTheory.TotientAsymptotic.SuffixClassKernel

namespace OAI

/-! Applying the recovered Ford kernel to a fixed actual collision class. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

theorem actual_fixed_class_bound (hford : FordLemma51Input) :
    ∃ C y₀ : ℝ, 0 < C ∧ 1 < y₀ ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, i ≤ R x H → L x H < m x → R x H < L x H → ∀ t y : ℝ,
    y₀ ≤ y → 0 < B y → (87/100 : ℝ)*fordBandScale x i ≤ B y →
    B y ≤ 2*fordBandScale x i →
    ∀ (I : Finset ℕ) (D : ℕ) (v : Fin (canceledIndices i (collisionLastIndex x i) I).card → ℕ)
      (grid : Fin I.card → ℕ)
      (Q : Finset (TotientTuple (R x H) × TotientTuple (R x H))),
    (∀ q ∈ Q, GoodCollisionBlock x t H i y q) →
    (∀ q ∈ Q, collisionSurvivors q.1.head q.2.head (chosenRemainder x H q.1.tail)
      (chosenRemainder x H q.2.tail) i (collisionLastIndex x i)=I) →
    (∀ q ∈ Q, collisionResidual (chosenRemainder x H q.1.tail) i=D) →
    (∀ q ∈ Q, canceledPrimesAt x H i (collisionLastIndex x i) I q.1=v) →
    (∀ q ∈ Q, pairGridLabel (comparisonPairAt x H (collisionLastIndex x i) I q)
      y (collisionMesh x y i)=grid) →
    Set.InjOn (fun q : TotientTuple (R x H) × TotientTuple (R x H) => pairSuffix q i) (↑Q : Set _) →
    (Q.card : ℝ) ≤ y/(D*shiftedProduct v)/Real.log y*
      Real.exp (6*(|Real.log C|+26)*((m x-i : ℕ) : ℝ)^2-B y/(4*((m x-i : ℕ) : ℝ)^4)) := by
  obtain ⟨C,y₀,hC,hy₀,hclass⟩ := actual_comparison_class_kernel_injective hford
  refine ⟨C,y₀,hC,hy₀,?_⟩
  filter_upwards [actual_ford_data,collision_kernel_domain,eventually_collision_indices]
    with H hdata hdomain hind
  filter_upwards [hdata,hdomain,m_tendsto.eventually (eventually_ge_atTop H)] with x hd hdom hm
  intro i hi hL hR t y hy hBy hlo hup I D v grid Q hQ hI hD hv hg hdet
  have hy1 : 1 < y := hy₀.trans_le hy
  obtain ⟨hh,hlog,hn,hlogB,hK,hZ,hZu,hcut⟩ := hdom i hi hL hR y hy1 hBy hlo hup
  rcases Q.eq_empty_or_nonempty with hqe | ⟨q₀,hq₀⟩
  · rw [hqe]
    simp only [Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (div_nonneg (div_nonneg (zero_lt_one.trans hy1).le (by positivity))
      (by linarith)) (Real.exp_pos _).le
  let k := collisionLastIndex x i
  let δ := collisionMesh x y i
  let Z := fordBandScale x k
  let Y := comparisonCutoffs y (pairedGridUpper δ ((7/10 : ℝ)*Z/B y) grid)
  let U := comparisonCutoffs y (pairedGridLower δ grid)
  have hdataq (q) (hq : q ∈ Q) :
      FordComparisonParameters I.card y (normalityScale x i) D (shiftedProduct v) Y U ∧
      FordComparisonConditions I.card y (normalityScale x i) D (shiftedProduct v) Y U
        (comparisonPairAt x H k I q) ∧
      (-2+(∑ j ∈ Finset.Icc 1 (I.card-1), a j*(B (Y j)/B y))+
        comparisonError I.card y (normalityScale x i) Y U ≤ -1-1/(2*((m x-i : ℕ) : ℝ)^4)) := by
    have hdq := hd i hi hL hR t y hy1 hBy hlo hup q (hQ q hq)
    dsimp only at hdq
    rw [hI q hq] at hdq
    have hr : collisionCanceledProduct q.1.head q.2.head (chosenRemainder x H q.1.tail)
        (chosenRemainder x H q.2.tail) i k=shiftedProduct v := by
      rw [← canceledPrimesAt_product q.1 q.2 I (hI q hq),hv q hq]
    change collisionCanceledProduct q.1.head q.2.head (chosenRemainder x H q.1.tail)
      (chosenRemainder x H q.2.tail) i (collisionLastIndex x i)=shiftedProduct v at hr
    simp only [pairUpperCoordinates,pairLowerCoordinates,hg q hq,hD q hq,hr] at hdq
    exact hdq.2
  obtain ⟨hp,hc,he⟩ := hdataq q₀ hq₀
  have hb : 0 < I.card := hp.1
  have hbc : I.card ≤ m x-i := by
    have hsub : I ⊆ Finset.Icc i k := by
      rw [← hI q₀ hq₀]
      exact Finset.filter_subset _ _
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have hcalc : k+1-i=collisionCutoff (m x-i)+1 := by dsimp [k,collisionLastIndex]; omega
    rw [hcalc] at hcard
    exact hcard.trans hcut
  have hY : B (Y I.card)=(7/10 : ℝ)*Z := normalized_grid_bottom grid hb hBy.ne'
  have hDf := (good_residual_omega_floor hi (hQ q₀ hq₀)).1
  rw [hD q₀ hq₀] at hDf
  have hDreal : (D.primeFactorsList.length : ℝ) ≤ 2*B y/((m x-i : ℕ) : ℝ)^8 :=
    (show (D.primeFactorsList.length : ℝ) ≤ ⌊fordBandScale x i/((m x-i : ℕ) : ℝ)^8⌋₊ by exact_mod_cast hDf).trans hK
  have hinj : Set.InjOn (comparisonEncoding x H k I) (↑Q : Set _) := by
    apply comparisonEncoding_injOn_of_suffix I Q hL (hind x hm i hi).2.2 hi
      (fun q hq => ⟨(hQ q hq).left.1,(hQ q hq).right.1⟩) hdet
      (fun j => let a := (if h : j ∈ canceledIndices i k I then v (((canceledIndices i k I).orderIsoOfFin rfl).symm ⟨j,h⟩) else 1); (a,a))
    intro q hq j hj hjI
    exact fixed_canceled_coordinates I q v (hI q hq) (hv q hq) j hj hjI
  apply hclass I Y U hy hlog hBy hh hn (by exact_mod_cast hbc) hlogB hDreal hK
    (comparison_cutoff_one_lt _ _ _) (by rw [hY]; positivity) (by rw [hY]; exact hZu)
    hp he hL hR (hind x hm i hi).2.2 Q (fun q hq => ⟨(hQ q hq).left.1,(hQ q hq).right.1⟩) hinj
  · exact hD
  · intro q hq
    exact (good_residual_omega_floor hi (hQ q hq)).2
  · exact fun q hq => (hdataq q hq).2.1

end TotientAsymptotic

end

end OAI
