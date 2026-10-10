import OAI.NumberTheory.TotientAsymptotic.ActualFixedClass
import OAI.NumberTheory.TotientAsymptotic.ComparisonClassSum
import OAI.NumberTheory.TotientAsymptotic.CollisionChoiceBounds

namespace OAI

/-! Summing all grids, canceled primes, and residuals for fixed survivors. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

theorem actual_survivor_class_sum (hford : FordLemma51Input) (hmertens : MertensProductInput) :
    ∃ C M y₀ : ℝ, 0 < C ∧ 0 < M ∧ 1 < y₀ ∧
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, i ≤ R x H → L x H < m x → R x H < L x H → ∀ t y : ℝ,
    y₀ ≤ y → 0 < B y → (87/100 : ℝ)*fordBandScale x i ≤ B y → B y ≤ 2*fordBandScale x i →
    ∀ (I : Finset ℕ) (Nz Np : ℕ),
    2 ≤ Nz → 2 ≤ Np → collisionSmoothCutoff x i ≤ Nz → y+1 ≤ Np →
    ∀ Q : Finset (TotientTuple (R x H) × TotientTuple (R x H)),
    (∀ q ∈ Q, GoodCollisionBlock x t H i y q) →
    (∀ q ∈ Q, collisionSurvivors q.1.head q.2.head (chosenRemainder x H q.1.tail)
      (chosenRemainder x H q.2.tail) i (collisionLastIndex x i)=I) →
    Set.InjOn (fun q : TotientTuple (R x H) × TotientTuple (R x H) => pairSuffix q i) (↑Q : Set _) →
    (Q.card : ℝ) ≤ y/Real.log y*
      Real.exp (6*(|Real.log C|+26)*((m x-i : ℕ) : ℝ)^2-B y/(4*((m x-i : ℕ) : ℝ)^4))*
      ((collisionGridFamilies (collisionMesh x y i) I.card).card : ℝ)*(M*Real.log Nz)*
      (2*(Real.log M+B Np))^(canceledIndices i (collisionLastIndex x i) I).card := by
  obtain ⟨C,y₀,hC,hy₀,hfixed⟩ := actual_fixed_class_bound hford
  obtain ⟨M,hM,hsum⟩ := comparison_class_sum_mertens hmertens
  refine ⟨C,M,y₀,hC,hM,hy₀,?_⟩
  filter_upwards [hfixed,actual_ford_data,collision_residual_below_cutoff,eventually_collision_indices]
    with H hfixed hdata hres hind
  filter_upwards [hfixed,hdata,hres,m_tendsto.eventually (eventually_ge_atTop H)]
    with x hf hd hr hm
  intro i hi hL hR t y hy hBy hlo hup I Nz Np hNz hNp hzN hyN Q hQ hI hdet
  let k := collisionLastIndex x i
  let c := (canceledIndices i k I).card
  let d := fun q : TotientTuple (R x H) × TotientTuple (R x H) =>
    collisionResidual (chosenRemainder x H q.1.tail) i
  let p := fun q : TotientTuple (R x H) × TotientTuple (R x H) => canceledPrimesAt x H i k I q.1
  let g := fun q : TotientTuple (R x H) × TotientTuple (R x H) =>
    pairGridLabel (comparisonPairAt x H k I q) y (collisionMesh x y i)
  let G := collisionGridFamilies (collisionMesh x y i) I.card
  let A := y/Real.log y*Real.exp
    (6*(|Real.log C|+26)*((m x-i : ℕ) : ℝ)^2-B y/(4*((m x-i : ℕ) : ℝ)^4))
  have hy1 : 1 < y := hy₀.trans_le hy
  apply hsum Q (Q.image d) G c Nz Np d p g A hNz hNp
    (mul_nonneg (div_nonneg (zero_lt_one.trans hy1).le (Real.log_pos hy1).le) (Real.exp_pos _).le)
  · intro a ha
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
    have hη := (chosenRemainder_spec (hQ q hq).left.1.2.2.1).1
    refine ⟨Nat.totient_pos.mpr (suffixPreimage_pos hη),?_⟩
    have hsm := (hr i hi _ hη).le.trans hzN
    exact_mod_cast hsm
  · exact fun q hq => Finset.mem_image.mpr ⟨q,hq,rfl⟩
  · intro q hq j
    have hp := canceledPrimesAt_prime_bound (hQ q hq) I (hind x hm i hi).2.2.le j
    exact ⟨hp.1,by exact_mod_cast hp.2.trans hyN⟩
  · intro q hq
    have hh := hd i hi hL hR t y hy1 hBy hlo hup q (hQ q hq)
    dsimp only at hh
    rw [hI q hq] at hh
    exact hh.1
  · intro a _ v _ z _
    let F := Q.filter (fun q => (d q,p q,g q)=(a,v,z))
    have hmem (q) (hq : q ∈ F) := (Finset.mem_filter.mp hq).1
    have heq (q) (hq : q ∈ F) := (Finset.mem_filter.mp hq).2
    have hc := hf i hi hL hR t y hy hBy hlo hup I a v z F
      (fun q hq => hQ q (hmem q hq)) (fun q hq => hI q (hmem q hq))
      (fun q hq => congrArg Prod.fst (heq q hq))
      (fun q hq => congrArg (fun w => w.2.1) (heq q hq))
      (fun q hq => congrArg (fun w => w.2.2) (heq q hq))
      (fun q hq q' hq' he => hdet (hmem q hq) (hmem q' hq') he)
    apply hc.trans_eq
    dsimp only [A]
    rw [shiftedProduct,Nat.cast_prod]
    simp only [div_eq_mul_inv,mul_inv_rev]
    rw [Finset.prod_inv_distrib]
    ring

end TotientAsymptotic

end

end OAI
