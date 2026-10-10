import OAI.Probability.DilutedSpin.ActualPrefix
import OAI.Probability.DilutedSpin.FinitePiInjective
import OAI.Probability.DilutedSpin.HeterogeneousFullVariance

namespace OAI

section
section
namespace DilutedSpinGlass.PhysicalRoot
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N : ℕ}

/-- Literal physical spin weight, with the independent physical root inputs
kept as a recursive product only for the variance calculation. -/
noncomputable def energy (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (h : RootPath Y N) (k : ℕ) (x : RootPath X k) (σ : Fin N → Spin) : ℝ :=
  (∑ j, V (rootArray k x j) σ)+∑ i, field (rootArray N h i)*spin (σ i)

/-- The interaction label includes the p uniform indices, with repetitions. -/
noncomputable def interactionValue {p : ℕ}
    (z : InteractionSample p × (Fin p → Fin N)) (σ : Fin N → Spin) : ℝ :=
  z.1.1 (fun l => σ (z.2 l))

theorem energy_eq_logWeight {p : ℕ} (h : RootPath ℝ N) (k : ℕ)
    (x : RootPath (InteractionSample p × (Fin p → Fin N)) k) (σ : Fin N → Spin) :
    energy interactionValue id h k x σ =
      logWeight (fun j => (rootArray k x j).1) (rootArray N h)
        (fun j => (rootArray k x j).2) σ := rfl

theorem measurable_interactionValue {p : ℕ} (σ : Fin N → Spin) :
    Measurable (fun z : InteractionSample p × (Fin p → Fin N) => interactionValue z σ) := by
  apply measurable_from_prod_countable_left
  intro inds
  exact (measurable_pi_apply (fun l => σ (inds l))).comp measurable_fst

theorem interactionValue_bound {p : ℕ} (z : InteractionSample p × (Fin p → Fin N))
    (σ : Fin N → Spin) : |interactionValue z σ| ≤ ‖z.1.1‖ := by
  simpa only [interactionValue,Real.norm_eq_abs] using norm_le_pi_norm z.1.1 (fun l => σ (z.2 l))

theorem sum_update_difference {Z : Type*} {n : ℕ} (g : Fin n → Z → ℝ)
    (x : Fin n → Z) (q : Fin n) (z : Z) :
    (∑ j, g j (x j))-(∑ j, g j (Function.update x q z j)) = g q (x q)-g q z := by
  classical
  rw [← Finset.sum_sub_distrib,Finset.sum_eq_single q]
  · simp only [Function.update_self]
  · intro j _ hj
    simp only [Function.update_of_ne hj,sub_self]
  · simp

theorem measurable_energy (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (hV : ∀ σ, Measurable (fun x => V x σ)) (hh : Measurable field)
    (k : ℕ) (σ : Fin N → Spin) :
    Measurable (fun z : RootPath Y N × RootPath X k => energy V field z.1 k z.2 σ) := by
  apply Measurable.add
  · exact Finset.measurable_sum _ (fun j _ => (hV σ).comp ((measurable_rootArray k j).comp measurable_snd))
  · exact Finset.measurable_sum _ (fun i _ =>
      ((hh.comp ((measurable_rootArray N i).comp measurable_fst))).mul_const _)

theorem abs_spin (s : Spin) : |spin s| = 1 := by
  cases s <;> norm_num [spin]

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem energy_bound (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    {C H : ℝ} (hV : ∀ x σ, |V x σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (h : RootPath Y N) (k : ℕ) (x : RootPath X k) (σ : Fin N → Spin) :
    |energy V field h k x σ| ≤ H*N+C*k := by
  apply (abs_add_le _ _).trans
  have hx := (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) => hV (rootArray k x j) σ))
  have hy : |∑ i, field (rootArray N h i)*spin (σ i)| ≤ H*N := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i : Fin N, H := Finset.sum_le_sum (fun i _ => by
        simpa only [abs_mul,abs_spin,mul_one] using hh (rootArray N h i))
      _ = H*N := by simp [mul_comm]
  have hx' : |∑ j, V (rootArray k x j) σ| ≤ C*k := by simpa [mul_comm] using hx
  linarith

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem energy_replace_interaction (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    {C : ℝ} (hV : ∀ x σ, |V x σ| ≤ C) (h : RootPath Y N)
    (k : ℕ) (q : Fin k) (x : RootPath X k) (z : X) (σ : Fin N → Spin) :
    |energy V field h k x σ-energy V field h k (replaceRoot k x q z) σ| ≤ 2*C := by
  simp only [energy,add_sub_add_right_eq_sub,rootArray_replace]
  rw [sum_update_difference (fun _ v => V v σ) (rootArray k x) q z]
  exact (abs_sub _ _).trans (by linarith [hV (rootArray k x q) σ,hV z σ])

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem energy_add_interaction (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    {C : ℝ} (hV : ∀ x σ, |V x σ| ≤ C) (h : RootPath Y N)
    (k : ℕ) (z : X) (x : RootPath X k) (σ : Fin N → Spin) :
    |energy V field h (k+1) (z,x) σ-energy V field h k x σ| ≤ C := by
  simpa only [energy,add_sub_add_right_eq_sub,rootArray,Fin.sum_univ_succ,
    Fin.cons_zero,Fin.cons_succ,add_sub_cancel_right] using hV z σ

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem energy_replace_field (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    {H : ℝ} (hh : ∀ y, |field y| ≤ H) (h : RootPath Y N) (q : Fin N) (z : Y)
    (k : ℕ) (x : RootPath X k) (σ : Fin N → Spin) :
    |energy V field h k x σ-energy V field (replaceRoot N h q z) k x σ| ≤ 2*H := by
  simp only [energy,add_sub_add_left_eq_sub,rootArray_replace]
  rw [sum_update_difference (fun i v => field v*spin (σ i)) (rootArray N h) q z,
    ← sub_mul,abs_mul,abs_spin,mul_one]
  exact (abs_sub _ _).trans (by linarith [hh (rootArray N h q),hh z])

end DilutedSpinGlass.PhysicalRoot
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

lemma uniform_equiv (e : Ω ≃ Ω) (F : Ω → ℝ) :
    (uniform : FiniteLaw Ω).expect (fun x => F (e x)) = (uniform : FiniteLaw Ω).expect F := by
  unfold expect uniform
  exact Equiv.sum_comp e (fun x => (Fintype.card Ω:ℝ)⁻¹*F x)

omit [Nonempty Ω] in
lemma expect_fourthRoot_le (P : FiniteLaw Ω) (F : Ω → ℝ) (hF : ∀ x, 0 ≤ F x) :
    P.expect (fun x => Real.sqrt (Real.sqrt (F x))) ≤ Real.sqrt (Real.sqrt (P.expect F)) :=
  (expect_sqrt_le P (fun x => Real.sqrt (F x)) (fun _ => Real.sqrt_nonneg _)).trans
    (Real.sqrt_le_sqrt (expect_sqrt_le P F hF))

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  {L : ℕ} [NeZero L]

 
noncomputable def depthLaw (α : Type) [Fintype α] [DecidableEq α] (L : ℕ) [NeZero L] :
    FiniteLaw (α → Fin L) := FiniteLaw.pi (fun _ : α => FiniteLaw.uniform)

noncomputable def average (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ) : ℝ :=
  (depthLaw α L).expect (fun q => if D q then F q else 0)

lemma average_eq (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ) :
    average D F = (∑ q ∈ Finset.univ.filter D, F q)/(L:ℝ)^(Fintype.card α) := by
  classical
  unfold average depthLaw FiniteLaw.expect FiniteLaw.pi FiniteLaw.uniform
  simp only [Fintype.card_fin,Finset.prod_const,Finset.card_univ]
  rw [← Finset.mul_sum,← Finset.sum_filter]
  rw [inv_pow,div_eq_mul_inv,mul_comm]

noncomputable def coordinateProjection (e : β → α) (τ : β → Equiv.Perm (Fin L))
    (q : α → Fin L) : β → Fin L := fun i => τ i (q (e i))

lemma depthLaw_projection (e : β → α) (he : Function.Injective e)
    (τ : β → Equiv.Perm (Fin L)) (F : (β → Fin L) → ℝ) :
    (depthLaw α L).expect (fun q => F (coordinateProjection e τ q)) = (depthLaw β L).expect F := by
  unfold depthLaw coordinateProjection
  rw [FiniteLaw.expect_pi_injective (fun _ : α => (FiniteLaw.uniform : FiniteLaw (Fin L))) e he
    (fun q : β → Fin L => F (fun i => τ i (q i)))]
  have h := FiniteLaw.expect_pi_weighted_map
    (fun _ : β => (FiniteLaw.uniform : FiniteLaw (Fin L)))
    (fun _ : β => (FiniteLaw.uniform : FiniteLaw (Fin L)))
    (fun i => τ i) (fun _ _ => 1) (fun _ _ => 1)
    (fun i g => by simpa only [one_mul] using FiniteLaw.uniform_equiv (τ i) g) F
  simpa only [Finset.prod_const_one,mul_one] using h

/-- Exact fiber comparison with normalized unused coordinates. The retained
coordinates may independently be shifted by any permutation. -/
theorem fiber_bound (e : β → α) (he : Function.Injective e)
    (τ : β → Equiv.Perm (Fin L)) (D : (α → Fin L) → Prop) (E : (β → Fin L) → Prop)
    (hDE : ∀ q, D q → E (coordinateProjection e τ q)) (F : (β → Fin L) → ℝ)
    (hF : ∀ q, 0 ≤ F q) : average D (fun q => F (coordinateProjection e τ q)) ≤ average E F := by
  calc
    _ ≤ (depthLaw α L).expect (fun q =>
        if E (coordinateProjection e τ q) then F (coordinateProjection e τ q) else 0) := by
      apply FiniteLaw.expect_mono
      intro q
      by_cases hd : D q
      · rw [ite_eq_left hd,ite_eq_left (hDE q hd)]
      · rw [ite_eq_right hd]
        split_ifs
        · exact hF _
        · exact le_rfl
    _ = _ := depthLaw_projection e he τ (fun y => if E y then F y else 0)

/-- The fourth-root form of decor:fiber-bound, with no diagonal restriction
of independently sampled aligned copies and no volume-ratio loss. -/
theorem fiber_fourthRoot_bound (e : β → α) (he : Function.Injective e)
    (τ : β → Equiv.Perm (Fin L)) (D : (α → Fin L) → Prop) (E : (β → Fin L) → Prop)
    (hDE : ∀ q, D q → E (coordinateProjection e τ q)) (F : (β → Fin L) → ℝ)
    (hF : ∀ q, 0 ≤ F q) :
    average D (fun q => Real.sqrt (Real.sqrt (F (coordinateProjection e τ q)))) ≤
      Real.sqrt (Real.sqrt (average E F)) := by
  apply (fiber_bound e he τ D E hDE (fun q => Real.sqrt (Real.sqrt (F q)))
    (fun _ => Real.sqrt_nonneg _)).trans
  have h := FiniteLaw.expect_fourthRoot_le (depthLaw β L) (fun q => if E q then F q else 0)
    (fun q => by
      split_ifs
      · exact hF _
      · exact le_rfl)
  have he : (fun q => Real.sqrt (Real.sqrt (if E q then F q else 0))) =
      (fun q => if E q then Real.sqrt (Real.sqrt (F q)) else 0) := by
    funext q
    split_ifs <;> simp
  rw [he] at h
  exact h

end DilutedSpinGlass.DepthAverage
end

end

end OAI
