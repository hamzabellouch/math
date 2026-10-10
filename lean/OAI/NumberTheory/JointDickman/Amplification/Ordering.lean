import OAI.NumberTheory.JointDickman.MainStatements
import OAI.NumberTheory.JointDickman.Arithmetic.DickmanDistribution
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-!
# The ordering corollary of the joint Dickman law

The proof uses disjoint strips between interior quantiles of the continuous
Dickman distribution. Every strip is a difference of two rectangles appearing
in the main theorem. No weak-convergence or boundary-event hypothesis is used.
-/

namespace JointDickman

open Filter
open scoped Topology BigOperators

theorem exists_dickman_quantile {y : ℝ} (hy : 0 < y) (hy1 : y < 1) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ dickmanCDF t = y := by
  have hmem : y ∈ Set.Icc (dickmanCDF 0) (dickmanCDF 1) := by
    simpa [dickmanCDF_eq_one le_rfl] using And.intro hy.le hy1.le
  obtain ⟨t, ht, hty⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    dickmanCDF_continuous.continuousOn hmem
  refine ⟨t, ?_, ?_, hty⟩
  · by_contra h
    have : t = 0 := le_antisymm (le_of_not_gt h) ht.1
    subst t
    exact hy.ne' (by simpa using hty.symm)
  · by_contra h
    have : t = 1 := le_antisymm ht.2 (le_of_not_gt h)
    subst t
    have : y = 1 := hty.symm.trans (dickmanCDF_eq_one le_rfl)
    exact hy1.ne this

/-- The normalized rectangle has exactly the same count as the paper's
moving-power event. -/
def normalizedRectangle (a b : ℝ) (n : ℕ) : Prop :=
  normalizedPrimeFactor n n ≤ a ∧ normalizedPrimeFactor n (n + 1) ≤ b

theorem realDensity_congr {P Q : ℕ → Prop}
    (h : ∀ n, 2 ≤ n → (P n ↔ Q n)) (X : ℝ) :
    realDensity P X = realDensity Q X := by
  classical
  unfold realDensity empiricalCount
  congr 3
  apply Finset.filter_congr
  intro n hn
  exact h n (Finset.mem_Icc.mp hn).1

theorem normalizedRectangle_density_tendsto (h : JointDickmanLaw)
    {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) :
    Tendsto (realDensity (normalizedRectangle a b)) atTop
      (𝓝 (dickmanCDF a * dickmanCDF b)) := by
  have heq : realDensity (normalizedRectangle a b) = realDensity (movingEvent a b) := by
    funext X
    exact realDensity_congr (fun n hn => (movingEvent_iff_normalized hn a b).symm) X
  rw [heq]
  simpa [dickmanCDF, not_le.mpr ha, not_le.mpr hb] using h a b ha ha1 hb hb1

/-- A horizontal strip below the strict ordering diagonal. -/
def increasingStrip (a b : ℝ) (n : ℕ) : Prop :=
  normalizedPrimeFactor n n ≤ a ∧
    a < normalizedPrimeFactor n (n + 1) ∧ normalizedPrimeFactor n (n + 1) ≤ b

/-- The reflected strip above the strict ordering diagonal. -/
def decreasingStrip (a b : ℝ) (n : ℕ) : Prop :=
  normalizedPrimeFactor n (n + 1) ≤ a ∧
    a < normalizedPrimeFactor n n ∧ normalizedPrimeFactor n n ≤ b

theorem increasingStrip_subset {a b : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hs : increasingStrip a b n) : n.maxPrimeFac < (n + 1).maxPrimeFac := by
  exact (normalizedPrimeFactor_order_iff hn (by omega) (by omega)).mp
    (lt_of_le_of_lt hs.1 hs.2.1)

theorem decreasingStrip_subset {a b : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hs : decreasingStrip a b n) : (n + 1).maxPrimeFac < n.maxPrimeFac := by
  exact (normalizedPrimeFactor_order_iff hn (by omega) (by omega)).mp
    (lt_of_le_of_lt hs.1 hs.2.1)

theorem realDensity_difference {P Q R : ℕ → Prop}
    (h : ∀ n, 2 ≤ n → (P n ↔ Q n ∧ ¬ R n))
    (hsub : ∀ n, 2 ≤ n → R n → Q n) (X : ℝ) :
    realDensity P X = realDensity Q X - realDensity R X := by
  classical
  have heq : empiricalCount Q ⌊X⌋₊ = empiricalCount P ⌊X⌋₊ +
      empiricalCount R ⌊X⌋₊ := by
    unfold empiricalCount
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.Icc 2 ⌊X⌋₊).filter Q) R
    have hQR : ((Finset.Icc 2 ⌊X⌋₊).filter Q).filter R =
        (Finset.Icc 2 ⌊X⌋₊).filter R := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro n hn
      exact ⟨And.right, fun hr => ⟨hsub n (Finset.mem_Icc.mp hn).1 hr, hr⟩⟩
    have hQP : ((Finset.Icc 2 ⌊X⌋₊).filter Q).filter (fun n => ¬R n) =
        (Finset.Icc 2 ⌊X⌋₊).filter P := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro n hn
      exact (h n (Finset.mem_Icc.mp hn).1).symm
    rw [hQR, hQP, add_comm] at hpart
    exact hpart.symm
  unfold realDensity
  rw [heq, Nat.cast_add, add_div]
  ring

theorem increasingStrip_density_tendsto (h : JointDickmanLaw)
    {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb1 : b < 1) (hab : a ≤ b) :
    Tendsto (realDensity (increasingStrip a b)) atTop
      (𝓝 (dickmanCDF a * (dickmanCDF b - dickmanCDF a))) := by
  have heq : realDensity (increasingStrip a b) = fun X =>
      realDensity (normalizedRectangle a b) X -
        realDensity (normalizedRectangle a a) X := by
    funext X
    apply realDensity_difference
    · intro n hn
      simp only [increasingStrip, normalizedRectangle]
      constructor
      · rintro ⟨hu, hv, hvb⟩
        exact ⟨⟨hu, hvb⟩, fun h => (not_le.mpr hv) h.2⟩
      · rintro ⟨⟨hu, hvb⟩, hn⟩
        exact ⟨hu, lt_of_not_ge (fun hv => hn ⟨hu, hv⟩), hvb⟩
    · intro n hn hs
      exact ⟨hs.1, hs.2.trans hab⟩
  rw [heq]
  convert (normalizedRectangle_density_tendsto h ha ha1 (ha.trans_le hab) hb1).sub
    (normalizedRectangle_density_tendsto h ha ha1 ha ha1) using 1
  congr 1
  ring

theorem decreasingStrip_density_tendsto (h : JointDickmanLaw)
    {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb1 : b < 1) (hab : a ≤ b) :
    Tendsto (realDensity (decreasingStrip a b)) atTop
      (𝓝 (dickmanCDF a * (dickmanCDF b - dickmanCDF a))) := by
  have heq : realDensity (decreasingStrip a b) = fun X =>
      realDensity (normalizedRectangle b a) X -
        realDensity (normalizedRectangle a a) X := by
    funext X
    apply realDensity_difference
    · intro n hn
      simp only [decreasingStrip, normalizedRectangle]
      constructor
      · rintro ⟨hv, hu, hub⟩
        exact ⟨⟨hub, hv⟩, fun h => (not_le.mpr hu) h.1⟩
      · rintro ⟨⟨hub, hv⟩, hn⟩
        exact ⟨hv, lt_of_not_ge (fun hu => hn ⟨hu, hv⟩), hub⟩
    · intro n hn hs
      exact ⟨hs.1.trans hab, hs.2⟩
  rw [heq]
  convert (normalizedRectangle_density_tendsto h (ha.trans_le hab) hb1 ha ha1).sub
    (normalizedRectangle_density_tendsto h ha ha1 ha ha1) using 1
  congr 1
  ring

/-- Disjoint finite collections of events give lower bounds for the density
of an event containing them. -/
theorem realDensity_sum_le_of_disjoint {ι : Type*} [Fintype ι]
    (P : ι → ℕ → Prop) (Q : ℕ → Prop)
    (hdisj : ∀ n, 2 ≤ n → ∀ i j, P i n → P j n → i = j)
    (hsub : ∀ i n, 2 ≤ n → P i n → Q n) {X : ℝ} (hX : 0 ≤ X) :
    ∑ i, realDensity (P i) X ≤ realDensity Q X := by
  classical
  let S (i : ι) := (Finset.Icc 2 ⌊X⌋₊).filter (P i)
  have hd : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint S := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro n hni hnj
    have hi' := Finset.mem_filter.mp hni
    have hj' := Finset.mem_filter.mp hnj
    exact hij (hdisj n (Finset.mem_Icc.mp hi'.1).1 i j hi'.2 hj'.2)
  have hs : Finset.univ.biUnion S ⊆ (Finset.Icc 2 ⌊X⌋₊).filter Q := by
    intro n hn
    obtain ⟨i, _, hni⟩ := Finset.mem_biUnion.mp hn
    have hi' := Finset.mem_filter.mp hni
    exact Finset.mem_filter.mpr ⟨hi'.1,
      hsub i n (Finset.mem_Icc.mp hi'.1).1 hi'.2⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_biUnion hd] at hc
  have hc' : (∑ i, (empiricalCount (P i) ⌊X⌋₊ : ℝ)) ≤
      (empiricalCount Q ⌊X⌋₊ : ℝ) := by
    exact_mod_cast hc
  simpa only [realDensity, Finset.sum_div] using
    div_le_div_of_nonneg_right hc' hX

theorem exists_quantile_grid (m : ℕ) :
    ∃ t : Fin (m + 1) → ℝ,
      (∀ i, 0 < t i ∧ t i < 1 ∧
        dickmanCDF (t i) = ((i.val : ℝ) + 1) / (m + 2)) ∧ StrictMono t := by
  have hex : ∀ i : Fin (m + 1), ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      dickmanCDF t = ((i.val : ℝ) + 1) / (m + 2) := by
    intro i
    apply exists_dickman_quantile
    · positivity
    · apply (div_lt_one (by positivity : (0 : ℝ) < m + 2)).mpr
      have hi : (i.val : ℝ) < m + 1 := by exact_mod_cast i.isLt
      linarith
  choose t ht using hex
  refine ⟨t, ht, ?_⟩
  intro i j hij
  have hv : (i.val : ℝ) < j.val := by exact_mod_cast hij
  have hD : dickmanCDF (t i) < dickmanCDF (t j) := by
    rw [(ht i).2.2, (ht j).2.2]
    exact (div_lt_div_iff_of_pos_right (by positivity)).mpr (by linarith)
  exact lt_of_not_ge (fun hji => (not_lt_of_ge (dickmanCDF_monotone hji)) hD)

private theorem increasingStrip_grid_disjoint {m : ℕ} {t : Fin (m + 1) → ℝ}
    (ht : StrictMono t) (n : ℕ) (i j : Fin m)
    (hi : increasingStrip (t i.castSucc) (t i.succ) n)
    (hj : increasingStrip (t j.castSucc) (t j.succ) n) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · have he : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      exact hij
    have h := ht.monotone he
    exact False.elim (not_lt_of_ge (hi.2.2.trans h) hj.2.1)
  · exact hij
  · have he : j.succ ≤ i.castSucc := by
      change j.val + 1 ≤ i.val
      exact hij
    have h := ht.monotone he
    exact False.elim (not_lt_of_ge (hj.2.2.trans h) hi.2.1)

private theorem decreasingStrip_grid_disjoint {m : ℕ} {t : Fin (m + 1) → ℝ}
    (ht : StrictMono t) (n : ℕ) (i j : Fin m)
    (hi : decreasingStrip (t i.castSucc) (t i.succ) n)
    (hj : decreasingStrip (t j.castSucc) (t j.succ) n) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · have he : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      exact hij
    have h := ht.monotone he
    exact False.elim (not_lt_of_ge (hi.2.2.trans h) hj.2.1)
  · exact hij
  · have he : j.succ ≤ i.castSucc := by
      change j.val + 1 ≤ i.val
      exact hij
    have h := ht.monotone he
    exact False.elim (not_lt_of_ge (hj.2.2.trans h) hi.2.1)

/-- The mass of the finite disjoint strip approximation. -/
noncomputable def orderingGridMass (m : ℕ) : ℝ :=
  ((m : ℝ) / (m + 2)) * (((m : ℝ) + 1) / (m + 2)) / 2

private theorem sum_fin_cast_add_one (m : ℕ) :
    ∑ i : Fin m, ((i.val : ℝ) + 1) = (m : ℝ) * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
    ring

private theorem quantile_grid_mass {m : ℕ} {t : Fin (m + 1) → ℝ}
    (hq : ∀ i, dickmanCDF (t i) = ((i.val : ℝ) + 1) / (m + 2)) :
    ∑ i : Fin m, dickmanCDF (t i.castSucc) *
      (dickmanCDF (t i.succ) - dickmanCDF (t i.castSucc)) = orderingGridMass m := by
  have hterm : ∀ i : Fin m, dickmanCDF (t i.castSucc) *
      (dickmanCDF (t i.succ) - dickmanCDF (t i.castSucc)) =
      ((i.val : ℝ) + 1) / ((m : ℝ) + 2) ^ 2 := by
    intro i
    simp only [hq, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  simp_rw [hterm]
  rw [← Finset.sum_div, sum_fin_cast_add_one]
  unfold orderingGridMass
  field_simp

theorem orderingGridMass_tendsto :
    Tendsto orderingGridMass atTop (𝓝 (1 / 2)) := by
  have hleft := tendsto_natCast_div_add_atTop (2 : ℝ)
  have hright : Tendsto (fun m : ℕ => ((m : ℝ) + 1) / (m + 2))
      atTop (𝓝 1) := by
    simpa [add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (d := (1 : ℝ)) (1 : ℝ) 2 1 (by norm_num))
  change Tendsto (fun m : ℕ =>
    ((m : ℝ) / (m + 2)) * (((m : ℝ) + 1) / (m + 2)) / 2)
    atTop (𝓝 (1 / 2))
  convert (hleft.mul hright).div_const 2 using 1
  norm_num

/-- Both strict orderings dominate finite strip approximations with the same
explicit limiting mass. The approximations approach mass one half. -/
theorem exists_ordering_lower_approximants (h : JointDickmanLaw) (m : ℕ) :
    ∃ f g : ℝ → ℝ,
      Tendsto f atTop (𝓝 (orderingGridMass m)) ∧
      Tendsto g atTop (𝓝 (orderingGridMass m)) ∧
      (∀ X, 0 ≤ X → f X ≤
        realDensity (fun n => n.maxPrimeFac < (n + 1).maxPrimeFac) X) ∧
      (∀ X, 0 ≤ X → g X ≤
        realDensity (fun n => (n + 1).maxPrimeFac < n.maxPrimeFac) X) := by
  obtain ⟨t, ht, hmono⟩ := exists_quantile_grid m
  let f (X : ℝ) := ∑ i : Fin m,
    realDensity (increasingStrip (t i.castSucc) (t i.succ)) X
  let g (X : ℝ) := ∑ i : Fin m,
    realDensity (decreasingStrip (t i.castSucc) (t i.succ)) X
  have hm : ∑ i : Fin m, dickmanCDF (t i.castSucc) *
      (dickmanCDF (t i.succ) - dickmanCDF (t i.castSucc)) = orderingGridMass m :=
    quantile_grid_mass (fun i => (ht i).2.2)
  have horder (i : Fin m) : t i.castSucc ≤ t i.succ :=
    hmono.monotone (by change i.val ≤ i.val + 1; omega)
  refine ⟨f, g, ?_, ?_, ?_, ?_⟩
  · rw [← hm]
    exact tendsto_finsetSum _ (fun i _ => increasingStrip_density_tendsto h
      (ht i.castSucc).1 (ht i.castSucc).2.1 (ht i.succ).2.1 (horder i))
  · rw [← hm]
    exact tendsto_finsetSum _ (fun i _ => decreasingStrip_density_tendsto h
      (ht i.castSucc).1 (ht i.castSucc).2.1 (ht i.succ).2.1 (horder i))
  · intro X hX
    exact realDensity_sum_le_of_disjoint _ _
      (fun n _ i j hi hj => increasingStrip_grid_disjoint hmono n i j hi hj)
      (fun _ _ hn hs => increasingStrip_subset hn hs) hX
  · intro X hX
    exact realDensity_sum_le_of_disjoint _ _
      (fun n _ i j hi hj => decreasingStrip_grid_disjoint hmono n i j hi hj)
      (fun _ _ hn hs => decreasingStrip_subset hn hs) hX

/-- Corollary 2: asymptotic independence and the continuous common marginal
force the increasing ordering to have ordinary density one half. -/
theorem increasingOrderLaw_of_jointDickmanLaw (h : JointDickmanLaw) :
    IncreasingOrderLaw := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨m, hm⟩ := ((tendsto_order.mp orderingGridMass_tendsto).1 a ha).exists
    obtain ⟨f, g, hf, hg, hfI, hgD⟩ := exists_ordering_lower_approximants h m
    filter_upwards [(tendsto_order.mp hf).1 a hm, eventually_ge_atTop (0 : ℝ)]
      with X haX hX
    exact haX.trans_le (hfI X hX)
  · intro b hb
    have htarget : 1 - b < (1 / 2 : ℝ) := by linarith
    obtain ⟨m, hm⟩ :=
      ((tendsto_order.mp orderingGridMass_tendsto).1 (1 - b) htarget).exists
    obtain ⟨f, g, hf, hg, hfI, hgD⟩ := exists_ordering_lower_approximants h m
    have hgap : 1 < b + orderingGridMass m := by linarith
    let c : ℝ := (1 + b + orderingGridMass m) / 2
    have hc : 1 < c := by dsimp [c]; linarith
    have hcb : c - b < orderingGridMass m := by dsimp [c]; linarith
    filter_upwards [(tendsto_order.mp ordering_density_sum_tendsto).2 c hc,
      (tendsto_order.mp hg).1 (c - b) hcb, eventually_ge_atTop (0 : ℝ)]
      with X hsum hgX hX
    have hD := hgD X hX
    linarith

theorem decreasingOrderLaw_of_jointDickmanLaw (h : JointDickmanLaw) :
    DecreasingOrderLaw :=
  increasingOrderLaw_iff_decreasingOrderLaw.mp (increasingOrderLaw_of_jointDickmanLaw h)

end JointDickman

end OAI
