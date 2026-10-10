import OAI.Computability.MeanPayoff.Drift

namespace OAI

section

namespace MeanPayoff
open scoped Classical

theorem linked_first {α : Type} {R : α → α → Prop} {q : α} {qs : List α}
    (h : Linked R q qs) : qs.getD 0 q = q := by
  rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, h.1]
  rfl

theorem linked_step {α : Type} {R : α → α → Prop} {q : α} {qs : List α}
    (h : Linked R q qs) {j : ℕ} (hj : j + 1 < qs.length) :
    R (qs.getD j q) (qs.getD (j + 1) q) := by
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj]
  exact List.isChain_iff_getElem.mp h.2 j hj

noncomputable def badTimes {α : Type} (bad : α → Prop) (qs : List α) (q : α) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun j => bad (qs.getD j q))).card

@[simp] theorem badTimes_zero {α : Type} (bad : α → Prop) (qs : List α) (q : α) :
    badTimes bad qs q 0 = 0 := by simp [badTimes]

theorem badTimes_succ {α : Type} (bad : α → Prop) (qs : List α) (q : α) (t : ℕ) :
    badTimes bad qs q (t + 1) = badTimes bad qs q t + if bad (qs.getD t q) then 1 else 0 := by
  have hn : t ∉ (Finset.range t).filter (fun j => bad (qs.getD j q)) := by simp
  simp only [badTimes, Finset.range_add_one, Finset.filter_insert]
  split_ifs <;> simp []

theorem linked_telescope {α : Type} (d : α → ℤ) (bad : α → Prop) (D : ℤ)
    {q : α} {qs : List α}
    (h : Linked (fun q q' => d q' ≤ d q ∧ (bad q → d q' ≤ d q - D)) q qs)
    {t : ℕ} (ht : t < qs.length) :
    d (qs.getD t q) + (badTimes bad qs q t : ℤ) * D ≤ d q := by
  induction t with
  | zero => rw [linked_first h]; simp
  | succ t ih =>
    have hi := ih (by omega)
    have hs := linked_step h ht
    rw [badTimes_succ]
    by_cases hb : bad (qs.getD t q)
    · simp only [hb, ite_true, Nat.cast_add, Nat.cast_one]
      nlinarith only [hi, hs.2 hb]
    · simp only [hb, ite_false, Nat.add_zero]
      linarith [hs.1]

theorem centerSteps_all_relation {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (R : BoxVector I → BoxVector I → Prop)
    (hstep : ∀ q, (centerUpdate P hR lower I hB q).All (R q))
    (t : ℕ) (q : BoxVector I) : (centerSteps P hR lower I hB t q).All (Linked R q) := by
  induction t generalizing q with
  | zero => exact linked_single R q
  | succ t ht =>
    rw [centerSteps, RandomTree.all_bind]
    apply RandomTree.all_mono _ (hstep q)
    intro q' hq'
    rw [RandomTree.map, RandomTree.all_bind]
    exact RandomTree.all_mono _ (ht q') (fun qs hqs => linked_cons hq' hqs)

def Moving {n Bmax : ℕ} (I : SolveBox n Bmax) (q q' : BoxVector I) : Prop :=
  ∀ i, |q'.val i - q.val i| ≤ (I.D : ℤ)

theorem centerSteps_moving {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (t : ℕ) (q : BoxVector I) :
    (centerSteps P hR lower I hB t q).All (Linked (Moving I) q) :=
  centerSteps_all_relation P hR lower I hB (Moving I)
    (centerUpdate_movement P hR lower I hB) t q

theorem centerSteps_metadata {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (t : ℕ) (q : BoxVector I) :
    (centerSteps P hR lower I hB t q).All
      (fun qs => qs.length = t + 1 ∧ Linked (Moving I) q qs) := by
  apply RandomTree.all_and
  · exact centerSteps_length P hR lower I hB t q
  · exact centerSteps_moving P hR lower I hB t q

theorem linked_drift {n Bmax : ℕ} (I : SolveBox n Bmax) {qs : List (BoxVector I)}
    (h : Linked (Moving I) I.midpoint qs) {j : ℕ} (hj : j < qs.length) :
    CenterDrift I j (qs.getD j I.midpoint) := by
  induction j with
  | zero => rw [linked_first h]; exact centerDrift_start I
  | succ j ih => exact centerDrift_move I (ih (by omega)) (linked_step h hj)

def HighBad (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax) (P : Budgets G.n)
    (y : Vec (Fin G.n)) (q : BoxVector I) : Prop :=
  mass P.alpha (nearHigh G y q.val I.D) ≤ (4 / 5) * P.k

def LowBad (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax) (P : Budgets G.n)
    (z : Vec (Fin G.n)) (q : BoxVector I) : Prop :=
  mass P.beta (nearLow G z q.val I.D) ≤ (4 / 5) * P.m

theorem high_core_displacement (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (P : Budgets G.n) (hB : 128 * globalS Bmax < I.width) {y : Vec (Fin G.n)}
    (hy : y ≤ I.b) {qs : List (BoxVector I)}
    (hlen : qs.length = globalS Bmax + 1) (h : Linked (HighStep G I P y) I.midpoint qs) :
    highCore I y ⊆ (NegativeDisplacement I (qs.getD (globalS Bmax) I.midpoint))ᶜ ∧
    (256 < badTimes (HighBad G I P y) qs I.midpoint (globalS Bmax) →
      highCore I y ⊆ PositiveDisplacement I (qs.getD (globalS Bmax) I.midpoint)) := by
  let q := qs.getD (globalS Bmax) I.midpoint
  let c := badTimes (HighBad G I P y) qs I.midpoint (globalS Bmax)
  have ht := linked_telescope (fun q : BoxVector I => deviation G y q.val)
    (HighBad G I P y) I.D h (by omega : globalS Bmax < qs.length)
  change deviation G y q.val + (c : ℤ) * I.D ≤ deviation G y I.midpoint.val at ht
  have hc : (0 : ℤ) ≤ c := Int.natCast_nonneg _
  have hD : (0 : ℤ) ≤ I.D := Int.natCast_nonneg _
  have hs : (0 : ℤ) ≤ globalS Bmax := Int.natCast_nonneg _
  have hb : (128 : ℤ) * globalS Bmax < I.width := by exact_mod_cast hB
  have hn : deviation G y q.val ≤ deviation G y I.midpoint.val := by
    nlinarith only [ht, mul_nonneg hc hD]
  have hn' := mul_le_mul_of_nonneg_left hn hs
  have hdisp (i : Fin G.n) (hi : i ∈ highCore I y) :
      (globalS Bmax : ℤ) * (q.val i - I.midpoint.val i) ≥
      (globalS Bmax : ℤ) * (deviation G y I.midpoint.val - deviation G y q.val) -
        I.width - globalS Bmax := by
    have hi₀ := high_initial_deficit G I hy hi
    have hi₁ := mul_le_mul_of_nonneg_left (le_deviation G y q.val i) hs
    nlinarith only [hi₀, hi₁]
  constructor
  · intro i hi
    have hd := hdisp i hi
    simp only [Finset.mem_compl, NegativeDisplacement, Finset.mem_filter,
      Finset.mem_univ, true_and, not_lt]
    change -2 * (I.width : ℤ) ≤ (globalS Bmax : ℤ) * (q.val i - I.midpoint.val i)
    nlinarith only [hd, hn', hb, hs]
  · intro hmore i hi
    have hd := hdisp i hi
    have hcnt : (257 : ℤ) ≤ c := by
      have hnat : 257 ≤ c := by omega
      exact_mod_cast hnat
    have ht' := mul_le_mul_of_nonneg_left ht hs
    have hcnt' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcnt hD) hs
    have hr : (I.width : ℤ) ≤ 64 * globalS Bmax * I.D := by
      exact_mod_cast (I.radius_bounds hB).1
    simp only [PositiveDisplacement, Finset.mem_filter, Finset.mem_univ, true_and]
    change 2 * (I.width : ℤ) < (globalS Bmax : ℤ) * (q.val i - I.midpoint.val i)
    nlinarith only [hd, ht', hcnt', hr, hb, hs]

theorem low_core_displacement (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (P : Budgets G.n) (hB : 128 * globalS Bmax < I.width) {z : Vec (Fin G.n)}
    (hz : I.a ≤ z) {qs : List (BoxVector I)}
    (hlen : qs.length = globalS Bmax + 1) (h : Linked (LowStep G I P z) I.midpoint qs) :
    lowCore I z ⊆ (PositiveDisplacement I (qs.getD (globalS Bmax) I.midpoint))ᶜ ∧
    (256 < badTimes (LowBad G I P z) qs I.midpoint (globalS Bmax) →
      lowCore I z ⊆ NegativeDisplacement I (qs.getD (globalS Bmax) I.midpoint)) := by
  let q := qs.getD (globalS Bmax) I.midpoint
  let c := badTimes (LowBad G I P z) qs I.midpoint (globalS Bmax)
  have ht := linked_telescope (fun q : BoxVector I => deviation G q.val z)
    (LowBad G I P z) I.D h (by omega : globalS Bmax < qs.length)
  change deviation G q.val z + (c : ℤ) * I.D ≤ deviation G I.midpoint.val z at ht
  have hc : (0 : ℤ) ≤ c := Int.natCast_nonneg _
  have hD : (0 : ℤ) ≤ I.D := Int.natCast_nonneg _
  have hs : (0 : ℤ) ≤ globalS Bmax := Int.natCast_nonneg _
  have hb : (128 : ℤ) * globalS Bmax < I.width := by exact_mod_cast hB
  have hn : deviation G q.val z ≤ deviation G I.midpoint.val z := by
    nlinarith only [ht, mul_nonneg hc hD]
  have hn' := mul_le_mul_of_nonneg_left hn hs
  have hdisp (i : Fin G.n) (hi : i ∈ lowCore I z) :
      (globalS Bmax : ℤ) * (q.val i - I.midpoint.val i) ≤
      I.width + globalS Bmax -
        (globalS Bmax : ℤ) * (deviation G I.midpoint.val z - deviation G q.val z) := by
    have hi₀ := low_initial_deficit G I hz hi
    have hi₁ := mul_le_mul_of_nonneg_left (le_deviation G q.val z i) hs
    nlinarith only [hi₀, hi₁]
  constructor
  · intro i hi
    have hd := hdisp i hi
    simp only [Finset.mem_compl, PositiveDisplacement, Finset.mem_filter,
      Finset.mem_univ, true_and, not_lt]
    change (globalS Bmax : ℤ) * (q.val i - I.midpoint.val i) ≤ 2 * (I.width : ℤ)
    nlinarith only [hd, hn', hb, hs]
  · intro hmore i hi
    have hd := hdisp i hi
    have hcnt : (257 : ℤ) ≤ c := by
      have hnat : 257 ≤ c := by omega
      exact_mod_cast hnat
    have ht' := mul_le_mul_of_nonneg_left ht hs
    have hcnt' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcnt hD) hs
    have hr : (I.width : ℤ) ≤ 64 * globalS Bmax * I.D := by
      exact_mod_cast (I.radius_bounds hB).1
    simp only [NegativeDisplacement, Finset.mem_filter, Finset.mem_univ, true_and]
    change (globalS Bmax : ℤ) * (q.val i - I.midpoint.val i) < -2 * (I.width : ℤ)
    nlinarith only [hd, ht', hcnt', hr, hb, hs]

end MeanPayoff

namespace MeanPayoff
open scoped Classical

namespace RandomTree

theorem uniform_probability (k : ℕ) (P : ℕ → Prop) :
    (uniformBelow k).probability P =
      (((Finset.range (2 ^ k)).filter P).card : ℚ) / 2 ^ k := by
  unfold probability
  rw [expect_uniformBelow, Finset.card_filter]
  congr 1
  simp

theorem sample_badTimes {α : Type} (Bmax : ℕ) (P : α → Prop) (qs : List α) (q : α)
    (h : badTimes P qs q (globalS Bmax) ≤ 256) :
    (uniformBelow (sampleExponent Bmax)).probability (fun j => P (qs.getD j q)) ≤
      256 / (globalS Bmax : ℚ) := by
  rw [uniform_probability]
  have hden : (2 : ℚ) ^ sampleExponent Bmax = (globalS Bmax : ℚ) := by
    simp only [globalS, Nat.cast_pow, Nat.cast_ofNat]
  rw [hden]
  change (badTimes P qs q (globalS Bmax) : ℚ) / (globalS Bmax : ℚ) ≤ _
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (Nat.cast_nonneg _)

end RandomTree

theorem nearHigh_child_core (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (hB : 128 * globalS Bmax < I.width) (y : Vec (Fin G.n)) (q : BoxVector I) :
    nearHigh G y q.val I.D ⊆
      highCore (I.wideCentered hB q.val) (centerSub y q.val (deviation G y q.val) I.E) := by
  intro i hi
  have hi' := (Finset.mem_filter.mp hi).2
  have hu : y i - deviation G y q.val + I.E ≤
      centerSub y q.val (deviation G y q.val) I.E i := le_max_left _ _
  have hs : (0 : ℤ) ≤ globalS Bmax := Int.natCast_nonneg _
  have hd : (globalS Bmax : ℤ) * I.D ≤ I.E := by exact_mod_cast (I.radius_bounds hB).2.1
  have hh : q.val i + I.E - 2 * I.D ≤ centerSub y q.val (deviation G y q.val) I.E i := by
    omega
  have hm := mul_le_mul_of_nonneg_left hh hs
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change (globalS Bmax : ℤ) * ↑(2 * I.E) - ↑(2 * I.E) ≤
    (globalS Bmax : ℤ) * (centerSub y q.val (deviation G y q.val) I.E i - (q.val i - I.E))
  push_cast
  nlinarith only [hm, hd]

theorem nearLow_child_core (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (hB : 128 * globalS Bmax < I.width) (z : Vec (Fin G.n)) (q : BoxVector I) :
    nearLow G z q.val I.D ⊆
      lowCore (I.wideCentered hB q.val) (centerSuper z q.val (deviation G q.val z) I.E) := by
  intro i hi
  have hi' := (Finset.mem_filter.mp hi).2
  have hu : centerSuper z q.val (deviation G q.val z) I.E i ≤
      z i + deviation G q.val z - I.E := min_le_left _ _
  have hs : (0 : ℤ) ≤ globalS Bmax := Int.natCast_nonneg _
  have hd : (globalS Bmax : ℤ) * I.D ≤ I.E := by exact_mod_cast (I.radius_bounds hB).2.1
  have hh : centerSuper z q.val (deviation G q.val z) I.E i ≤ q.val i - I.E + 2 * I.D := by
    omega
  have hm := mul_le_mul_of_nonneg_left hh hs
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change (globalS Bmax : ℤ) * ↑(2 * I.E) - ↑(2 * I.E) ≤
    (globalS Bmax : ℤ) * ((q.val i + I.E) - centerSuper z q.val (deviation G q.val z) I.E i)
  push_cast
  nlinarith only [hm, hd]

def Alternative {n : ℕ} {P : Budgets n} (side : Bool) (w : Fin n → ℚ)
    (S : Finset (Fin n)) (budget : ℚ) (O : Orientation P) : Prop :=
  O.chooseY = side ∨ ∃ H ∈ O.exceptions, (4 / 5) * budget < mass w (S ∩ H.val)

def HighAlternative {n Bmax : ℕ} (I : SolveBox n Bmax) (P : Budgets n)
    (y : Vec (Fin n)) : Orientation P → Prop :=
  Alternative true P.alpha (lowerActive I.a y) P.k

def LowAlternative {n Bmax : ℕ} (I : SolveBox n Bmax) (P : Budgets n)
    (z : Vec (Fin n)) : Orientation P → Prop :=
  Alternative false P.beta (upperActive I.b z) P.m

theorem alternative_mono {n : ℕ} {P : Budgets n} {side : Bool} {w : Fin n → ℚ}
    (hw : ∀ i, 0 ≤ w i) {S T : Finset (Fin n)} {budget : ℚ} {O O' : Orientation P}
    (hst : S ⊆ T) (hs : O'.chooseY = O.chooseY) (hl : ∀ H ∈ O.exceptions, H ∈ O'.exceptions)
    (h : Alternative side w S budget O) : Alternative side w T budget O' := by
  rcases h with h | ⟨H, hH, hm⟩
  · exact Or.inl (hs.trans h)
  · refine Or.inr ⟨H, hl H hH, hm.trans_le ?_⟩
    apply mass_mono hw
    intro i hi
    exact Finset.mem_inter.mpr ⟨hst (Finset.mem_inter.mp hi).1, (Finset.mem_inter.mp hi).2⟩

theorem alternative_witness {n : ℕ} {P : Budgets n} {side : Bool} {w : Fin n → ℚ}
    (hw : ∀ i, 0 ≤ w i) {S Core : Finset (Fin n)} {budget : ℚ} {O : Orientation P}
    (hc : (4 / 5) * budget < mass w Core) (hcs : Core ⊆ S)
    (H : SmallSet P) (hH : H ∈ O.exceptions) (h : Core ⊆ H.val) :
    Alternative side w S budget O := by
  refine Or.inr ⟨H, hH, hc.trans_le (mass_mono hw ?_)⟩
  exact Finset.subset_inter hcs h

end MeanPayoff
end

end OAI
