import OAI.Probability.InvariantIsing.Magnetic.MagneticAdjacentSquare
import OAI.Probability.InvariantIsing.Magnetic.MagneticTerminalOrder
import OAI.Probability.InvariantIsing.Magnetic.MagneticHeightLists
import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldInverseConvex

namespace OAI

/-! A literal increase of an interior height decreases each earlier
conditional square mean at fixed prescribed magnetization. -/

noncomputable section
open Set
open scoped NNReal

namespace InvariantIsing

private lemma nonneg_toNNReal_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.toNNReal (a + b) = Real.toNNReal a + Real.toNNReal b := by
  rw [Real.toNNReal_of_nonneg (add_nonneg ha hb), Real.toNNReal_of_nonneg ha,
    Real.toNNReal_of_nonneg hb]
  rfl

private lemma closedSquare_congr {L M : List (ℝ × ℝ≥0)} (he : L = M)
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1)
    (i : Fin (L.length + 1)) (j : Fin (M.length + 1)) (hij : i.val = j.val)
    (ζ : ℝ) (p : ℝ × ℝ) :
    closedMagneticContinuation L (magneticScalarSquareFourJet L hL i).toMagneticContinuationJet ζ p =
    closedMagneticContinuation M (magneticScalarSquareFourJet M hM j).toMagneticContinuationJet ζ p := by
  subst M
  have hi : i = j := Fin.ext hij
  subst j
  rfl

lemma magneticFieldLevel_eq_closed (h : FieldStep) (i : Fin (h.depth + 1))
    {s : ℝ} (hs : |s| < 1) :
    magneticFieldLevel h s i = closedMagneticContinuation (scalarFieldIncrements h)
      (magneticScalarSquareFourJet _ (scalarFieldIncrements_positive h)
        (Fin.cast (by rw [scalarFieldIncrements_length]) i)).toMagneticContinuationJet
      0 (h.height 0, s) := by
  rw [congrFun (magneticFieldLevel_eq_slab h i) s, closedMagneticContinuation, ite_eq_left hs]

theorem magneticFieldLevel_interior_update_le (h : FieldStep) (j : Fin h.depth)
    (hj : 0 < j.val) {t s : ℝ} (ht : 0 ≤ t)
    (htb : t ≤ (fieldIncrement h j.succ).2)
    (hk : Function.update h.height j.castSucc (h.height j.castSucc + t) ∈
      fieldStrictHeightCone h.depth) (hs : |s| < 1)
    (i : Fin (h.depth + 1)) (hij : i.val < j.val) :
    magneticFieldLevel (fieldStepOfStrictHeights h
      (Function.update h.height j.castSucc (h.height j.castSucc + t)) hk) s i ≤
      magneticFieldLevel h s i := by
  let k := fieldStepOfStrictHeights h
    (Function.update h.height j.castSucc (h.height j.castSucc + t)) hk
  let P := (scalarFieldIncrements h).take (j.val - 1)
  let S := (scalarFieldIncrements h).drop (j.val + 1)
  let a := (fieldIncrement h j.castSucc).1
  let b := (fieldIncrement h j.succ).1
  let x := Real.toNNReal (fieldIncrement h j.castSucc).2
  let δ := Real.toNNReal t
  let y := Real.toNNReal ((fieldIncrement h j.succ).2 - t)
  let N := P ++ (a, x + δ) :: (b, y) :: S
  let O := P ++ (a, x) :: (b, δ + y) :: S
  have hx : Real.toNNReal ((fieldIncrement h j.castSucc).2 + t) = x + δ :=
    nonneg_toNNReal_add _ _ (fieldIncrement_nonneg h _) ht
  have hy : δ + y = Real.toNNReal (fieldIncrement h j.succ).2 := by
    dsimp only [δ, y]
    rw [← nonneg_toNNReal_add _ _ ht (sub_nonneg.mpr htb)]
    congr 1
    ring
  have hn : scalarFieldIncrements k = N := by
    rw [scalarFieldIncrements_update_interior h j hj t hk, hx]
  have ho : scalarFieldIncrements h = O := by
    rw [scalarFieldIncrements_interior_layout h j hj]
    dsimp only [O, P, S, a, b, x]
    rw [hy]
  have hN : ∀ av ∈ N, 0 < av.1 := by
    intro av hav
    apply scalarFieldIncrements_positive k av
    rwa [hn]
  have hO : ∀ av ∈ O, 0 < av.1 := by
    intro av hav
    apply scalarFieldIncrements_positive h av
    rwa [ho]
  have hP : ∀ av ∈ P, 0 < av.1 := fun av hav =>
    scalarFieldIncrements_positive h av (List.mem_of_mem_take hav)
  have hP1 : ∀ av ∈ P, av.1 ≤ 1 := fun av hav =>
    scalarFieldIncrements_exponent_le_one h av (List.mem_of_mem_take hav)
  have hS : ∀ av ∈ S, 0 < av.1 := fun av hav =>
    scalarFieldIncrements_positive h av (List.mem_of_mem_drop hav)
  have hS1 : ∀ av ∈ S, av.1 ≤ 1 := fun av hav =>
    scalarFieldIncrements_exponent_le_one h av (List.mem_of_mem_drop hav)
  have ha : 0 < a := by
    change 0 < h.cut j.castSucc.castSucc
    rw [← h.first]
    exact h.ordered_cut (Fin.lt_def.mpr hj)
  have hab : a ≤ b := by
    change h.cut j.castSucc.castSucc ≤ h.cut j.succ.castSucc
    exact h.ordered_cut.monotone (Fin.le_iff_val_le_val.mpr (Nat.le_succ _))
  have hb : b ≤ 1 := by
    change h.cut j.succ.castSucc ≤ 1
    rw [← h.last]
    exact h.ordered_cut.monotone (Fin.le_last _)
  have hip : i.val ≤ P.length := by
    dsimp only [P]
    rw [List.length_take, scalarFieldIncrements_length, Nat.min_eq_left (by omega)]
    omega
  have hcmp := magneticClosedSquare_adjacent_transfer P S hP hP1 hS hS1 ha hab hb
    x δ y hN hO i.val hip (le_refl 0) (by norm_num) (h.nonneg 0)
    ⟨(abs_lt.mp hs).1.le, (abs_lt.mp hs).2.le⟩
  have hroot : k.height 0 = h.height 0 := by
    change Function.update h.height j.castSucc (h.height j.castSucc + t) 0 = h.height 0
    apply Function.update_of_ne
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero, Fin.val_castSucc] at hv
    omega
  rw [magneticFieldLevel_eq_closed k i hs, magneticFieldLevel_eq_closed h i hs, hroot]
  have en := closedSquare_congr hn (scalarFieldIncrements_positive k) hN
    (Fin.cast (by rw [scalarFieldIncrements_length]; rfl) i)
    ⟨i.val, by dsimp only [N]; simp only [List.length_append, List.length_cons]; omega⟩
    rfl 0 (h.height 0, s)
  have eo := closedSquare_congr ho (scalarFieldIncrements_positive h) hO
    (Fin.cast (by rw [scalarFieldIncrements_length]) i)
    ⟨i.val, by dsimp only [O]; simp only [List.length_append, List.length_cons]; omega⟩
    rfl 0 (h.height 0, s)
  exact en.le.trans (hcmp.trans eo.ge)

theorem magneticFieldLevel_terminal_update_le (h : FieldStep) {t s : ℝ} (ht : 0 ≤ t)
    (hk : Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t) ∈
      fieldStrictHeightCone h.depth) (hs : |s| < 1)
    (i : Fin (h.depth + 1)) (hi : i.val < h.depth) :
    magneticFieldLevel (fieldStepOfStrictHeights h
      (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t)) hk) s i ≤
      magneticFieldLevel h s i := by
  have hn : 0 < h.depth := by omega
  let k := fieldStepOfStrictHeights h
    (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t)) hk
  let P := (scalarFieldIncrements h).take (h.depth - 1)
  let a := (fieldIncrement h (Fin.last h.depth)).1
  let x := Real.toNNReal (fieldIncrement h (Fin.last h.depth)).2
  let δ := Real.toNNReal t
  let N := P ++ [(a, x + δ)]
  let O := P ++ [(a, x)]
  have hx : Real.toNNReal ((fieldIncrement h (Fin.last h.depth)).2 + t) = x + δ :=
    nonneg_toNNReal_add _ _ (fieldIncrement_nonneg h _) ht
  have hnew : scalarFieldIncrements k = N := by
    rw [scalarFieldIncrements_update_terminal h hn t hk, hx]
  have hold : scalarFieldIncrements h = O := scalarFieldIncrements_terminal_layout h hn
  have hN : ∀ av ∈ N, 0 < av.1 := by
    intro av hav
    apply scalarFieldIncrements_positive k av
    rwa [hnew]
  have hO : ∀ av ∈ O, 0 < av.1 := by
    intro av hav
    apply scalarFieldIncrements_positive h av
    rwa [hold]
  have hP : ∀ av ∈ P, 0 < av.1 := fun av hav =>
    scalarFieldIncrements_positive h av (List.mem_of_mem_take hav)
  have hP1 : ∀ av ∈ P, av.1 ≤ 1 := fun av hav =>
    scalarFieldIncrements_exponent_le_one h av (List.mem_of_mem_take hav)
  have ha : 0 < a := by
    change 0 < h.cut (Fin.last h.depth).castSucc
    rw [← h.first]
    exact h.ordered_cut (Fin.lt_def.mpr hn)
  have ha1 : a ≤ 1 := by
    change h.cut (Fin.last h.depth).castSucc ≤ 1
    rw [← h.last]
    exact h.ordered_cut.monotone (Fin.le_last _)
  have hip : i.val ≤ P.length := by
    dsimp only [P]
    rw [List.length_take, scalarFieldIncrements_length, Nat.min_eq_left (by omega)]
    omega
  have hcmp := magneticClosedSquare_terminal_variance_mono P hP hP1 ha ha1 x δ hN hO
    i.val hip (le_refl 0) (by norm_num) (h.nonneg 0)
    ⟨(abs_lt.mp hs).1.le, (abs_lt.mp hs).2.le⟩
  have hroot : k.height 0 = h.height 0 := by
    change Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t) 0 = h.height 0
    apply Function.update_of_ne
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero, Fin.val_last] at hv
    omega
  rw [magneticFieldLevel_eq_closed k i hs, magneticFieldLevel_eq_closed h i hs, hroot]
  have en := closedSquare_congr hnew (scalarFieldIncrements_positive k) hN
    (Fin.cast (by rw [scalarFieldIncrements_length]; rfl) i)
    ⟨i.val, by dsimp only [N]; simp only [List.length_append, List.length_singleton]; omega⟩
    rfl 0 (h.height 0, s)
  have eo := closedSquare_congr hold (scalarFieldIncrements_positive h) hO
    (Fin.cast (by rw [scalarFieldIncrements_length]) i)
    ⟨i.val, by dsimp only [O]; simp only [List.length_append, List.length_singleton]; omega⟩
    rfl 0 (h.height 0, s)
  exact en.le.trans (hcmp.trans eo.ge)

end InvariantIsing

end

end OAI
