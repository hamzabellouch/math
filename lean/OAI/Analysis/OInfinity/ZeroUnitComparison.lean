import OAI.Analysis.OInfinity.ZeroUnitBuffer

namespace OAI

/-! # Zero-unit finite comparison with a concrete central buffer

The two complementary isometries remain supplied as actual elements. The
common-corner restriction uses only the closed algebra of the buffer and
its commutant, so no arbitrary-map uniqueness theorem is invoked.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- Elements in the closed buffer algebra commute with its full star
commutant, not just with individual row generators. -/
lemma bufferAlgebra_commutes_commutant (r : ℕ → E)
    (x : StarSubalgebra.centralizer ℂ (Set.range r))
    (y : closedCanonicalRowAlgebra r) : Commute (x : E) (y : E) := by
  have hy : (y : E) ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (Set.range r) : Set E) :=
    StarSubalgebra.topologicalClosure_adjoin_le_centralizer_centralizer ℂ (Set.range r) y.property
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp hy) x x.property).1

/-- Restrict a full binary row in the buffer commutant and its finite
buffer encoding to their actual common unit, then compare them there. -/
lemma exists_buffer_common_binary_comparison
    (r : ℕ → E)
    (q : StarSubalgebra.centralizer ℂ (Set.range r))
    (p : closedCanonicalRowAlgebra r)
    (hq : star q = q) (hqq : q * q = q)
    (hp : star p = p) (hpp : p * p = p)
    (hqp0 : (q : E) * (p : E) ≠ 0)
    (a : Fin 2 → StarSubalgebra.centralizer ℂ (Set.range r))
    (b : Fin 2 → closedCanonicalRowAlgebra r)
    (ha : ∀ i j, star (a i) * a j = if i = j then q else 0)
    (hb : ∀ i j, star (b i) * b j = if i = j then p else 0)
    (has : (∑ i, a i * star (a i)) = q)
    (hbs : (∑ i, b i * star (b i)) = p)
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      (u : E) * (1 - (q : E) * (p : E)) = 1 - (q : E) * (p : E) ∧
      (1 - (q : E) * (p : E)) * (u : E) = 1 - (q : E) * (p : E) ∧
      ∀ i ≤ m, ‖(u : E) * (((a 0 : E) ^ i * (a 1 : E)) * (p : E)) *
        star (u : E) - ((b 0 : E) ^ i * (b 1 : E)) * (q : E)‖ < ε := by
  let C := StarSubalgebra.centralizer ℂ (Set.range r)
  let D := closedCanonicalRowAlgebra r
  let : IsClosed (C : Set E) := Set.isClosed_centralizer _
  have hc (x : C) (y : D) : Commute (x : E) (y : E) :=
    bufferAlgebra_commutes_commutant r x y
  let f := commutingProjectionRestriction C (p : E)
    (congrArg D.subtype hp) (congrArg D.subtype hpp) (fun x => hc x p)
  let g := commutingProjectionRestriction D (q : E)
    (congrArg C.subtype hq) (congrArg C.subtype hqq) (fun y => (hc q y).symm)
  have hrestr := restrict_commuting_binary_rows C D hc q p hq hqq hp hpp a b ha hb has hbs
  change (∀ i j, star (f (a i)) * f (a j) = if i = j then (q : E) * (p : E) else 0) ∧
    (∀ i j, star (g (b i)) * g (b j) = if i = j then (q : E) * (p : E) else 0) ∧
    (∑ i, f (a i) * star (f (a i))) = (q : E) * (p : E) ∧
    (∑ i, g (b i) * star (g (b i))) = (q : E) * (p : E) ∧
    bergRowsCommute (fun i => f (a i)) (fun i => g (b i)) at hrestr
  have hqp : Commute (q : E) (p : E) := hc q p
  have hqs : star (q : E) = (q : E) := congrArg C.subtype hq
  have hps : star (p : E) = (p : E) := congrArg D.subtype hp
  have hq2 : (q : E) * (q : E) = (q : E) := congrArg C.subtype hqq
  have hp2 : (p : E) * (p : E) = (p : E) := congrArg D.subtype hpp
  have hstar : star ((q : E) * (p : E)) = (q : E) * (p : E) := by
    rw [star_mul, hqs, hps, hqp.eq]
  have hsq : ((q : E) * (p : E)) * ((q : E) * (p : E)) = (q : E) * (p : E) := by
    calc
      _ = (q : E) * ((p : E) * (q : E)) * (p : E) := by noncomm_ring
      _ = _ := by rw [← hqp.eq, ← mul_assoc, hq2, mul_assoc, hp2]
  obtain ⟨u, hu, hur, hul, he⟩ := exists_relative_binary_power_conjugacy
    ((q : E) * (p : E)) hstar hsq hqp0
    (fun i => f (a i)) (fun i => g (b i))
    hrestr.1 hrestr.2.1 hrestr.2.2.1 hrestr.2.2.2.1 hrestr.2.2.2.2 m ε hε
  refine ⟨u, hu, hur, hul, fun i hi => ?_⟩
  have haev : f (a 0) ^ i * f (a 1) = ((a 0 : E) ^ i * (a 1 : E)) * (p : E) := by
    rw [← nonunital_map_pow_mul]
    change ((a 0 ^ i * a 1 : C) : E) * (p : E) = _
    rfl
  have hbev : g (b 0) ^ i * g (b 1) = ((b 0 : E) ^ i * (b 1 : E)) * (q : E) := by
    rw [← nonunital_map_pow_mul]
    change ((b 0 ^ i * b 1 : D) : E) * (q : E) = _
    rfl
  simpa only [haev, hbev] using he i hi

/-- Compare the finite encoding of a zero-unit row with the actual negative
buffer row. Both a complement isometry and an isometry inside the initial
corner are retained as concrete data. The resulting ambient unitary is
connected to one; this does not compare the original unsplit generators. -/
lemma exists_zeroUnit_buffer_comparison_with_unit [Nontrivial E]
    (r : ℕ → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (q w z : StarSubalgebra.centralizer ℂ (Set.range r))
    (hq : star q = q) (hqq : q * q = q) (hq0 : q ≠ 0)
    (hw : star w * w = 1) (hww : w * star w = 1 - q)
    (hz : star z * z = 1) (hqz : q * z = z)
    (a : Fin 2 → StarSubalgebra.centralizer ℂ (Set.range r))
    (ha : ∀ i j, star (a i) * a j = if i = j then q else 0)
    (has : (∑ i, a i * star (a i)) = q)
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      (u : E) * (q : E) * star (u : E) = canonicalTailProjection r 1 ∧
      ∀ i ≤ m, ‖(u : E) * ((a 0 : E) ^ i * (a 1 : E)) * star (u : E) -
        canonicalNegativeRow r i‖ < ε := by
  let C := StarSubalgebra.centralizer ℂ (Set.range r)
  let D := closedCanonicalRowAlgebra r
  let : IsClosed (C : Set E) := Set.isClosed_centralizer _
  let R : ℕ → D := fun i => ⟨r i, mem_closedCanonicalRowAlgebra r i⟩
  have hR (i j : ℕ) : star (R i) * R j = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · rw [ite_eq_left hij]
      apply Subtype.ext
      change star (r i) * r j = 1
      simpa only [ite_eq_left hij] using hr i j
    · rw [ite_eq_right hij]
      apply Subtype.ext
      change star (r i) * r j = 0
      simpa only [ite_eq_right hij] using hr i j
  let p := canonicalTailProjection R 1
  let P := canonicalTailProjection r 1
  have hpc : (p : E) = P := canonicalTailProjection_coe D R 1
  have hp : star p = p := canonicalTailProjection_star R 1
  have hpp : p * p = p := canonicalTailProjection_idempotent R hR 1
  have hP : star P = P := canonicalTailProjection_star r 1
  have hPP : P * P = P := canonicalTailProjection_idempotent r hr 1
  have hP0 : P ≠ 0 := canonicalTailProjection_ne_zero r hr 1
  have hPdef : P = 1 - r 0 * star (r 0) := by
    dsimp only [P]
    rw [show (1 : ℕ) = 0 + 1 by rfl, canonicalTailProjection_succ, canonicalTailProjection_zero]
  have hqE : star (q : E) = (q : E) := congrArg C.subtype hq
  have hqqE : (q : E) * (q : E) = (q : E) := congrArg C.subtype hqq
  have hq0E : (q : E) ≠ 0 := fun h => hq0 (Subtype.ext h)
  have hwE : star (w : E) * (w : E) = 1 := congrArg C.subtype hw
  have hwwE : (w : E) * star (w : E) = 1 - (q : E) := congrArg C.subtype hww
  have hzE : star (z : E) * (z : E) = 1 := congrArg C.subtype hz
  have hqzE : (q : E) * (z : E) = (z : E) := congrArg C.subtype hqz
  have hcomm (x : C) (y : D) : Commute (x : E) (y : E) :=
    bufferAlgebra_commutes_commutant r x y
  have hxrow (x : C) (j : ℕ) : Commute (x : E) (r j) ∧ Commute (x : E) (star (r j)) := by
    have h := (StarSubalgebra.mem_centralizer_iff ℂ).mp x.property (r j) ⟨j, rfl⟩
    exact ⟨h.1.symm, h.2.symm⟩
  have hqP : Commute (q : E) P := by simpa only [hpc] using hcomm q p
  have hzP : Commute (z : E) P := by simpa only [hpc] using hcomm z p
  have hPw : Commute P (w : E) := by simpa only [hpc] using (hcomm w p).symm
  have hPz : Commute P (z : E) := hzP.symm
  have hqP0 : (q : E) * P ≠ 0 := by
    let v := (z : E) * r 1
    have hv : star v * v = 1 := by
      dsimp only [v]
      rw [star_mul]
      calc
        _ = star (r 1) * (star (z : E) * (z : E)) * r 1 := by noncomm_ring
        _ = 1 := by rw [hzE, mul_one]; simpa only [ite_true] using hr 1 1
    have hPr : P * r 1 = r 1 := by
      simpa only [Nat.lt_irrefl, ite_false] using canonicalTailProjection_mul_generator r hr 1 1
    have hs : ((q : E) * P) * v = v := by
      dsimp only [v]
      calc
        _ = (q : E) * (P * (z : E)) * r 1 := by noncomm_ring
        _ = ((q : E) * (z : E)) * (P * r 1) := by rw [← hzP.eq]; noncomm_ring
        _ = _ := by rw [hqzE, hPr]
    intro hzero
    have hv0 : v = 0 := by simpa only [hzero, zero_mul] using hs.symm
    have h10 : (1 : E) = 0 := by simpa only [hv0, star_zero, zero_mul] using hv.symm
    exact one_ne_zero h10
  obtain ⟨b0, b1, hb0, hb1, hb01, hbs, hbe⟩ :=
    exists_canonicalNegative_binary_encoding R hR m
  let b : Fin 2 → D := ![b0, b1]
  have hb10 : star b1 * b0 = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hb01
  have hb (i j : Fin 2) : star (b i) * b j = if i = j then p else 0 := by
    fin_cases i <;> fin_cases j <;> simp [b, p, hb0, hb1, hb01, hb10]
  have hbs' : (∑ i, b i * star (b i)) = p := by
    simpa only [Fin.sum_univ_two, b, Matrix.cons_val_zero, Matrix.cons_val_one] using hbs
  let A : Fin 2 → E := fun i => a i
  let B : Fin 2 → E := fun i => b i
  have haE (i j : Fin 2) : star (A i) * A j = if i = j then (q : E) else 0 := by
    have h := congrArg C.subtype (ha i j)
    simpa only [map_mul, map_star, apply_ite, map_zero, StarSubalgebra.subtype_apply] using h
  have hasE : (∑ i, A i * star (A i)) = (q : E) := by
    have h := congrArg C.subtype has
    simpa only [map_sum, map_mul, map_star, StarSubalgebra.subtype_apply] using h
  have hbE (i j : Fin 2) : star (B i) * B j = if i = j then P else 0 := by
    have h := congrArg D.subtype (hb i j)
    simpa only [map_mul, map_star, apply_ite, map_zero, StarSubalgebra.subtype_apply, hpc] using h
  have hbsE : (∑ i, B i * star (B i)) = P := by
    have h := congrArg D.subtype hbs'
    simpa only [map_sum, map_mul, map_star, StarSubalgebra.subtype_apply, hpc] using h
  let δ := ε / 3
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨c, _hcL, hcq, hcg, hcc, hec⟩ := exists_commuting_binary_corner_shrink
    (q : E) hqE hqqE hq0E A (fun i : Fin 2 => r i) haE hasE
    (fun i j => by simpa only [Fin.ext_iff] using hr i j)
    (fun i j => hxrow (a i) j) (fun j => (hxrow q j).1) m δ hδ
  simp only [Fin.val_zero] at hcc hec
  rw [← hPdef] at hcc
  have hbw (i : Fin 2) : Commute (B i) (w : E) ∧ Commute (B i) (star (w : E)) :=
    ⟨(hcomm w (b i)).symm, (hcomm (star w) (b i)).symm⟩
  have hbz (i : Fin 2) : Commute (B i) (z : E) ∧ Commute (B i) (star (z : E)) :=
    ⟨(hcomm z (b i)).symm, (hcomm (star z) (b i)).symm⟩
  obtain ⟨d, _hdL, hdp, hdg, hdd, hed⟩ := exists_complementary_binary_corner_shrink
    P (q : E) (w : E) (z : E) hP hPP hP0 hwE hwwE hzE hqzE hPw hPz
    B hbE hbsE hbw hbz m δ hδ
  have hdd' : d * star d = (q : E) * P := hdd.trans hqP.eq.symm
  have hqpc : (q : E) * (p : E) ≠ 0 := by simpa only [hpc] using hqP0
  obtain ⟨v, _hv, hvr, hvl, hev⟩ := exists_buffer_common_binary_comparison
    r q p hq hqq hp hpp hqpc a b ha hb has hbs' m δ hδ
  have hvR : Commute (v : E) ((q : E) * P) := by
    have h := hvr.trans hvl.symm
    rw [mul_sub, sub_mul, mul_one, one_mul] at h
    change (v : E) * ((q : E) * P) = ((q : E) * P) * (v : E)
    simpa only [hpc] using sub_right_inj.mp h
  let W := star d * (v : E) * c
  obtain ⟨hWq, hWP, hWright⟩ := commonCornerTransfer_products
    (q : E) P ((q : E) * P) c d v hcg hcc hcq hdg hdd' hdp hvR
  have hdn : ‖d‖ ≤ 1 := by
    have hn := congrArg norm hdg
    rw [CStarRing.norm_star_mul_self] at hn
    have hPn : ‖P‖ ≤ 1 := IsStarProjection.norm_le P (isStarProjection_iff'.mpr ⟨hPP, hP⟩)
    nlinarith [norm_nonneg d]
  have hclose (i : ℕ) (hi : i ≤ m) :
      ‖W * (A 0 ^ i * A 1) * star W - (B 0 ^ i * B 1)‖ < ε := by
    have hbl : P * (B 0 ^ i * B 1) = B 0 ^ i * B 1 := by
      have hs0 := finiteRow_left_support P B hP hPP hbE hbsE 0
      have hs1 := finiteRow_left_support P B hP hPP hbE hbsE 1
      cases i with
      | zero => simpa only [pow_zero, one_mul] using hs1
      | succ i =>
        calc
          _ = (P * B 0) * (B 0 ^ i * B 1) := by rw [pow_succ']; noncomm_ring
          _ = _ := by rw [hs0, pow_succ']; noncomm_ring
    have hbr : (B 0 ^ i * B 1) * P = B 0 ^ i * B 1 := by
      rw [mul_assoc, finiteRow_right_support P B hP hPP hbE 1]
    have hvclose := hev i hi
    rw [hpc] at hvclose
    have hcclose := hec i hi
    rw [← hPdef] at hcclose
    have he := commonCornerTransfer_error P c d (A 0 ^ i * A 1) (B 0 ^ i * B 1)
      ((A 0 ^ i * A 1) * P) ((B 0 ^ i * B 1) * (q : E)) v hdg hbl hbr hdn δ
      hcclose (hed i hi) hvclose
    exact he.trans_eq (by dsimp only [δ]; ring)
  let spare := (w : E) * r 0
  have hsGram : star spare * spare = 1 := by
    dsimp only [spare]
    rw [star_mul]
    calc
      _ = star (r 0) * (star (w : E) * (w : E)) * r 0 := by noncomm_ring
      _ = 1 := by rw [hwE, mul_one]; simpa only [ite_true] using hr 0 0
  have hqw : (q : E) * (w : E) = 0 := by
    calc
      _ = (1 - (w : E) * star (w : E)) * (w : E) := by rw [hwwE]; noncomm_ring
      _ = 0 := by rw [sub_mul, one_mul, mul_assoc, hwE, mul_one, sub_self]
  have hqsp : (q : E) * spare = 0 := by dsimp only [spare]; rw [← mul_assoc, hqw, zero_mul]
  have hPsp : P * spare = 0 := by
    have hPr : P * r 0 = 0 := by
      simpa only [show (0 : ℕ) < 1 by omega, ite_true] using canonicalTailProjection_mul_generator r hr 1 0
    dsimp only [spare]
    rw [← mul_assoc, hPw.eq, mul_assoc, hPr, mul_zero]
  have hWpartial : W * star W * W = W := by rw [mul_assoc, hWq, hWright]
  obtain ⟨u, hu, _huEq, huq⟩ := exists_explicit_connected_unitary_extension W spare
    hWpartial hsGram (by rw [hWq]; exact hqsp) (by rw [hWP]; exact hPsp)
  have huq' : (u : E) * (q : E) = W := by
    have hWq' : star W * W = (q : E) := hWq
    rw [hWq'] at huq
    exact huq
  have huRange : (u : E) * (q : E) * star (u : E) = P := by
    have hstar := congrArg star huq'
    rw [star_mul, hqE] at hstar
    calc
      _ = (u : E) * ((q : E) * (q : E)) * star (u : E) := by rw [hqqE]
      _ = ((u : E) * (q : E)) * ((q : E) * star (u : E)) := by noncomm_ring
      _ = P := by rw [huq', hstar]; exact hWP
  refine ⟨u, hu, huRange, fun i hi => ?_⟩
  have hxl : (q : E) * (A 0 ^ i * A 1) = A 0 ^ i * A 1 := by
    have hs0 := finiteRow_left_support (q : E) A hqE hqqE haE hasE 0
    have hs1 := finiteRow_left_support (q : E) A hqE hqqE haE hasE 1
    cases i with
    | zero => simpa only [pow_zero, one_mul] using hs1
    | succ i =>
      calc
        _ = ((q : E) * A 0) * (A 0 ^ i * A 1) := by rw [pow_succ']; noncomm_ring
        _ = _ := by rw [hs0, pow_succ']; noncomm_ring
  have hxr : (A 0 ^ i * A 1) * (q : E) = A 0 ^ i * A 1 := by
    rw [mul_assoc, finiteRow_right_support (q : E) A hqE hqqE haE 1]
  have hue : (u : E) * (A 0 ^ i * A 1) * star (u : E) =
      W * (A 0 ^ i * A 1) * star W := by
    calc
      _ = ((u : E) * (q : E)) * (A 0 ^ i * A 1) * star ((u : E) * (q : E)) := by
        rw [star_mul, hqE]
        symm
        calc
          _ = (u : E) * ((q : E) * (A 0 ^ i * A 1) * (q : E)) * star (u : E) := by noncomm_ring
          _ = _ := by rw [hxl, hxr]
      _ = _ := by rw [huq']
  have hbeE : B 0 ^ i * B 1 = canonicalNegativeRow r i := by
    have h := congrArg D.subtype (hbe i hi)
    simpa only [map_pow, map_mul, StarSubalgebra.subtype_apply, canonicalNegativeRow_coe,
      B, b, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  change ‖(u : E) * (A 0 ^ i * A 1) * star (u : E) - canonicalNegativeRow r i‖ < ε
  rw [hue, ← hbeE]
  exact hclose i hi

/-- The comparison-only form preserves the original finite interface. -/
lemma exists_zeroUnit_buffer_comparison [Nontrivial E]
    (r : ℕ → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (q w z : StarSubalgebra.centralizer ℂ (Set.range r))
    (hq : star q = q) (hqq : q * q = q) (hq0 : q ≠ 0)
    (hw : star w * w = 1) (hww : w * star w = 1 - q)
    (hz : star z * z = 1) (hqz : q * z = z)
    (a : Fin 2 → StarSubalgebra.centralizer ℂ (Set.range r))
    (ha : ∀ i j, star (a i) * a j = if i = j then q else 0)
    (has : (∑ i, a i * star (a i)) = q)
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      ∀ i ≤ m, ‖(u : E) * ((a 0 : E) ^ i * (a 1 : E)) * star (u : E) -
        canonicalNegativeRow r i‖ < ε := by
  obtain ⟨u, hu, _, he⟩ := exists_zeroUnit_buffer_comparison_with_unit
    r hr q w z hq hqq hq0 hw hww hz hqz a ha has m ε hε
  exact ⟨u, hu, he⟩

end WeakPureInfiniteness

end

end OAI
