import OAI.Computability.MeanPayoff.CountedRecursion

namespace OAI

section

namespace MeanPayoff

theorem volume_add {n : ℕ} {a r b : Vec (Fin n)} (har : a ≤ r) (hrb : r ≤ b) :
    volume b a = volume b r + volume r a := by
  unfold volume
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have ha : a i ≤ r i := har i
  have hb : r i ≤ b i := hrb i
  change (b i - a i).toNat = (b i - r i).toNat + (r i - a i).toNat
  omega

theorem volume_floor_drop {n Bmax : ℕ} (I : SolveBox n Bmax) (r : BoxVector I)
    (h : ∃ i, (I.delta : ℤ) ≤ r.val i - I.a i) :
    volume (I.withFloor r).b (I.withFloor r).a + I.delta ≤ volume I.b I.a := by
  obtain ⟨i, hi⟩ := h
  have hcoord : I.delta ≤ (r.val i - I.a i).toNat := by omega
  have hv : I.delta ≤ volume r.val I.a := hcoord.trans
    (Finset.single_le_sum (fun j _ => Nat.zero_le ((r.val j - I.a j).toNat)) (Finset.mem_univ i))
  have heq := volume_add r.property.1 r.property.2
  change volume I.b r.val + I.delta ≤ volume I.b I.a
  omega

theorem volume_ceiling_drop {n Bmax : ℕ} (I : SolveBox n Bmax) (r : BoxVector I)
    (h : ∃ i, (I.delta : ℤ) ≤ I.b i - r.val i) :
    volume (I.withCeiling r).b (I.withCeiling r).a + I.delta ≤ volume I.b I.a := by
  obtain ⟨i, hi⟩ := h
  have hcoord : I.delta ≤ (I.b i - r.val i).toNat := by omega
  have hv : I.delta ≤ volume I.b r.val := hcoord.trans
    (Finset.single_le_sum (fun j _ => Nat.zero_le ((I.b j - r.val j).toNat)) (Finset.mem_univ i))
  have heq := volume_add r.property.1 r.property.2
  change volume r.val I.a + I.delta ≤ volume I.b I.a
  omega

theorem quotient_drop {v w d : ℕ} (hd : 0 < d) (h : w + d ≤ v) : w / d + 1 ≤ v / d := by
  have hh := Nat.div_le_div_right (c := d) h
  rwa [Nat.add_div_right _ hd] at hh

namespace CountedAlgorithm

theorem bounded_centerUpdate {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {N : ℕ} (hN : LowerBound lower N)
    (I : SolveBox n Bmax) (hB : 128 * globalS Bmax < I.width) (q : BoxVector I) :
    (centerUpdate P hR lower I hB q).Bounded (2 * globalJ n Bmax * N) := by
  unfold centerUpdate
  apply Counted.bounded_mono (Counted.bounded_bind _ (SolveBox.bounded_repeated _ (hN _ _ _) _)
    (fun _ => Counted.bounded_map _ (SolveBox.bounded_repeated _ (hN _ _ _) _)))
  nlinarith

theorem bounded_centerSteps {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {N : ℕ} (hN : LowerBound lower N)
    (I : SolveBox n Bmax) (hB : 128 * globalS Bmax < I.width) (t : ℕ) (q : BoxVector I) :
    (centerSteps P hR lower I hB t q).Bounded (t * (2 * globalJ n Bmax * N)) := by
  induction t generalizing q with
  | zero => exact Counted.bounded_pure _
  | succ t ih =>
    unfold centerSteps
    apply Counted.bounded_mono (Counted.bounded_bind _
      (bounded_centerUpdate P hR lower hN I hB q) (fun q' => Counted.bounded_map _ (ih q')))
    simp only [Nat.add_mul, one_mul]
    omega

theorem bounded_orientationTail (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (I : SolveBox G.n Bmax) (qs : List (BoxVector I))
    (child : BoxVector I → Counted (Orientation P)) {N : ℕ} (hN : ∀ q, (child q).Bounded N) :
    (orientationTail G P I qs child).Bounded N := by
  unfold orientationTail
  dsimp only
  split_ifs
  · exact Counted.bounded_pure _
  · exact Counted.bounded_pure _
  · simpa only [zero_add] using Counted.bounded_bind _ (Counted.bounded_lift _)
      (fun j => Counted.bounded_map _ (hN _))

theorem bounded_orient (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {N : ℕ} (hN : LowerBound lower N)
    (I : SolveBox G.n Bmax) :
    (orient G P hR lower I).Bounded
      ((Nat.clog 2 I.width + 1) * (globalS Bmax * (2 * globalJ G.n Bmax * N))) := by
  induction I using (measure (fun I : SolveBox G.n Bmax => I.width)).wf.induction with
  | h I ih =>
      rw [orient]
      split_ifs with hB
      · exact Counted.bounded_pure _
      · have hb : 128 * globalS Bmax < I.width := lt_of_not_ge hB
        have hs := globalS_large Bmax
        have hr := (I.radius_bounds hb).2.2.2
        have hc := clog_double_decrease (by omega : 1 < I.width) (by omega : 2 * (2 * I.E) ≤ I.width)
        have hchild : ∀ q : BoxVector I,
            (orient G P hR lower (I.wideCentered hb q.val)).Bounded
              ((Nat.clog 2 (2 * I.E) + 1) * (globalS Bmax * (2 * globalJ G.n Bmax * N))) := by
          intro q
          exact ih (I.wideCentered hb q.val) (by exact I.E_smaller)
        have htail := fun qs => bounded_orientationTail G P I qs _ hchild
        have hineq : globalS Bmax * (2 * globalJ G.n Bmax * N) +
            (Nat.clog 2 (2 * I.E) + 1) * (globalS Bmax * (2 * globalJ G.n Bmax * N)) ≤
            (Nat.clog 2 I.width + 1) * (globalS Bmax * (2 * globalJ G.n Bmax * N)) := by
          calc
            _ = (Nat.clog 2 (2 * I.E) + 1 + 1) * (globalS Bmax * (2 * globalJ G.n Bmax * N)) := by ring
            _ ≤ _ := Nat.mul_le_mul_right _ (Nat.add_le_add_right hc 1)
        dsimp only
        with_reducible
          exact Counted.bounded_mono
            (Counted.bounded_bind
              (t := centerSteps P hR lower I hb (globalS Bmax) I.midpoint)
              (fun qs => orientationTail G P I qs (fun q => orient G P hR lower (I.wideCentered hb q.val)))
              (bounded_centerSteps P hR lower hN I hb (globalS Bmax) I.midpoint) htail) hineq

theorem bounded_orient_global (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {N : ℕ} (hN : LowerBound lower N)
    (I : SolveBox G.n Bmax) :
    (orient G P hR lower I).Bounded
      ((globalG Bmax + 1) * (globalS Bmax * (2 * globalJ G.n Bmax * N))) := by
  apply Counted.bounded_mono (bounded_orient G P hR lower hN I)
  apply Nat.mul_le_mul_right
  have hh := Nat.clog_mono_right 2 (show I.width ≤ Bmax + 1 from I.bounded.trans (Nat.le_succ Bmax))
  unfold globalG
  omega

theorem bounded_orientPlus {n : ℕ} {P : Budgets n} {t : Counted (Orientation P)}
    {N : ℕ} (hN : t.Bounded N) (J : ℕ) : (orientPlus t J).Bounded (J * N) :=
  Counted.bounded_map _ (Counted.bounded_trials hN J)

theorem bounded_tighten {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {N : ℕ} (hN : LowerBound lower N)
    (I : SolveBox n Bmax) (hB : 128 * globalS Bmax < I.width) :
    (tighten P hR lower I hB).Bounded
      ((volume I.b I.a / I.delta + 1) * (2 * globalJ n Bmax * N)) := by
  rw [tighten]
  refine Counted.bounded_mono (Counted.bounded_bind (M := globalJ n Bmax * N +
    (volume I.b I.a / I.delta) * (2 * globalJ n Bmax * N)) _
    (SolveBox.bounded_repeated _ (hN _ _ _) _) ?_) ?_
  · intro r₁
    split_ifs with h₁
    · have hv := quotient_drop (I.delta_positive hB) (volume_floor_drop I r₁ h₁)
      apply Counted.bounded_mono (Counted.bounded_map _
        (bounded_tighten P hR lower hN (I.withFloor r₁) hB))
      change (volume (I.withFloor r₁).b (I.withFloor r₁).a / I.delta + 1) * _ ≤ _
      exact (Nat.mul_le_mul_right _ hv).trans (Nat.le_add_left _ _)
    · refine Counted.bounded_mono (Counted.bounded_bind (M :=
        (volume I.b I.a / I.delta) * (2 * globalJ n Bmax * N)) _
        (SolveBox.bounded_repeated _ (hN _ _ _) _) ?_) ?_
      · intro r₂
        split_ifs with h₂
        · have hv := quotient_drop (I.delta_positive hB) (volume_ceiling_drop I r₂ h₂)
          apply Counted.bounded_mono (Counted.bounded_map _
            (bounded_tighten P hR lower hN (I.withCeiling r₂) hB))
          change (volume (I.withCeiling r₂).b (I.withCeiling r₂).a / I.delta + 1) * _ ≤ _
          exact Nat.mul_le_mul_right _ hv
        · exact Counted.bounded_pure _
      · exact le_rfl
  · nlinarith
termination_by volume I.b I.a
 decreasing_by
  · have hv := volume_floor_drop I r₁ h₁
    have hd := I.delta_positive hB
    omega
  · have hv := volume_ceiling_drop I r₂ h₂
    have hd := I.delta_positive hB
    omega

end CountedAlgorithm


def widthPotential (s B : ℕ) : ℕ :=
  8 * s * Nat.log 2 B + (8 * s * B) / (2 ^ Nat.log 2 B)

theorem widthPotential_bound (s B : ℕ) (hs : 0 < s) :
    widthPotential s B < 8 * s * (Nat.log 2 B + 2) := by
  have hp : 0 < 2 ^ Nat.log 2 B := pow_pos (by norm_num) _
  have hb := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) B
  rw [pow_succ] at hb
  have hd : 8 * s * B / 2 ^ Nat.log 2 B < 16 * s := by
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    nlinarith
  unfold widthPotential
  nlinarith

theorem widthPotential_decreases {s B C : ℕ} (hs : 0 < s) (hC : 0 < C)
    (hCB : C < B) (hdrop : B ≤ 8 * s * (B - C)) :
    widthPotential s C < widthPotential s B := by
  have hB : 0 < B := hC.trans hCB
  have hp : 0 < 2 ^ Nat.log 2 B := pow_pos (by norm_num) _
  have hpb : 2 ^ Nat.log 2 B ≤ B := Nat.pow_log_le_self 2 (by omega)
  have hlog : Nat.log 2 C ≤ Nat.log 2 B := Nat.log_mono_right hCB.le
  have hlower : 8 * s ≤ (8 * s * B) / 2 ^ Nat.log 2 B := by
    apply (Nat.le_div_iff_mul_le hp).mpr
    exact Nat.mul_le_mul_left _ hpb
  rcases eq_or_lt_of_le hlog with heq | hlt
  · have hsub : 8 * s * C + 2 ^ Nat.log 2 B ≤ 8 * s * B := by
      have ht : C + (B - C) = B := Nat.add_sub_of_le hCB.le
      nlinarith
    have hdiv := Nat.div_le_div_right (c := 2 ^ Nat.log 2 B) hsub
    rw [Nat.add_div_right _ hp] at hdiv
    unfold widthPotential
    rw [heq]
    omega
  · have hc := widthPotential_bound s C hs
    have hm : 8 * s * (Nat.log 2 C + 2) ≤ 8 * s * (Nat.log 2 B + 1) := by
      apply Nat.mul_le_mul_left
      omega
    unfold widthPotential at hc ⊢
    nlinarith



theorem SolveBox.delta_lower {n Bmax : ℕ} (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) : I.width ≤ 8 * globalS Bmax * I.delta := by
  have hs := globalS_large Bmax
  have hp := I.delta_positive hB
  have hd := Nat.lt_mul_div_succ I.width (by omega : 0 < 4 * globalS Bmax)
  change I.width < 4 * globalS Bmax * (I.delta + 1) at hd
  nlinarith

theorem SolveBox.volume_width {n Bmax : ℕ} (I : SolveBox n Bmax) :
    volume I.b I.a ≤ n * I.width := by
  calc
    _ ≤ ∑ _i : Fin n, I.width := Finset.sum_le_sum (fun i _ => (Int.toNat_le).mpr (I.width_bound i))
    _ = _ := by simp

theorem SolveBox.tightening_passes {n Bmax : ℕ} (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) : volume I.b I.a / I.delta ≤ 8 * n * globalS Bmax := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul (I.delta_positive hB)).mpr
  have hm := Nat.mul_le_mul_left n (I.delta_lower hB)
  have hv := I.volume_width
  have hd := I.delta_positive hB
  nlinarith

theorem SolveBox.C_potential {n Bmax : ℕ} (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) :
    widthPotential (globalS Bmax) I.C < widthPotential (globalS Bmax) I.width := by
  apply widthPotential_decreases (by have hh := globalS_large Bmax; omega)
    I.C_positive (I.C_smaller hB)
  have h := I.delta_lower hB
  have hd := I.delta_smaller
  have he : I.width - I.C = I.delta := by unfold SolveBox.C; omega
  simpa only [he, Nat.mul_assoc] using h

namespace CountedAlgorithm

theorem bounded_tighten_global {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {N : ℕ} (hN : LowerBound lower N)
    (I : SolveBox n Bmax) (hB : 128 * globalS Bmax < I.width) :
    (tighten P hR lower I hB).Bounded ((16 * n * globalS Bmax + 2) * globalJ n Bmax * N) := by
  apply Counted.bounded_mono (bounded_tighten P hR lower hN I hB)
  calc
    _ ≤ (8 * n * globalS Bmax + 1) * (2 * globalJ n Bmax * N) :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_right (I.tightening_passes hB) 1)
    _ = _ := by ring

theorem bounded_finishChoice (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (hR : 1 ≤ P.parameter) (lower : LowerSolver (Bmax := Bmax) P) {N : ℕ} (hN : LowerBound lower N)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width) (O : Orientation P)
    (up : Counted (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : Counted (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le)))
    {M : ℕ} (hu : up.Bounded M) (hl : lo.Bounded M) :
    (finishChoice G P hR lower I hB O up lo).Bounded
      (O.exceptions.length * (globalJ G.n Bmax * N) + M) := by
  unfold finishChoice
  split_ifs
  · exact Counted.bounded_bind _
      (Counted.bounded_traverse _ (fun H => I.bounded_repeated (hN _ _ _) _) _)
      (fun _ => Counted.bounded_map _ hu)
  · exact Counted.bounded_bind _
      (Counted.bounded_traverse _ (fun H => I.bounded_repeated (hN _ _ _) _) _)
      (fun _ => Counted.bounded_map _ hl)

end CountedAlgorithm
end MeanPayoff
end

end OAI
