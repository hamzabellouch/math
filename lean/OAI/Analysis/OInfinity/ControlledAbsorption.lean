import OAI.Analysis.OInfinity.BufferedPaths
import OAI.Analysis.OInfinity.IncompleteBinaryPath

namespace OAI

/-! # Controlled paths for the concrete absorption unitary

The two-swap Fock completion has its actual `4π` path. The absorption
polynomial is `2`-Lipschitz on unitaries. Consequently its path bound
depends on the fixed anchor, independently of the requested Fock error.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

lemma BufferAbsorptionCorner.rotation_sub_norm_le [Nontrivial E]
    (D : BufferAbsorptionCorner E) (u v : unitary E) :
    ‖(D.rotation u : E) - D.rotation v‖ ≤ ‖(u : E) - v‖ := by
  have hwn : ‖D.w‖ ≤ 1 := by
    have h := congrArg norm D.w_gram
    rw [CStarRing.norm_star_mul_self, norm_one] at h
    nlinarith [norm_nonneg D.w]
  have hrn : ‖D.remainder‖ ≤ 1 := by
    have h := congrArg norm D.remainder_range
    rw [CStarRing.norm_self_mul_star, norm_one] at h
    nlinarith [norm_nonneg D.remainder]
  have he : (D.rotation u : E) - D.rotation v =
      D.w * ((u : E) - v) * D.remainder := by
    change D.rotationValue u - D.rotationValue v = _
    unfold BufferAbsorptionCorner.rotationValue
    noncomm_ring
  rw [he]
  calc
    _ ≤ ‖D.w‖ * ‖(u : E) - v‖ * ‖D.remainder‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖(u : E) - v‖ * 1 := by gcongr
    _ = _ := by ring

lemma BufferAbsorptionCorner.absorption_sub_norm_le [Nontrivial E]
    (D : BufferAbsorptionCorner E) (u v : unitary E) :
    ‖(D.absorption u : E) - D.absorption v‖ ≤ 2 * ‖(u : E) - v‖ := by
  have he : (D.absorption u : E) - D.absorption v =
      (D.rotation u : E) * (star (u : E) - star (v : E)) +
        ((D.rotation u : E) - D.rotation v) * star (v : E) := by
    change (D.rotation u : E) * star (u : E) -
      (D.rotation v : E) * star (v : E) = _
    noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(D.rotation u : E) * (star (u : E) - star (v : E))‖ +
        ‖((D.rotation u : E) - D.rotation v) * star (v : E)‖ := norm_add_le _ _
    _ = ‖(u : E) - v‖ + ‖(D.rotation u : E) - D.rotation v‖ := by
      rw [CStarRing.norm_coe_unitary_mul, ← star_sub, norm_star]
      change _ + ‖((D.rotation u : E) - D.rotation v) * (star v : unitary E)‖ = _
      rw [CStarRing.norm_mul_coe_unitary]
    _ ≤ 2 * ‖(u : E) - v‖ := by
      have h := D.rotation_sub_norm_le u v
      linarith

/-- Multiply the fixed anchor path by the normalized absorption path. -/
lemma BufferAbsorptionCorner.controlled_absorption_path [Nontrivial E]
    (D : BufferAbsorptionCorner E) (L K : ℝ)
    (p₀ : Path (1 : unitary E) D.anchor)
    (hp₀ : ∀ a b, ‖(p₀ a : E) - p₀ b‖ ≤ L * |(a : ℝ) - b|)
    (u : unitary E) (p : Path (1 : unitary E) u)
    (hp : ∀ a b, ‖(p a : E) - p b‖ ≤ K * |(a : ℝ) - b|) :
    ∃ q : Path (1 : unitary E) (D.absorption u),
      ∀ a b, ‖(q a : E) - q b‖ ≤ (L + 2 * K) * |(a : ℝ) - b| := by
  let r : Path (1 : unitary E) (star D.anchor * D.absorption u) := {
    toFun a := star D.anchor * D.absorption (p a)
    continuous_toFun := continuous_const.mul (D.absorption_continuous.comp p.continuous)
    source' := by simp only [p.source, BufferAbsorptionCorner.absorption,
      BufferAbsorptionCorner.anchor, star_one, mul_one, Unitary.star_mul_self]
    target' := by rw [p.target] }
  have hr (a b : unitInterval) :
      ‖(r a : E) - r b‖ ≤ (2 * K) * |(a : ℝ) - b| := by
    change ‖(star D.anchor : E) * (D.absorption (p a) : E) -
      (star D.anchor : E) * (D.absorption (p b) : E)‖ ≤ _
    rw [← mul_sub]
    change ‖((star D.anchor : unitary E) : E) *
      ((D.absorption (p a) : E) - D.absorption (p b))‖ ≤ _
    rw [CStarRing.norm_coe_unitary_mul]
    calc
      _ ≤ 2 * ‖(p a : E) - p b‖ := D.absorption_sub_norm_le (p a) (p b)
      _ ≤ 2 * (K * |(a : ℝ) - b|) := mul_le_mul_of_nonneg_left (hp a b) (by norm_num)
      _ = _ := by ring
  have hend : D.absorption u = D.anchor * (star D.anchor * D.absorption u) := by
    rw [← mul_assoc, Unitary.mul_star_self, one_mul]
  refine ⟨(p₀.mul r).cast (by simp) hend, ?_⟩
  exact unitaryPath_mul_sub_norm_le p₀ r L (2 * K) hp₀ hr

/-- The actual Fock completion gives a path cost independent of its accuracy. -/
lemma BufferAbsorptionCorner.exists_controlled_vacuum_absorption_on [Nontrivial E]
    (D : BufferAbsorptionCorner E) (s t : I → E) (r z : E) (P : I → Prop)
    (hrr : star r * r = 1) (hr : ∀ i, star r * s i = 0)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hzz : star z * z = 1) (hqz : D.q * z = 0)
    (hzr : star z * r = 0) (hzs : ∀ i, star z * s i = 0)
    (htq : ∀ i, t i * D.q = t i) (ht : ∑ i, t i * star (t i) = D.q)
    (htt : ∀ i j, star (t i) * t j = if i = j then D.q else 0)
    (hat : ∀ i, P i → Commute (star D.a) (t i))
    (hbt : ∀ i, P i → Commute (star D.b) (t i))
    (L : ℝ) (p₀ : Path (1 : unitary E) D.anchor)
    (hp₀ : ∀ a b, ‖(p₀ a : E) - p₀ b‖ ≤ L * |(a : ℝ) - b|)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ W : unitary E,
      (∃ p : Path (1 : unitary E) W,
        ∀ a b, ‖(p a : E) - p b‖ ≤ (L + 8 * Real.pi) * |(a : ℝ) - b|) ∧
      ∀ i, P i → ‖(W : E) * s i - (t i + D.w * s i * star D.w) * (W : E)‖ < ε := by
  let δ := ε / 6
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / δ ^ 2)
  have hsmall : 2 / ((m : ℝ) + 1) < δ ^ 2 := by
    have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
    have hm' : 2 < (m : ℝ) * δ ^ 2 := (div_lt_iff₀ hδsq).mp hm
    apply (div_lt_iff₀ (by positivity : 0 < (m : ℝ) + 1)).mpr
    nlinarith
  let v := finiteRowIsometry s t r D.q m
  have hvg : star v * v = D.q := finiteRowIsometry_gram s t r D.q
    D.projection.isIdempotentElem.eq D.projection.isSelfAdjoint.star_eq hrr hr hs htq ht m
  have hvq : v * D.q = v := relativeIsometry_mul_support v D.q hvg
    D.projection.isSelfAdjoint.star_eq D.projection.isIdempotentElem.eq
  have hvz : star v * z = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star
      (finiteRowIsometry_unused s t r D.q z hzr hzs m)
  obtain ⟨u, huv, p, hp⟩ := exists_controlled_unitary_extension v z
    (by rw [mul_assoc, hvg, hvq]) hzz (by rw [hvg]; exact hqz)
    (by rw [mul_assoc, hvz, mul_zero])
  have huq : (u : E) * D.q = v := by simpa only [hvg] using huv
  have hvn : ‖v‖ ≤ 1 := finiteRowIsometry_norm_le s t r D.q
    D.projection.isIdempotentElem.eq D.projection.isSelfAdjoint.star_eq hrr hr hs htq ht m
  obtain ⟨q, hq⟩ := D.controlled_absorption_path L (4 * Real.pi) p₀ hp₀ u p hp
  refine ⟨D.absorption u, ⟨q, ?_⟩, ?_⟩
  · simpa only [show L + 2 * (4 * Real.pi) = L + 8 * Real.pi by ring] using hq
  · intro i hi
    have hf : ‖s i * v - v * t i‖ < δ := by
      have h := finiteRowIsometry_forward_norm_sq s t r D.q
        D.projection.isIdempotentElem.eq D.projection.isSelfAdjoint.star_eq
        hrr hr hs htq ht htt m i
      change ‖s i * v - v * t i‖ ^ 2 ≤ _ at h
      nlinarith [norm_nonneg (s i * v - v * t i)]
    have hb : ‖star v * s i - t i * star v‖ < δ := by
      have h := finiteRowIsometry_backward_norm_sq s t r D.q
        D.projection.isIdempotentElem.eq D.projection.isSelfAdjoint.star_eq
        hrr hr hs htq ht htt m i
      have he : star v * s i - t i * star v =
          star (star (s i) * v - v * star (t i)) := by
        simp only [star_sub, star_mul, star_star]
      rw [he, norm_star]
      have hone : ((m : ℝ) + 1)⁻¹ ≤ 2 / ((m : ℝ) + 1) := by
        rw [← one_div]
        exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
      change ‖star (s i) * v - v * star (t i)‖ ^ 2 ≤ _ at h
      nlinarith [norm_nonneg (star (s i) * v - v * star (t i))]
    calc
      _ ≤ 2 * ‖s i * v - v * t i‖ + 3 * ‖star v * s i - t i * star v‖ :=
        D.absorption_error_bound u v (s i) (t i) huq (htq i) (hat i hi) (hbt i hi) hvn
      _ < ε := by dsimp only [δ] at hf hb; linarith


/-- The selected proper target row inherits the same accuracy-independent bound. -/
lemma BufferAbsorptionCorner.exists_controlled_proper_vacuum_absorption [Nontrivial E]
    (D : BufferAbsorptionCorner E) (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (n : ℕ) (hqz : D.q * s (n + 2) = 0)
    (hqt : ∀ i, Commute D.q (t i))
    (hat : ∀ i, Commute (star D.a) (t i))
    (hbt : ∀ i, Commute (star D.b) (t i))
    (L : ℝ) (p₀ : Path (1 : unitary E) D.anchor)
    (hp₀ : ∀ a b, ‖(p₀ a : E) - p₀ b‖ ≤ L * |(a : ℝ) - b|)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : unitary E,
      (∃ p : Path (1 : unitary E) U,
        ∀ a b, ‖(p a : E) - p b‖ ≤ (L + 8 * Real.pi) * |(a : ℝ) - b|) ∧
      ∀ i : Fin n,
        ‖(U : E) * s i * star (U : E) -
          (t i * D.q + D.w * s i * star D.w)‖ < ε := by
  let x : Fin (n + 1) → E := fun i => t i * D.q
  have hxs (i : Fin (n + 1)) : D.q * x i = x i ∧ x i * D.q = x i := by
    constructor
    · change D.q * (t i * D.q) = t i * D.q
      rw [← mul_assoc, (hqt i).eq, mul_assoc, D.projection.isIdempotentElem.eq]
    · change (t i * D.q) * D.q = t i * D.q
      rw [mul_assoc, D.projection.isIdempotentElem.eq]
  have hx (i j : Fin (n + 1)) : star (x i) * x j = if i = j then D.q else 0 := by
    change star (t i * D.q) * (t j * D.q) = _
    rw [star_mul, D.projection.isSelfAdjoint.star_eq]
    calc
      _ = D.q * (star (t i) * t j) * D.q := by noncomm_ring
      _ = _ := by
        by_cases hij : i = j
        · subst j
          simp only [ht, ite_true, mul_one, D.projection.isIdempotentElem.eq]
        · rw [ht, ite_eq_right (fun h => hij (Fin.ext h)),
            ite_eq_right hij, mul_zero, zero_mul]
  obtain ⟨T, hTx, hTq, hT, hTs⟩ := D.extend_finite_proper_row n x hxs hx
  let S : Fin (n + 1) → E := Fin.cons (s n) (fun i : Fin n => s i)
  have hS (i j : Fin (n + 1)) : star (S i) * S j = if i = j then 1 else 0 := by
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [S, Fin.cons_zero, ite_true] using hs n n
    · have hne : n ≠ (j : ℕ) := by omega
      simpa only [S, Fin.cons_zero, Fin.cons_succ, hne, ite_false,
        (Fin.succ_ne_zero j).symm] using hs n j
    · have hne : (i : ℕ) ≠ n := by omega
      simpa only [S, Fin.cons_zero, Fin.cons_succ, hne, ite_false,
        Fin.succ_ne_zero] using hs i n
    · simpa only [S, Fin.cons_succ, Fin.succ_inj, Fin.ext_iff,
        Fin.val_succ, Nat.succ.injEq] using hs i j
  have hroot (i : Fin (n + 1)) : star (s (n + 1)) * S i = 0 := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [S, Fin.cons_zero, Nat.add_one_ne_self, ite_false] using hs (n + 1) n
    · have hne : n + 1 ≠ (j : ℕ) := by omega
      simpa only [S, Fin.cons_succ, hne, ite_false] using hs (n + 1) j
  have hspare (i : Fin (n + 1)) : star (s (n + 2)) * S i = 0 := by
    refine Fin.cases ?_ (fun j => ?_) i
    · have hne : n + 2 ≠ n := by omega
      simpa only [S, Fin.cons_zero, hne, ite_false] using hs (n + 2) n
    · have hne : n + 2 ≠ (j : ℕ) := by omega
      simpa only [S, Fin.cons_succ, hne, ite_false] using hs (n + 2) j
  have haT (i : Fin (n + 1)) (hi : 0 < (i : ℕ)) : Commute (star D.a) (T i) := by
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro h; exact (Nat.lt_irrefl 0 h).elim
    · intro _
      rw [hTx]
      change Commute (star D.a) (t j * D.q)
      exact (hat j).mul_right (D.a_star_right.trans D.a_star_left.symm)
  have hbT (i : Fin (n + 1)) (hi : 0 < (i : ℕ)) : Commute (star D.b) (T i) := by
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro h; exact (Nat.lt_irrefl 0 h).elim
    · intro _
      rw [hTx]
      change Commute (star D.b) (t j * D.q)
      exact (hbt j).mul_right (D.b_star_right.trans D.b_star_left.symm)
  obtain ⟨U, hU, hUi⟩ := D.exists_controlled_vacuum_absorption_on S T (s (n + 1)) (s (n + 2))
    (fun i => 0 < (i : ℕ))
    (by simpa only [ite_true] using hs (n + 1) (n + 1)) hroot hS
    (by simpa only [ite_true] using hs (n + 2) (n + 2)) hqz
    (by rw [hs, ite_eq_right (by omega)]) hspare
    (fun i => (hTq i).2) hTs hT haT hbT L p₀ hp₀ ε hε
  refine ⟨U, hU, fun i => ?_⟩
  have hi := hUi i.succ (by simp)
  rw [hTx] at hi
  change ‖(U : E) * s i - (x i.castSucc + D.w * s i * star D.w) * (U : E)‖ < ε at hi
  have hmul : ((U : E) * s i - (x i.castSucc + D.w * s i * star D.w) * (U : E)) *
      star (U : E) = (U : E) * s i * star (U : E) -
        (x i.castSucc + D.w * s i * star D.w) := by
    rw [sub_mul, mul_assoc _ (U : E), Unitary.mul_star_self_of_mem U.property, mul_one]
  have hnorm := CStarRing.norm_mul_mem_unitary
    ((U : E) * s i - (x i.castSucc + D.w * s i * star D.w) * (U : E))
    (Unitary.star_mem U.property)
  rw [hmul] at hnorm
  have hc : ‖(U : E) * s i * star (U : E) -
      (x i.castSucc + D.w * s i * star D.w)‖ < ε := by
    rw [hnorm]
    exact hi
  simpa only [x, Fin.val_castSucc] using hc



/-- The concrete canonical corner has a single path bound for every depth
and every requested final error. The exact terminal representation remains
in the target of the estimate. -/
lemma exists_canonical_uniform_buffered_paths [Nontrivial E]
    (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hst : bergRowsCommute s t) (n : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ D : BufferAbsorptionCorner E, D.q ≠ 0 ∧
      (∀ i : Fin (n + 1), ‖s i * D.q - D.q * s i‖ < κ) ∧
      (∀ i : Fin (n + 1),
        ‖D.q * s i * D.q - zeroCornerRow D.q D.a D.b n i‖ < κ) ∧
      ∃ L : ℝ, 0 ≤ L ∧ ∀ (m : ℕ) (ε : ℝ), 0 < ε →
        ∃ v : unitary E,
          (∀ i : Fin n, ‖(v : E) * s i * star (v : E) -
            bufferedAbsorptionValue D.w (t i) (s i) m‖ < ε) ∧
          ∃ p : Path (1 : unitary E) v,
            ∀ a b, ‖(p a : E) - p b‖ ≤ L * |(a : ℝ) - b| := by
  obtain ⟨D, hanchor, hqne, hqz, hqc, hcomp, ⟨z, hz, hqz'⟩, hcomm⟩ :=
    exists_canonical_connected_absorption_corner_with_isometry s hs n κ hκ
  have htc (i : ℕ) : ∀ j, Commute (s j) (t i) ∧ Commute (star (s j)) (t i) := by
    intro j
    exact ⟨(hst j i).1, by simpa only [star_star] using (hst j i).2.star_star⟩
  have htcs (i : ℕ) : ∀ j, Commute (s j) (star (t i)) ∧
      Commute (star (s j)) (star (t i)) := by
    intro j
    exact ⟨(hst j i).2, (hst j i).1.star_star⟩
  have hqt (i : ℕ) := (hcomm (t i) (htc i)).1
  have hat (i : ℕ) : Commute (star D.a) (t i) := by
    simpa only [star_star] using (hcomm (star (t i)) (htcs i)).2.2.1.star_star
  have hbt (i : ℕ) : Commute (star D.b) (t i) := by
    simpa only [star_star] using (hcomm (star (t i)) (htcs i)).2.2.2.star_star
  have htw (i : ℕ) : Commute (t i) D.w := (hcomm (t i) (htc i)).2.1.symm
  have htsw (i : ℕ) : Commute (t i) (star D.w) := by
    simpa only [star_star] using (hcomm (star (t i)) (htcs i)).2.1.star_star.symm
  have hswq : star D.w * D.q = 0 := by
    have heq : D.q = 1 - D.w * star D.w := by rw [D.w_range]; abel
    rw [heq, mul_sub, mul_one, ← mul_assoc, D.w_gram, one_mul, sub_self]
  have hswz : star D.w * z = 0 := by
    calc
      _ = star D.w * (D.q * z) := by rw [hqz']
      _ = (star D.w * D.q) * z := by rw [mul_assoc]
      _ = 0 := by rw [hswq, zero_mul]
  obtain ⟨L₀, hL₀, p₀, hp₀⟩ := exists_lipschitz_joined_unitary_path D.anchor hanchor
  refine ⟨D, hqne, hqc, hcomp, 9 * Real.pi + (L₀ + 8 * Real.pi), by positivity,
    fun m ε hε => ?_⟩
  let η := ε / ((m : ℝ) + 1)
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨u, ⟨p, hp⟩, hui⟩ := D.exists_controlled_proper_vacuum_absorption
    s t hs ht n hqz hqt hat hbt L₀ p₀ hp₀ η hη
  have hpaths := exists_uniform_bufferedIteration_paths s hs D.w z D.w_gram hz hswz
    u (L₀ + 8 * Real.pi) (by positivity) p hp
  obtain ⟨q, hq⟩ := hpaths m
  refine ⟨bufferedIterationUnitary D.w D.w_gram u m, ?_, q, hq⟩
  intro i
  have hstep (j : Fin n) : ‖(u : E) * s j * star (u : E) -
      bufferedAbsorptionValue D.w (t j) (s j) 1‖ ≤ η := by
    simpa only [bufferedAbsorptionValue_one, D.w_range, sub_sub_cancel] using (hui j).le
  have hb := bufferedIterationUnitary_error (fun i : Fin n => s i) (fun i : Fin n => t i)
    D.w D.w_gram (fun i => htw i) (fun i => htsw i) u η hstep m i
  apply hb.trans_lt
  have hid : ((m : ℝ) + 1) * η = ε := by
    dsimp only [η]
    field_simp
  nlinarith

end WeakPureInfiniteness

end

end OAI
