import OAI.Analysis.OInfinity.JointCycleIdentity

namespace OAI

/-! # Binary fragmentation and cancellation of localized unitaries

This is the finite path calculation underlying Brin's baker-map
fragmentation argument (2009, Lemma 1, steps 4--5). The binary row here is
coisometric in its unit. It is not the incomplete canonical row in O∞.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

def binaryCornerUnitary (a : E) (ha : star a * a = 1) (u : unitary E) : unitary E :=
  ⟨cornerCompression a u, cornerCompression_mem 1 a u (by simp) ha (mul_one a)
    (one_mul _) (mul_one _) u.property.1 u.property.2⟩

lemma binaryCornerUnitary_one (a : E) (ha : star a * a = 1) :
    binaryCornerUnitary a ha 1 = 1 := by
  apply Subtype.ext
  exact cornerCompression_unit 1 a (mul_one a)

lemma binaryCornerUnitary_mul (a : E) (ha : star a * a = 1) (u v : unitary E) :
    binaryCornerUnitary a ha (u * v) =
      binaryCornerUnitary a ha u * binaryCornerUnitary a ha v := by
  apply Subtype.ext
  exact (cornerCompression_mul 1 a u v ha (mul_one a) (mul_one _)).symm

lemma binaryCornerUnitary_star (a : E) (ha : star a * a = 1) (u : unitary E) :
    binaryCornerUnitary a ha (star u) = star (binaryCornerUnitary a ha u) := by
  apply Subtype.ext
  exact (cornerCompression_star a u).symm

lemma binaryCornerUnitary_continuous (a : E) (ha : star a * a = 1) :
    Continuous (binaryCornerUnitary a ha) := by
  apply Continuous.subtype_mk
  change Continuous (fun u : unitary E => a * (u : E) * star a + (1 - a * star a))
  fun_prop

lemma binaryCornerUnitary_sub_norm_le (a : E) (ha : star a * a = 1)
    (u v : unitary E) :
    ‖(binaryCornerUnitary a ha u : E) - binaryCornerUnitary a ha v‖ ≤ ‖(u : E) - v‖ := by
  have hna : ‖a‖ ≤ 1 := by
    have hn1 : ‖(1 : E)‖ ≤ 1 := by
      have h := congrArg norm (show star (1 : E) * 1 = 1 by simp)
      rw [CStarRing.norm_star_mul_self] at h
      nlinarith [norm_nonneg (1 : E)]
    have h := congrArg norm ha
    rw [CStarRing.norm_star_mul_self] at h
    nlinarith [norm_nonneg a]
  have he : (binaryCornerUnitary a ha u : E) - binaryCornerUnitary a ha v =
      a * ((u : E) - v) * star a := by
    change cornerCompression a u - cornerCompression a v = _
    unfold cornerCompression
    noncomm_ring
  rw [he]
  calc
    _ ≤ ‖a‖ * ‖(u : E) - v‖ * ‖a‖ := by
      simpa only [norm_star] using
        (norm_mul_le (a * ((u : E) - v)) (star a)).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖(u : E) - v‖ * 1 := by gcongr
    _ = _ := by ring

def binaryCornerPath (a : E) (ha : star a * a = 1) {u v : unitary E} (p : Path u v) :
    Path (binaryCornerUnitary a ha u) (binaryCornerUnitary a ha v) :=
  p.map (binaryCornerUnitary_continuous a ha)

lemma binaryCornerPath_sub_norm_le (a : E) (ha : star a * a = 1)
    {u v : unitary E} (p : Path u v) (L : ℝ)
    (hp : ∀ t s, ‖(p t : E) - p s‖ ≤ L * |(t : ℝ) - s|) (t s : unitInterval) :
    ‖(binaryCornerPath a ha p t : E) - binaryCornerPath a ha p s‖ ≤
      L * |(t : ℝ) - s| :=
  (binaryCornerUnitary_sub_norm_le a ha (p t) (p s)).trans (hp t s)

lemma binaryCornerUnitary_comp (a b : E) (ha : star a * a = 1)
    (hb : star b * b = 1) (hab : star (a * b) * (a * b) = 1) (u : unitary E) :
    binaryCornerUnitary a ha (binaryCornerUnitary b hb u) =
      binaryCornerUnitary (a * b) hab u := by
  apply Subtype.ext
  change cornerCompression a (cornerCompression b u) = cornerCompression (a * b) u
  simp only [cornerCompression, star_mul]
  noncomm_ring

lemma binaryProduct_isometry (a b : E) (ha : star a * a = 1) (hb : star b * b = 1) :
    star (a * b) * (a * b) = 1 := by
  rw [star_mul]
  calc
    _ = star b * (star a * a) * b := by noncomm_ring
    _ = 1 := by rw [ha, mul_one, hb]

lemma binaryCornerUnitary_commute (a b : E) (ha : star a * a = 1)
    (hb : star b * b = 1) (hab : star a * b = 0) (u v : unitary E) :
    Commute (binaryCornerUnitary a ha u) (binaryCornerUnitary b hb v) := by
  apply Subtype.ext
  change cornerCompression a u * cornerCompression b v =
    cornerCompression b v * cornerCompression a u
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  rw [cornerCompression_pair_product a b u v hab,
    cornerCompression_pair_product b a v u hba]
  abel

/-- Cancelling two disjoint copies has a fixed path cost, independent of `u`. -/
lemma exists_binaryCornerCancellation (a b : E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hab : star a * b = 0)
    (u : unitary E) :
    ∃ p : Path (binaryCornerUnitary a ha u * binaryCornerUnitary b hb (star u)) 1,
      ∀ t s, ‖(p t : E) - p s‖ ≤ (2 * Real.pi) * |(t : ℝ) - s| := by
  obtain ⟨v, hv, hv0, hv1, hbound⟩ := exists_controlled_cornerCancellation_path
    1 a b u (by simp) ha hb hab (mul_one a) (mul_one b)
    (one_mul _) (mul_one _) u.property.1 u.property.2
  let p := unitaryQuarterPath v hv
  have h0 : binaryCornerUnitary a ha u * binaryCornerUnitary b hb (star u) = v 0 := by
    apply Subtype.ext
    exact hv0.symm
  have h1 : (1 : unitary E) = v (Real.pi / 2) := by
    apply Subtype.ext
    exact hv1.symm
  exact ⟨p.cast h0 h1, unitaryQuarterPath_sub_norm_le v hv hbound⟩

/-- A constant multiplier changes neither the speed nor endpoints' precision. -/
lemma binaryPath_mul_const_sub_norm_le {u v : unitary E} (p : Path u v)
    (c : unitary E) (L : ℝ)
    (hp : ∀ t s, ‖(p t : E) - p s‖ ≤ L * |(t : ℝ) - s|) (t s : unitInterval) :
    ‖((p.mul (Path.refl c)) t : E) - (p.mul (Path.refl c)) s‖ ≤
      L * |(t : ℝ) - s| := by
  change ‖(p t : E) * c - (p s : E) * c‖ ≤ _
  rw [← sub_mul, CStarRing.norm_mul_coe_unitary]
  exact hp t s

lemma binaryPath_symm_sub_norm_le {u v : unitary E} (p : Path u v) (L : ℝ)
    (hp : ∀ t s, ‖(p t : E) - p s‖ ≤ L * |(t : ℝ) - s|) (t s : unitInterval) :
    ‖(p.symm t : E) - p.symm s‖ ≤ L * |(t : ℝ) - s| := by
  change ‖(p (unitInterval.symm t) : E) - p (unitInterval.symm s)‖ ≤ _
  have h := hp (unitInterval.symm t) (unitInterval.symm s)
  have he : |((unitInterval.symm t : unitInterval) : ℝ) - unitInterval.symm s| =
      |(t : ℝ) - s| := by
    rw [unitInterval.coe_symm_eq, unitInterval.coe_symm_eq,
      show (1 - (t : ℝ)) - (1 - s) = -((t : ℝ) - s) by ring, abs_neg]
  simpa only [he] using h

/-- One proper localized copy contracts using the splitting path in its
parent and two disjoint-copy cancellations. No approximate commutation is
needed. This is the finite content of Brin's small-rectangle argument. -/
lemma exists_binaryQuarter_path (a b A B : E)
    (ha : star a * a = 1) (hb : star b * b = 1)
    (hA : star A * A = 1) (hB : star B * B = 1) (hAB : star A * B = 0)
    (u : unitary E) (L : ℝ) (hL : 0 ≤ L)
    (p : Path u (binaryCornerUnitary a ha u * binaryCornerUnitary b hb u))
    (hp : ∀ t s, ‖(p t : E) - p s‖ ≤ L * |(t : ℝ) - s|) :
    ∃ r : Path (binaryCornerUnitary (A * a) (binaryProduct_isometry A a hA ha) u) 1,
      ∀ t s, ‖(r t : E) - r s‖ ≤ (4 * (L + 2 * Real.pi)) * |(t : ℝ) - s| := by
  let R := A * a
  let S := A * b
  have hR : star R * R = 1 := binaryProduct_isometry A a hA ha
  have hS : star S * S = 1 := binaryProduct_isometry A b hA hb
  have hSB : star S * B = 0 := by
    dsimp only [S]
    rw [star_mul, mul_assoc, hAB, mul_zero]
  let uR := binaryCornerUnitary R hR u
  let uS := binaryCornerUnitary S hS u
  let uB := binaryCornerUnitary B hB (star u)
  obtain ⟨c₁, hc₁⟩ := exists_binaryCornerCancellation A B hA hB hAB u
  obtain ⟨c₂, hc₂⟩ := exists_binaryCornerCancellation S B hS hB hSB u
  have he : binaryCornerUnitary A hA
      (binaryCornerUnitary a ha u * binaryCornerUnitary b hb u) * uB = uR * uS * uB := by
    rw [binaryCornerUnitary_mul, binaryCornerUnitary_comp A a hA ha hR,
      binaryCornerUnitary_comp A b hA hb hS]
  let d₀ := (binaryCornerPath A hA p).mul (Path.refl uB)
  let d : Path (binaryCornerUnitary A hA u * uB) (uR * uS * uB) := d₀.cast rfl he.symm
  let e₀ := (Path.refl uR).mul c₂
  let e : Path (uR * uS * uB) uR := e₀.cast (mul_assoc _ _ _) (mul_one _).symm
  have hd : ∀ t s, ‖(d t : E) - d s‖ ≤ L * |(t : ℝ) - s| := by
    intro t s
    exact binaryPath_mul_const_sub_norm_le (binaryCornerPath A hA p) uB L
      (binaryCornerPath_sub_norm_le A hA p L hp) t s
  have heBound : ∀ t s, ‖(e t : E) - e s‖ ≤ (2 * Real.pi) * |(t : ℝ) - s| := by
    intro t s
    change ‖(uR : E) * (c₂ t : E) - (uR : E) * (c₂ s : E)‖ ≤ _
    rw [← mul_sub, CStarRing.norm_coe_unitary_mul]
    exact hc₂ t s
  let K := L + 2 * Real.pi
  have hLK : L ≤ K := by dsimp only [K]; linarith [Real.pi_pos]
  have hpiK : 2 * Real.pi ≤ K := by dsimp only [K]; linarith
  have hdK : ∀ t s, ‖(d.symm t : E) - d.symm s‖ ≤ K * |(t : ℝ) - s| := by
    intro t s
    exact (binaryPath_symm_sub_norm_le d L hd t s).trans
      (mul_le_mul_of_nonneg_right hLK (abs_nonneg _))
  have hcK : ∀ t s, ‖(c₁ t : E) - c₁ s‖ ≤ K * |(t : ℝ) - s| := by
    intro t s
    exact (hc₁ t s).trans (mul_le_mul_of_nonneg_right hpiK (abs_nonneg _))
  let f := d.symm.trans c₁
  have hf : ∀ t s, ‖(f t : E) - f s‖ ≤ (2 * K) * |(t : ℝ) - s| :=
    unitaryPath_trans_sub_norm_le d.symm c₁ K hdK hcK
  have heK : ∀ t s, ‖(e.symm t : E) - e.symm s‖ ≤ (2 * K) * |(t : ℝ) - s| := by
    intro t s
    apply (binaryPath_symm_sub_norm_le e (2 * Real.pi) heBound t s).trans
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    dsimp only [K]
    linarith [Real.pi_pos]
  refine ⟨e.symm.trans f, ?_⟩
  intro t s
  simpa only [K, show 2 * (2 * (L + 2 * Real.pi)) = 4 * (L + 2 * Real.pi) by ring] using
    unitaryPath_trans_sub_norm_le e.symm f (2 * K) heK hf t s

/-- Binary fragmentation reduces a splitting path to a contraction with
a uniform linear bound on its speed. The only input path is from the
unitary to its two compressed copies. -/
lemma exists_binaryFragmentation_path (a b : E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hab : star a * b = 0)
    (u : unitary E) (L : ℝ) (hL : 0 ≤ L)
    (p : Path u (binaryCornerUnitary a ha u * binaryCornerUnitary b hb u))
    (hp : ∀ t s, ‖(p t : E) - p s‖ ≤ L * |(t : ℝ) - s|) :
    ∃ r : Path u 1,
      ∀ t s, ‖(r t : E) - r s‖ ≤ (32 * (L + 2 * Real.pi)) * |(t : ℝ) - s| := by
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  let p' : Path u (binaryCornerUnitary b hb u * binaryCornerUnitary a ha u) :=
    p.cast rfl (binaryCornerUnitary_commute a b ha hb hab u u).eq.symm
  have hp' : ∀ t s, ‖(p' t : E) - p' s‖ ≤ L * |(t : ℝ) - s| := hp
  obtain ⟨rAA, hAA⟩ := exists_binaryQuarter_path a b a b ha hb ha hb hab u L hL p hp
  obtain ⟨rAB, hAB⟩ := exists_binaryQuarter_path b a a b hb ha ha hb hab u L hL p' hp'
  obtain ⟨rBA, hBA⟩ := exists_binaryQuarter_path a b b a ha hb hb ha hba u L hL p hp
  obtain ⟨rBB, hBB⟩ := exists_binaryQuarter_path b a b a hb ha hb ha hba u L hL p' hp'
  let f := binaryCornerUnitary a ha u * binaryCornerUnitary b hb u
  let U :=
    (binaryCornerUnitary (a * a) (binaryProduct_isometry a a ha ha) u *
      binaryCornerUnitary (a * b) (binaryProduct_isometry a b ha hb) u) *
    (binaryCornerUnitary (b * a) (binaryProduct_isometry b a hb ha) u *
      binaryCornerUnitary (b * b) (binaryProduct_isometry b b hb hb) u)
  have hU : U = binaryCornerUnitary a ha f * binaryCornerUnitary b hb f := by
    dsimp only [U, f]
    rw [binaryCornerUnitary_mul, binaryCornerUnitary_mul,
      binaryCornerUnitary_comp a a ha ha (binaryProduct_isometry a a ha ha),
      binaryCornerUnitary_comp a b ha hb (binaryProduct_isometry a b ha hb),
      binaryCornerUnitary_comp b a hb ha (binaryProduct_isometry b a hb ha),
      binaryCornerUnitary_comp b b hb hb (binaryProduct_isometry b b hb hb)]
  let liftP : Path f U :=
    ((binaryCornerPath a ha p).mul (binaryCornerPath b hb p)).cast rfl hU
  have hLift : ∀ t s, ‖(liftP t : E) - liftP s‖ ≤ (2 * L) * |(t : ℝ) - s| := by
    intro t s
    change ‖(((binaryCornerPath a ha p).mul (binaryCornerPath b hb p)) t : E) -
      ((binaryCornerPath a ha p).mul (binaryCornerPath b hb p)) s‖ ≤ _
    simpa only [show L + L = 2 * L by ring] using
      unitaryPath_mul_sub_norm_le (binaryCornerPath a ha p) (binaryCornerPath b hb p)
        L L (binaryCornerPath_sub_norm_le a ha p L hp)
        (binaryCornerPath_sub_norm_le b hb p L hp) t s
  have hp₂ : ∀ t s, ‖(p t : E) - p s‖ ≤ (2 * L) * |(t : ℝ) - s| := by
    intro t s
    exact (hp t s).trans (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
  let first : Path u U := p.trans liftP
  have hFirst : ∀ t s, ‖(first t : E) - first s‖ ≤ (4 * L) * |(t : ℝ) - s| := by
    intro t s
    simpa only [show 2 * (2 * L) = 4 * L by ring] using
      unitaryPath_trans_sub_norm_le p liftP (2 * L) hp₂ hLift t s
  let last : Path U 1 := ((rAA.mul rAB).mul (rBA.mul rBB)).cast rfl (by simp)
  let K := 4 * (L + 2 * Real.pi)
  have hLast : ∀ t s, ‖(last t : E) - last s‖ ≤ (4 * K) * |(t : ℝ) - s| := by
    have hleft : ∀ t s, ‖((rAA.mul rAB) t : E) - (rAA.mul rAB) s‖ ≤
        (K + K) * |(t : ℝ) - s| :=
      unitaryPath_mul_sub_norm_le rAA rAB K K hAA hAB
    have hright : ∀ t s, ‖((rBA.mul rBB) t : E) - (rBA.mul rBB) s‖ ≤
        (K + K) * |(t : ℝ) - s| :=
      unitaryPath_mul_sub_norm_le rBA rBB K K hBA hBB
    intro t s
    change ‖(((rAA.mul rAB).mul (rBA.mul rBB)) t : E) -
      ((rAA.mul rAB).mul (rBA.mul rBB)) s‖ ≤ _
    simpa only [show (K + K) + (K + K) = 4 * K by ring] using
      unitaryPath_mul_sub_norm_le (rAA.mul rAB) (rBA.mul rBB)
        (K + K) (K + K) hleft hright t s
  have hFirst' : ∀ t s, ‖(first t : E) - first s‖ ≤ (4 * K) * |(t : ℝ) - s| := by
    intro t s
    apply (hFirst t s).trans
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    dsimp only [K]
    linarith [Real.pi_pos]
  refine ⟨first.trans last, ?_⟩
  intro t s
  simpa only [K, show 2 * (4 * (4 * (L + 2 * Real.pi))) =
      32 * (L + 2 * Real.pi) by ring] using
    unitaryPath_trans_sub_norm_le first last (4 * K) hFirst' hLast t s

/-- A short path for the actual splitting defect gives the splitting path
needed above, with the same speed. -/
lemma exists_binaryFragmentation_of_defect_path (a b : E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hab : star a * b = 0)
    (u : unitary E) (L : ℝ) (hL : 0 ≤ L)
    (p : Path (1 : unitary E)
      (u * star (binaryCornerUnitary a ha u * binaryCornerUnitary b hb u)))
    (hp : ∀ t s, ‖(p t : E) - p s‖ ≤ L * |(t : ℝ) - s|) :
    ∃ r : Path u 1,
      ∀ t s, ‖(r t : E) - r s‖ ≤ (32 * (L + 2 * Real.pi)) * |(t : ℝ) - s| := by
  let v := binaryCornerUnitary a ha u * binaryCornerUnitary b hb u
  have he : (u * star v) * v = u := by simp [mul_assoc]
  let q : Path v u := (p.mul (Path.refl v)).cast (one_mul v).symm he.symm
  have hq : ∀ t s, ‖(q t : E) - q s‖ ≤ L * |(t : ℝ) - s| :=
    binaryPath_mul_const_sub_norm_le p v L hp
  exact exists_binaryFragmentation_path a b ha hb hab u L hL q.symm
    (binaryPath_symm_sub_norm_le q L hq)

end WeakPureInfiniteness

end

end OAI
