import OAI.Analysis.OInfinity.BufferAbsorption
import OAI.Analysis.OInfinity.ZeroCorner

namespace OAI

/-! # The concrete absorption anchor is connected

For the binary pair constructed by the two-swap zero-corner completion,
the absorption anchor times that completion is the elementary swap of
`q` and `w q w*`.  Both factors have explicit paths to the identity.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E] [Nontrivial E]

/-- The additional equations are satisfied by the explicit zero-corner
completion.  They identify the anchor's component without a K₁ assumption. -/
lemma BufferAbsorptionCorner.anchor_joined_of_completion
    (D : BufferAbsorptionCorner E) (u : unitary E)
    (hu : Joined (1 : unitary E) u)
    (huq : (u : E) * D.q = D.b)
    (huw : (u : E) * D.w = (1 - D.q) + D.a) :
    Joined (1 : unitary E) D.anchor := by
  let x := D.w * D.q
  have hxg : star x * x = D.q := by
    dsimp only [x]
    rw [star_mul, D.projection.isSelfAdjoint.star_eq]
    calc
      _ = D.q * (star D.w * D.w) * D.q := by noncomm_ring
      _ = D.q := by rw [D.w_gram, mul_one, D.projection.isIdempotentElem.eq]
  have hxq : x * D.q = x := by
    dsimp only [x]
    rw [mul_assoc, D.projection.isIdempotentElem.eq]
  have hxp : x * star x * x = x := by rw [mul_assoc, hxg, hxq]
  have hxx : x * x = 0 := by
    dsimp only [x]
    calc
      _ = D.w * (D.q * D.w) * D.q := by noncomm_ring
      _ = 0 := by rw [D.w_orthogonal, mul_zero, zero_mul]
  let T := partialIsometrySwapUnitary x hxp hxx
  have hTq : (T : E) * D.q = x := by
    change partialIsometrySwap x * D.q = x
    rw [← hxg]
    exact partialIsometrySwap_mul_initial x hxp hxx
  have hxw : x * D.w = 0 := by
    dsimp only [x]
    rw [mul_assoc, D.w_orthogonal, mul_zero]
  have hxsw : star x * D.w = D.q := by
    dsimp only [x]
    rw [star_mul, D.projection.isSelfAdjoint.star_eq, mul_assoc, D.w_gram, mul_one]
  have hTw : (T : E) * D.w = D.q + D.w * (1 - D.q) := by
    change partialIsometrySwap x * D.w = _
    dsimp only [partialIsometrySwap]
    rw [add_mul, add_mul, sub_mul, sub_mul, one_mul, hxw, hxsw, hxg,
      D.w_orthogonal, mul_assoc x (star x), hxsw, hxq]
    dsimp only [x]
    noncomm_ring
  have hap : star D.a * (1 - D.q) = 0 := by
    rw [mul_sub, mul_one, D.a_star_right, sub_self]
  have hbp : star D.b * (1 - D.q) = 0 := by
    rw [mul_sub, mul_one, D.b_star_right, sub_self]
  have hrp : D.remainder * (1 - D.q) = 1 - D.q := by
    change (star D.b + (1 - D.q)) * (1 - D.q) = _
    rw [add_mul, hbp, D.projection.one_sub.isIdempotentElem.eq, zero_add]
  have hrb : D.remainder * D.b = D.q := by
    change (star D.b + (1 - D.q)) * D.b = _
    rw [add_mul, D.b_gram, sub_mul, one_mul, D.b_left]
    abel
  have han : (D.anchor : E) = star D.a + D.w * D.remainder := by
    change star D.a + D.w * (1 : E) * D.remainder = _
    rw [mul_one]
  have hZq : ((D.anchor * u : unitary E) : E) * D.q = x := by
    change ((D.anchor : E) * (u : E)) * D.q = x
    rw [mul_assoc, huq, han, add_mul, D.orthogonal,
      mul_assoc, hrb, zero_add]
  have hZw : ((D.anchor * u : unitary E) : E) * D.w = D.q + D.w * (1 - D.q) := by
    change ((D.anchor : E) * (u : E)) * D.w = _
    rw [mul_assoc, huw, mul_add, han, add_mul, add_mul,
      hap, mul_assoc D.w D.remainder, hrp, D.a_gram,
      mul_assoc D.w D.remainder, D.remainder_a]
    simp only [mul_zero, zero_add, add_zero]
    abel
  have hsplit : D.q + D.w * star D.w = 1 := by rw [D.w_range]; abel
  have hZT : D.anchor * u = T := by
    apply Subtype.ext
    calc
      _ = ((D.anchor * u : unitary E) : E) * (D.q + D.w * star D.w) := by
        rw [hsplit, mul_one]
      _ = (((D.anchor * u : unitary E) : E) * D.q) +
          ((((D.anchor * u : unitary E) : E) * D.w) * star D.w) := by noncomm_ring
      _ = (T : E) * D.q + ((T : E) * D.w) * star D.w := by rw [hZq, hZw, hTq, hTw]
      _ = (T : E) * (D.q + D.w * star D.w) := by noncomm_ring
      _ = _ := by rw [hsplit, mul_one]
  have hTs : Joined (1 : unitary E) T := partialIsometrySwapUnitary_joined x hxp hxx
  have hus : Joined (1 : unitary E) (star u) := by
    simpa only [star_one] using hu.map (continuous_star : Continuous (star : unitary E → unitary E))
  have he : T * star u = D.anchor := by
    rw [← hZT]
    apply Subtype.ext
    change ((D.anchor : E) * (u : E)) * star (u : E) = (D.anchor : E)
    rw [mul_assoc, Unitary.mul_star_self_of_mem u.property, mul_one]
  simpa only [one_mul, he] using hTs.mul hus

/-- A two-swap completion acts on its prescribed initial projection. -/
private lemma completion_on_initial (v r : E) (hv : v * star v * v = v)
    (hr : star r * r = 1) (hpr : (star v * v) * r = 0)
    (hqr : (v * star v) * r = 0) :
    partialIsometryCompletion r (star v * v) v * (star v * v) = v := by
  obtain ⟨u, _, hue, hup⟩ := exists_explicit_connected_unitary_extension v r hv hr hpr hqr
  rw [← hue]
  exact hup

/-- The actual three-isometry construction supplies all the extra anchor
equations as well as the binary row. -/
lemma exists_connected_buffer_corner (w r z : E)
    (hw : star w * w = 1) (hr : star r * r = 1) (hz : star z * z = 1)
    (hwr : star w * r = 0) (hwz : star w * z = 0) (hrz : star r * z = 0) :
    ∃ D : BufferAbsorptionCorner E,
      D.q = 1 - w * star w ∧ D.w = w ∧ D.a = r * D.q ∧
      Joined (1 : unitary E) D.anchor ∧
      ∀ y : E,
        Commute w y → Commute (star w) y →
        Commute r y → Commute (star r) y →
        Commute z y → Commute (star z) y →
        Commute D.a y ∧ Commute (star D.a) y ∧
        Commute D.b y ∧ Commute (star D.b) y := by
  let p := w * star w
  let q := 1 - p
  have hpp : p * p = p := by
    dsimp only [p]
    rw [mul_assoc, ← mul_assoc (star w), hw, one_mul]
  have hps : star p = p := by simp only [p, star_mul, star_star]
  have hqs : star q = q := by simp only [q, star_sub, star_one, hps]
  have hqq : q * q = q := by dsimp only [q]; noncomm_ring [hpp]
  have hqw : q * w = 0 := by
    dsimp only [q, p]
    rw [sub_mul, one_mul, mul_assoc, hw, mul_one, sub_self]
  obtain ⟨a, b, u, hu, hae, hbe, hue, ha, hb, hab, hs⟩ :=
    exists_zero_corner_cuntz_pair w r z hw hr hz hwr hwz hrz
  change a = r * q at hae
  change b = (u : E) * q at hbe
  change star a * a = q at ha
  change star b * b = q at hb
  change a * star a + b * star b = q at hs
  let D : BufferAbsorptionCorner E :=
    ⟨q, w, a, b, isStarProjection_iff'.mpr ⟨hqq, hqs⟩,
      hw, by dsimp only [q]; abel, hqw, ha, hb, hab, hs⟩
  let v := (p + a) * star w
  have hpz : p * z = 0 := by dsimp only [p]; rw [mul_assoc, hwz, mul_zero]
  have hpa : p * a = 0 := by
    rw [hae]
    dsimp only [p]
    calc
      _ = w * (star w * r) * q := by noncomm_ring
      _ = 0 := by rw [hwr, mul_zero, zero_mul]
  have hap : star a * p = 0 := by
    simpa only [star_mul, hps, star_zero] using congrArg star hpa
  have hvgram : star v * v = p := by
    have hinner : star (p + a) * (p + a) = 1 := by
      rw [star_add, hps, add_mul, mul_add, mul_add, hpp, hpa, hap, ha]
      dsimp only [q]; noncomm_ring
    dsimp only [v]
    rw [star_mul, star_star]
    calc
      _ = w * (star (p + a) * (p + a)) * star w := by noncomm_ring
      _ = p := by rw [hinner, mul_one]
  have hvpartial : v * star v * v = v := by
    rw [mul_assoc, hvgram]
    dsimp only [v, p]
    calc
      _ = (w * star w + a) * (star w * w) * star w := by noncomm_ring
      _ = _ := by rw [hw, mul_one]
  have hvz : (v * star v) * z = 0 := by
    have hasz : star a * z = 0 := by
      rw [hae, star_mul, mul_assoc, hrz, mul_zero]
    have hsz : star (p + a) * z = 0 := by
      rw [star_add, hps, add_mul, hpz, hasz, add_zero]
    dsimp only [v]
    rw [star_mul, star_star]
    calc
      _ = (p + a) * (star w * w) * (star (p + a) * z) := by noncomm_ring
      _ = 0 := by rw [hw, mul_one, hsz, mul_zero]
  have hup : (u : E) * p = v := by
    rw [hue]
    change partialIsometryCompletion z p ((p + r * q) * star w) * p = v
    rw [← hae]
    change partialIsometryCompletion z p v * p = v
    rw [← hvgram]
    exact completion_on_initial v z hvpartial hz (by rw [hvgram]; exact hpz) hvz
  have huw : (u : E) * w = p + a := by
    have hpw : p * w = w := by
      dsimp only [p]
      rw [mul_assoc, hw, mul_one]
    calc
      _ = (u : E) * (p * w) := by rw [hpw]
      _ = ((u : E) * p) * w := by noncomm_ring
      _ = v * w := by rw [hup]
      _ = p + a := by dsimp only [v]; rw [mul_assoc, hw, mul_one]
  have huwD : (u : E) * D.w = 1 - D.q + D.a := by
    change (u : E) * w = 1 - (1 - p) + a
    rw [huw]
    noncomm_ring
  refine ⟨D, rfl, rfl, hae, D.anchor_joined_of_completion u hu hbe.symm huwD, ?_⟩
  intro y hwy hwsy hry hrsy hzy hzsy
  have hpcy : Commute p y := hwy.mul_left hwsy
  have hqcy : Commute q y := (Commute.one_left y).sub_left hpcy
  have hac : Commute a y := by rw [hae]; exact hry.mul_left hqcy
  have hasc : Commute (star a) y := by
    rw [hae, star_mul, hqs]
    exact hqcy.mul_left hrsy
  have huc : Commute (u : E) y := by
    rw [hue]
    exact zeroCornerCompletion_commutes w r z y hwy hwsy hry hrsy hzy hzsy
  have husc : Commute (star (u : E)) y := by
    have huc' : Commute (u : E) (star y) := by
      rw [hue]
      apply zeroCornerCompletion_commutes w r z (star y)
      · simpa only [star_star] using hwsy.star_star
      · exact hwy.star_star
      · simpa only [star_star] using hrsy.star_star
      · exact hry.star_star
      · simpa only [star_star] using hzsy.star_star
      · exact hzy.star_star
    simpa only [star_star] using huc'.star_star
  refine ⟨hac, hasc, ?_, ?_⟩
  · change Commute b y
    rw [hbe]
    exact huc.mul_left hqcy
  · change Commute (star b) y
    rw [hbe, star_mul, hqs]
    exact hqcy.mul_left husc

/-- Finite-row absorption by an actual three-isometry buffer, now with an
ambient path from the identity. The target is a coisometric row in the
literal complement of the first buffer isometry. -/
lemma exists_connected_finite_buffer_absorption {I : Type*} [Fintype I] [DecidableEq I]
    (s t : I → E) (r w a b : E)
    (hr : star r * r = 1) (hrs : ∀ i, star r * s i = 0)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hw : star w * w = 1) (ha : star a * a = 1) (hb : star b * b = 1)
    (hwa : star w * a = 0) (hwb : star w * b = 0) (hab : star a * b = 0)
    (hwr : Commute w r) (hwsr : Commute (star w) r)
    (hws : ∀ i, Commute w (s i) ∧ Commute (star w) (s i))
    (hwt : ∀ i, Commute w (t i) ∧ Commute (star w) (t i))
    (hat : ∀ i, Commute a (t i) ∧ Commute (star a) (t i))
    (hbt : ∀ i, Commute b (t i) ∧ Commute (star b) (t i))
    (htq : ∀ i, t i * (1 - w * star w) = t i)
    (ht : ∑ i, t i * star (t i) = 1 - w * star w)
    (htt : ∀ i j, star (t i) * t j = if i = j then 1 - w * star w else 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : unitary E, Joined (1 : unitary E) U ∧
      ∀ i, ‖(U : E) * s i - (t i + w * s i * star w) * (U : E)‖ < ε := by
  obtain ⟨D, hDq, hDw, _, hDjoin, hDc⟩ :=
    exists_connected_buffer_corner w a b hw ha hb hwa hwb hab
  have hqr : Commute D.q r := by
    rw [hDq]
    exact (Commute.one_left r).sub_left (hwr.mul_left hwsr)
  have hqs (i : I) : Commute D.q (s i) := by
    rw [hDq]
    exact (Commute.one_left (s i)).sub_left ((hws i).1.mul_left (hws i).2)
  have hDa (i : I) : Commute (star D.a) (t i) :=
    (hDc (t i) (hwt i).1 (hwt i).2 (hat i).1 (hat i).2 (hbt i).1 (hbt i).2).2.1
  have hDb (i : I) : Commute (star D.b) (t i) :=
    (hDc (t i) (hwt i).1 (hwt i).2 (hat i).1 (hat i).2 (hbt i).1 (hbt i).2).2.2.2
  obtain ⟨U, hU, hUi⟩ := D.exists_finite_absorption s t r hr hrs hs hqr hqs
    (by simpa only [hDq] using htq) (by simpa only [hDq] using ht)
    (by simpa only [hDq] using htt) hDa hDb ε hε
  refine ⟨U, hDjoin.trans hU, ?_⟩
  simpa only [hDw] using hUi

end WeakPureInfiniteness

end

end OAI
