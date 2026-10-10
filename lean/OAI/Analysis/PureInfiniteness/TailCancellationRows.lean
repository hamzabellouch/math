import OAI.Analysis.OInfinity.BufferAbsorption

namespace OAI

/-! Literal row identities for removing the full tail in the absorption
construction. The complementary subcorner is fixed, not estimated away. -/
noncomputable section
namespace WeakPureInfiniteness.TailCancellation

variable {E : Type*} [CStarAlgebra E]

def full (z : E) : E := z * star z
def rest (D : BufferAbsorptionCorner E) (z : E) : E := D.q - full z
def support (z : E) : E := 1 - full z

def sourceRow (D : BufferAbsorptionCorner E) (z : E) (s t : ℕ → E) (i : ℕ) : E :=
  D.w * s i * star D.w + t i * rest D z

def targetRow (z : E) (t : ℕ → E) (i : ℕ) : E := t i * support z

structure Geometry (D : BufferAbsorptionCorner E) (z : E) : Prop where
  p_proj : IsStarProjection (full z)
  q_p : D.q * full z = full z
  p_q : full z * D.q = full z
  f_proj : IsStarProjection (rest D z)
  Q_proj : IsStarProjection (support z)
  p_w : full z * D.w = 0
  w_star_p : star D.w * full z = 0
  f_w : rest D z * D.w = 0
  w_star_f : star D.w * rest D z = 0
  Q_w : support z * D.w = D.w
  w_star_Q : star D.w * support z = star D.w
  Q_f : support z * rest D z = rest D z
  f_Q : rest D z * support z = rest D z
  sum : D.w * star D.w + rest D z = support z

lemma geometry (D : BufferAbsorptionCorner E) (z : E)
    (hz : star z * z = 1) (hqz : D.q * z = z) : Geometry D z := by
  have hqs := D.projection.isSelfAdjoint.star_eq
  have hqq := D.projection.isIdempotentElem.eq
  have hps : star (full z) = full z := by simp only [full, star_mul, star_star]
  have hpp : full z * full z = full z := by
    change (z * star z) * (z * star z) = z * star z
    calc
      _ = z * (star z * z) * star z := by noncomm_ring
      _ = _ := by rw [hz, mul_one]
  have hqp : D.q * full z = full z := by
    dsimp only [full]
    rw [← mul_assoc, hqz]
  have hpq : full z * D.q = full z := by
    simpa only [star_mul, hqs, hps] using congrArg star hqp
  have hfs : star (rest D z) = rest D z := by
    simp only [rest, star_sub, hqs, hps]
  have hff : rest D z * rest D z = rest D z := by
    dsimp only [rest]
    rw [sub_mul, mul_sub, mul_sub, hqq, hqp, hpq, hpp]
    abel
  have hQs : star (support z) = support z := by simp only [support, star_sub, star_one, hps]
  have hQQ : support z * support z = support z := by
    dsimp only [support]
    simp only [sub_mul, mul_sub, one_mul, mul_one, hpp]
    abel
  have hpw : full z * D.w = 0 := by
    rw [← hpq, mul_assoc, D.w_orthogonal, mul_zero]
  have hwsp : star D.w * full z = 0 := by
    simpa only [star_mul, hps, star_zero] using congrArg star hpw
  have hfw : rest D z * D.w = 0 := by
    rw [rest, sub_mul, D.w_orthogonal, hpw, sub_self]
  have hwsf : star D.w * rest D z = 0 := by
    simpa only [star_mul, hfs, star_zero] using congrArg star hfw
  have hQw : support z * D.w = D.w := by rw [support, sub_mul, one_mul, hpw, sub_zero]
  have hwsQ : star D.w * support z = star D.w := by
    simpa only [star_mul, hQs] using congrArg star hQw
  have hQf : support z * rest D z = rest D z := by
    dsimp only [support, rest]
    rw [sub_mul, mul_sub, mul_sub, one_mul, one_mul, hpq, hpp]
    abel
  have hfQ : rest D z * support z = rest D z := by
    simpa only [star_mul, hfs, hQs] using congrArg star hQf
  exact {
    p_proj := ⟨hpp, hps⟩, q_p := hqp, p_q := hpq,
    f_proj := ⟨hff, hfs⟩, Q_proj := ⟨hQQ, hQs⟩,
    p_w := hpw, w_star_p := hwsp, f_w := hfw, w_star_f := hwsf,
    Q_w := hQw, w_star_Q := hwsQ, Q_f := hQf, f_Q := hfQ,
    sum := by rw [rest, support, D.w_range]; abel }

lemma support_ne_zero [Nontrivial E] (D : BufferAbsorptionCorner E) (z : E)
    (G : Geometry D z) : support z ≠ 0 := by
  intro h
  have hw : D.w = 0 := by simpa only [h, zero_mul] using G.Q_w.symm
  have hone : (1 : E) = 0 := by simpa only [hw, star_zero, mul_zero] using D.w_gram.symm
  exact one_ne_zero hone

lemma rest_commute (D : BufferAbsorptionCorner E) (z a : E)
    (hq : Commute D.q a) (hp : Commute (full z) a) : Commute (rest D z) a :=
  hq.sub_left hp

lemma support_commute (z a : E) (hp : Commute (full z) a) : Commute (support z) a :=
  (Commute.one_left a).sub_left hp

lemma orthogonal_sum_gram (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (w f : E) (hw : star w * w = 1) (hfs : star f = f) (hff : f * f = f)
    (hwf : star w * f = 0) (hfc : ∀ i, Commute f (t i)) (i j : ℕ) :
    star (w * s i * star w + t i * f) * (w * s j * star w + t j * f) =
      if i = j then w * star w + f else 0 := by
  have hAA (i j : ℕ) : star (w * s i * star w) * (w * s j * star w) =
      if i = j then w * star w else 0 := by
    simp only [star_mul, star_star]
    calc
      _ = w * (star (s i) * (star w * w) * s j) * star w := by noncomm_ring
      _ = _ := by rw [hw, mul_one, hs]; split_ifs <;> simp
  have hAB (i j : ℕ) : star (w * s i * star w) * (t j * f) = 0 := by
    simp only [star_mul, star_star]
    calc
      _ = (w * star (s i)) * (star w * (t j * f)) := by noncomm_ring
      _ = (w * star (s i)) * ((star w * f) * t j) := by
        rw [← (hfc j).eq]
        noncomm_ring
      _ = 0 := by rw [hwf, zero_mul, mul_zero]
  have hBA : star (t i * f) * (w * s j * star w) = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star (hAB j i)
  have hBB : star (t i * f) * (t j * f) = if i = j then f else 0 := by
    simp only [star_mul, hfs]
    calc
      _ = f * (star (t i) * t j) * f := by noncomm_ring
      _ = _ := by rw [ht]; split_ifs <;> simp [hff]
  rw [star_add, add_mul, mul_add, mul_add, hAA, hAB, hBA, hBB]
  split_ifs <;> simp

lemma source_gram (D : BufferAbsorptionCorner E) (z : E) (G : Geometry D z)
    (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hq : ∀ i, Commute D.q (t i)) (hp : ∀ i, Commute (full z) (t i)) (i j : ℕ) :
    star (sourceRow D z s t i) * sourceRow D z s t j = if i = j then support z else 0 := by
  have h := orthogonal_sum_gram s t hs ht D.w (rest D z) D.w_gram
    G.f_proj.isSelfAdjoint.star_eq G.f_proj.isIdempotentElem.eq G.w_star_f
    (fun i => rest_commute D z _ (hq i) (hp i)) i j
  simpa only [sourceRow, G.sum] using h

lemma target_gram (z : E) (hQ : IsStarProjection (support z)) (t : ℕ → E)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0) (i j : ℕ) :
    star (targetRow z t i) * targetRow z t j = if i = j then support z else 0 := by
  dsimp only [targetRow]
  rw [star_mul, hQ.isSelfAdjoint.star_eq]
  calc
    _ = support z * (star (t i) * t j) * support z := by noncomm_ring
    _ = _ := by rw [ht]; split_ifs <;> simp [hQ.isIdempotentElem.eq]

lemma source_support (D : BufferAbsorptionCorner E) (z : E) (G : Geometry D z)
    (s t : ℕ → E) (hp : ∀ i, Commute (full z) (t i)) (i : ℕ) :
    support z * sourceRow D z s t i = sourceRow D z s t i ∧
      sourceRow D z s t i * support z = sourceRow D z s t i := by
  have hc := support_commute z (t i) (hp i)
  have hl : support z * (D.w * s i * star D.w) = D.w * s i * star D.w := by
    calc
      _ = (support z * D.w) * s i * star D.w := by noncomm_ring
      _ = _ := by rw [G.Q_w]
  have hr : (D.w * s i * star D.w) * support z = D.w * s i * star D.w := by
    rw [mul_assoc, G.w_star_Q]
  have hlf : support z * (t i * rest D z) = t i * rest D z := by
    rw [← mul_assoc, hc.eq, mul_assoc, G.Q_f]
  have hrf : (t i * rest D z) * support z = t i * rest D z := by rw [mul_assoc, G.f_Q]
  constructor <;> simp only [sourceRow, mul_add, add_mul, hl, hr, hlf, hrf]

lemma target_support (z : E) (hQ : IsStarProjection (support z)) (t : ℕ → E)
    (hp : ∀ i, Commute (full z) (t i)) (i : ℕ) :
    support z * targetRow z t i = targetRow z t i ∧
      targetRow z t i * support z = targetRow z t i := by
  have hc := support_commute z (t i) (hp i)
  constructor
  · dsimp only [targetRow]
    rw [← mul_assoc, hc.eq, mul_assoc, hQ.isIdempotentElem.eq]
  · exact mul_assoc (t i) (support z) (support z) |>.trans
      (congrArg (fun a => t i * a) hQ.isIdempotentElem.eq)

lemma conjugate_fixed_corner (u : unitary E) (p a : E) (hps : star p = p)
    (hu : (u : E) * p = p) (hpa : Commute p a) :
    (u : E) * (a * p) * star (u : E) = a * p := by
  have hus : p * star (u : E) = p := by
    simpa only [star_mul, hps] using congrArg star hu
  calc
    _ = ((u : E) * p) * a * star (u : E) := by rw [← hpa.eq]; noncomm_ring
    _ = a * (p * star (u : E)) := by rw [hu, hpa.eq]; noncomm_ring
    _ = _ := by rw [hus]

lemma recombination_norm (D : BufferAbsorptionCorner E) (z : E) (G : Geometry D z)
    (s t : ℕ → E) (u : unitary E) (hu : (u : E) * full z = full z)
    (hp : ∀ i, Commute (full z) (t i)) (i : ℕ) :
    ‖(u : E) * (t i * D.q + D.w * s i * star D.w) * star (u : E) - t i‖ =
      ‖(u : E) * sourceRow D z s t i * star (u : E) - targetRow z t i‖ := by
  have he : t i * D.q + D.w * s i * star D.w = sourceRow D z s t i + t i * full z := by
    dsimp only [sourceRow, rest]
    noncomm_ring
  have ht : t i = targetRow z t i + t i * full z := by
    dsimp only [targetRow, support]
    noncomm_ring
  have hf := conjugate_fixed_corner u (full z) (t i) G.p_proj.isSelfAdjoint.star_eq hu (hp i)
  have hconj : (u : E) * (t i * D.q + D.w * s i * star D.w) * star (u : E) =
      (u : E) * sourceRow D z s t i * star (u : E) + t i * full z := by
    rw [he, mul_add, add_mul, hf]
  apply congrArg norm
  calc
    _ = ((u : E) * sourceRow D z s t i * star (u : E) + t i * full z) -
        (targetRow z t i + t i * full z) := congrArg₂ (· - ·) hconj ht
    _ = _ := by abel

end WeakPureInfiniteness.TailCancellation

end

end OAI
