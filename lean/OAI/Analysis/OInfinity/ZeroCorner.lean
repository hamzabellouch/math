import OAI.Analysis.OInfinity.CentralIsometries

namespace OAI

/-! # An explicit coisometric pair in the complementary corner

Three orthogonal isometries suffice to construct two relative isometries
whose ranges add up to `1 - r₀ * star r₀`. The construction uses the checked
two-swap completion, with its connected unitary retained explicitly. The
unit of this pair is the stated corner projection, not the ambient unit.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma partialIsometrySwap_commutes (a y : E)
    (ha : Commute a y) (hastar : Commute (star a) y) :
    Commute (partialIsometrySwap a) y := by
  exact (ha.add_left hastar).add_left
    (((Commute.one_left y).sub_left (hastar.mul_left ha)).sub_left (ha.mul_left hastar))

lemma partialIsometryCompletion_commutes (r p v y : E)
    (hr : Commute r y) (hrstar : Commute (star r) y)
    (hp : Commute p y) (hpstar : Commute (star p) y)
    (hv : Commute v y) (hvstar : Commute (star v) y) :
    Commute (partialIsometryCompletion r p v) y := by
  apply Commute.mul_left
  · apply partialIsometrySwap_commutes
    · exact hv.mul_left hrstar
    · simpa only [star_mul, star_star] using hr.mul_left hvstar
  · apply partialIsometrySwap_commutes
    · exact hr.mul_left hp
    · simpa only [star_mul] using hpstar.mul_left hrstar

lemma exists_zero_corner_cuntz_pair [Nontrivial E] (r₀ r₁ r₂ : E)
    (h₀ : star r₀ * r₀ = 1) (h₁ : star r₁ * r₁ = 1) (h₂ : star r₂ * r₂ = 1)
    (h₀₁ : star r₀ * r₁ = 0) (h₀₂ : star r₀ * r₂ = 0) (h₁₂ : star r₁ * r₂ = 0) :
    let q := 1 - r₀ * star r₀
    ∃ (a b : E) (u : unitary E), Joined (1 : unitary E) u ∧
      a = r₁ * q ∧ b = (u : E) * q ∧
      (u : E) = partialIsometryCompletion r₂ (r₀ * star r₀)
        (((r₀ * star r₀) + r₁ * q) * star r₀) ∧
      star a * a = q ∧ star b * b = q ∧ star a * b = 0 ∧
      a * star a + b * star b = q := by
  intro q
  let p := r₀ * star r₀
  let a := r₁ * q
  let z := p + a
  let v := z * star r₀
  have hpstar : star p = p := by simp only [p, star_mul, star_star]
  have hpp : p * p = p := by
    dsimp only [p]
    rw [mul_assoc, ← mul_assoc (star r₀), h₀, one_mul]
  have hqstar : star q = q := by change star (1 - p) = 1 - p; rw [star_sub, star_one, hpstar]
  have hqq : q * q = q := by change (1 - p) * (1 - p) = 1 - p; noncomm_ring [hpp]
  have hpq : p * q = 0 := by change p * (1 - p) = 0; noncomm_ring [hpp]
  have hqp : q * p = 0 := by change (1 - p) * p = 0; noncomm_ring [hpp]
  have hpr₁ : p * r₁ = 0 := by
    change (r₀ * star r₀) * r₁ = 0
    rw [mul_assoc, h₀₁, mul_zero]
  have hr₁p : star r₁ * p = 0 := by
    simpa only [star_mul, hpstar, star_zero] using congrArg star hpr₁
  have hpa : p * a = 0 := by dsimp only [a]; rw [← mul_assoc, hpr₁, zero_mul]
  have hasp : star a * p = 0 := by
    simpa only [star_mul, hpstar, star_zero] using congrArg star hpa
  have hqa : q * a = a := by change (1 - p) * a = a; rw [sub_mul, one_mul, hpa, sub_zero]
  have haq : a * q = a := by dsimp only [a]; rw [mul_assoc, hqq]
  have haas : star a * a = q := by
    dsimp only [a]
    rw [star_mul, hqstar]
    calc
      _ = q * (star r₁ * r₁) * q := by noncomm_ring
      _ = q := by rw [h₁, mul_one, hqq]
  have hziso : star z * z = 1 := by
    change star (p + a) * (p + a) = 1
    rw [star_add, hpstar, add_mul, mul_add, mul_add, hpp, hpa, hasp, haas]
    change p + 0 + (0 + (1 - p)) = 1
    noncomm_ring
  have hztarget : z * star z = p + a * star a := by
    change (p + a) * star (p + a) = p + a * star a
    rw [star_add, hpstar]
    have hap : a * p = 0 := by dsimp only [a]; rw [mul_assoc, hqp, mul_zero]
    have hpas' : p * star a = 0 := by
      simpa only [star_mul, hpstar, star_zero] using congrArg star hap
    noncomm_ring [hpp, hap, hpas']
  have hvsource : star v * v = p := by
    change star (z * star r₀) * (z * star r₀) = p
    rw [star_mul, star_star]
    calc
      _ = r₀ * (star z * z) * star r₀ := by noncomm_ring
      _ = p := by rw [hziso, mul_one]
  have hvtarget : v * star v = p + a * star a := by
    change (z * star r₀) * star (z * star r₀) = _
    rw [star_mul, star_star]
    calc
      _ = z * (star r₀ * r₀) * star z := by noncomm_ring
      _ = _ := by rw [h₀, mul_one, hztarget]
  have hvpartial : v * star v * v = v := by
    change (z * star r₀) * star (z * star r₀) * (z * star r₀) = z * star r₀
    rw [star_mul, star_star]
    calc
      _ = z * (star r₀ * r₀) * (star z * z) * star r₀ := by noncomm_ring
      _ = _ := by rw [h₀, hziso, mul_one, mul_one]
  have hpr₂ : p * r₂ = 0 := by
    change (r₀ * star r₀) * r₂ = 0
    rw [mul_assoc, h₀₂, mul_zero]
  have hasr₂ : star a * r₂ = 0 := by
    dsimp only [a]
    rw [star_mul, mul_assoc, h₁₂, mul_zero]
  have hvr₂ : (v * star v) * r₂ = 0 := by
    rw [hvtarget, add_mul, hpr₂, mul_assoc, hasr₂, mul_zero, add_zero]
  obtain ⟨u, hu, hueq, huvp⟩ := exists_explicit_connected_unitary_extension v r₂
    hvpartial h₂ (by rw [hvsource]; exact hpr₂) hvr₂
  have hup : (u : E) * p = v := by simpa only [hvsource] using huvp
  have hupu : (u : E) * p * star (u : E) = p + a * star a := by
    calc
      _ = ((u : E) * p) * star ((u : E) * p) := by
        rw [star_mul, hpstar]
        symm
        calc
          _ = (u : E) * (p * p) * star (u : E) := by noncomm_ring
          _ = _ := by rw [hpp]
      _ = _ := by rw [hup, hvtarget]
  let b := (u : E) * q
  have hbsource : star b * b = q := by
    dsimp only [b]
    rw [star_mul, hqstar]
    calc
      _ = q * (star (u : E) * (u : E)) * q := by noncomm_ring
      _ = q := by rw [Unitary.coe_star_mul_self, mul_one, hqq]
  have hbtarget : b * star b = q - a * star a := by
    dsimp only [b]
    rw [star_mul, hqstar]
    calc
      _ = (u : E) * q * star (u : E) := by
        calc
          _ = (u : E) * (q * q) * star (u : E) := by noncomm_ring
          _ = _ := by rw [hqq]
      _ = 1 - (p + a * star a) := by
        change (u : E) * (1 - p) * star (u : E) = _
        rw [mul_sub, sub_mul, mul_one, Unitary.mul_star_self_of_mem u.property, hupu]
      _ = _ := by change 1 - (p + a * star a) = (1 - p) - a * star a; abel
  have hbq : b * q = b := by dsimp only [b]; rw [mul_assoc, hqq]
  have hbpartial : b * star b * b = b := by rw [mul_assoc, hbsource, hbq]
  have haapartial : (a * star a) * (a * star a) = a * star a := by
    calc
      _ = a * (star a * a) * star a := by noncomm_ring
      _ = _ := by rw [haas, haq]
  have haaq : (a * star a) * q = a * star a := by
    have h := congrArg star hqa
    simpa only [star_mul, hqstar, mul_assoc] using congrArg (fun y => a * y) h
  have habproj : (a * star a) * (b * star b) = 0 := by
    rw [hbtarget, mul_sub, haaq, haapartial, sub_self]
  have haab : (a * star a) * b = 0 := by
    rw [← hbpartial, ← mul_assoc, habproj, zero_mul]
  have hab : star a * b = 0 := by
    apply (CStarRing.star_mul_self_eq_zero_iff _).mp
    rw [star_mul, star_star]
    calc
      _ = star b * ((a * star a) * b) := by noncomm_ring
      _ = 0 := by rw [haab, mul_zero]
  refine ⟨a, b, u, hu, rfl, rfl, ?_, haas, hbsource, hab, ?_⟩
  · simpa only [hvsource] using hueq
  · rw [hbtarget]
    abel

/-- The zero-corner completion is a fixed finite polynomial, so it retains
exact commutation with every element commuting with the three input
isometries and their adjoints. -/
lemma zeroCornerCompletion_commutes (r₀ r₁ r₂ y : E)
    (h₀ : Commute r₀ y) (h₀s : Commute (star r₀) y)
    (h₁ : Commute r₁ y) (h₁s : Commute (star r₁) y)
    (h₂ : Commute r₂ y) (h₂s : Commute (star r₂) y) :
    Commute (partialIsometryCompletion r₂ (r₀ * star r₀)
      (((r₀ * star r₀) + r₁ * (1 - r₀ * star r₀)) * star r₀)) y := by
  have hp := h₀.mul_left h₀s
  have hps : Commute (star (r₀ * star r₀)) y := by
    simpa only [star_mul, star_star] using hp
  have hq := (Commute.one_left y).sub_left hp
  have hqs : Commute (star (1 - r₀ * star r₀)) y := by
    simpa only [star_sub, star_one, star_mul, star_star] using hq
  apply partialIsometryCompletion_commutes _ _ _ _ h₂ h₂s hp hps
  · exact (hp.add_left (h₁.mul_left hq)).mul_left h₀s
  · simpa only [star_mul, star_add, star_star] using
      h₀.mul_left (hps.add_left (hqs.mul_left h₁s))

private structure ZeroCornerControl (x a : E) (N C : ℝ) : Prop where
  norm_bound : ‖a‖ ≤ N
  bound : ‖a * x - x * a‖ ≤ C
  star_bound : ‖star a * x - x * star a‖ ≤ C

private lemma zeroCornerControl_one [Nontrivial E] (x : E) : ZeroCornerControl x 1 1 0 := by
  constructor <;> simp

private lemma zeroCornerControl_star {x a : E} {N C : ℝ}
    (h : ZeroCornerControl x a N C) : ZeroCornerControl x (star a) N C := by
  exact ⟨by simpa only [norm_star] using h.norm_bound, h.star_bound,
    by simpa only [star_star] using h.bound⟩

private lemma zeroCornerControl_add {x a b : E} {N M C D : ℝ}
    (ha : ZeroCornerControl x a N C) (hb : ZeroCornerControl x b M D) :
    ZeroCornerControl x (a + b) (N + M) (C + D) := by
  constructor
  · exact (norm_add_le _ _).trans (add_le_add ha.norm_bound hb.norm_bound)
  · have he : (a + b) * x - x * (a + b) = (a * x - x * a) + (b * x - x * b) := by
      noncomm_ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add ha.bound hb.bound)
  · have he : star (a + b) * x - x * star (a + b) =
        (star a * x - x * star a) + (star b * x - x * star b) := by
      rw [star_add]; noncomm_ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add ha.star_bound hb.star_bound)

private lemma zeroCornerControl_sub {x a b : E} {N M C D : ℝ}
    (ha : ZeroCornerControl x a N C) (hb : ZeroCornerControl x b M D) :
    ZeroCornerControl x (a - b) (N + M) (C + D) := by
  constructor
  · exact (norm_sub_le _ _).trans (add_le_add ha.norm_bound hb.norm_bound)
  · have he : (a - b) * x - x * (a - b) = (a * x - x * a) - (b * x - x * b) := by
      noncomm_ring
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add ha.bound hb.bound)
  · have he : star (a - b) * x - x * star (a - b) =
        (star a * x - x * star a) - (star b * x - x * star b) := by
      rw [star_sub]; noncomm_ring
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add ha.star_bound hb.star_bound)

private lemma zeroCornerControl_mul_bound {x a b : E} {N M C D : ℝ}
    (haN : ‖a‖ ≤ N) (hbM : ‖b‖ ≤ M)
    (ha : ‖a * x - x * a‖ ≤ C) (hb : ‖b * x - x * b‖ ≤ D) :
    ‖(a * b) * x - x * (a * b)‖ ≤ N * D + C * M := by
  have hC : 0 ≤ C := (norm_nonneg _).trans ha
  have hD : 0 ≤ D := (norm_nonneg _).trans hb
  have he : (a * b) * x - x * (a * b) =
      a * (b * x - x * b) + (a * x - x * a) * b := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖a * (b * x - x * b)‖ + ‖(a * x - x * a) * b‖ := norm_add_le _ _
    _ ≤ ‖a‖ * ‖b * x - x * b‖ + ‖a * x - x * a‖ * ‖b‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ N * D + C * M := add_le_add
      (mul_le_mul haN hb (norm_nonneg _) ((norm_nonneg _).trans haN))
      (mul_le_mul ha hbM (norm_nonneg _) hC)

private lemma zeroCornerControl_mul {x a b : E} {N M C D : ℝ}
    (ha : ZeroCornerControl x a N C) (hb : ZeroCornerControl x b M D) :
    ZeroCornerControl x (a * b) (N * M) (N * D + C * M) := by
  constructor
  · exact (norm_mul_le _ _).trans
      (mul_le_mul ha.norm_bound hb.norm_bound (norm_nonneg _) ((norm_nonneg _).trans ha.norm_bound))
  · exact zeroCornerControl_mul_bound ha.norm_bound hb.norm_bound ha.bound hb.bound
  · rw [star_mul]
    have h := zeroCornerControl_mul_bound
      (zeroCornerControl_star hb).norm_bound (zeroCornerControl_star ha).norm_bound
      hb.star_bound ha.star_bound
    convert h using 1; ring

private lemma zeroCornerControl_swap [Nontrivial E] {x a : E} {N C : ℝ}
    (ha : ZeroCornerControl x a N C) :
    ZeroCornerControl x (partialIsometrySwap a)
      (N + N + (1 + N * N + N * N))
      (C + C + (0 + (N * C + C * N) + (N * C + C * N))) := by
  exact zeroCornerControl_add (zeroCornerControl_add ha (zeroCornerControl_star ha))
    (zeroCornerControl_sub (zeroCornerControl_sub (zeroCornerControl_one x)
      (zeroCornerControl_mul (zeroCornerControl_star ha) ha))
        (zeroCornerControl_mul ha (zeroCornerControl_star ha)))

/-- A uniform polynomial estimate, valid before the Cuntz relations are used.
The deliberately coarse constant keeps the input tolerance independent of
the test element and of the ambient algebra. -/
lemma zeroCornerCompletion_commutator_bound [Nontrivial E] (r₀ r₁ r₂ x : E) (δ : ℝ)
    (hN : ∀ r ∈ ({r₀, r₁, r₂} : Set E), ‖r‖ ≤ 1)
    (hC : ∀ r ∈ ({r₀, r₁, r₂} : Set E),
      ‖r * x - x * r‖ ≤ δ ∧ ‖star r * x - x * star r‖ ≤ δ) :
    let U := partialIsometryCompletion r₂ (r₀ * star r₀)
      (((r₀ * star r₀) + r₁ * (1 - r₀ * star r₀)) * star r₀)
    ‖U * x - x * U‖ ≤ 1290 * δ ∧ ‖star U * x - x * star U‖ ≤ 1290 * δ := by
  have h₀ : ZeroCornerControl x r₀ 1 δ :=
    ⟨hN r₀ (by simp), (hC r₀ (by simp)).1, (hC r₀ (by simp)).2⟩
  have h₁ : ZeroCornerControl x r₁ 1 δ :=
    ⟨hN r₁ (by simp), (hC r₁ (by simp)).1, (hC r₁ (by simp)).2⟩
  have h₂ : ZeroCornerControl x r₂ 1 δ :=
    ⟨hN r₂ (by simp), (hC r₂ (by simp)).1, (hC r₂ (by simp)).2⟩
  have hp := zeroCornerControl_mul h₀ (zeroCornerControl_star h₀)
  have hq := zeroCornerControl_sub (zeroCornerControl_one x) hp
  have hz := zeroCornerControl_add hp (zeroCornerControl_mul h₁ hq)
  have hv := zeroCornerControl_mul hz (zeroCornerControl_star h₀)
  have hA := zeroCornerControl_swap (zeroCornerControl_mul hv (zeroCornerControl_star h₂))
  have hB := zeroCornerControl_swap (zeroCornerControl_mul h₂ hp)
  have hU := zeroCornerControl_mul hA hB
  dsimp only [partialIsometryCompletion]
  constructor
  · convert hU.bound using 1; ring
  · convert hU.star_bound using 1; ring

lemma zeroCornerPair_commutator_bound [Nontrivial E] (r₀ r₁ r₂ x : E) (δ : ℝ) (hδ : 0 ≤ δ)
    (hN : ∀ r ∈ ({r₀, r₁, r₂} : Set E), ‖r‖ ≤ 1)
    (hC : ∀ r ∈ ({r₀, r₁, r₂} : Set E),
      ‖r * x - x * r‖ ≤ δ ∧ ‖star r * x - x * star r‖ ≤ δ)
    (u : unitary E)
    (hu : (u : E) = partialIsometryCompletion r₂ (r₀ * star r₀)
      (((r₀ * star r₀) + r₁ * (1 - r₀ * star r₀)) * star r₀)) :
    let q := 1 - r₀ * star r₀
    ‖(r₁ * q) * x - x * (r₁ * q)‖ ≤ 2582 * δ ∧
      ‖((u : E) * q) * x - x * ((u : E) * q)‖ ≤ 2582 * δ := by
  have h₀ : ZeroCornerControl x r₀ 1 δ :=
    ⟨hN r₀ (by simp), (hC r₀ (by simp)).1, (hC r₀ (by simp)).2⟩
  have h₁ : ZeroCornerControl x r₁ 1 δ :=
    ⟨hN r₁ (by simp), (hC r₁ (by simp)).1, (hC r₁ (by simp)).2⟩
  have hq := zeroCornerControl_sub (zeroCornerControl_one x)
    (zeroCornerControl_mul h₀ (zeroCornerControl_star h₀))
  have hubounds := zeroCornerCompletion_commutator_bound r₀ r₁ r₂ x δ hN hC
  have hU : ZeroCornerControl x (u : E) 1 (1290 * δ) := by
    refine ⟨(CStarRing.norm_coe_unitary u).le, ?_, ?_⟩
    · simpa only [hu] using hubounds.1
    · simpa only [hu] using hubounds.2
  constructor
  · have hb := (zeroCornerControl_mul h₁ hq).bound
    nlinarith
  · have hb := (zeroCornerControl_mul hU hq).bound
    nlinarith

private lemma zeroCorner_star_commutator_norm (a x : E) :
    ‖star a * x - x * star a‖ = ‖a * star x - star x * a‖ := by
  rw [← norm_star (a * star x - star x * a)]
  simp only [star_sub, star_mul, star_star]
  exact norm_sub_rev _ _

/-- Global central rows produce a coisometric pair in their complementary
corner with arbitrarily small finite-set commutators. The corner unit is
kept explicit in the conclusion. -/
lemma exists_approximately_central_zero_corner_pair [Nontrivial E] (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hc : ∀ i j, Commute (s i) (t j) ∧ Commute (s i) (star (t j)))
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (q a b : E), q ≠ 0 ∧ star q = q ∧ q * q = q ∧
      star a * a = q ∧ star b * b = q ∧ star a * b = 0 ∧
      a * star a + b * star b = q ∧
      (∀ i < n, ‖a * s i - s i * a‖ < δ ∧ ‖b * s i - s i * b‖ < δ ∧
        ‖a * star (s i) - star (s i) * a‖ < δ ∧
        ‖b * star (s i) - star (s i) * b‖ < δ) ∧
      ∀ k, Commute a (t k) ∧ Commute b (t k) ∧
        Commute a (star (t k)) ∧ Commute b (star (t k)) := by
  let η := δ / 3000
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨r, hr, hcomm, hother⟩ := exists_approximately_central_cuntz_row s t hs hc n η hη
  have hiso (j : ℕ) : star (r j) * r j = 1 := by simpa using hr j j
  have hnorm (j : ℕ) : ‖r j‖ = 1 := by
    have h := congrArg norm (hiso j)
    rw [CStarRing.norm_star_mul_self, norm_one] at h
    nlinarith [norm_nonneg (r j)]
  let q := 1 - r 0 * star (r 0)
  obtain ⟨a, b, u, hujoin, ha, hb, hu, haa, hbb, hab, hsum⟩ :=
    exists_zero_corner_cuntz_pair (r 0) (r 1) (r 2) (hiso 0) (hiso 1) (hiso 2)
      (by simpa using hr 0 1) (by simpa using hr 0 2) (by simpa using hr 1 2)
  have hqstar : star q = q := by simp only [q, star_sub, star_one, star_mul, star_star]
  have hp : (r 0 * star (r 0)) * (r 0 * star (r 0)) = r 0 * star (r 0) := by
    rw [mul_assoc, ← mul_assoc (star (r 0)), hiso, one_mul]
  have hqq : q * q = q := by dsimp only [q]; noncomm_ring [hp]
  have hqne : q ≠ 0 := by
    intro hzero
    have hqr : q * r 1 = r 1 := by
      dsimp only [q]
      rw [sub_mul, one_mul, mul_assoc, show star (r 0) * r 1 = 0 by simpa using hr 0 1,
        mul_zero, sub_zero]
    rw [hzero, zero_mul] at hqr
    have hz := hiso 1
    rw [← hqr, star_zero, zero_mul] at hz
    exact zero_ne_one hz
  have hN : ∀ z ∈ ({r 0, r 1, r 2} : Set E), ‖z‖ ≤ 1 := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl <;> exact (hnorm _).le
  refine ⟨q, a, b, hqne, hqstar, hqq, haa, hbb, hab, hsum, ?_, ?_⟩
  · intro i hi
    have hC : ∀ z ∈ ({r 0, r 1, r 2} : Set E),
        ‖z * s i - s i * z‖ ≤ η ∧ ‖star z * s i - s i * star z‖ ≤ η := by
      intro z hz
      have hz' (j : ℕ) : ‖r j * s i - s i * r j‖ ≤ η ∧
          ‖star (r j) * s i - s i * star (r j)‖ ≤ η := by
        exact ⟨(hcomm j i hi).1.le,
          by rw [zeroCorner_star_commutator_norm]; exact (hcomm j i hi).2.le⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl <;> exact hz' _
    have hCs : ∀ z ∈ ({r 0, r 1, r 2} : Set E),
        ‖z * star (s i) - star (s i) * z‖ ≤ η ∧
        ‖star z * star (s i) - star (s i) * star z‖ ≤ η := by
      intro z hz
      have hz' (j : ℕ) : ‖r j * star (s i) - star (s i) * r j‖ ≤ η ∧
          ‖star (r j) * star (s i) - star (s i) * star (r j)‖ ≤ η := by
        exact ⟨(hcomm j i hi).2.le, by
          rw [zeroCorner_star_commutator_norm, star_star]
          exact (hcomm j i hi).1.le⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl <;> exact hz' _
    have hsmall : 2582 * η < δ := by dsimp only [η]; nlinarith
    have h₁ := zeroCornerPair_commutator_bound (r 0) (r 1) (r 2) (s i) η hη.le hN hC u hu
    have h₂ := zeroCornerPair_commutator_bound (r 0) (r 1) (r 2) (star (s i)) η hη.le hN hCs u hu
    dsimp only at h₁ h₂
    rw [← ha, ← hb] at h₁ h₂
    exact ⟨h₁.1.trans_lt hsmall, h₁.2.trans_lt hsmall,
      h₂.1.trans_lt hsmall, h₂.2.trans_lt hsmall⟩
  · intro k
    have hpoly (y : E) (hry : ∀ j, Commute (r j) y ∧ Commute (star (r j)) y) :
        Commute a y ∧ Commute b y := by
      have hqc := (Commute.one_left y).sub_left ((hry 0).1.mul_left (hry 0).2)
      have huc : Commute (u : E) y := by
        rw [hu]
        exact zeroCornerCompletion_commutes _ _ _ _
          (hry 0).1 (hry 0).2 (hry 1).1 (hry 1).2 (hry 2).1 (hry 2).2
      exact ⟨by rw [ha]; exact (hry 1).1.mul_left hqc,
        by rw [hb]; exact huc.mul_left hqc⟩
    have h₁ := hpoly (t k) (fun j => ⟨(hother j k).1, (hother j k).2.star_left⟩)
    have h₂ := hpoly (star (t k)) (fun j => ⟨(hother j k).2, (hother j k).1.star_star⟩)
    exact ⟨h₁.1, h₁.2, h₂.1, h₂.2⟩

end WeakPureInfiniteness

end

end OAI
