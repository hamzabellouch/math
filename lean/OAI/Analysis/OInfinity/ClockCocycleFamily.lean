import OAI.Analysis.OInfinity.ClockFragmentation

namespace OAI

/-! # Finite families of clocked cocycle contractions

A single joint partition must control every coefficient homotopy. The
maximum cocycle length is fixed before the clock and all error tolerances
are chosen. The final theorem constructs the finite family on that one
partition; it makes no choice of independent towers for different lengths.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

def clockCocycleCost (n : ℕ) : ℝ :=
  2 * ((Fintype.card (Fin (n + 1) → Fin 2) : ℝ) * (5 * ((n : ℝ) + 1))) +
    50 * ((n : ℝ) + 1)

lemma clockCocycleCost_pos (n : ℕ) : 0 < clockCocycleCost n := by
  unfold clockCocycleCost
  positivity

private lemma family_product_commutator (u v : unitary E) (x : E) :
    ‖((u * v : unitary E) : E) * x - x * (u * v : unitary E)‖ ≤
      ‖(u : E) * x - x * (u : E)‖ + ‖(v : E) * x - x * (v : E)‖ := by
  have he : ((u * v : unitary E) : E) * x - x * (u * v : unitary E) =
      ((u : E) * x - x * (u : E)) * (v : E) +
        (u : E) * ((v : E) * x - x * (v : E)) := by
    change ((u : E) * (v : E)) * x - x * ((u : E) * (v : E)) = _
    noncomm_ring
  rw [he]
  simpa only [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul] using norm_add_le
    (((u : E) * x - x * (u : E)) * (v : E))
    ((u : E) * ((v : E) * x - x * (v : E)))


/-- Finite fragmentation is applied to the supplied partition;
only its actual mixed quarter paths are needed. -/
lemma clocked_cocycle_path_on_partition (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1)
    (hcomm : bergRowsCommute s t) {N : ℕ} (e : ZMod N → E)
    (he : ∀ j, IsStarProjection (e j)) (η : ℝ) (hη : 0 < η)
    (hS : ∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ ≤ η)
    (hT : ∀ j, ‖finiteRowShift t (e j) - e (j + 1)‖ ≤ η) (n : ℕ)
    (hquarter : ∀ i r l : Fin 2, i ≠ l → ∃ p : Path
      (binaryCornerUnitary (s i * s r)
        (binaryProduct_isometry _ _ (by simpa using hs i i) (by simpa using hs r r))
        (binaryRowCocycleUnitary s t hs ht hsum htsum n) *
      binaryCornerUnitary (s l) (by simpa using hs l l)
        (star (binaryRowCocycleUnitary s t hs ht hsum htsum n))) 1,
      ClockPathControl p e (8 * Real.pi) η η) :
    ∃ p : Path (binaryRowCocycleUnitary s t hs ht hsum htsum n) 1,
      ClockPathControl p e (320 * Real.pi) (32 * η)
        (40 * (clockCocycleCost n * η + 2 * η)) := by
  let B : ℝ := (Fintype.card (Fin (n + 1) → Fin 2) : ℝ) * (5 * ((n : ℝ) + 1))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let A := 2 * B + 50 * ((n : ℝ) + 1)
  let u := binaryRowCocycleUnitary s t hs ht hsum htsum n
  let α := binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
    (by simpa using hs 1 1) (by simpa using hs 0 1)
  let v := α u
  let C := A * η
  let D := 2 * (n : ℝ) * η
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hrow (i : Fin 2) (j : ZMod N) :
      ‖s i * e j - e (j + 1) * s i‖ ≤ η :=
    cyclic_row_generator_transport s hs e η (fun k => hS k) i j
  have hu (j : ZMod N) : ‖(u : E) * e j - e j * (u : E)‖ ≤ D := by
    have h := binaryRowCocycle_joint_commutator_le s t hs ht hsum htsum e η η
      (fun k => hS k) (fun k => hT k) j n
    exact h.trans_eq (by dsimp only [D]; ring)
  have hDC : D ≤ C := by
    dsimp only [D, C, A]
    nlinarith [mul_nonneg hB hη.le, mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hη.le]
  have hηC : η ≤ C := by
    dsimp only [C, A]
    nlinarith [mul_nonneg hB hη.le, mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hη.le]
  have hv (j : ZMod N) : ‖(v : E) * e j - e j * (v : E)‖ ≤ 10 * (D + η) := by
    have h0 := clock_corner_commutator e (fun k => (he k).isSelfAdjoint.star_eq)
      (s 0) (by simpa using hs 0 0) 1 η D hη.le hD (hrow 0) u hu j
    have h1 := clock_corner_commutator e (fun k => (he k).isSelfAdjoint.star_eq)
      (s 1) (by simpa using hs 1 1) 1 η D hη.le hD (hrow 1) u hu j
    have h := family_product_commutator
      (binaryCornerUnitary (s 0) (by simpa using hs 0 0) u)
      (binaryCornerUnitary (s 1) (by simpa using hs 1 1) u) (e j)
    change ‖(v : E) * e j - e j * (v : E)‖ ≤ _ at h
    exact h.trans (by linarith)
  obtain ⟨c, hc, q, hq⟩ := exists_jointCycle_affine_control s t hs ht hsum htsum hcomm
    e (fun j => (he j).isSelfAdjoint.star_eq) η hη.le
    (fun j => hS j) (fun j => hT j) n
  have hd : u * star v = star c := by
    apply Subtype.ext
    change (u : E) * star (v : E) = star (c : E)
    rw [hc]
    exact binaryRowCocycleUnitary_defect s t hs ht hsum htsum n
  let q₁ : Path (1 : unitary E) (u * star v) :=
    (q.map (continuous_star : Continuous (star : unitary E → unitary E))).cast (by simp) hd
  have hq₁ : ClockPathControl q₁ e (2 * Real.pi) 0 (2 * B * η) := by
    have hh := (hq.map_star (fun j => (he j).isSelfAdjoint.star_eq)).cast
      (show (1 : unitary E) = star (1 : unitary E) by simp) hd
    convert hh using 1; simp only [B]; ring
  have hcancel : (u * star v) * v = u := by simp [mul_assoc]
  let p₀ : Path v u := (q₁.mul (Path.refl v)).cast (one_mul v).symm hcancel.symm
  let p : Path u v := p₀.symm
  have hp : ClockPathControl p e (2 * Real.pi) η C := by
    apply ((hq₁.mul (clockPathControl_refl v e _ hv)).cast (one_mul v).symm hcancel.symm).symm.mono
    · simp
    · simpa using hη.le
    · dsimp only [C, A, D]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hη.le]
  have hc₁ : ∀ i j : Fin 2, i ≠ j → ∃ c : Path
      (binaryCornerUnitary (s i) (by simpa using hs i i) u *
        binaryCornerUnitary (s j) (by simpa using hs j j) (star u)) 1,
      ClockPathControl c e (8 * Real.pi) η C := by
    intro i j hij
    obtain ⟨r, hr⟩ := exists_balanced_clockCancellation e
      (fun k => (he k).isSelfAdjoint.star_eq) (s i) (s j) u
      (by simpa using hs i i) (by simpa using hs j j)
      (by simp only [hs, ite_eq_right hij]) 1 D η hD hη.le (hrow i) (hrow j) hu
    refine ⟨r, hr.mono (by linarith [Real.pi_pos]) hη.le ?_⟩
    dsimp only [C, A, D]
    nlinarith [mul_nonneg hB hη.le, mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hη.le]
  have hc₂ : ∀ i r l : Fin 2, i ≠ l → ∃ c : Path
      (binaryCornerUnitary (s i * s r)
        (binaryProduct_isometry _ _ (by simpa using hs i i) (by simpa using hs r r)) u *
        binaryCornerUnitary (s l) (by simpa using hs l l) (star u)) 1,
      ClockPathControl c e (8 * Real.pi) η C := by
    intro i r l hil
    obtain ⟨q, hq⟩ := hquarter i r l hil
    exact ⟨q, hq.mono le_rfl le_rfl hηC⟩
  obtain ⟨r, hr⟩ := exists_clocked_binaryFragmentation s hs e
    (fun j => (he j).isSelfAdjoint.star_eq) u (2 * Real.pi) (8 * Real.pi) η C η
    (by positivity) (by positivity) hη.le hC hη.le (fun j => (hu j).trans hDC) hrow p hp hc₁ hc₂
  refine ⟨r, ?_⟩
  have hr' : ClockPathControl r e (320 * Real.pi) (32 * η) (40 * (C + 2 * η)) := by
    convert hr using 1; ring
  simpa only [C, A, B, clockCocycleCost] using hr'


private lemma family_isometry_norm (x : E) (hx : star x * x = 1) : ‖x‖ ≤ 1 := by
  have h := congrArg norm hx
  rw [CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg x, (IsStarProjection.one E).norm_le]


private lemma family_near_commutator (x y e : E) (he : ‖e‖ ≤ 1) :
    ‖x * e - e * x‖ ≤ 2 * ‖x - y‖ + ‖y * e - e * y‖ := by
  have hid : x * e - e * x = (x - y) * e - e * (x - y) + (y * e - e * y) := by noncomm_ring
  rw [hid]
  calc
    _ ≤ ‖(x - y) * e - e * (x - y)‖ + ‖y * e - e * y‖ := norm_add_le _ _
    _ ≤ (‖(x - y) * e‖ + ‖e * (x - y)‖) + ‖y * e - e * y‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (‖x - y‖ * ‖e‖ + ‖e‖ * ‖x - y‖) + ‖y * e - e * y‖ := by gcongr <;> apply norm_mul_le
    _ ≤ (‖x - y‖ * 1 + 1 * ‖x - y‖) + ‖y * e - e * y‖ := by gcongr
    _ = _ := by ring



/-- A single clock supplies all mixed quarter paths up to the prescribed finite length. -/
lemma exists_joint_clocked_quarter_family_angular [Nontrivial E] (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1)
    (hcomm : bergRowsCommute s t) (m M : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (k : unitary E) (e : ZMod (2 ^ m) → E),
      (k : E) ^ (2 ^ m) = 1 ∧
      (∀ j, IsStarProjection (e j)) ∧ (∑ j, e j) = 1 ∧
      (∀ j l, j ≠ l → e j * e l = 0) ∧
      (∀ j, (k : E) * e j = e (j + 1) * (k : E)) ∧
      ‖finiteRowShift s k - (k : E)‖ < ε ∧
      (∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ < ε) ∧
      (∀ j, ‖finiteRowShift t (e j) - e (j + 1)‖ < ε) ∧
      ∀ n : ℕ, n ≤ M → ∀ i r l : Fin 2, i ≠ l → ∃ p : ℝ → unitary E, Continuous p ∧
        (p 0 : E) = cornerCompression (s i * s r)
          (binaryRowCocycleUnitary s t hs ht hsum htsum n : E) *
          cornerCompression (s l) (star (binaryRowCocycleUnitary s t hs ht hsum htsum n : E)) ∧
        (p (Real.pi / 2) : E) = 1 ∧ (∀ θ, Joined (1 : unitary E) (p θ)) ∧
        (∀ θ j, ‖(p θ : E) * e j - e j * (p θ : E)‖ < ε) ∧
        ∀ θ φ, ‖(p θ : E) - p φ‖ ≤ 16 * |θ - φ| + ε := by
  let γ := ε / 8
  have hγ : 0 < γ := by dsimp only [γ]; positivity
  obtain ⟨δ, hδ, hpolar⟩ := exists_clockCorrected_unitary_path (E := E) γ hγ
  let η := min (δ / ((M : ℝ) + 2)) (ε / (160 * ((M : ℝ) + 1)))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hcδ : ((M : ℝ) + 2) * η ≤ δ := by
    have h := min_le_left (δ / ((M : ℝ) + 2)) (ε / (160 * ((M : ℝ) + 1)))
    change η ≤ δ / ((M : ℝ) + 2) at h
    calc
      ((M : ℝ) + 2) * η = η * ((M : ℝ) + 2) := mul_comm _ _
      _ ≤ δ := (le_div_iff₀ (by positivity)).mp h
  have htε : 40 * ((M : ℝ) + 1) * η ≤ ε / 4 := by
    have h := min_le_right (δ / ((M : ℝ) + 2)) (ε / (160 * ((M : ℝ) + 1)))
    change η ≤ ε / (160 * ((M : ℝ) + 1)) at h
    have hh := (le_div_iff₀ (show 0 < 160 * ((M : ℝ) + 1) by positivity)).mp h
    nlinarith
  have hηε : η < ε := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) M) hη.le]
  obtain ⟨K, e, hK, hKN, he, hesum, heo, hcycle, hKshift, hKgen, hKt,
      _hKfixed, hS, hT, hVcell, hVK⟩ :=
    exists_joint_binary_clock s t hs ht hsum htsum hcomm m η hη
  let k : unitary E := ⟨K, hK⟩
  have hsn (i : Fin 2) : ‖s i‖ ≤ 1 :=
    family_isometry_norm _ (by simpa only [ite_true] using hs i i)
  have hgen (i : Fin 2) : ‖s i * K - K * s i‖ ≤ η := by
    rw [norm_sub_rev]
    exact (hKgen i).le
  have hprod (i r : Fin 2) : ‖(s i * s r) * K - K * (s i * s r)‖ ≤ 2 * η := by
    have hid : (s i * s r) * K - K * (s i * s r) =
        s i * (s r * K - K * s r) + (s i * K - K * s i) * s r := by noncomm_ring
    rw [hid]
    calc
      _ ≤ ‖s i * (s r * K - K * s r)‖ + ‖(s i * K - K * s i) * s r‖ := norm_add_le _ _
      _ ≤ ‖s i‖ * ‖s r * K - K * s r‖ + ‖s i * K - K * s i‖ * ‖s r‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 1 * η + η * 1 := add_le_add
        (mul_le_mul (hsn i) (hgen r) (norm_nonneg _) (by norm_num))
        (mul_le_mul (hgen i) (hsn r) (norm_nonneg _) hη.le)
      _ = _ := by ring
  refine ⟨k, e, hKN, he, hesum, heo, hcycle, hKshift.trans hηε,
    (fun j => (hS j).trans hηε), (fun j => (hT j).trans hηε), ?_⟩
  intro n hn i r l hil
  have hnreal : (n : ℝ) ≤ M := by exact_mod_cast hn
  let u := binaryRowCocycleUnitary s t hs ht hsum htsum n
  have haa : star (s i * s r) * (s i * s r) = 1 :=
    binaryProduct_isometry _ _ (by simpa only [ite_true] using hs i i)
      (by simpa only [ite_true] using hs r r)
  have hbb : star (s l) * s l = 1 := by simpa only [ite_true] using hs l l
  have hab : star (s i * s r) * s l = 0 := by
    rw [star_mul, mul_assoc, hs i l, ite_eq_right hil, mul_zero]
  have hca : ‖(s i * s r) * (k : E) - (k : E) * (s i * s r)‖ ≤ δ :=
    (hprod i r).trans (by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) M) hη.le])
  have hcb : ‖s l * (k : E) - (k : E) * s l‖ ≤ δ :=
    (hgen l).trans (by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) M) hη.le])
  have hcu : ‖(u : E) * (k : E) - (k : E) * (u : E)‖ ≤ δ :=
    (hVK n).trans (by
      have hm := mul_le_mul_of_nonneg_right hnreal hη.le
      nlinarith)
  obtain ⟨p, hp, hp0, hp1, hpjoin, hpnear⟩ :=
    hpolar k (s i * s r) (s l) u haa hbb hab u.prop hca hcb hcu
  let β := 2 * ((M : ℝ) + 1) * η
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  have hA (j : ZMod (2 ^ m)) : ‖(s i * s r) * e j - e (j + 2) * (s i * s r)‖ ≤ β :=
    (cyclic_row_two_letter_transport s hs e η (fun q => (hS q).le) i r j).trans (by
      dsimp only [β]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) M) hη.le])
  have hB (j : ZMod (2 ^ m)) : ‖s l * e j - e (j + 1) * s l‖ ≤ β :=
    (cyclic_row_generator_transport s hs e η (fun q => (hS q).le) l j).trans (by
      dsimp only [β]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) M) hη.le])
  have hU (j : ZMod (2 ^ m)) : ‖(u : E) * e j - e j * (u : E)‖ ≤ β :=
    (hVcell j n).trans (by
      have hm := mul_le_mul_of_nonneg_right hnreal hη.le
      dsimp only [β]
      nlinarith)
  refine ⟨p, hp, hp0, hp1, hpjoin, ?_, ?_⟩
  · intro θ j
    have hz := clockCorrectedCancellation_cell_commutator k e
      (fun q => (he q).isSelfAdjoint.star_eq) hcycle (s i * s r) (s l) u
      haa hbb β hβ hA hB hU θ j
    have hnear := family_near_commutator (p θ : E)
      (clockCorrectedCancellation k (s i * s r) (s l) u θ) (e j) (he j).norm_le
    have hsmall : 20 * β ≤ ε / 4 := by dsimp only [β]; nlinarith [htε]
    have hn := hpnear θ
    change ‖(p θ : E) - clockCorrectedCancellation k (s i * s r) (s l) u θ‖ < γ at hn
    dsimp only [γ] at hn
    nlinarith
  · intro θ φ
    have hsample := clockCorrected_near_path_sample_bound k (s i * s r) (s l) u haa hbb u.prop
      p γ (fun q => (hpnear q).le) θ φ
    dsimp only [γ] at hsample
    linarith



lemma exists_joint_clocked_quarter_family [Nontrivial E] (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1)
    (hcomm : bergRowsCommute s t) (m M : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ e : ZMod (2 ^ m) → E,
      (∀ j, IsStarProjection (e j)) ∧ (∑ j, e j) = 1 ∧
      (∀ j l, j ≠ l → e j * e l = 0) ∧
      (∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ < ε) ∧
      (∀ j, ‖finiteRowShift t (e j) - e (j + 1)‖ < ε) ∧
      ∀ n : ℕ, n ≤ M → ∀ i r l : Fin 2, i ≠ l → ∃ p : Path
        (binaryCornerUnitary (s i * s r)
          (binaryProduct_isometry _ _ (by simpa using hs i i) (by simpa using hs r r))
          (binaryRowCocycleUnitary s t hs ht hsum htsum n) *
        binaryCornerUnitary (s l) (by simpa using hs l l)
          (star (binaryRowCocycleUnitary s t hs ht hsum htsum n))) 1,
        ClockPathControl p e (8 * Real.pi) ε ε := by
  obtain ⟨k, e, _hk, he, hes, heo, _hc, _hkshift, hS, hT, hpaths⟩ :=
    exists_joint_clocked_quarter_family_angular s t hs ht hsum htsum hcomm m M ε hε
  refine ⟨e, he, hes, heo, hS, hT, ?_⟩
  intro n hn i r l hil
  obtain ⟨p, hp, hp0, hp1, _hjoin, hpc, hpm⟩ := hpaths n hn i r l hil
  let q := unitaryQuarterPath p hp
  have h0 : binaryCornerUnitary (s i * s r)
      (binaryProduct_isometry _ _ (by simpa using hs i i) (by simpa using hs r r))
      (binaryRowCocycleUnitary s t hs ht hsum htsum n) *
      binaryCornerUnitary (s l) (by simpa using hs l l)
        (star (binaryRowCocycleUnitary s t hs ht hsum htsum n)) = p 0 := by
    apply Subtype.ext
    exact hp0.symm
  have h1 : (1 : unitary E) = p (Real.pi / 2) := by
    apply Subtype.ext
    exact hp1.symm
  refine ⟨q.cast h0 h1, ?_⟩
  constructor
  · intro a b
    change ‖(p ((Real.pi / 2) * (a : ℝ)) : E) - p ((Real.pi / 2) * (b : ℝ))‖ ≤ _
    apply (hpm _ _).trans_eq
    rw [← mul_sub, abs_mul, abs_of_pos (half_pos Real.pi_pos)]
    ring
  · intro a j
    exact (hpc _ j).le

/-- One actual joint partition controls every cocycle path in the chosen
finite range. Both errors are selected after that range and the tower
height have been fixed. -/
lemma exists_joint_clocked_cocycle_family [Nontrivial E] (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1)
    (hcomm : bergRowsCommute s t) (m M : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ e : ZMod (2 ^ m) → E,
      (∀ j, IsStarProjection (e j)) ∧ (∑ j, e j) = 1 ∧
      (∀ j l, j ≠ l → e j * e l = 0) ∧
      (∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ < ε) ∧
      (∀ j, ‖finiteRowShift t (e j) - e (j + 1)‖ < ε) ∧
      ∀ n : ℕ, n ≤ M → ∃ p : Path (binaryRowCocycleUnitary s t hs ht hsum htsum n) 1,
        ClockPathControl p e (320 * Real.pi) ε ε := by
  let T := 1 + ∑ n ∈ Finset.range (M + 1), (clockCocycleCost n + 2)
  have hterm (n : ℕ) : 0 ≤ clockCocycleCost n + 2 := by linarith [clockCocycleCost_pos n]
  have hT : 0 < T := by
    have hsum0 : 0 ≤ ∑ n ∈ Finset.range (M + 1), (clockCocycleCost n + 2) :=
      Finset.sum_nonneg (fun n _ => hterm n)
    dsimp only [T]
    linarith
  let η := min (ε / 64) (ε / (80 * T))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηε : η < ε := by
    have h := min_le_left (ε / 64) (ε / (80 * T))
    change η ≤ ε / 64 at h
    linarith
  have hmesh : 32 * η ≤ ε := by
    have h := min_le_left (ε / 64) (ε / (80 * T))
    change η ≤ ε / 64 at h
    linarith
  have hsmall : 40 * T * η ≤ ε := by
    have h := min_le_right (ε / 64) (ε / (80 * T))
    change η ≤ ε / (80 * T) at h
    have hm := (le_div_iff₀ (show 0 < 80 * T by positivity)).mp h
    nlinarith
  obtain ⟨e, he, hes, heo, hS, hTshift, hquarters⟩ :=
    exists_joint_clocked_quarter_family s t hs ht hsum htsum hcomm m M η hη
  refine ⟨e, he, hes, heo, (fun j => (hS j).trans hηε),
    (fun j => (hTshift j).trans hηε), ?_⟩
  intro n hn
  obtain ⟨p, hp⟩ := clocked_cocycle_path_on_partition s t hs ht hsum htsum hcomm e he η hη
    (fun j => (hS j).le) (fun j => (hTshift j).le) n (hquarters n hn)
  have hcost : clockCocycleCost n + 2 ≤ T := by
    have hsingle := Finset.single_le_sum (fun k _ => hterm k)
      (show n ∈ Finset.range (M + 1) from Finset.mem_range.mpr (by omega))
    dsimp only [T]
    linarith
  have hcommbound : 40 * (clockCocycleCost n * η + 2 * η) ≤ ε := by
    calc
      _ = (40 * (clockCocycleCost n + 2)) * η := by ring
      _ ≤ (40 * T) * η := mul_le_mul_of_nonneg_right (by linarith) hη.le
      _ ≤ ε := hsmall
  exact ⟨p, hp.mono le_rfl hmesh hcommbound⟩

end WeakPureInfiniteness

end

end OAI
