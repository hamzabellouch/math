import OAI.Analysis.OInfinity.ClockedCancellation
import OAI.Analysis.OInfinity.AffineReflectionPath

namespace OAI

/-! # Controlled fragmentation on a joint cyclic partition

The clock-corrected quarter paths have a uniform sampled modulus, with an
arbitrarily small additive error. The finite fragmentation operations below
retain that modulus and the actual cell commutators. No continuity estimate
for an arbitrary choice of a polar decomposition is used.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E]

/-- The two estimates needed when a finite path is sampled on the cyclic tower. -/
structure ClockPathControl {u v : unitary E} (p : Path u v) (e : I → E)
    (L ρ C : ℝ) : Prop where
  modulus : ∀ t s, ‖(p t : E) - p s‖ ≤ L * |(t : ℝ) - s| + ρ
  commutator : ∀ t j, ‖(p t : E) * e j - e j * (p t : E)‖ ≤ C

lemma ClockPathControl.mono {u v : unitary E} {p : Path u v} {e : I → E}
    {L ρ C L' ρ' C' : ℝ} (h : ClockPathControl p e L ρ C)
    (hL : L ≤ L') (hρ : ρ ≤ ρ') (hC : C ≤ C') : ClockPathControl p e L' ρ' C' where
  modulus t s := (h.modulus t s).trans
    (add_le_add (mul_le_mul_of_nonneg_right hL (abs_nonneg _)) hρ)
  commutator t j := (h.commutator t j).trans hC

lemma ClockPathControl.cast {u v u' v' : unitary E} {p : Path u v} {e : I → E}
    {L ρ C : ℝ} (h : ClockPathControl p e L ρ C) (hu : u' = u) (hv : v' = v) :
    ClockPathControl (p.cast hu hv) e L ρ C := by
  constructor
  · intro t s
    change ‖(p t : E) - p s‖ ≤ _
    exact h.modulus t s
  · intro t j
    change ‖(p t : E) * e j - e j * (p t : E)‖ ≤ _
    exact h.commutator t j

lemma ClockPathControl.symm {u v : unitary E} {p : Path u v} {e : I → E}
    {L ρ C : ℝ} (h : ClockPathControl p e L ρ C) : ClockPathControl p.symm e L ρ C where
  modulus t s := by
    change ‖(p (unitInterval.symm t) : E) - p (unitInterval.symm s)‖ ≤ _
    have ht := h.modulus (unitInterval.symm t) (unitInterval.symm s)
    simpa only [unitInterval.coe_symm_eq,
      show (1 - (t : ℝ)) - (1 - s) = -((t : ℝ) - s) by ring, abs_neg] using ht
  commutator t j := h.commutator (unitInterval.symm t) j

private lemma clock_product_commutator (u v : unitary E) (x : E) :
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

lemma ClockPathControl.mul {u v w z : unitary E} {p : Path u v} {q : Path w z}
    {e : I → E} {L ρ C K σ D : ℝ}
    (hp : ClockPathControl p e L ρ C) (hq : ClockPathControl q e K σ D) :
    ClockPathControl (p.mul q) e (L + K) (ρ + σ) (C + D) where
  modulus t s := by
    have he : ((p.mul q) t : E) - (p.mul q) s =
        ((p t : E) - p s) * (q t : E) + (p s : E) * ((q t : E) - q s) := by
      change (p t : E) * (q t : E) - (p s : E) * (q s : E) = _
      noncomm_ring
    rw [he]
    calc
      _ ≤ ‖((p t : E) - p s) * (q t : E)‖ + ‖(p s : E) * ((q t : E) - q s)‖ := norm_add_le _ _
      _ = ‖(p t : E) - p s‖ + ‖(q t : E) - q s‖ := by
        rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
      _ ≤ (L * |(t : ℝ) - s| + ρ) + (K * |(t : ℝ) - s| + σ) :=
        add_le_add (hp.modulus t s) (hq.modulus t s)
      _ = _ := by ring
  commutator t j := (clock_product_commutator (p t) (q t) (e j)).trans
    (add_le_add (hp.commutator t j) (hq.commutator t j))

lemma clockPathControl_refl (u : unitary E) (e : I → E) (C : ℝ)
    (hu : ∀ j, ‖(u : E) * e j - e j * (u : E)‖ ≤ C) :
    ClockPathControl (Path.refl u) e 0 0 C where
  modulus _ _ := by simp
  commutator _ j := hu j

/-- Concatenation doubles the mesh speed and adds at most two additive errors. -/
lemma ClockPathControl.trans {u v w : unitary E} {p : Path u v} {q : Path v w}
    {e : I → E} {L ρ C : ℝ} (hρ : 0 ≤ ρ)
    (hp : ClockPathControl p e L ρ C) (hq : ClockPathControl q e L ρ C) :
    ClockPathControl (p.trans q) e (2 * L) (2 * ρ) C where
  modulus := by
    have hord : ∀ t s : unitInterval, (t : ℝ) ≤ s →
        ‖((p.trans q) t : E) - (p.trans q) s‖ ≤ 2 * L * |(t : ℝ) - s| + 2 * ρ := by
      intro t s hts
      by_cases ht : (t : ℝ) ≤ 1 / 2
      · by_cases hs : (s : ℝ) ≤ 1 / 2
        · rw [Path.trans_apply, dite_eq_left ht, Path.trans_apply, dite_eq_left hs]
          calc
            _ ≤ L * |2 * (t : ℝ) - 2 * (s : ℝ)| + ρ := hp.modulus _ _
            _ ≤ _ := by rw [← mul_sub, abs_mul]; norm_num; nlinarith
        · rw [Path.trans_apply, dite_eq_left ht, Path.trans_apply, dite_eq_right hs]
          let t' : unitInterval := ⟨2 * t, by constructor <;> linarith [t.2.1]⟩
          let s' : unitInterval := ⟨2 * s - 1, by constructor <;> linarith [s.2.2]⟩
          change ‖(p t' : E) - q s'‖ ≤ _
          calc
            _ ≤ ‖(p t' : E) - v‖ + ‖(v : E) - q s'‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
            _ ≤ (L * |2 * (t : ℝ) - 1| + ρ) + (L * |0 - (2 * (s : ℝ) - 1)| + ρ) := by
              apply add_le_add
              · simpa only [Path.target, Set.Icc.coe_one] using hp.modulus t' 1
              · simpa only [Path.source, Set.Icc.coe_zero] using hq.modulus 0 s'
            _ = _ := by
              rw [abs_of_nonpos (by linarith : 2 * (t : ℝ) - 1 ≤ 0),
                abs_of_nonpos (by linarith : 0 - (2 * (s : ℝ) - 1) ≤ 0),
                abs_of_nonpos (sub_nonpos.mpr hts)]
              ring
      · have hs : ¬ (s : ℝ) ≤ 1 / 2 := by linarith
        rw [Path.trans_apply, dite_eq_right ht, Path.trans_apply, dite_eq_right hs]
        calc
          _ ≤ L * |(2 * (t : ℝ) - 1) - (2 * (s : ℝ) - 1)| + ρ := hq.modulus _ _
          _ ≤ _ := by
            rw [show (2 * (t : ℝ) - 1) - (2 * (s : ℝ) - 1) = 2 * ((t : ℝ) - s) by ring,
              abs_mul]
            norm_num
            nlinarith
    intro t s
    rcases le_total (t : ℝ) (s : ℝ) with hts | hst
    · exact hord t s hts
    · rw [norm_sub_rev, abs_sub_comm]
      exact hord s t hst
  commutator t j := by
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [Path.trans_apply, dite_eq_left ht]
      exact hp.commutator _ j
    · rw [Path.trans_apply, dite_eq_right ht]
      exact hq.commutator _ j

private lemma clock_fragment_isometry_norm (a : E) (ha : star a * a = 1) : ‖a‖ ≤ 1 := by
  have h := congrArg norm ha
  rw [CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg a, (IsStarProjection.one E).norm_le]

lemma clock_corner_commutator {N : ℕ} (e : ZMod N → E)
    (he : ∀ j, star (e j) = e j) (a : E) (ha : star a * a = 1)
    (d : ZMod N) (δ C : ℝ) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hat : ∀ j, ‖a * e j - e (j + d) * a‖ ≤ δ)
    (u : unitary E) (hu : ∀ j, ‖(u : E) * e j - e j * (u : E)‖ ≤ C) (j : ZMod N) :
    ‖(binaryCornerUnitary a ha u : E) * e j - e j * (binaryCornerUnitary a ha u : E)‖ ≤
      5 * (C + δ) := by
  have han := clock_fragment_isometry_norm a ha
  have hun := clock_fragment_isometry_norm (u : E) u.prop.1
  have hnorm : ‖(u : E) - 1‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [(IsStarProjection.one E).norm_le])
  have huc (i : ZMod N) : ‖((u : E) - 1) * e i - e i * ((u : E) - 1)‖ ≤ C + δ := by
    have hid : ((u : E) - 1) * e i - e i * ((u : E) - 1) =
        (u : E) * e i - e i * (u : E) := by noncomm_ring
    rw [hid]
    exact (hu i).trans (le_add_of_nonneg_right hδ)
  have h := tower_sandwich_transport e he a a ((u : E) - 1) d d (C + δ)
    (add_nonneg hC hδ) han han hnorm
    (fun i => (hat i).trans (le_add_of_nonneg_left hC))
    (fun i => (hat i).trans (le_add_of_nonneg_left hC)) huc j
  have hid : (binaryCornerUnitary a ha u : E) * e j - e j * (binaryCornerUnitary a ha u : E) =
      (a * ((u : E) - 1) * star a) * e j - e j * (a * ((u : E) - 1) * star a) := by
    change cornerCompression a u * e j - e j * cornerCompression a u = _
    unfold cornerCompression
    noncomm_ring
  rw [hid]
  simpa only [add_sub_cancel_right] using h

lemma ClockPathControl.corner {N : ℕ} {u v : unitary E} {p : Path u v}
    {e : ZMod N → E} {L ρ C δ : ℝ} (hp : ClockPathControl p e L ρ C)
    (he : ∀ j, star (e j) = e j) (a : E) (ha : star a * a = 1) (d : ZMod N)
    (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hat : ∀ j, ‖a * e j - e (j + d) * a‖ ≤ δ) :
    ClockPathControl (binaryCornerPath a ha p) e L ρ (5 * (C + δ)) where
  modulus t s := (binaryCornerUnitary_sub_norm_le a ha (p t) (p s)).trans (hp.modulus t s)
  commutator t j := clock_corner_commutator e he a ha d δ C hδ hC hat (p t)
    (fun l => hp.commutator t l) j


/-- The actual corrected angular paths, expressed on the unit interval
with the two estimates used by fragmentation. -/
lemma exists_joint_clocked_quarter_control [Nontrivial E] (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1)
    (hcomm : bergRowsCommute s t) (m n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ e : ZMod (2 ^ m) → E,
      (∀ j, IsStarProjection (e j)) ∧ (∑ j, e j) = 1 ∧
      (∀ j l, j ≠ l → e j * e l = 0) ∧
      (∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ < ε) ∧
      (∀ j, ‖finiteRowShift t (e j) - e (j + 1)‖ < ε) ∧
      ∀ i r l : Fin 2, i ≠ l → ∃ p : Path
        (binaryCornerUnitary (s i * s r)
          (binaryProduct_isometry (s i) (s r) (by simpa using hs i i) (by simpa using hs r r))
          (binaryRowCocycleUnitary s t hs ht hsum htsum n) *
        binaryCornerUnitary (s l) (by simpa using hs l l)
          (star (binaryRowCocycleUnitary s t hs ht hsum htsum n))) 1,
        ClockPathControl p e (8 * Real.pi) ε ε := by
  obtain ⟨k, e, _hk, he, hes, heo, _hc, _hkshift, hS, hT, hpaths⟩ :=
    exists_joint_clocked_quarter_paths s t hs ht hsum htsum hcomm m n ε hε
  refine ⟨e, he, hes, heo, hS, hT, ?_⟩
  intro i r l hil
  obtain ⟨p, hp, hp0, hp1, _hjoin, hpc, hpm⟩ := hpaths i r l hil
  let q := unitaryQuarterPath p hp
  have h0 : binaryCornerUnitary (s i * s r)
      (binaryProduct_isometry (s i) (s r) (by simpa using hs i i) (by simpa using hs r r))
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

private lemma clock_fragment_product_transport {N : ℕ} (e : ZMod N → E)
    (a b : E) (han : ‖a‖ ≤ 1) (hbn : ‖b‖ ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ j, ‖a * e j - e (j + 1) * a‖ ≤ δ)
    (hb : ∀ j, ‖b * e j - e (j + 1) * b‖ ≤ δ) (j : ZMod N) :
    ‖a * b * e j - e (j + 2) * (a * b)‖ ≤ 2 * δ := by
  have hid : a * b * e j - e (j + 2) * (a * b) =
      a * (b * e j - e (j + 1) * b) + (a * e (j + 1) - e (j + 2) * a) * b := by
    noncomm_ring
  have hat := ha (j + 1)
  rw [show (j + 1) + 1 = j + 2 by ring] at hat
  rw [hid]
  calc
    _ ≤ ‖a * (b * e j - e (j + 1) * b)‖ + ‖(a * e (j + 1) - e (j + 2) * a) * b‖ := norm_add_le _ _
    _ ≤ ‖a‖ * ‖b * e j - e (j + 1) * b‖ + ‖a * e (j + 1) - e (j + 2) * a‖ * ‖b‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ 1 * δ + δ * 1 := add_le_add
      (mul_le_mul han (hb j) (norm_nonneg _) (by norm_num))
      (mul_le_mul hat hbn (norm_nonneg _) hδ)
    _ = _ := by ring

/-- The finite quarter-fragmentation step preserves cell commutators and
an additive sampled modulus. Its cancellation paths are kept literal. -/
lemma exists_clocked_binaryQuarter {N : ℕ} (e : ZMod N → E)
    (he : ∀ j, star (e j) = e j) (a b A B : E)
    (ha : star a * a = 1) (hb : star b * b = 1)
    (hA : star A * A = 1) (hB : star B * B = 1)
    (u : unitary E) (L K ρ C δ : ℝ)
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hu : ∀ j, ‖(u : E) * e j - e j * (u : E)‖ ≤ C)
    (haT : ∀ j, ‖a * e j - e (j + 1) * a‖ ≤ δ)
    (hAT : ∀ j, ‖A * e j - e (j + 1) * A‖ ≤ δ)
    (hBT : ∀ j, ‖B * e j - e (j + 1) * B‖ ≤ δ)
    (p : Path u (binaryCornerUnitary a ha u * binaryCornerUnitary b hb u))
    (hp : ClockPathControl p e L ρ C)
    (c₁ : Path (binaryCornerUnitary A hA u * binaryCornerUnitary B hB (star u)) 1)
    (hc₁ : ClockPathControl c₁ e K ρ C)
    (c₂ : Path (binaryCornerUnitary (A * b) (binaryProduct_isometry A b hA hb) u *
      binaryCornerUnitary B hB (star u)) 1)
    (hc₂ : ClockPathControl c₂ e K ρ C) :
    ∃ r : Path (binaryCornerUnitary (A * a) (binaryProduct_isometry A a hA ha) u) 1,
      ClockPathControl r e (4 * (L + K)) (4 * ρ) (10 * (C + 2 * δ)) := by
  let R := A * a
  let S := A * b
  have hR : star R * R = 1 := binaryProduct_isometry A a hA ha
  have hS : star S * S = 1 := binaryProduct_isometry A b hA hb
  let uR := binaryCornerUnitary R hR u
  let uS := binaryCornerUnitary S hS u
  let uB := binaryCornerUnitary B hB (star u)
  have heq : binaryCornerUnitary A hA
      (binaryCornerUnitary a ha u * binaryCornerUnitary b hb u) * uB = uR * uS * uB := by
    rw [binaryCornerUnitary_mul, binaryCornerUnitary_comp A a hA ha hR,
      binaryCornerUnitary_comp A b hA hb hS]
  have huStar (j : ZMod N) : ‖((star u : unitary E) : E) * e j - e j * ((star u : unitary E) : E)‖ ≤ C := by
    simpa only [Unitary.coe_star] using (adjoint_unitary_commutator_norm u (e j) (he j)).le.trans (hu j)
  have huBc (j : ZMod N) : ‖(uB : E) * e j - e j * (uB : E)‖ ≤ 5 * (C + δ) :=
    clock_corner_commutator e he B hB 1 δ C hδ hC hBT (star u) huStar j
  have huRc (j : ZMod N) : ‖(uR : E) * e j - e j * (uR : E)‖ ≤ 5 * (C + 2 * δ) :=
    clock_corner_commutator e he R hR 2 (2 * δ) C (by positivity) hC
      (clock_fragment_product_transport e A a (clock_fragment_isometry_norm A hA)
        (clock_fragment_isometry_norm a ha) δ hδ hAT haT) u hu j
  let d₀ := (binaryCornerPath A hA p).mul (Path.refl uB)
  let d : Path (binaryCornerUnitary A hA u * uB) (uR * uS * uB) := d₀.cast rfl heq.symm
  let f₀ := (Path.refl uR).mul c₂
  let f : Path (uR * uS * uB) uR := f₀.cast (mul_assoc _ _ _) (mul_one _).symm
  let H := 10 * (C + 2 * δ)
  have hd : ClockPathControl d e (L + K) ρ H := by
    have h := (hp.corner he A hA 1 hδ hC hAT).mul (clockPathControl_refl uB e _ huBc)
    apply (h.cast rfl heq.symm).mono
    · linarith
    · simp
    · dsimp only [H]; linarith
  have hf : ClockPathControl f e (L + K) ρ H := by
    have h := (clockPathControl_refl uR e _ huRc).mul hc₂
    apply (h.cast (mul_assoc _ _ _) (mul_one _).symm).mono
    · linarith
    · simp
    · dsimp only [H]; linarith
  have hc : ClockPathControl c₁ e (L + K) ρ H := hc₁.mono (by linarith) le_rfl (by dsimp only [H]; linarith)
  have hfirst := hd.symm.trans hρ hc
  have hfs : ClockPathControl f.symm e (2 * (L + K)) (2 * ρ) H :=
    hf.symm.mono (by linarith) (by linarith) le_rfl
  exact ⟨f.symm.trans (d.symm.trans c₁), by
    simpa only [H, show 2 * (2 * (L + K)) = 4 * (L + K) by ring,
      show 2 * (2 * ρ) = 4 * ρ by ring] using hfs.trans (by positivity) hfirst⟩


/-- The complete finite binary fragmentation, with its actual supplied
quarter paths and quantitative tower control. -/
lemma exists_clocked_binaryFragmentation {N : ℕ} (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (e : ZMod N → E) (he : ∀ j, star (e j) = e j)
    (u : unitary E) (L K ρ C δ : ℝ)
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hu : ∀ j, ‖(u : E) * e j - e j * (u : E)‖ ≤ C)
    (hT : ∀ i j, ‖s i * e j - e (j + 1) * s i‖ ≤ δ)
    (p : Path u (binaryCornerUnitary (s 0) (by simpa using hs 0 0) u *
      binaryCornerUnitary (s 1) (by simpa using hs 1 1) u))
    (hp : ClockPathControl p e L ρ C)
    (hc₁ : ∀ i j : Fin 2, i ≠ j → ∃ c : Path
      (binaryCornerUnitary (s i) (by simpa using hs i i) u *
        binaryCornerUnitary (s j) (by simpa using hs j j) (star u)) 1,
      ClockPathControl c e K ρ C)
    (hc₂ : ∀ i r l : Fin 2, i ≠ l → ∃ c : Path
      (binaryCornerUnitary (s i * s r)
        (binaryProduct_isometry _ _ (by simpa using hs i i) (by simpa using hs r r)) u *
        binaryCornerUnitary (s l) (by simpa using hs l l) (star u)) 1,
      ClockPathControl c e K ρ C) :
    ∃ r : Path u 1,
      ClockPathControl r e (32 * (L + K)) (32 * ρ) (40 * (C + 2 * δ)) := by
  let a := s 0
  let b := s 1
  have ha : star a * a = 1 := by simpa only [a, ite_true] using hs 0 0
  have hb : star b * b = 1 := by simpa only [b, ite_true] using hs 1 1
  have hab : star a * b = 0 := by simpa [a, b] using hs 0 1
  have hba : star b * a = 0 := by simpa [a, b] using hs 1 0
  let p' : Path u (binaryCornerUnitary b hb u * binaryCornerUnitary a ha u) :=
    p.cast rfl (binaryCornerUnitary_commute a b ha hb hab u u).eq.symm
  have hp' : ClockPathControl p' e L ρ C :=
    hp.cast rfl (binaryCornerUnitary_commute a b ha hb hab u u).eq.symm
  obtain ⟨cab, hcab⟩ := hc₁ 0 1 (by decide)
  obtain ⟨cba, hcba⟩ := hc₁ 1 0 (by decide)
  obtain ⟨caab, hcaab⟩ := hc₂ 0 1 1 (by decide)
  obtain ⟨caaa, hcaaa⟩ := hc₂ 0 0 1 (by decide)
  obtain ⟨cbbb, hcbbb⟩ := hc₂ 1 1 0 (by decide)
  obtain ⟨cbba, hcbba⟩ := hc₂ 1 0 0 (by decide)
  obtain ⟨rAA, hAA⟩ := exists_clocked_binaryQuarter e he a b a b ha hb ha hb
    u L K ρ C δ hL hK hρ hC hδ hu (hT 0) (hT 0) (hT 1) p hp cab hcab caab hcaab
  obtain ⟨rAB, hAB⟩ := exists_clocked_binaryQuarter e he b a a b hb ha ha hb
    u L K ρ C δ hL hK hρ hC hδ hu (hT 1) (hT 0) (hT 1) p' hp' cab hcab caaa hcaaa
  obtain ⟨rBA, hBA⟩ := exists_clocked_binaryQuarter e he a b b a ha hb hb ha
    u L K ρ C δ hL hK hρ hC hδ hu (hT 0) (hT 1) (hT 0) p hp cba hcba cbbb hcbbb
  obtain ⟨rBB, hBB⟩ := exists_clocked_binaryQuarter e he b a b a hb ha hb ha
    u L K ρ C δ hL hK hρ hC hδ hu (hT 1) (hT 1) (hT 0) p' hp' cba hcba cbba hcbba
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
  have hLift : ClockPathControl liftP e (2 * L) (2 * ρ) (10 * (C + δ)) := by
    simpa only [show L + L = 2 * L by ring, show ρ + ρ = 2 * ρ by ring,
      show 5 * (C + δ) + 5 * (C + δ) = 10 * (C + δ) by ring] using
      ((hp.corner he a ha 1 hδ hC (hT 0)).mul (hp.corner he b hb 1 hδ hC (hT 1))).cast rfl hU
  let Q := 4 * (L + K)
  let H := 10 * (C + 2 * δ)
  have hp₂ : ClockPathControl p e (2 * L) (2 * ρ) H :=
    hp.mono (by linarith) (by linarith) (by dsimp only [H]; linarith)
  have hlift₂ : ClockPathControl liftP e (2 * L) (2 * ρ) H :=
    hLift.mono le_rfl le_rfl (by dsimp only [H]; linarith)
  let first : Path u U := p.trans liftP
  have hFirst : ClockPathControl first e (4 * L) (4 * ρ) H := by
    simpa only [show 2 * (2 * L) = 4 * L by ring,
      show 2 * (2 * ρ) = 4 * ρ by ring] using hp₂.trans (by positivity) hlift₂
  let last : Path U 1 := ((rAA.mul rAB).mul (rBA.mul rBB)).cast rfl (by simp)
  have hLast : ClockPathControl last e (4 * Q) (16 * ρ) (4 * H) := by
    simpa only [Q, H, show (4 * (L + K) + 4 * (L + K)) +
      (4 * (L + K) + 4 * (L + K)) = 4 * (4 * (L + K)) by ring,
      show (4 * ρ + 4 * ρ) + (4 * ρ + 4 * ρ) = 16 * ρ by ring,
      show (10 * (C + 2 * δ) + 10 * (C + 2 * δ)) +
      (10 * (C + 2 * δ) + 10 * (C + 2 * δ)) = 4 * (10 * (C + 2 * δ)) by ring] using
      ((hAA.mul hAB).mul (hBA.mul hBB)).cast rfl (by simp)
  have hFirst' : ClockPathControl first e (4 * Q) (16 * ρ) (4 * H) :=
    hFirst.mono (by dsimp only [Q]; linarith) (by linarith) (by dsimp only [H]; linarith)
  refine ⟨first.trans last, ?_⟩
  simpa only [Q, H, show 2 * (4 * (4 * (L + K))) = 32 * (L + K) by ring,
    show 2 * (16 * ρ) = 32 * ρ by ring,
    show 4 * (10 * (C + 2 * δ)) = 40 * (C + 2 * δ) by ring] using
    hFirst'.trans (by positivity) hLast


/-- Equal-degree cancellation needs no clock correction: its literal
quarter rotation already almost commutes with the partition. -/
lemma exists_balanced_clockCancellation {N : ℕ} (e : ZMod N → E)
    (he : ∀ j, star (e j) = e j) (a b : E) (u : unitary E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hab : star a * b = 0)
    (d : ZMod N) (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (haT : ∀ j, ‖a * e j - e (j + d) * a‖ ≤ δ)
    (hbT : ∀ j, ‖b * e j - e (j + d) * b‖ ≤ δ)
    (hu : ∀ j, ‖(u : E) * e j - e j * (u : E)‖ ≤ C) :
    ∃ p : Path (binaryCornerUnitary a ha u * binaryCornerUnitary b hb (star u)) 1,
      ClockPathControl p e (2 * Real.pi) 0 (20 * (C + δ)) := by
  let v (θ : ℝ) : unitary E := ⟨cornerCancellationPath a b u θ,
    cornerCancellationPath_mem 1 a b u (by simp) ha hb hab
      (mul_one _) (mul_one _) (one_mul _) (mul_one _) u.prop.1 u.prop.2 θ⟩
  have hv : Continuous v := (cornerCancellationPath_continuous a b (u : E)).subtype_mk _
  have h0 : binaryCornerUnitary a ha u * binaryCornerUnitary b hb (star u) = v 0 := by
    apply Subtype.ext
    exact (cornerCancellationPath_zero a b (u : E)).symm
  have h1 : (1 : unitary E) = v (Real.pi / 2) := by
    apply Subtype.ext
    exact (cornerCancellationPath_quarter 1 a b u (by simp) ha hb hab
      (mul_one _) (mul_one _) (one_mul _) (mul_one _) u.prop.1 u.prop.2).symm
  refine ⟨(unitaryQuarterPath v hv).cast h0 h1, ?_⟩
  constructor
  · intro t s
    change ‖((unitaryQuarterPath v hv) t : E) - (unitaryQuarterPath v hv) s‖ ≤ _
    simpa only [add_zero] using unitaryQuarterPath_sub_norm_le v hv
      (cornerCancellationPath_sub_norm_le 1 a b u (by simp) ha hb hab
        (mul_one _) (mul_one _) (one_mul _) (mul_one _) u.prop.1 u.prop.2) t s
  · intro t j
    let θ := (Real.pi / 2) * (t : ℝ)
    have h := cornerCancellationPath_tower_transport e he a b u ha hb hab d d
      (C + δ) (add_nonneg hC hδ)
      (fun l => (haT l).trans (le_add_of_nonneg_left hC))
      (fun l => (hbT l).trans (le_add_of_nonneg_left hC))
      (fun l => (hu l).trans (le_add_of_nonneg_right hδ)) θ j
    have hid : e j * (1 + (Real.cos θ ^ 2) •
        (a * ((u : E) - 1) * star a + b * (star (u : E) - 1) * star b)) +
        e (j + d - d) * ((Real.sin θ * Real.cos θ) • (a * ((u : E) - 1) * star b)) -
        e (j + d - d) * ((Real.sin θ * Real.cos θ) • (b * (star (u : E) - 1) * star a)) =
        e j * cornerCancellationPath a b u θ := by
      rw [cornerCancellationPath_three_terms a b u ha hb hab u.prop.2 θ]
      simp only [add_sub_cancel_right, mul_add, mul_sub, mul_smul_comm, smul_sub]
      module
    rw [hid] at h
    exact h


private lemma clock_jointWord_norm (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (n : ℕ) (w : Fin (n + 1) → Fin 2) : ‖finiteJointWord s t n w‖ ≤ 1 := by
  induction n with
  | zero =>
      change ‖t (w 0)‖ ≤ 1
      exact clock_fragment_isometry_norm _ (by simpa using ht (w 0) (w 0))
  | succ n ih =>
      change ‖s (w 0) * finiteJointWord s t n (Fin.tail w)‖ ≤ 1
      apply (norm_mul_le _ _).trans
      exact (mul_le_mul (clock_fragment_isometry_norm _ (by simpa using hs (w 0) (w 0)))
        (ih (Fin.tail w)) (norm_nonneg _) (by norm_num)).trans (by norm_num)

private lemma clock_jointWord_transport {N : ℕ} (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (e : ZMod N → E) (η : ℝ) (hη : 0 ≤ η)
    (hS : ∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ ≤ η)
    (hT : ∀ j, ‖finiteRowShift t (e j) - e (j + 1)‖ ≤ η)
    (n : ℕ) (w : Fin (n + 1) → Fin 2) (j : ZMod N) :
    ‖finiteJointWord s t n w * e j - e (j + ((n + 1 : ℕ) : ZMod N)) *
      finiteJointWord s t n w‖ ≤ ((n : ℝ) + 1) * η := by
  induction n generalizing j with
  | zero =>
      simpa only [finiteJointWord, Nat.cast_zero, Nat.cast_one, zero_add, one_mul] using
        cyclic_row_generator_transport t ht e η hT (w 0) j
  | succ n ih =>
      let v := finiteJointWord s t n (Fin.tail w)
      have hv := ih (Fin.tail w) j
      have ha := cyclic_row_generator_transport s hs e η hS (w 0) (j + ((n + 1 : ℕ) : ZMod N))
      have hind : j + ((n + 1 : ℕ) : ZMod N) + 1 = j + ((n + 1 + 1 : ℕ) : ZMod N) := by
        push_cast
        ring
      rw [hind] at ha
      have hid : (s (w 0) * v) * e j - e (j + ((n + 1 + 1 : ℕ) : ZMod N)) * (s (w 0) * v) =
          s (w 0) * (v * e j - e (j + ((n + 1 : ℕ) : ZMod N)) * v) +
          (s (w 0) * e (j + ((n + 1 : ℕ) : ZMod N)) -
            e (j + ((n + 1 + 1 : ℕ) : ZMod N)) * s (w 0)) * v := by noncomm_ring
      change ‖(s (w 0) * v) * e j - e (j + ((n + 1 + 1 : ℕ) : ZMod N)) * (s (w 0) * v)‖ ≤ _
      rw [hid]
      calc
        _ ≤ ‖s (w 0) * (v * e j - e (j + ((n + 1 : ℕ) : ZMod N)) * v)‖ +
            ‖(s (w 0) * e (j + ((n + 1 : ℕ) : ZMod N)) -
              e (j + ((n + 1 + 1 : ℕ) : ZMod N)) * s (w 0)) * v‖ := norm_add_le _ _
        _ ≤ ‖s (w 0)‖ * ‖v * e j - e (j + ((n + 1 : ℕ) : ZMod N)) * v‖ +
            ‖s (w 0) * e (j + ((n + 1 : ℕ) : ZMod N)) -
              e (j + ((n + 1 + 1 : ℕ) : ZMod N)) * s (w 0)‖ * ‖v‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ 1 * (((n : ℝ) + 1) * η) + η * 1 := add_le_add
          (mul_le_mul (clock_fragment_isometry_norm _ (by simpa using hs (w 0) (w 0)))
            hv (norm_nonneg _) (by norm_num))
          (mul_le_mul ha (clock_jointWord_norm s t hs ht n (Fin.tail w)) (norm_nonneg _) hη)
        _ = _ := by push_cast; ring

/-- Balanced finite matrix words commute approximately with the actual
joint partition. This applies to each reflection in the cycle factorization. -/
lemma finiteJointPermutation_commutator_le {N : ℕ} (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (e : ZMod N → E) (he : ∀ j, star (e j) = e j) (η : ℝ) (hη : 0 ≤ η)
    (hS : ∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ ≤ η)
    (hT : ∀ j, ‖finiteRowShift t (e j) - e (j + 1)‖ ≤ η)
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 1) → Fin 2)) (j : ZMod N) :
    ‖finiteRowPermutation (finiteJointWord s t n) σ * e j -
      e j * finiteRowPermutation (finiteJointWord s t n) σ‖ ≤
      (Fintype.card (Fin (n + 1) → Fin 2) : ℝ) * (5 * (((n : ℝ) + 1) * η)) := by
  let D := ((n : ℝ) + 1) * η
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hterm (w : Fin (n + 1) → Fin 2) :
      ‖(finiteJointWord s t n (σ w) * star (finiteJointWord s t n w)) * e j -
        e j * (finiteJointWord s t n (σ w) * star (finiteJointWord s t n w))‖ ≤ 5 * D := by
    have h := tower_sandwich_transport e he (finiteJointWord s t n (σ w))
      (finiteJointWord s t n w) 1 ((n + 1 : ℕ) : ZMod N) ((n + 1 : ℕ) : ZMod N)
      D hD (clock_jointWord_norm s t hs ht n (σ w)) (clock_jointWord_norm s t hs ht n w)
      (by exact (IsStarProjection.one E).norm_le.trans (by norm_num))
      (clock_jointWord_transport s t hs ht e η hη hS hT n (σ w))
      (clock_jointWord_transport s t hs ht e η hη hS hT n w)
      (by intro l; simpa using hD) j
    simpa only [mul_one, add_sub_cancel_right] using h
  rw [finiteRowPermutation, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ w, ‖(finiteJointWord s t n (σ w) * star (finiteJointWord s t n w)) * e j -
        e j * (finiteJointWord s t n (σ w) * star (finiteJointWord s t n w))‖ := norm_sum_le _ _
    _ ≤ ∑ _w : Fin (n + 1) → Fin 2, 5 * D := Finset.sum_le_sum (fun w _ => hterm w)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, D]


lemma ClockPathControl.map_star {u v : unitary E} {p : Path u v} {e : I → E}
    {L ρ C : ℝ} (hp : ClockPathControl p e L ρ C) (he : ∀ j, star (e j) = e j) :
    ClockPathControl (p.map (continuous_star : Continuous (star : unitary E → unitary E))) e L ρ C where
  modulus t s := by
    change ‖star (p t : E) - star (p s : E)‖ ≤ _
    rw [← star_sub, norm_star]
    exact hp.modulus t s
  commutator t j := by
    change ‖star (p t : E) * e j - e j * star (p t : E)‖ ≤ _
    exact (adjoint_unitary_commutator_norm (p t) (e j) (he j)).le.trans (hp.commutator t j)

/-- The literal two-reflection path for the splitting defect retains the
finite joint-word commutator bound. -/
lemma exists_jointCycle_affine_control {N : ℕ} (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1)
    (hcomm : bergRowsCommute s t) (e : ZMod N → E)
    (he : ∀ j, star (e j) = e j) (η : ℝ) (hη : 0 ≤ η)
    (hS : ∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ ≤ η)
    (hT : ∀ j, ‖finiteRowShift t (e j) - e (j + 1)‖ ≤ η) (n : ℕ) :
    ∃ (c : unitary E), (c : E) = finiteJointCycleCoboundary t s n ∧
      ∃ p : Path (1 : unitary E) c, ClockPathControl p e (2 * Real.pi) 0
        (2 * (Fintype.card (Fin (n + 1) → Fin 2) : ℝ) * (5 * (((n : ℝ) + 1) * η))) := by
  let r := finiteJointWord t s n
  have hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0 :=
    finiteJointWord_gram 1 t s (by simp) (by simp) ht hs htsum hsum n
  have hrs : (∑ i, r i * star (r i)) = 1 :=
    finiteJointWord_sum 1 t s (by simp) (by simp) ht htsum hsum n
  let a := finiteRowPermutationUnitary 1 r (by simp) (by simp) hr hrs (finiteCoordinateReflection (n + 1) 0)
  let b := finiteRowPermutationUnitary 1 r (by simp) (by simp) hr hrs (finiteCoordinateReflection (n + 1) 1)
  let c := finiteRowPermutationUnitary 1 r (by simp) (by simp) hr hrs (finiteCoordinateCycle (n + 1))
  have ha : star (a : E) = (a : E) :=
    finiteRowPermutationUnitary_involution 1 r (by simp) (by simp) hr hrs _ (finiteCoordinateReflection_sq (n + 1) 0)
  have hb : star (b : E) = (b : E) :=
    finiteRowPermutationUnitary_involution 1 r (by simp) (by simp) hr hrs _ (finiteCoordinateReflection_sq (n + 1) 1)
  have hc : c = a * b := by
    dsimp only [c, a, b]
    let σ : Equiv.Perm (Fin (n + 1) → Fin 2) := finiteCoordinateReflection (n + 1) 0
    let τ : Equiv.Perm (Fin (n + 1) → Fin 2) := finiteCoordinateReflection (n + 1) 1
    have hfactor : (finiteCoordinateCycle (n + 1) : Equiv.Perm (Fin (n + 1) → Fin 2)) = σ * τ :=
      finiteCoordinateCycle_factor (n + 1)
    rw [hfactor]
    exact finiteRowPermutationUnitary_mul 1 r (by simp) (by simp) hr hrs σ τ
  let H := (Fintype.card (Fin (n + 1) → Fin 2) : ℝ) * (5 * (((n : ℝ) + 1) * η))
  have hca (j : ZMod N) : ‖(a : E) * e j - e j * (a : E)‖ ≤ H := by
    change ‖(finiteRowPermutation r (finiteCoordinateReflection (n + 1) 0) + (1 - 1)) * e j -
      e j * (finiteRowPermutation r (finiteCoordinateReflection (n + 1) 0) + (1 - 1))‖ ≤ H
    simpa only [sub_self, add_zero] using
      finiteJointPermutation_commutator_le t s ht hs e he η hη hT hS n
        (finiteCoordinateReflection (n + 1) 0) j
  have hcb (j : ZMod N) : ‖(b : E) * e j - e j * (b : E)‖ ≤ H := by
    change ‖(finiteRowPermutation r (finiteCoordinateReflection (n + 1) 1) + (1 - 1)) * e j -
      e j * (finiteRowPermutation r (finiteCoordinateReflection (n + 1) 1) + (1 - 1))‖ ≤ H
    simpa only [sub_self, add_zero] using
      finiteJointPermutation_commutator_le t s ht hs e he η hη hT hS n
        (finiteCoordinateReflection (n + 1) 1) j
  have hpa : ClockPathControl (affineReflectionPath a ha) e Real.pi 0 H := by
    constructor
    · intro x y
      simpa only [add_zero] using affineReflectionPath_sub_norm_le a ha x y
    · intro x j
      exact (affineReflectionPath_commutator_bound a ha x (e j)).trans (hca j)
  have hpb : ClockPathControl (affineReflectionPath b hb) e Real.pi 0 H := by
    constructor
    · intro x y
      simpa only [add_zero] using affineReflectionPath_sub_norm_le b hb x y
    · intro x j
      exact (affineReflectionPath_commutator_bound b hb x (e j)).trans (hcb j)
  refine ⟨c, ?_, ((affineReflectionPath a ha).mul (affineReflectionPath b hb)).cast (by simp) hc, ?_⟩
  · change finiteRowPermutation r (finiteCoordinateCycle (n + 1)) + (1 - 1) = _
    rw [sub_self, add_zero]
    exact (finiteJointCycleCoboundary_eq_permutation 1 t s (by simp) (by simp)
      ht hs htsum hsum (fun i j => (hcomm j i).1.symm) n).symm
  · simpa only [H, add_zero, show Real.pi + Real.pi = 2 * Real.pi by ring,
      show 2 * (Fintype.card (Fin (n + 1) → Fin 2) : ℝ) * (5 * (((n : ℝ) + 1) * η)) =
        (Fintype.card (Fin (n + 1) → Fin 2) : ℝ) * (5 * (((n : ℝ) + 1) * η)) +
        (Fintype.card (Fin (n + 1) → Fin 2) : ℝ) * (5 * (((n : ℝ) + 1) * η)) by ring] using (hpa.mul hpb).cast (by simp) hc


/-- Actual cocycle contractions on an actual joint partition. The speed is
uniform in the cocycle length; both additive sampling error and cell
commutators can be made arbitrarily small. The source rows here are full
coisometric binary rows. -/
lemma exists_joint_clocked_cocycle_path [Nontrivial E] (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1)
    (hcomm : bergRowsCommute s t) (m n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ e : ZMod (2 ^ m) → E,
      (∀ j, IsStarProjection (e j)) ∧ (∑ j, e j) = 1 ∧
      (∀ j l, j ≠ l → e j * e l = 0) ∧
      (∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ < ε) ∧
      (∀ j, ‖finiteRowShift t (e j) - e (j + 1)‖ < ε) ∧
      ∃ p : Path (binaryRowCocycleUnitary s t hs ht hsum htsum n) 1,
        ClockPathControl p e (320 * Real.pi) ε ε := by
  let B : ℝ := (Fintype.card (Fin (n + 1) → Fin 2) : ℝ) * (5 * ((n : ℝ) + 1))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let A := 2 * B + 50 * ((n : ℝ) + 1)
  have hA : 0 < A := by dsimp only [A]; positivity
  let δ := min (ε / 64) (ε / (80 * (A + 2)))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδε : δ < ε := by
    have h := min_le_left (ε / 64) (ε / (80 * (A + 2)))
    change δ ≤ ε / 64 at h
    linarith
  have hρ : 32 * δ ≤ ε := by
    have h := min_le_left (ε / 64) (ε / (80 * (A + 2)))
    change δ ≤ ε / 64 at h
    linarith
  have hCε : 40 * (A * δ + 2 * δ) ≤ ε := by
    have h := min_le_right (ε / 64) (ε / (80 * (A + 2)))
    change δ ≤ ε / (80 * (A + 2)) at h
    have hm := (le_div_iff₀ (show 0 < 80 * (A + 2) by positivity)).mp h
    nlinarith
  obtain ⟨e, he, hes, heo, hS, hT, hquarter⟩ :=
    exists_joint_clocked_quarter_control s t hs ht hsum htsum hcomm m n δ hδ
  let u := binaryRowCocycleUnitary s t hs ht hsum htsum n
  let α := binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
    (by simpa using hs 1 1) (by simpa using hs 0 1)
  let v := α u
  let C := A * δ
  let D := 2 * (n : ℝ) * δ
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hrow (i : Fin 2) (j : ZMod (2 ^ m)) :
      ‖s i * e j - e (j + 1) * s i‖ ≤ δ :=
    cyclic_row_generator_transport s hs e δ (fun k => (hS k).le) i j
  have hu (j : ZMod (2 ^ m)) : ‖(u : E) * e j - e j * (u : E)‖ ≤ D := by
    have h := binaryRowCocycle_joint_commutator_le s t hs ht hsum htsum e δ δ
      (fun k => (hS k).le) (fun k => (hT k).le) j n
    exact h.trans_eq (by dsimp only [D]; ring)
  have hDC : D ≤ C := by
    dsimp only [D, C, A]
    nlinarith [mul_nonneg hB hδ.le, mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hδ.le]
  have hδC : δ ≤ C := by
    dsimp only [C, A]
    nlinarith [mul_nonneg hB hδ.le, mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hδ.le]
  have hv (j : ZMod (2 ^ m)) : ‖(v : E) * e j - e j * (v : E)‖ ≤ 10 * (D + δ) := by
    have h0 := clock_corner_commutator e (fun k => (he k).isSelfAdjoint.star_eq)
      (s 0) (by simpa using hs 0 0) 1 δ D hδ.le hD (hrow 0) u hu j
    have h1 := clock_corner_commutator e (fun k => (he k).isSelfAdjoint.star_eq)
      (s 1) (by simpa using hs 1 1) 1 δ D hδ.le hD (hrow 1) u hu j
    have h := clock_product_commutator
      (binaryCornerUnitary (s 0) (by simpa using hs 0 0) u)
      (binaryCornerUnitary (s 1) (by simpa using hs 1 1) u) (e j)
    change ‖(v : E) * e j - e j * (v : E)‖ ≤ _ at h
    exact h.trans (by linarith)
  obtain ⟨c, hc, q, hq⟩ := exists_jointCycle_affine_control s t hs ht hsum htsum hcomm
    e (fun j => (he j).isSelfAdjoint.star_eq) δ hδ.le
    (fun j => (hS j).le) (fun j => (hT j).le) n
  have hd : u * star v = star c := by
    apply Subtype.ext
    change (u : E) * star (v : E) = star (c : E)
    rw [hc]
    exact binaryRowCocycleUnitary_defect s t hs ht hsum htsum n
  let q₁ : Path (1 : unitary E) (u * star v) :=
    (q.map (continuous_star : Continuous (star : unitary E → unitary E))).cast (by simp) hd
  have hq₁ : ClockPathControl q₁ e (2 * Real.pi) 0 (2 * B * δ) := by
    have hh := (hq.map_star (fun j => (he j).isSelfAdjoint.star_eq)).cast
      (show (1 : unitary E) = star (1 : unitary E) by simp) hd
    convert hh using 1; simp only [B]; ring
  have hcancel : (u * star v) * v = u := by simp [mul_assoc]
  let p₀ : Path v u := (q₁.mul (Path.refl v)).cast (one_mul v).symm hcancel.symm
  let p : Path u v := p₀.symm
  have hp : ClockPathControl p e (2 * Real.pi) δ C := by
    apply ((hq₁.mul (clockPathControl_refl v e _ hv)).cast (one_mul v).symm hcancel.symm).symm.mono
    · simp
    · simpa using hδ.le
    · dsimp only [C, A, D]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hδ.le]
  have hc₁ : ∀ i j : Fin 2, i ≠ j → ∃ c : Path
      (binaryCornerUnitary (s i) (by simpa using hs i i) u *
        binaryCornerUnitary (s j) (by simpa using hs j j) (star u)) 1,
      ClockPathControl c e (8 * Real.pi) δ C := by
    intro i j hij
    obtain ⟨r, hr⟩ := exists_balanced_clockCancellation e
      (fun k => (he k).isSelfAdjoint.star_eq) (s i) (s j) u
      (by simpa using hs i i) (by simpa using hs j j)
      (by simp only [hs, ite_eq_right hij]) 1 D δ hD hδ.le (hrow i) (hrow j) hu
    refine ⟨r, hr.mono (by linarith [Real.pi_pos]) hδ.le ?_⟩
    dsimp only [C, A, D]
    nlinarith [mul_nonneg hB hδ.le, mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hδ.le]
  have hc₂ : ∀ i r l : Fin 2, i ≠ l → ∃ c : Path
      (binaryCornerUnitary (s i * s r)
        (binaryProduct_isometry _ _ (by simpa using hs i i) (by simpa using hs r r)) u *
        binaryCornerUnitary (s l) (by simpa using hs l l) (star u)) 1,
      ClockPathControl c e (8 * Real.pi) δ C := by
    intro i r l hil
    obtain ⟨q, hq⟩ := hquarter i r l hil
    exact ⟨q, hq.mono le_rfl le_rfl hδC⟩
  obtain ⟨r, hr⟩ := exists_clocked_binaryFragmentation s hs e
    (fun j => (he j).isSelfAdjoint.star_eq) u (2 * Real.pi) (8 * Real.pi) δ C δ
    (by positivity) (by positivity) hδ.le hC hδ.le (fun j => (hu j).trans hDC) hrow p hp hc₁ hc₂
  refine ⟨e, he, hes, heo, (fun j => (hS j).trans hδε), (fun j => (hT j).trans hδε), r, ?_⟩
  have hr' : ClockPathControl r e (320 * Real.pi) (32 * δ) (40 * (C + 2 * δ)) := by
    convert hr using 1; ring
  exact hr'.mono le_rfl hρ hCε

end WeakPureInfiniteness

end

end OAI
