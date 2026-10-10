import OAI.Computability.StarHeight.ClockResidues

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uC uC2 uC3 uT uC4 uAlphabet uAlphabet2 uAlphabet3
universe uAlphabet4

namespace PeriodicClock

open RobustClock
open scoped BigOperators

lemma prime_mesh {C : Type uC} [Fintype C] (B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : C → ℕ, Function.Injective n ∧
      (∀ c, Nat.Prime (n c) ∧ B < n c ∧ 1 / (2 * (n c : ℝ)) < ε) := by
  obtain ⟨L, hL⟩ := exists_nat_gt (1 / ε)
  obtain ⟨n, hn, hprime⟩ := large_primes (C := C) (max B L)
  refine ⟨n, hn, fun c => ⟨(hprime c).1,
    lt_of_le_of_lt (le_max_left _ _) (hprime c).2, ?_⟩⟩
  have hl : (1 / ε : ℝ) < n c := hL.trans (by
    exact_mod_cast lt_of_le_of_lt (le_max_right _ _) (hprime c).2)
  have hnpos : (0 : ℝ) < n c := by exact_mod_cast (hprime c).1.pos
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n c)).mpr
  have hh := (div_lt_iff₀ hε).mp hl
  nlinarith

lemma prime_pairwise {C : Type uC2} (n : C → ℕ) (hinj : Function.Injective n)
    (hn : ∀ c, Nat.Prime (n c)) : Pairwise (Function.onFun Nat.Coprime n) := by
  intro i j hij
  apply (hn i).coprime_iff_not_dvd.mpr
  intro hd
  have he : n i = n j := ((hn j).eq_one_or_self_of_dvd (n i) hd).resolve_left (hn i).ne_one
  exact hij (hinj he)

lemma small_coprime {p B : ℕ} (hp : Nat.Prime p) (hB : 0 < B) (hBp : B < p) :
    Nat.Coprime B p := by
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  exact (not_le_of_gt hBp) (Nat.le_of_dvd hB hd)

lemma unbounded_residue {C : Type uC3} [Fintype C] (n : C → ℕ)
    (hn : ∀ c, 0 < n c) (hp : Pairwise (Function.onFun Nat.Coprime n))
    {B : ℕ} (hB : 0 < B) (hBc : ∀ c, Nat.Coprime B (n c))
    {ε : ℝ} (hε : 0 < ε) (hmesh : ∀ c, 1 / (2 * (n c : ℝ)) < ε)
    (r : ℤ) (v : C → RobustClock.Circle) (L : ℤ) :
    ∃ z : ℤ, L < z ∧ z % B = r % B ∧
      dist (speedMap (fun c => 1 / (n c : ℝ)) z) v < ε := by
  classical
  let φ := speedMap (fun c => 1 / (n c : ℝ))
  let R := ∏ c, n c
  have hR : (0 : ℤ) < R := by exact_mod_cast Finset.prod_pos (fun c _ => hn c)
  have hpR : φ (R : ℤ) = 0 := by
    simpa only [φ, Nat.cast_one] using period n (fun _ => 1) hn
  obtain ⟨a, _, ha⟩ := net n hn hp B hBc hε hmesh (v - φ r)
  let b : ℤ := r + (a : ℤ) * B
  have hb : dist (φ b) v < ε := by
    dsimp [b]
    rw [map_add]
    have hh : v = φ r + (v - φ r) := by abel
    conv_lhs => rw [hh]
    rw [dist_add_left]
    exact ha
  let q : ℤ := |L| + |b| + 1
  let z := b + (q * B) * R
  have hq : 0 < q := by dsimp [q]; positivity
  have hBR : (1 : ℤ) ≤ (B : ℤ) * R := by
    have hB' : (0 : ℤ) < B := by exact_mod_cast hB
    have hh := mul_pos hB' hR
    omega
  have hzl : L < z := by
    have hh := mul_le_mul_of_nonneg_left hBR hq.le
    dsimp [z, q] at *
    have hL := le_abs_self L
    have hbb := neg_abs_le b
    nlinarith
  have hzm : z % B = r % B := by
    dsimp [z, b]
    rw [mul_right_comm q (B : ℤ) (R : ℤ), Int.add_mul_emod_self_right,
      Int.add_mul_emod_self_right]
  refine ⟨z, hzl, hzm, ?_⟩
  have hφz : φ z = φ b := by
    dsimp [z]
    have hmul := map_zsmul φ (q * B) (R : ℤ)
    simp only [zsmul_eq_mul, Int.cast_id] at hmul
    rw [map_add, hmul, hpR, smul_zero, add_zero]
  change dist (φ z) v < ε
  rwa [hφz]

end PeriodicClock

namespace ScheduleClock

open RobustClock PeriodicClock
open scoped BigOperators

theorem exists_stencil_clock {T : Type uT} {C : Type uC4} [Fintype T] [Fintype C]
    (N : ℕ) (S : Specification T (Fin N) C) (B : ℕ) (hB : 0 < B)
    (r : Fin N → ℤ) (lower : (Fin N → ℤ) → ℕ → ℕ) :
    ∃ (R : ℕ) (p : Fin N → ℤ) (n a : C → ℕ),
      0 < R ∧
      (∀ i, p i % B = r i % B ∧ (2 * (B * R) + 2 : ℤ) < p i) ∧
      (∀ i j, i < j → 2 * p i + (2 * (B * R) + 2 : ℤ) < p j) ∧
      Function.Injective n ∧
      (∀ c, Nat.Prime (n c) ∧ lower p (B * R) < n c ∧ 1 ≤ a c ∧ a c < n c) ∧
      (∀ i, dist (speedMap (fun c => (a c : ℝ) / n c) (p i)) (S.v i) < S.η) ∧
      (∀ v : C → RobustClock.Circle, ∃ j : ℕ, j < R ∧
        dist (speedMap (fun c => (a c : ℝ) / n c) (j * B)) v < S.ρ) := by
  classical
  let ε := min (S.ρ / 3) (S.η / 3)
  have hε : 0 < ε := lt_min (div_pos S.radius_pos (by norm_num))
    (div_pos S.tolerance_pos (by norm_num))
  obtain ⟨n₀, hn₀inj, hn₀⟩ := prime_mesh (C := C) B hε
  have hprim c := (hn₀ c).1
  have hn₀pos c := (hprim c).pos
  have hpair := prime_pairwise n₀ hn₀inj hprim
  have hcop c := small_coprime (hprim c) hB (hn₀ c).2.1
  let R := ∏ c, n₀ c
  have hR : 0 < R := Finset.prod_pos (fun c _ => hn₀pos c)
  obtain ⟨p, hp, hspread⟩ := SpacedStencil.exists_points N (2 * (B * R : ℕ) + 2)
    (fun i z => z % B = r i % B ∧
      dist (speedMap (fun c => 1 / (n₀ c : ℝ)) z) (S.v i) < ε)
    (fun i L => unbounded_residue n₀ hn₀pos hpair hB hcop hε
      (fun c => (hn₀ c).2.2) (r i) (S.v i) L)
  let F : Finset ℤ := Finset.univ.image p ∪ (Finset.range R).image (fun j => (j * B : ℕ))
  have hs c : 0 < (1 / (n₀ c : ℝ)) ∧ 1 / (n₀ c : ℝ) < 1 := by
    have hh : (1 : ℝ) < n₀ c := by exact_mod_cast (hprim c).one_lt
    exact ⟨by positivity, (div_lt_one (by positivity)).mpr hh⟩
  obtain ⟨n, a, hn, hna, hclose⟩ := approximate_finite (fun c => 1 / (n₀ c : ℝ)) hs
    (lower p (B * R)) F hε
  refine ⟨R, p, n, a, hR, fun i => ⟨(hp i).1.1, (hp i).2⟩, hspread,
    hn, hna, ?_, ?_⟩
  · intro i
    have hc := hclose (p i) (Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, rfl⟩))
    have ht := (dist_triangle _ _ _).trans_lt (add_lt_add hc (hp i).1.2)
    have he : ε ≤ S.η / 3 := min_le_right _ _
    exact ht.trans (by linarith [S.tolerance_pos])
  · intro v
    obtain ⟨j, hj, hjv⟩ := net n₀ hn₀pos hpair B hcop hε (fun c => (hn₀ c).2.2) v
    have hc := hclose ((j * B : ℕ) : ℤ) (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨j, Finset.mem_range.mpr hj, rfl⟩))
    refine ⟨j, hj, ?_⟩
    have ht := (dist_triangle _ _ _).trans_lt (add_lt_add hc hjv)
    have he : ε ≤ S.ρ / 3 := min_le_left _ _
    exact ht.trans (by linarith [S.radius_pos])

end ScheduleClock

namespace EpisodeEnd

open LocalMarkers

variable {Alphabet : Type uAlphabet}

def FirstMismatch (w v : ℤ → Alphabet) (z : ℤ) (K : ℕ) (q : ℤ) : Prop :=
  z + K ≤ q ∧ w q ≠ v q ∧ AgreesOn w v z q

lemma firstMismatch_unique {w v : ℤ → Alphabet} {z z' q q' : ℤ} {K : ℕ}
    (h : FirstMismatch w v z K q) (h' : FirstMismatch w v z' K q')
    (hover : |z - z'| < K) : q = q' := by
  have hq := h.1
  have hq' := h'.1
  have hz : z ≤ q' := by
    have hh := (abs_lt.mp hover).2
    omega
  have hz' : z' ≤ q := by
    have hh := (abs_lt.mp hover).1
    omega
  rcases lt_trichotomy q q' with hq | hq | hq
  · exact False.elim (h.2.1 (h'.2.2 q hz' hq))
  · exact hq
  · exact False.elim (h'.2.1 (h.2.2 q' hz hq))

lemma shortCont_congr {d K : ℕ} {w w' v : ℤ → Alphabet} {z : ℤ}
    (he : AgreesOn w w' z (z + K)) :
    ShortContinuation d K w z v ↔ ShortContinuation d K w' z v := by
  constructor <;> intro h
  · refine ⟨h.1, fun x hx hx' => ?_⟩
    exact (he x hx hx').symm.trans (h.2 x hx hx')
  · refine ⟨h.1, fun x hx hx' => ?_⟩
    exact (he x hx hx').trans (h.2 x hx hx')

def EndAt (d K : ℕ) (tail : ℤ) (w : ℤ → Alphabet) (z : ℤ)
    (η : Option ℤ) (b : ℤ) : Prop :=
  match η with
  | some q => b = q + tail
  | none => ∃ v, ShortContinuation d K w z v ∧ FirstMismatch w v z K (b - tail)

def clockAnchor (ζ : Option ℤ) (b tail : ℤ) : ℤ := ζ.getD (b - tail)

lemma EndAt.unique {d K : ℕ} {tail z b b' : ℤ} {w : ℤ → Alphabet} {η : Option ℤ}
    (hK : (d : ℤ) ^ 2 ≤ K) (hKpos : 0 < K)
    (h : EndAt d K tail w z η b) (h' : EndAt d K tail w z η b') : b = b' := by
  cases η with
  | some q => exact h.trans h'.symm
  | none =>
    obtain ⟨v, hv, hm⟩ := h
    obtain ⟨v', hv', hm'⟩ := h'
    have he := short_continuations_equal hv hv' (by simpa using hK)
    subst v'
    have hh := firstMismatch_unique hm hm' (by simpa using hKpos)
    omega

lemma shared_end {d K : ℕ} {tail s z z' b b' : ℤ}
    {w w' : ℤ → Alphabet} {η : Option ℤ}
    (htail : 0 < tail) (hover : (d : ℤ) ^ 2 ≤ (K : ℤ) - |z - z'|)
    (hover' : |z - z'| < K)
    (hseed : s ≤ z ∧ z + K ≤ min b b' ∧ s ≤ z' ∧ z' + K ≤ min b b')
    (he : AgreesOn w w' s (min b b'))
    (h : EndAt d K tail w z η b) (h' : EndAt d K tail w' z' η b') :
    b = b' := by
  cases η with
  | some q => exact h.trans h'.symm
  | none =>
    obtain ⟨v, hv, hm⟩ := h
    obtain ⟨v', hv', hm'⟩ := h'
    have hseed' : AgreesOn w w' z' (z' + K) := by
      intro x hx hx'
      exact he x (hseed.2.2.1.trans hx) (lt_of_lt_of_le hx' hseed.2.2.2)
    have hvw : ShortContinuation d K w z' v' := (shortCont_congr hseed').mpr hv'
    have hvv := short_continuations_equal hv hvw hover
    subst v'
    have hmlo := hm.1
    have hmlo' := hm'.1
    have hz : z ≤ b' - tail := by
      have hh := (abs_lt.mp hover').2
      omega
    have hz' : z' ≤ b - tail := by
      have hh := (abs_lt.mp hover').1
      omega
    rcases lt_trichotomy b b' with hb | hb | hb
    · have hq : b - tail < b' - tail := by omega
      have hqbounds : s ≤ b - tail ∧ b - tail < min b b' := by omega
      have hletter := he (b - tail) hqbounds.1 hqbounds.2
      exact False.elim (hm.2.1 (hletter.trans (hm'.2.2 _ hz' hq)))
    · exact hb
    · have hq : b' - tail < b - tail := by omega
      have hqbounds : s ≤ b' - tail ∧ b' - tail < min b b' := by omega
      have hletter := he (b' - tail) hqbounds.1 hqbounds.2
      exact False.elim (hm'.2.1 (hletter.symm.trans (hm.2.2 _ hz hq)))

lemma transfer_end {d K : ℕ} {tail z z' b : ℤ} {w : ℤ → Alphabet} {η : Option ℤ}
    (hover : (d : ℤ) ^ 2 ≤ (K : ℤ) - |z - z'|)
    (hover' : |z - z'| < K)
    (hseed : η = none → ∃ v', ShortContinuation d K w z' v')
    (h : EndAt d K tail w z η b) : EndAt d K tail w z' η b := by
  cases η with
  | some q => exact h
  | none =>
    obtain ⟨v, hv, hm⟩ := h
    obtain ⟨v', hv'⟩ := hseed rfl
    have he := short_continuations_equal hv hv' hover
    subst v'
    refine ⟨v, hv', ?_⟩
    have hmlo := hm.1
    have hz' : z' ≤ b - tail := by
      have hh := (abs_lt.mp hover').1
      omega
    have hq : z' + K ≤ b - tail := by
      by_contra hn
      exact hm.2.1 (hv'.2 _ hz' (by omega))
    refine ⟨hq, hm.2.1, fun x hx hx' => ?_⟩
    by_cases hxz : z ≤ x
    · exact hm.2.2 x hxz hx'
    · apply hv'.2 x hx
      have hh := (abs_lt.mp hover').2
      omega

end EpisodeEnd

namespace LocalMarkers

variable (Alphabet : Type uAlphabet2) (d K : ℕ)

structure Rule where
  r : ℤ
  radius_ge : (K : ℤ) ≤ r
  markers : (ℤ → Alphabet) → Set ℤ
  separated : ∀ w x, x ∈ markers w → ∀ y, y ∈ markers w → x ≠ y →
    (d : ℤ) ≤ |x - y|
  locality : ∀ w w' x, AgreesOn w w' (x - r) (x + r) →
    (x ∈ markers w ↔ x ∈ markers w')
  translate : ∀ w a x, x ∈ markers (fun i => w (i + a)) ↔ x + a ∈ markers w
  periodic : ∀ w z, (∀ x : ℤ, z - d ≤ x → x ≤ z + d → x ∉ markers w) →
    ∃ a : ℕ, 0 < a ∧ a < d ∧ Period (fun i : Fin K => w (z + i.val)) a

lemma nonempty_rule [Fintype Alphabet] (hd : 2 ≤ d) (hK : 3 * d ^ 2 < K) :
    Nonempty (Rule Alphabet d K) := by
  obtain ⟨r, hr, m, hsep, hloc, htrans, hper⟩ := exists_markers (Alphabet := Alphabet) hd hK
  exact ⟨⟨r, hr, m, hsep, hloc, htrans, hper⟩⟩

end LocalMarkers

namespace EndSearch

open LocalMarkers

lemma search_congr {S S' : Set ℤ} {B D a z : ℤ}
    (he : ∀ m, z - (a + (B - 1) * D) ≤ m → m ≤ z + (a + (B - 1) * D) →
      (m ∈ S ↔ m ∈ S')) : search S B D a z = search S' B D a z := by
  have hf : eligibleSet S B D a z = eligibleSet S' B D a z := by
    ext m
    simp only [eligibleSet, Finset.mem_filter, Finset.mem_Icc, Eligible]
    constructor
    · rintro ⟨⟨hl, hr⟩, hm, hw⟩
      exact ⟨⟨hl, hr⟩, (he m hl hr).mp hm, hw⟩
    · rintro ⟨⟨hl, hr⟩, hm, hw⟩
      exact ⟨⟨hl, hr⟩, (he m hl hr).mpr hm, hw⟩
  simp only [search, hf]

lemma search_local {Alphabet : Type uAlphabet3} {d K : ℕ} (R : Rule Alphabet d K)
    (B D a z : ℤ) {w w' : ℤ → Alphabet}
    (he : AgreesOn w w' (z - (a + (B - 1) * D) - R.r)
      (z + (a + (B - 1) * D) + R.r)) :
    search (R.markers w) B D a z = search (R.markers w') B D a z := by
  apply search_congr
  intro m hm hm'
  apply R.locality
  intro x hx hx'
  exact he x (by omega) (by omega)

lemma absent_continuation {Alphabet : Type uAlphabet4} {d K : ℕ} (R : Rule Alphabet d K)
    (hK : d ≤ K) {B D z : ℤ} {w : ℤ → Alphabet} (hB : 0 < B) (hD : 0 ≤ D)
    (hn : search (R.markers w) B D d z = none) :
    ∃ v, ShortContinuation d K w z v := by
  apply short_continuation_exists hK
  apply R.periodic
  intro m hlo hhi hm
  apply (search_none hB hD).mp hn m
  exact ⟨hm, (abs_le.mpr (show -(d : ℤ) ≤ m - z ∧ m - z ≤ d by omega)).trans
    (width_bounds hB hD).1⟩

end EndSearch

end GeneralizedStarHeight

end OAI
