import OAI.Computability.StarHeight.SuffixDecoder

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uM uT uP uC uM2 uAlphabet2 uM3
universe uAlphabet3 uT2 uP2 uC2 uAlphabet4 uM4

namespace WordIntervals

variable {Alphabet : Type uAlphabet} {M : Type uM} [Monoid M]

@[simp] lemma product_self (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet) (s : ℤ) :
    product T f s s = 1 := by
  simp only [product,piece,sub_self,Int.toNat_zero,segment,List.ofFn_zero]
  exact map_one T

lemma product_chain (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    {g : ℕ} (p : Fin (g+1) → ℤ) (hp : Monotone p) :
    (List.ofFn (fun i : Fin g => product T f (p i.castSucc) (p i.succ))).prod =
      product T f (p 0) (p (Fin.last g)) := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [List.ofFn_succ,List.prod_cons]
    have htail := ih (fun i => p i.succ) (hp.comp (fun _ _ hab => Fin.succ_le_succ_iff.mpr hab))
    change product T f (p 0) (p 1) *
      (List.ofFn (fun i : Fin g => product T f (p i.castSucc.succ) (p i.succ.succ))).prod = _
    rw [htail]
    exact (product_append T f (hp (Fin.zero_le _)) (hp (Fin.le_last _))).symm

lemma product_chain_with_ends (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    {g : ℕ} (p : Fin (g+1) → ℤ) (hp : Monotone p) {s b : ℤ}
    (hs : s ≤ p 0) (hb : p (Fin.last g) ≤ b) :
    product T f s b = product T f s (p 0) *
      (List.ofFn (fun i : Fin g => product T f (p i.castSucc) (p i.succ))).prod *
      product T f (p (Fin.last g)) b := by
  rw [product_chain T f p hp]
  rw [← product_append T f hs (hp (Fin.zero_le _))]
  exact product_append T f (hs.trans (hp (Fin.zero_le _))) hb

end WordIntervals

namespace ScheduleClock

open RobustClock PeriodicClock
open scoped BigOperators

theorem exists_ordered_stencil_clock {T : Type uT} {P : Type uP} {C : Type uC} [Fintype T] [Fintype P]
    [LinearOrder P] [Fintype C] (S : Specification T P C) (B : ℕ) (hB : 0 < B)
    (r : P → ℤ) (lower : (P → ℤ) → ℕ → ℕ) :
    ∃ (R : ℕ) (p : P → ℤ) (n a : C → ℕ),
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
  obtain ⟨p, hp, hspread⟩ := SpacedStencil.exists_points_fintype (2 * (B * R : ℕ) + 2)
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

namespace ClockAffine

@[ext] lemma Snapshot.ext {M : Type uM2} [Monoid M] {g : ℕ} {a b : Snapshot M g}
    (hp : a.product = b.product) (hb : a.boundaries = b.boundaries) : a = b := by
  cases a; cases b; cases hp; cases hb; rfl

end ClockAffine

namespace BoundarySnapshot

open WordIntervals

variable {Alphabet : Type uAlphabet2} {M : Type uM3} [Monoid M] {g : ℕ}

def Present (search : Fin (g+1) → Option ℤ) (s b : ℤ) : Prop :=
  ∃ p : Fin (g+1) → ℤ, (∀ i, search i = some (p i)) ∧
    Monotone p ∧ s ≤ p 0 ∧ p (Fin.last g) ≤ b

lemma present_unique {search : Fin (g+1) → Option ℤ} {p q : Fin (g+1) → ℤ}
    (hp : ∀ i, search i = some (p i)) (hq : ∀ i, search i = some (q i)) : p = q := by
  funext i
  exact Option.some.inj ((hp i).symm.trans (hq i))

noncomputable def factors (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    (s b : ℤ) (search : Fin (g+1) → Option ℤ) : Option (ClockAffine.Factors M g) := by
  classical
  exact if h : Present search s b then
    some ⟨product T f s (h.choose 0),
      (fun i => product T f (h.choose i.castSucc) (h.choose i.succ)),
      product T f (h.choose (Fin.last g)) b⟩
  else none

lemma factors_present (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    {s b : ℤ} {search : Fin (g+1) → Option ℤ} {p : Fin (g+1) → ℤ}
    (hp : ∀ i, search i = some (p i)) (hmono : Monotone p)
    (hs : s ≤ p 0) (hb : p (Fin.last g) ≤ b) :
    factors T f s b search = some ⟨product T f s (p 0),
      (fun i => product T f (p i.castSucc) (p i.succ)),product T f (p (Fin.last g)) b⟩ := by
  have h : Present search s b := ⟨p,hp,hmono,hs,hb⟩
  rw [factors,dite_eq_left h]
  have he := present_unique h.choose_spec.1 hp
  simp only [he]

lemma factors_absent (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    {s b : ℤ} {search : Fin (g+1) → Option ℤ} {i : Fin (g+1)}
    (hi : search i = none) : factors T f s b search = none := by
  unfold factors
  split_ifs with hp
  · have hh := (hp.choose_spec.1 i).symm.trans hi
    cases hh
  · rfl

noncomputable def actual (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    (s b : ℤ) (search : Fin (g+1) → Option ℤ) : ClockAffine.Snapshot M g where
  product := product T f s b
  boundaries := factors T f s b search
  product_eq := by
    intro d hd
    unfold factors at hd
    split_ifs at hd with hp
    · cases Option.some.inj hd
      exact product_chain_with_ends T f hp.choose hp.choose_spec.2.1
        hp.choose_spec.2.2.1 hp.choose_spec.2.2.2

noncomputable def later (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    (a b : ℤ) (search : Fin (g+1) → Option ℤ) : ClockAffine.Later M g where
  tailProduct := product T f a b
  boundaries := factors T f a b search
  tail_eq := (actual T f a b search).product_eq

lemma actual_eq_substitute (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    {s a b : ℤ} {search : Fin (g+1) → Option ℤ}
    (hsa : s ≤ a) (hab : a ≤ b)
    (hstart : ∀ i p, search i = some p → a ≤ p)
 :
    actual T f s b search = (later T f a b search).substitute (product T f s a) := by
  classical
  have hpres : Present search s b ↔ Present search a b := by
    constructor
    · rintro ⟨p,hp,hm,_,hb⟩
      exact ⟨p,hp,hm,hstart 0 _ (hp 0),hb⟩
    · rintro ⟨p,hp,hm,ha,hb⟩
      exact ⟨p,hp,hm,hsa.trans ha,hb⟩
  have hprod := product_append T f hsa hab
  apply ClockAffine.Snapshot.ext
  · exact hprod
  · change factors T f s b search = (factors T f a b search).map _
    by_cases hh : Present search a b
    · let p := hh.choose
      have hp : ∀ i, search i = some (p i) := hh.choose_spec.1
      rw [factors_present T f hp hh.choose_spec.2.1
        (hsa.trans hh.choose_spec.2.2.1) hh.choose_spec.2.2.2,
        factors_present T f hp hh.choose_spec.2.1 hh.choose_spec.2.2.1 hh.choose_spec.2.2.2]
      simp only [Option.map_some]
      congr 2
      exact product_append T f hsa hh.choose_spec.2.2.1
    · simp only [factors,dite_eq_right hh,dite_eq_right (fun h => hh (hpres.mp h)),Option.map_none]

end BoundarySnapshot

namespace CanonicalEpisodes.Parameters

open EpisodeEnd

variable {Alphabet : Type uAlphabet3} (C : CanonicalEpisodes.Parameters Alphabet)

lemma end_lower {f : ℤ → Alphabet} {t b : ℤ}
    (he : EndAt C.d C.K C.tail f (t+C.offset) (C.small f (t+C.offset)) b) :
    t+C.offset - ((C.d : ℤ)+(C.B-1)*C.S) + C.tail ≤ b := by
  cases h : C.small f (t+C.offset) with
  | none =>
    rw [h] at he
    obtain ⟨v,hv,hm⟩ := he
    have hwidth : 0 ≤ (C.d : ℤ)+(C.B-1)*C.S := by
      have hB : 0 ≤ C.B-1 := by have := C.B_pos; omega
      have hS := C.S_nonneg
      positivity
    have hh := hm.1
    omega
  | some q =>
    rw [h] at he
    have hq := ((EndSearch.search_some C.B_pos C.S_nonneg).mp h).1.2
    have hw := (EndSearch.width_bounds (x := q-(t+C.offset)) (a := C.d)
      C.B_pos C.S_nonneg).2
    have hl := (abs_le.mp (hq.trans hw)).1
    dsimp only [EndAt] at he
    omega

end CanonicalEpisodes.Parameters

namespace ClockAffine

open RobustClock

variable {T : Type uT2} {P : Type uP2} {C : Type uC2} [Fintype T] [Fintype P] [Fintype C]
    (clock : Specification T P C)

lemma no_off_outside {z : C → RobustClock.Circle} (hz : z ∉ clock.W) :
    offChoice clock z = none := by
  cases hc : offChoice clock z with
  | none => rfl
  | some ab =>
    have hh := offChoice_some clock hc
    exact False.elim (hh.1 ((clock.diagonal z hz ab.1 ab.2).mp hh.2.1))

lemma net_cut (φ : ℤ →+ (C → RobustClock.Circle)) (B : ℕ) {R : ℕ}
    (hnet : ∀ v : C → RobustClock.Circle, ∃ a : ℕ, a < R ∧ dist (φ (a*B)) v < clock.ρ)
    {z : C → RobustClock.Circle} (hz : z ∉ clock.W) (tag : T) (base : ℤ) :
    ∃ a : ℕ, a < R ∧ φ (base+a*B) ∈ clock.I tag ∧ z-φ (base+a*B) ∈ clock.J tag := by
  obtain ⟨i,hi⟩ := clock.interior z hz tag
  obtain ⟨a,ha,had⟩ := hnet (i-φ base)
  refine ⟨a,ha,hi _ ?_⟩
  rw [map_add]
  have he : i = φ base + (i-φ base) := by abel
  rw [he]
  simpa only [dist_add_left] using had

end ClockAffine

namespace BoundarySnapshot

variable {g : ℕ}

def positions (search : Fin (g+1) → Option ℤ) : Fin (g+1) → ℤ :=
  fun i => (search i).getD 0

lemma positions_return {search : Fin (g+1) → Option ℤ} {i : Fin (g+1)}
    (hi : search i ≠ none) : search i = some (positions search i) := by
  cases h : search i with
  | none => exact False.elim (hi h)
  | some q => simp [positions,h]

lemma present_of_bounds {search : Fin (g+1) → Option ℤ} {s b : ℤ}
    (hp : ∀ i, search i ≠ none)
    (hstart : ∀ i p, search i = some p → s ≤ p)
    (hend : ∀ i p, search i = some p → p ≤ b)
    (horder : ∀ i j p q, i ≤ j → search i = some p → search j = some q → p ≤ q) :
    Present search s b :=
  ⟨positions search,fun i => positions_return (hp i),
    fun i j hij => horder i j _ _ hij (positions_return (hp i)) (positions_return (hp j)),
    hstart _ _ (positions_return (hp _)),hend _ _ (positions_return (hp _))⟩

lemma factors_positions {Alphabet : Type uAlphabet4} {M : Type uM4} [Monoid M]
    (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    {search : Fin (g+1) → Option ℤ} {s b : ℤ} (hp : Present search s b) :
    factors T f s b search = some ⟨WordIntervals.product T f s (positions search 0),
      (fun i => WordIntervals.product T f (positions search i.castSucc) (positions search i.succ)),
      WordIntervals.product T f (positions search (Fin.last g)) b⟩ := by
  obtain ⟨p,hp,hm,hs,hb⟩ := hp
  have he : positions search = p := by
    funext i
    simp only [positions,hp,Option.getD_some]
  simpa only [he] using factors_present T f hp hm hs hb

end BoundarySnapshot

end GeneralizedStarHeight

end OAI
