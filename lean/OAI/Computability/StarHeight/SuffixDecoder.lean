import OAI.Computability.StarHeight.ExceptionalOrigins

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uJ uC uP uAlphabet2 uM uG uG2
universe uC2 uAlphabet3 uJ2 uC3 uKind uP2 uP3

namespace SuffixDecoder

open LocalMarkers EpisodeEnd

variable {Alphabet : Type uAlphabet} {J : Type uJ} {C : Type uC} {P : Type uP} (A : ExceptionalOrigins.Parameters Alphabet J C)

def origin (p : P → ℤ) (lag k : ℤ) (i : P) : ℤ := k + lag - p i

structure Test (τ : P → ℤ) (reference : P) (k b : ℤ) (f : ℤ → Alphabet)
    (decoded : P) : Prop where
  visible : ∀ i, A.Visible k b (τ i) (A.anchor f (b-A.endRule.tail) (τ i))
  reference_guard : (∃ i, A.endRule.large f (τ i + A.endRule.offset) = none) →
    (∀ i, A.endRule.small f (τ i + A.endRule.offset) = none) ∧
    EndAt A.endRule.d A.endRule.K A.endRule.tail f (τ reference + A.endRule.offset)
      (A.endRule.small f (τ reference + A.endRule.offset)) b
  unique : A.Failed f (τ decoded) (A.anchor f (b-A.endRule.tail) (τ decoded)) ∧
    ∀ i, A.Failed f (τ i) (A.anchor f (b-A.endRule.tail) (τ i)) → i = decoded
  final_guard : EndAt A.endRule.d A.endRule.K A.endRule.tail f
    (τ decoded + A.endRule.offset) (A.endRule.small f (τ decoded + A.endRule.offset)) b

lemma searches_agree {τ : P → ℤ} {reference decoded : P} {k b b' : ℤ}
    {f g : ℤ → Alphabet} (htest : Test A τ reference k b' g decoded)
    (hvis : ∀ i, A.Visible k b (τ i) (A.anchor f (b-A.endRule.tail) (τ i)))
    (he : AgreesOn f g k (min b b')) (i : P) :
    A.endRule.small f (τ i + A.endRule.offset) = A.endRule.small g (τ i + A.endRule.offset) ∧
      A.endRule.large f (τ i + A.endRule.offset) = A.endRule.large g (τ i + A.endRule.offset) := by
  have hv := (hvis i).base
  have hv' := (htest.visible i).base
  apply A.endRule.searches_congr
    (show A.endRule.Visible k (min b b') (τ i + A.endRule.offset) from
      ⟨hv.1,le_min hv.2.1 hv'.2.1,hv.2.2.1,le_min hv.2.2.2 hv'.2.2.2⟩) he

lemma reference_forces_end {τ : P → ℤ} {reference actual decoded : P} {k b b' : ℤ}
    {f g : ℤ → Alphabet} (htest : Test A τ reference k b' g decoded)
    (hvis : ∀ i, A.Visible k b (τ i) (A.anchor f (b-A.endRule.tail) (τ i)))
    (he : AgreesOn f g k (min b b'))
    (hover : (A.endRule.d : ℤ)^2 ≤ A.endRule.K - |τ actual - τ reference|)
    (hover' : |τ actual - τ reference| < A.endRule.K)
    (hend : EndAt A.endRule.d A.endRule.K A.endRule.tail f
      (τ actual + A.endRule.offset) (A.endRule.small f (τ actual + A.endRule.offset)) b)
    (habsent : ∃ i, A.endRule.large g (τ i + A.endRule.offset) = none) : b = b' := by
  obtain ⟨hsmall,href⟩ := htest.reference_guard habsent
  have hη := (searches_agree A htest hvis he actual).1.trans (hsmall actual)
  rw [hη] at hend
  rw [hsmall reference] at href
  have hv := (hvis actual).base
  have hv' := (htest.visible actual).base
  have hr := (hvis reference).base
  have hr' := (htest.visible reference).base
  apply shared_end A.endRule.tail_pos (by simpa only [add_sub_add_right_eq_sub] using hover)
    (by simpa only [add_sub_add_right_eq_sub] using hover')
    ⟨hv.2.2.1,le_min hv.2.2.2 hv'.2.2.2,hr.2.2.1,le_min hr.2.2.2 hr'.2.2.2⟩ he hend href

lemma true_anchor {τ : P → ℤ} {reference actual decoded : P} {k b b' : ℤ}
    {f g : ℤ → Alphabet} (htest : Test A τ reference k b' g decoded)
    (hvis : ∀ i, A.Visible k b (τ i) (A.anchor f (b-A.endRule.tail) (τ i)))
    (he : AgreesOn f g k (min b b'))
    (hover : (A.endRule.d : ℤ)^2 ≤ A.endRule.K - |τ actual - τ reference|)
    (hover' : |τ actual - τ reference| < A.endRule.K)
    (hend : EndAt A.endRule.d A.endRule.K A.endRule.tail f
      (τ actual + A.endRule.offset) (A.endRule.small f (τ actual + A.endRule.offset)) b) :
    A.anchor f (b-A.endRule.tail) (τ actual) = A.anchor g (b'-A.endRule.tail) (τ actual) := by
  have hs := (searches_agree A htest hvis he actual).2
  cases hz : A.endRule.large g (τ actual + A.endRule.offset) with
  | none =>
    have hb := reference_forces_end A htest hvis he hover hover' hend ⟨actual,hz⟩
    simp only [ExceptionalOrigins.Parameters.anchor,hs,hz,hb]
  | some q => simp only [ExceptionalOrigins.Parameters.anchor,hs,hz,Option.getD_some]

lemma sound {τ : P → ℤ} {reference actual decoded : P} {k b b' : ℤ}
    {f g : ℤ → Alphabet} (hw₀ : 0 ≤ A.w₀) (htest : Test A τ reference k b' g decoded)
    (hvis : ∀ i, A.Visible k b (τ i) (A.anchor f (b-A.endRule.tail) (τ i)))
    (he : AgreesOn f g k (min b b'))
    (hover : (A.endRule.d : ℤ)^2 ≤ A.endRule.K - |τ actual - τ reference|)
    (hover' : |τ actual - τ reference| < A.endRule.K)
    (hend : EndAt A.endRule.d A.endRule.K A.endRule.tail f
      (τ actual + A.endRule.offset) (A.endRule.small f (τ actual + A.endRule.offset)) b)
    (hfailed : A.Failed f (τ actual) (A.anchor f (b-A.endRule.tail) (τ actual))) :
    decoded = actual ∧ b' = b := by
  have hQ := true_anchor A htest hvis he hover hover' hend
  have hv' := htest.visible actual
  rw [← hQ] at hv'
  have hv := ExceptionalOrigins.Parameters.Visible.min A (hvis actual) hv'
  have hf := (A.Failed_congr hw₀ hv he).mp hfailed
  rw [hQ] at hf
  have hd := htest.unique.2 actual hf
  subst decoded
  refine ⟨rfl,?_⟩
  have hη := (searches_agree A htest hvis he actual).1
  have hguard := htest.final_guard
  rw [← hη] at hguard
  have hb := (hvis actual).base
  have hb' := (htest.visible actual).base
  have hseed := le_min hb.2.2.2 hb'.2.2.2
  have hh := shared_end A.endRule.tail_pos
    (by simpa only [sub_self,abs_zero,sub_zero] using A.endRule.seed_square)
    (by simpa only [sub_self,abs_zero] using
      (show (0 : ℤ) < A.endRule.K by exact_mod_cast A.endRule.seed_pos))
    ⟨hb.2.2.1,hseed,hb.2.2.1,hseed⟩ he hend hguard
  exact hh.symm

lemma all_small_absent {τ : P → ℤ} {f : ℤ → Alphabet} {H : ℤ}
    (hnear : ∀ i j, |τ i - τ j| ≤ H)
    (hnest : (A.endRule.d : ℤ) + (A.endRule.B-1)*A.endRule.S + H ≤ 3*A.endRule.d)
    (habsent : ∃ i, A.endRule.large f (τ i + A.endRule.offset) = none) :
    ∀ i, A.endRule.small f (τ i + A.endRule.offset) = none := by
  obtain ⟨j,hj⟩ := habsent
  intro i
  by_contra hi
  apply (EndSearch.nested A.endRule.B_pos A.endRule.S_nonneg hnest
    (by simpa only [add_sub_add_right_eq_sub] using hnear j i) hi) hj

lemma available_at {τ : P → ℤ} {reference actual : P} {k b H : ℤ} {f : ℤ → Alphabet}
    (hvis : ∀ i, A.Visible k b (τ i) (A.anchor f (b-A.endRule.tail) (τ i)))
    (hnear : ∀ i j, |τ i - τ j| ≤ H)
    (hnest : (A.endRule.d : ℤ) + (A.endRule.B-1)*A.endRule.S + H ≤ 3*A.endRule.d)
    (hover : (A.endRule.d : ℤ)^2 ≤ A.endRule.K - |τ actual - τ reference|)
    (hover' : |τ actual - τ reference| < A.endRule.K)
    (hend : EndAt A.endRule.d A.endRule.K A.endRule.tail f
      (τ actual + A.endRule.offset) (A.endRule.small f (τ actual + A.endRule.offset)) b)
    (hfailed : A.Failed f (τ actual) (A.anchor f (b-A.endRule.tail) (τ actual)))
    (hothers : ∀ i, i ≠ actual → ¬ A.Failed f (τ i) (A.anchor f (b-A.endRule.tail) (τ i))) :
    Test A τ reference k b f actual := by
  refine ⟨hvis,?_,⟨hfailed,?_⟩,hend⟩
  · intro ha
    have hsmall := all_small_absent A hnear hnest ha
    refine ⟨hsmall,?_⟩
    have he := hend
    rw [hsmall actual] at he
    rw [hsmall reference]
    apply transfer_end (by simpa only [add_sub_add_right_eq_sub] using hover)
      (by simpa only [add_sub_add_right_eq_sub] using hover') (h := he)
    intro _
    exact EndSearch.absent_continuation A.endRule.rule
      (by nlinarith [A.endRule.seed_long]) A.endRule.B_pos A.endRule.S_nonneg (hsmall reference)
  · intro i hi
    by_contra hn
    exact hothers i hn hi

end SuffixDecoder

namespace PeriodicCuts

open LocalMarkers WordIntervals

variable {Alphabet : Type uAlphabet2} {M : Type uM} [Monoid M] [Fintype M]

lemma markerless_run {d K : ℕ} (R : Rule Alphabet d K) (hd : 2 ≤ d)
    (hK : 3 * d^2 < K) (f : ℤ → Alphabet) (z H ext : ℤ)
    (hlen : 2 * (d : ℤ) ≤ H + ext)
    (hn : ∀ x, z ≤ x → x ≤ z + H + ext → x ∉ R.markers f) :
    ∃ v : ℤ → Alphabet, (∃ a : ℕ, 0 < a ∧ a < d ∧ Function.Periodic v (a : ℤ)) ∧
      AgreesOn f v (z + d) (z + H + ext - d + K) := by
  apply periodic_run hd hK f (z + d) (z + H + ext - d) (by omega)
  intro x hx hx'
  apply R.periodic
  intro y hy hy'
  exact hn y (by omega) (by omega)

lemma segment_shift_period {v : ℤ → Alphabet} {p : ℕ}
    (hp : Function.Periodic v (p : ℤ)) (s : ℤ) (m n : ℕ) :
    segment v (s + m * p) n = segment v s n := by
  apply List.ofFn_inj.mpr
  funext i
  simpa only [add_right_comm] using hp.nat_mul m (s + i.val)

omit [Fintype M] in
lemma product_periods (T : FreeMonoid Alphabet →* M) {v : ℤ → Alphabet} {p : ℕ}
    (hp : Function.Periodic v (p : ℤ)) (s : ℤ) (m : ℕ) :
    T (segment v s (m * p)) = T (segment v s p) ^ m := by
  induction m with
  | zero =>
    simp only [Nat.zero_mul,WordIntervals.segment,List.ofFn_zero,pow_zero]
    exact map_one T
  | succ m ih =>
    rw [Nat.succ_mul,segment_add]
    rw [show T (segment v s (m*p) ++ segment v (s + (m*p : ℕ)) p) =
      T (segment v s (m*p)) * T (segment v (s + (m*p : ℕ)) p) from map_mul T _ _,ih]
    push_cast
    rw [segment_shift_period hp, pow_succ]

lemma fixed_prefix (T : FreeMonoid Alphabet →* M) {f v : ℤ → Alphabet}
    {p : ℕ} (hp : Function.Periodic v (p : ℤ)) (s k₀ : ℤ) (q : ℕ)
    (hs : s ≤ k₀ - Fintype.card M * p)
    (he : AgreesOn f v (k₀ - Fintype.card M * p)
      (k₀ + (q * (Fintype.card M).factorial : ℕ) * p)) :
    product T f s (k₀ + (q * (Fintype.card M).factorial : ℕ) * p) =
      product T f s k₀ := by
  let N := Fintype.card M
  let x := k₀ - N * p
  have hxp : x ≤ k₀ := by
    have hn : (0 : ℤ) ≤ N * p := by positivity
    dsimp [x]
    omega
  have hk : k₀ ≤ k₀ + (q * N.factorial : ℕ) * p := by
    have hn : (0 : ℤ) ≤ (q * N.factorial : ℕ) * p := by positivity
    omega
  have hleft : product T f x k₀ = T (segment v x p) ^ N := by
    rw [product_congr T hxp (fun i hi hi' => he i hi (hi'.trans_le hk))]
    have hh : k₀ - x = (N*p : ℕ) := by dsimp [x]; ring
    simp only [product,piece,hh,Int.toNat_natCast]
    exact product_periods T hp x N
  have hright : product T f x (k₀ + (q * N.factorial : ℕ) * p) =
      T (segment v x p) ^ (N + q * N.factorial) := by
    rw [product_congr T (hxp.trans hk) he]
    have hh : k₀ + (q * N.factorial : ℕ) * p - x = ((N + q * N.factorial)*p : ℕ) := by
      dsimp [x]; ring
    simp only [product,piece,hh,Int.toNat_natCast]
    exact product_periods T hp x _
  rw [product_append T f hs (hxp.trans hk),product_append T f hs hxp,hright,hleft]
  rw [FiniteMonoidPeriod.pow_factorial _ (le_refl _) q]

lemma progression {B n R d K : ℕ} {r h : ℤ}
    (S : IntegerSchedules.Inner B n R (Fintype.card M) d K r h)
    (rule : Rule Alphabet d K) (hd : 2 ≤ d) (hK : 3*d^2 < K)
    (hr : 0 ≤ r) (hB : 0 < B) (hn : 0 < n)
    (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet) (s z : ℤ) (u : Fin B)
    (hs : s ≤ z + d)
    (hnomarker : ∀ x, z ≤ x → x ≤ z + S.H u + S.extension → x ∉ rule.markers f) :
    ∃ p : ℕ, 0 < p ∧ p < d ∧
      ∀ a : ℕ, a < n →
        a * p * (Fintype.card M).factorial < n * d * (Fintype.card M).factorial ∧
        product T f s (z + S.H u + S.lag + (a*p*(Fintype.card M).factorial*B : ℕ)) =
          product T f s (z + S.H u + S.lag) := by
  have hH := S.H_large u
  have hext := S.extension_pos
  obtain ⟨v,⟨p,hp,hpd,hv⟩,he⟩ := markerless_run rule hd hK f z (S.H u) S.extension
    (by omega) hnomarker
  refine ⟨p,hp,hpd,fun a ha => ?_⟩
  have hap : a * p < n * d := (Nat.mul_lt_mul_of_pos_right ha hp).trans
    (Nat.mul_lt_mul_of_pos_left hpd hn)
  have hfact := Nat.factorial_pos (Fintype.card M)
  have hindex : a * p * (Fintype.card M).factorial < n * d * (Fintype.card M).factorial :=
    Nat.mul_lt_mul_of_pos_right hap hfact
  refine ⟨hindex,?_⟩
  have hpz : (p : ℤ) < d := by exact_mod_cast hpd
  have hN : 0 ≤ (Fintype.card M : ℤ) := by positivity
  have hpre : z + d ≤ z + S.H u + S.lag - Fintype.card M * p := by
    have hl := S.lag_bound
    push_cast at hl
    nlinarith [mul_le_mul_of_nonneg_left hpz.le hN]
  have hlast : z + S.H u + S.lag + (a*p*(Fintype.card M).factorial*B : ℕ) <
      z + S.H u + S.extension - d + K := by
    have hb : a*p*(Fintype.card M).factorial*B < n*d*(Fintype.card M).factorial*B :=
      Nat.mul_lt_mul_of_pos_right hindex hB
    have hbz : ((a*p*(Fintype.card M).factorial*B : ℕ) : ℤ) <
        (n*d*(Fintype.card M).factorial*B : ℕ) := by exact_mod_cast hb
    have hh := S.extension_bound
    omega
  have hstep : ((a*B*(Fintype.card M).factorial : ℕ) : ℤ) * p =
      (a*p*(Fintype.card M).factorial*B : ℕ) := by push_cast; ring
  simpa only [hstep] using fixed_prefix T hv s (z + S.H u + S.lag) (a*B)
    (hs.trans hpre) (fun i hi hi' => he i (hpre.trans hi) (by rw [hstep] at hi'; omega))

end PeriodicCuts

namespace PeriodicClock

open scoped BigOperators

lemma map_modEq {G : Type uG} [AddCommGroup G] (φ : ℤ →+ G) {n x y : ℤ}
    (hn : φ n = 0) (he : Int.ModEq n x y) : φ x = φ y := by
  obtain ⟨a,ha⟩ := Int.modEq_iff_dvd.mp he
  have hh : φ (y-x) = 0 := by
    rw [ha,mul_comm,← Int.zsmul_eq_mul,map_zsmul,hn,smul_zero]
  rw [map_sub,sub_eq_zero] at hh
  exact hh.symm

lemma sweep {G : Type uG2} [AddCommGroup G] (φ : ℤ →+ G) {n p : ℕ}
    (hn : 0 < n) (hφ : φ n = 0) (hcop : Nat.Coprime p n) (x y : ℤ) :
    ∃ a : ℕ, a < n ∧ φ (x + a*p) = φ (x+y) := by
  have : NeZero n := ⟨hn.ne'⟩
  let b : ZMod n := ↑((ZMod.unitOfCoprime p hcop)⁻¹) * (y : ZMod n)
  refine ⟨b.val,ZMod.val_lt b,?_⟩
  have he : (b.val : ZMod n) * p = (y : ZMod n) := by
    rw [ZMod.natCast_zmod_val]
    dsimp [b]
    rw [mul_right_comm,← ZMod.coe_unitOfCoprime p hcop,Units.inv_mul,one_mul]
  have hm : Int.ModEq (n : ℤ) ((b.val : ℤ)*p) y := by
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    simpa only [Int.cast_mul,Int.cast_natCast] using he
  rw [map_add,map_add,map_modEq φ hφ hm]

lemma progression_coprime {C : Type uC2} [Fintype C] (n : C → ℕ)
    (hn : ∀ c, Nat.Prime (n c)) {p N B d : ℕ}
    (hp : 0 < p) (hpd : p < d) (hN : 0 < N) (hB : 0 < B)
    (hlarge : ∀ c, d < n c ∧ N < n c ∧ B < n c) :
    Nat.Coprime (p*N*B) (∏ c, n c) := by
  exact (coprime_product_of_small n hn hp (fun c => hpd.trans (hlarge c).1)).mul_left
    (coprime_product_of_small n hn hN (fun c => (hlarge c).2.1)) |>.mul_left
    (coprime_product_of_small n hn hB (fun c => (hlarge c).2.2))

end PeriodicClock

namespace SuffixDecoder

open ExceptionalOrigins EpisodeEnd

variable {Alphabet : Type uAlphabet3} {J : Type uJ2} {C : Type uC3} {Kind : Type uKind} [Fintype Kind] {μ : ℕ}
    (A : Parameters Alphabet J C)

lemma available_copy (p : Kind × Fin μ → ℤ) (lag s b H : ℤ)
    (f : ℤ → Alphabet) (reference : Kind × Fin μ) (kind : Kind)
    (hbad : (A.bad p f (s+lag) (b-A.endRule.tail)).card < μ)
    (hvis : ∀ a i, A.Visible (s+p a) b (s+lag+(p a-p i))
      (A.anchor f (b-A.endRule.tail) (s+lag+(p a-p i))))
    (hnear : ∀ i j, |p i-p j| ≤ H)
    (hnest : (A.endRule.d : ℤ)+(A.endRule.B-1)*A.endRule.S+H ≤ 3*A.endRule.d)
    (hover : (A.endRule.d : ℤ)^2 ≤ A.endRule.K-H)
    (hover' : H < A.endRule.K)
    (hend : EndAt A.endRule.d A.endRule.K A.endRule.tail f
      (s+lag+A.endRule.offset) (A.endRule.small f (s+lag+A.endRule.offset)) b)
    (hfailed : A.Failed f (s+lag) (A.anchor f (b-A.endRule.tail) (s+lag))) :
    ∃ copy : Fin μ, Test A (origin p lag (s+p (kind,copy))) reference
      (s+p (kind,copy)) b f (kind,copy) := by
  classical
  obtain ⟨copy,hcopy⟩ := StencilSparsity.good_copy μ _ hbad kind
  let actual := (kind,copy)
  have ht : ∀ i, origin p lag (s+p actual) i = s+lag+(p actual-p i) := by
    intro i
    dsimp [origin]
    ring
  have htactual : origin p lag (s+p actual) actual = s+lag := by
    rw [ht]
    ring
  refine ⟨copy, available_at A (τ := origin p lag (s+p actual)) (actual := actual) (H := H) ?_ ?_
    hnest ?_ ?_ ?_ ?_ ?_⟩
  · intro i
    rw [ht]
    exact hvis actual i
  · intro i j
    rw [ht,ht,show s+lag+(p actual-p i)-(s+lag+(p actual-p j)) = p j-p i by ring]
    exact hnear j i
  · rw [ht,ht,show s+lag+(p actual-p actual)-(s+lag+(p actual-p reference)) =
      p reference-p actual by ring]
    exact hover.trans (by have := hnear reference actual; omega)
  · rw [ht,ht,show s+lag+(p actual-p actual)-(s+lag+(p actual-p reference)) =
      p reference-p actual by ring]
    exact (hnear reference actual).trans_lt hover'
  · simpa only [htactual] using hend
  · simpa only [htactual] using hfailed
  · intro i hi hfail
    apply hcopy i
    simp only [Parameters.bad,Finset.mem_filter,Finset.mem_univ,true_and]
    refine ⟨Ne.symm hi,?_⟩
    simpa only [ht] using hfail

end SuffixDecoder

namespace SpacedStencil

lemma exists_points_fintype {P : Type uP2} [Fintype P] [LinearOrder P]
    (K : ℤ) (U : P → ℤ → Prop) (hU : ∀ i L, ∃ q, L < q ∧ U i q) :
    ∃ p : P → ℤ, (∀ i, U i (p i) ∧ K < p i) ∧
      ∀ i j, i < j → 2*p i+K < p j := by
  let e := Fintype.orderIsoFinOfCardEq P rfl
  obtain ⟨q,hq,hsep⟩ := exists_points (Fintype.card P) K (fun i => U (e i))
    (fun i L => hU (e i) L)
  refine ⟨fun i => q (e.symm i),?_,?_⟩
  · intro i
    simpa only [e.apply_symm_apply] using hq (e.symm i)
  · intro i j hij
    exact hsep _ _ (e.symm.strictMono hij)

lemma exists_boundaries {P : Type uP3} [Fintype P] {g : ℕ}
    (label : P → Fin g) (p : P → ℤ)
    (honto : Function.Surjective label) (hpos : ∀ a, 0 < p a)
    (hgap : ∀ a b, label a < label b → p a+1 < p b) :
    ∃ β : Fin (g+1) → ℤ, β 0 = 0 ∧ StrictMono β ∧
      ∀ a, β (label a).castSucc < p a ∧ p a < β (label a).succ := by
  classical
  have hsep : ∀ j : Fin (g+1), ∃ z : ℤ, (j=0 → z=0) ∧
      (∀ a, (label a).val < j.val → p a < z) ∧
      (∀ a, j.val ≤ (label a).val → z < p a) := by
    intro j
    by_cases hj : j=0
    · subst j
      exact ⟨0,fun _ => rfl,fun a ha => False.elim (Nat.not_lt_zero _ ha),fun a _ => hpos a⟩
    · have hjpos : 0 < j.val := Fin.pos_iff_ne_zero.mpr hj
      let F := Finset.univ.filter (fun a => (label a).val < j.val)
      have hF : F.Nonempty := by
        have hg : 0 < g := by omega
        obtain ⟨a,ha⟩ := honto ⟨0,hg⟩
        refine ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
        simpa only [ha] using hjpos
      obtain ⟨a,ha,hamax⟩ := Finset.exists_max_image F p hF
      have halabel := (Finset.mem_filter.mp ha).2
      refine ⟨p a+1,fun h => False.elim (hj h),?_,?_⟩
      · intro b hb
        have hh := hamax b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩)
        omega
      · intro b hb
        exact hgap a b (by change (label a).val < (label b).val; omega)
  choose β hβ using hsep
  refine ⟨β,(hβ 0).1 rfl,?_,?_⟩
  · intro i j hij
    have hi : i.val < g := by have := j.isLt; exact lt_of_lt_of_le hij (Nat.le_of_lt_succ this)
    obtain ⟨a,ha⟩ := honto ⟨i.val,hi⟩
    have hleft := (hβ i).2.2 a (by simp only [ha]; exact le_refl _)
    have hright := (hβ j).2.1 a (by simp only [ha]; exact hij)
    exact hleft.trans hright
  · intro a
    exact ⟨(hβ (label a).castSucc).2.2 a (le_refl _),
      (hβ (label a).succ).2.1 a (Nat.lt_succ_self _)⟩

end SpacedStencil

end GeneralizedStarHeight

end OAI
