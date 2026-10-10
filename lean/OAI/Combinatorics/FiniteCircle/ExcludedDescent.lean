import OAI.Combinatorics.FiniteCircle.MaskDescent

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

theorem PhaseSupported.neg {G : Type*} [AddCommGroup G] {S : Finset ℕ}
    {x : G} (hx : PhaseSupported S x) : PhaseSupported S (-x) := by
  change _ • (-x) = 0
  rw [smul_neg, hx, neg_zero]

 theorem circleCost_support_lower_pow {M h K e : ℕ} [NeZero M] (hh : 1 ≤ h)
    {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime ∧ q ≤ h^e) (hcard : S.card ≤ K)
    {x : ZMod M} (hx : x ≠ 0) (hs : PhaseSupported S x) :
    1 / ((h:ℝ)^(e*K)) ≤ circleCost x := by
  let Q := ∏ q ∈ S, q
  have hQ : 0 < Q := Finset.prod_pos (fun q hq => (hS q hq).1.pos)
  have hQu : Q ≤ h^(e*K) := by
    calc
      Q ≤ ∏ _q ∈ S, h^e := Finset.prod_le_prod (fun q hq => (hS q hq).2)
      _ = h^(e*S.card) := by simp only [Finset.prod_const]; rw [← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right hh (Nat.mul_le_mul_left e hcard)
  have he := circleCost_order_lower hQ hx hs
  have hp : (0:ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  rw [div_le_iff₀ (pow_pos hp _)]
  have hc := circleCost_nonneg x
  have hQu' : (Q:ℝ) ≤ (h:ℝ)^(e*K) := by exact_mod_cast hQu
  nlinarith

def pairResetBudget (K T n l : ℕ) : ℕ := (n+l*T+K-3)/(K-2)

 theorem pairResetBudget_mono {K T n m l r : ℕ} (h : n+l*T ≤ m+r*T) :
    pairResetBudget K T n l ≤ pairResetBudget K T m r := by
  unfold pairResetBudget
  exact Nat.div_le_div_right (by omega)

 theorem pairResetBudget_overflow {K T n s l : ℕ} (hK : 3 ≤ K)
    (hs : s < T) (hover : K < n+s) :
    pairResetBudget K T 2 l+1 ≤ pairResetBudget K T n (l+1) := by
  have hstep : 2+l*T+K-3+(K-2) ≤ n+(l+1)*T+K-3 := by
    rw [Nat.add_mul]; omega
  have hdiv := Nat.div_le_div_right (c := K-2) hstep
  rw [Nat.add_div_right _ (by omega : 0 < K-2)] at hdiv
  exact hdiv

noncomputable def pairDescentBound (m K T B n l : ℕ) : ℝ :=
  1/((4:ℝ)^l*(B:ℝ)^(l+3*pairResetBudget K T n l)*(m:ℝ)^(5*K))

 theorem pairDescentBound_pos {m K T B n l : ℕ} (hm : 0 < m) (hB : 0 < B) :
    0 < pairDescentBound m K T B n l := by
  unfold pairDescentBound; positivity

 theorem pairDescentBound_step {m K T B n s l e : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    (he : l+3*pairResetBudget K T s l+e ≤ l+1+3*pairResetBudget K T n (l+1)) :
    pairDescentBound m K T B n (l+1) ≤
      (1/(4*(B:ℝ)^e))*pairDescentBound m K T B s l := by
  have hb : (1:ℝ) ≤ B := by exact_mod_cast hB
  have hp : (0:ℝ) < m := by exact_mod_cast hm
  have hlu := pow_le_pow_right₀ hb he
  unfold pairDescentBound
  rw [one_div_mul_one_div]
  apply one_div_le_one_div_of_le
  · positivity
  · calc
      4*(B:ℝ)^e*((4:ℝ)^l*(B:ℝ)^(l+3*pairResetBudget K T s l)*(m:ℝ)^(5*K)) =
        (4:ℝ)^(l+1)*(B:ℝ)^(l+3*pairResetBudget K T s l+e)*(m:ℝ)^(5*K) := by
          rw [pow_succ, pow_add]; ring
      _ ≤ _ := by gcongr

 theorem pairDescentBound_base {m K T B n : ℕ} (hm : 0 < m) (hB : 1 ≤ B) :
    pairDescentBound m K T B n 0 ≤ 1/(m:ℝ)^(5*K) := by
  have hb : (1:ℝ) ≤ B := by exact_mod_cast hB
  have hp : (0:ℝ) < m := by exact_mod_cast hm
  unfold pairDescentBound
  simp only [pow_zero, one_mul, zero_add]
  apply one_div_le_one_div_of_le (by positivity)
  exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hb)

theorem excluded_denominator_descent {m H M K T B : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (hT : 2 ≤ T) (hB : 1 ≤ B) (hmB : m ≤ B^4) (hmTB : m ≤ T*B)
    (hsmall : 2*T ≤ m) (hK : 3 ≤ K)
    (hd : ∀ l (k : Fin m), p l k ∣ M) (hn : ∀ l (k : Fin m), 0 < p l k)
    (hp : ∀ l, 1 ≤ l → l ≤ H → ∀ k : Fin m, (p l k).Prime)
    (hin : ∀ l, 1 ≤ l → l ≤ H → ∀ k : Fin m, p l k ≤ m^5)
    (hinj : ∀ l, 1 ≤ l → l ≤ H → Function.Injective (fun k : Fin m => p l k))
    (hlevel : ∀ l r, 1 ≤ l → l ≤ H → 1 ≤ r → r ≤ H → l ≠ r →
      ∀ i j : Fin m, p l i ≠ p r j) :
    ∀ l, l ≤ H → ∀ (S : Finset ℕ) (x : ZMod M), S.card ≤ K →
      (∀ q ∈ S, q.Prime ∧ q ≤ m^5) → LowerFresh m p l S → x ≠ 0 →
      PhaseSupported S x → pairDescentBound m K T B S.card l ≤ excludedCost m p M hd hn l x := by
  classical
  have hm : 0 < m := by omega
  have hBp : 0 < B := by omega
  intro l
  induction l with
  | zero =>
    intro _ S x hcard hS _ hx hs
    exact (pairDescentBound_base hm hB).trans (circleCost_support_lower_pow (by omega) hS hcard hx hs)
  | succ l ih =>
    intro hlH S x hcard hS hfresh hx hs
    let : ∀ k : Fin m, NeZero (p (l+1) k) := fun k => ⟨(hn _ k).ne'⟩
    let f := excludedCost m p M hd hn l
    obtain ⟨z,hact,hinact⟩ := excluded_minimizer_options (by omega) (hd (l+1)) (hn (l+1)) f x
    let A := Finset.univ.filter (fun k : Fin m => z k ≠ 0)
    let P := A.image (fun k : Fin m => p (l+1) k)
    have hpP (q : ℕ) (hq : q ∈ P) : q.Prime ∧ q ≤ m^5 := by
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hq
      exact ⟨hp (l+1) (by omega) hlH k, hin (l+1) (by omega) hlH k⟩
    have hfreshP : LowerFresh m p l P := by
      intro j hj hjl k hk
      obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hk
      exact hlevel j (l+1) hj (by omega) (by omega) hlH (by omega) k t ht.symm
    have hdis : Disjoint S P := by
      apply Finset.disjoint_left.mpr
      intro q hq hqP
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hqP
      exact hfresh (l+1) (by omega) (by omega) k hq
    have hchild (i j : Fin m) (hi : z i ≠ 0) (hij : i ≠ j) :
        pairDescentBound m K T B 2 l ≤ f (subcircle (hd (l+1) i) (z i)-subcircle (hd (l+1) j) (z j)) := by
      have hne : p (l+1) i ≠ p (l+1) j := (hinj (l+1) (by omega) hlH).ne hij
      let Q : Finset ℕ := {p (l+1) i,p (l+1) j}
      have hQ : Q.card = 2 := by simp [Q,hne]
      have hfr : LowerFresh m p l Q := by
        intro r hr hrl k hk
        simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with hk | hk
        · exact hlevel r (l+1) hr (by omega) (by omega) hlH (by omega) k i hk
        · exact hlevel r (l+1) hr (by omega) (by omega) hlH (by omega) k j hk
      have hpi := hp (l+1) (by omega) hlH i
      have hpj := hp (l+1) (by omega) hlH j
      have hsupp : PhaseSupported Q (subcircle (hd (l+1) i) (z i)-subcircle (hd (l+1) j) (z j)) := by
        simpa only [Finset.singleton_union, sub_eq_add_neg] using
          (support_subcircle (hd (l+1) i) (z i)).add (support_subcircle (hd (l+1) j) (z j)).neg
      have hnon : subcircle (hd (l+1) i) (z i)-subcircle (hd (l+1) j) (z j) ≠ 0 := by
        rw [sub_eq_add_neg]
        apply phase_add_supported_ne_zero (support_subcircle (hd (l+1) i) (z i))
          (support_subcircle (hd (l+1) j) (z j)).neg
        · simpa using hpi
        · simpa using hpj
        · simpa using hne
        · simpa only [map_zero] using (subcircle_injective (hd (l+1) i)).ne hi
      have hQP (q : ℕ) (hq : q ∈ Q) : q.Prime ∧ q ≤ m^5 := by
        simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact ⟨hpi,hin (l+1) (by omega) hlH i⟩
        · exact ⟨hpj,hin (l+1) (by omega) hlH j⟩
      simpa only [hQ] using ih (by omega) Q _ (by omega) hQP hfr hnon hsupp
    have hreset : (A.card:ℝ)/(4*m)*pairDescentBound m K T B 2 l ≤ excludedCost m p M hd hn (l+1) x :=
      hact _ (pairDescentBound_pos hm hBp).le hchild
    have hspos : 0 < S.card := support_card_pos hx hs
    have hmreal : (0:ℝ) < m := by exact_mod_cast hm
    have hBreal : (0:ℝ) < B := by exact_mod_cast hBp
    by_cases hlarge : T ≤ A.card
    · have hbudget : pairResetBudget K T 2 l ≤ pairResetBudget K T S.card (l+1) := by
        apply pairResetBudget_mono
        rw [Nat.add_mul]; omega
      have hstep := pairDescentBound_step (K := K) (T := T) (n := S.card) (s := 2) (l := l) (e := 1) hm hB (by omega)
      have hfac : 1/(4*(B:ℝ)^1) ≤ (A.card:ℝ)/(4*m) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        simp only [pow_one]
        have hmTB' : (m:ℝ) ≤ T*B := by exact_mod_cast hmTB
        have ha : (T:ℝ) ≤ A.card := by exact_mod_cast hlarge
        nlinarith
      exact hstep.trans ((mul_le_mul_of_nonneg_right hfac (pairDescentBound_pos hm hBp).le).trans hreset)
    · have hsm : A.card < T := by omega
      by_cases hover : K < S.card+A.card
      · have hapos : 0 < A.card := by omega
        have hbudget := pairResetBudget_overflow (l := l) hK hsm hover
        have hstep := pairDescentBound_step (K := K) (T := T) (n := S.card) (s := 2) (l := l) (e := 4) hm hB (by omega)
        have hfac : 1/(4*(B:ℝ)^4) ≤ (A.card:ℝ)/(4*m) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have ha : (1:ℝ) ≤ A.card := by exact_mod_cast hapos
          have hmB' : (m:ℝ) ≤ (B:ℝ)^4 := by exact_mod_cast hmB
          nlinarith [pow_nonneg (Nat.cast_nonneg B : (0:ℝ) ≤ B) 4]
        exact hstep.trans ((mul_le_mul_of_nonneg_right hfac (pairDescentBound_pos hm hBp).le).trans hreset)
      · have hPC : P.card ≤ A.card := Finset.card_image_le
        have hunion : (S ∪ P).card ≤ S.card+A.card := (Finset.card_union_le S P).trans (by omega)
        have hnew := hs.add (support_mask_sum (hd (l+1)) z)
        have hnz : (x+∑ k,subcircle (hd (l+1) k) (z k)) ≠ 0 :=
          phase_add_supported_ne_zero hs (support_mask_sum (hd (l+1)) z)
            (fun q hq => (hS q hq).1) (fun q hq => (hpP q hq).1) hdis hx
        have hfr : LowerFresh m p l (S ∪ P) := by
          intro j hj hjl k hk
          rcases Finset.mem_union.mp hk with hk | hk
          · exact hfresh j hj (by omega) k hk
          · exact hfreshP j hj hjl k hk
        have hSUP (q : ℕ) (hq : q ∈ S ∪ P) : q.Prime ∧ q ≤ m^5 := by
          rcases Finset.mem_union.mp hq with hq | hq
          · exact hS q hq
          · exact hpP q hq
        have hlower := ih (by omega) (S ∪ P) _ (by omega) hSUP hfr hnz hnew
        have hbudget : pairResetBudget K T (S∪P).card l ≤ pairResetBudget K T S.card (l+1) := by
          apply pairResetBudget_mono
          rw [Nat.add_mul]; omega
        have hstep := pairDescentBound_step (K := K) (T := T) (n := S.card) (s := (S∪P).card) (l := l) (e := 0) hm hB (by omega)
        simp only [pow_zero,mul_one] at hstep
        exact hstep.trans ((mul_le_mul_of_nonneg_left hlower (by norm_num : (0:ℝ) ≤ 1/4)).trans
          (hinact (by change 2*A.card ≤ m; omega)))

 theorem resetBudget_bound {h T : ℕ} (hh : 1000000 ≤ h) (hT : 1 ≤ T) :
    resetBudget (h/100) T 1 h ≤ 200*T := by
  let K := h/100
  have hKh : h ≤ 198*(K-1) := by dsimp [K]; omega
  have hK : K ≤ 2*(K-1) := by dsimp [K]; omega
  have hmul := Nat.mul_le_mul_right T hKh
  have hmulK := Nat.mul_le_mul_left (2*(K-1)) hT
  unfold resetBudget
  apply Nat.div_le_of_le_mul
  change 1+h*T+K-2 ≤ (K-1)*(200*T)
  calc
    _ ≤ h*T+K := by omega
    _ ≤ 198*(K-1)*T+2*(K-1)*T := Nat.add_le_add hmul (hK.trans (by simpa using hmulK))
    _ = _ := by ring

 theorem pairResetBudget_bound {h T : ℕ} (hh : 1000000 ≤ h) (hT : 1 ≤ T) :
    pairResetBudget (h/100) T 1 h ≤ 200*T := by
  let K := h/100
  have hKh : h ≤ 198*(K-2) := by dsimp [K]; omega
  have hK : K ≤ 2*(K-2) := by dsimp [K]; omega
  have hmul := Nat.mul_le_mul_right T hKh
  have hmulK := Nat.mul_le_mul_left (2*(K-2)) hT
  unfold pairResetBudget
  apply Nat.div_le_of_le_mul
  change 1+h*T+K-3 ≤ (K-2)*(200*T)
  calc
    _ ≤ h*T+K := by omega
    _ ≤ 198*(K-2)*T+2*(K-2)*T := Nat.add_le_add hmul (hK.trans (by simpa using hmulK))
    _ = _ := by ring

 theorem mask_budget_exponent {n : ℕ} (hn : 1000000 ≤ n) :
    2*resetBudget (n^4/100) (n^2) 1 (n^4)+16*(n^4/100) ≤ n^4/2 := by
  have hn2 : 2000 ≤ n^2 := by nlinarith
  have hn4 : 1000000 ≤ n^4 := by nlinarith [sq_nonneg (n^2:ℤ)]
  have hb := resetBudget_bound hn4 (show 1 ≤ n^2 by omega)
  have hk := Nat.mul_div_le (n^4) 100
  have hp : 40000*n^2 ≤ 34*n^4 := by nlinarith
  omega

 theorem excluded_budget_exponent {n : ℕ} (hn : 1000000 ≤ n) :
    3*pairResetBudget (n^4/100) (n^3) 1 (n^4)+20*(n^4/100) ≤ n^4 := by
  have hn3 : 1 ≤ n^3 := Nat.one_le_pow _ _ (by omega)
  have hn4 : 1000000 ≤ n^4 := by nlinarith [Nat.pow_le_pow_left (show 2 ≤ n by omega) 4]
  have hb := pairResetBudget_bound hn4 hn3
  have hk := Nat.mul_div_le (n^4) 100
  have hp := Nat.mul_le_mul_right (n^3) (show 1000 ≤ n by omega)
  have he : n*n^3=n^4 := by ring
  rw [he] at hp
  omega

 theorem four_eight_pow_le {n h : ℕ} (hn : 256 ≤ n) (hh : 2 ≤ h) (he : h=2*(h/2)) :
    4*(8:ℝ)^h ≤ (n:ℝ)^(h/2) := by
  have hfour : (4:ℝ) ≤ 2^h := by
    calc
      (4:ℝ) = 2^2 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hh
  calc
    4*(8:ℝ)^h ≤ (2:ℝ)^h*8^h := mul_le_mul_of_nonneg_right hfour (by positivity)
    _ = (16:ℝ)^h := by rw [← mul_pow]; norm_num
    _ = (256:ℝ)^(h/2) := by conv_lhs => rw [he, pow_mul]; norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hn) _

 theorem mask_descent_numeric {n : ℕ} (hn : 1000000 ≤ n) (he : n^4=2*(n^4/2)) :
    1/(n:ℝ)^(3*n^4) ≤ (1/((2:ℝ)^(n^4)*4)) * descentBound (n^4) (n^4/100) (n^2) 1 (n^4) := by
  have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hh : 2 ≤ n^4 := by nlinarith [Nat.pow_le_pow_left (show 2≤n by omega) 4]
  have hf := four_eight_pow_le (show 256≤n by omega) hh he
  have hb := mask_budget_exponent hn
  let b := resetBudget (n^4/100) (n^2) 1 (n^4)
  let K := n^4/100
  have hex : n^4/2+(2*(n^4+b)+16*K) ≤ 3*n^4 := by dsimp [b,K]; omega
  have hg : (2:ℝ)^(n^4)*4*((4:ℝ)^(n^4)*(n:ℝ)^(2*(n^4+b))*(n:ℝ)^(16*K)) ≤ (n:ℝ)^(3*n^4) := by
    calc
      _ = (4*(8:ℝ)^(n^4)) * (n:ℝ)^(2*(n^4+b)+16*K) := by rw [show (8:ℝ)=2*4 by norm_num, mul_pow]; simp only [pow_add]; ring
      _ ≤ (n:ℝ)^(n^4/2) * (n:ℝ)^(2*(n^4+b)+16*K) := mul_le_mul_of_nonneg_right hf (by positivity)
      _ = (n:ℝ)^(n^4/2+(2*(n^4+b)+16*K)) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hn1 hex
  unfold descentBound
  rw [one_div_mul_one_div]
  push_cast
  simp only [← pow_mul]
  change 1/(n:ℝ)^(3*n^4) ≤ 1/((2:ℝ)^(n^4)*4*((4:ℝ)^(n^4)*(n:ℝ)^(2*(n^4+b))*(n:ℝ)^(4*(4*K))))
  have heK : 4*(4*K)=16*K := by omega
  rw [heK]
  exact one_div_le_one_div_of_le (by positivity) hg

 theorem excluded_descent_numeric {n : ℕ} (hn : 1000000 ≤ n) (he : n^4=2*(n^4/2)) :
    1/(n:ℝ)^(3*n^4) ≤ (1/((2:ℝ)^(n^4)*4)) * pairDescentBound (n^4) (n^4/100) (n^3) n 1 (n^4) := by
  have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hh : 2 ≤ n^4 := by nlinarith [Nat.pow_le_pow_left (show 2≤n by omega) 4]
  have hf := four_eight_pow_le (show 256≤n by omega) hh he
  have hb := excluded_budget_exponent hn
  let b := pairResetBudget (n^4/100) (n^3) 1 (n^4)
  let K := n^4/100
  have hex : n^4/2+(n^4+3*b+20*K) ≤ 3*n^4 := by dsimp [b,K]; omega
  have hg : (2:ℝ)^(n^4)*4*((4:ℝ)^(n^4)*(n:ℝ)^(n^4+3*b)*(n:ℝ)^(20*K)) ≤ (n:ℝ)^(3*n^4) := by
    calc
      _ = (4*(8:ℝ)^(n^4)) * (n:ℝ)^(n^4+3*b+20*K) := by rw [show (8:ℝ)=2*4 by norm_num, mul_pow]; simp only [pow_add]; ring
      _ ≤ (n:ℝ)^(n^4/2) * (n:ℝ)^(n^4+3*b+20*K) := mul_le_mul_of_nonneg_right hf (by positivity)
      _ = (n:ℝ)^(n^4/2+(n^4+3*b+20*K)) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hn1 hex
  unfold pairDescentBound
  rw [one_div_mul_one_div]
  push_cast
  simp only [← pow_mul]
  change 1/(n:ℝ)^(3*n^4) ≤ 1/((2:ℝ)^(n^4)*4*((4:ℝ)^(n^4)*(n:ℝ)^(n^4+3*b)*(n:ℝ)^(4*(5*K))))
  have heK : 4*(5*K)=20*K := by omega
  rw [heK]
  exact one_div_le_one_div_of_le (by positivity) hg

end FiniteCircle

end OAI
