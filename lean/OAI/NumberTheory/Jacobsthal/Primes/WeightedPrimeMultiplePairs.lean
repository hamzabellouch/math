import OAI.NumberTheory.Jacobsthal.Estimates.UniformLower
import OAI.NumberTheory.Jacobsthal.Partitions.SignedIntervalGeometry

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Dependency.SiegelWalfisz
open _root_.Finset
open scoped Topology

noncomputable def primeMultiplesIn (d : ℕ) (P x y : ℝ) : Finset ℤ := by
  classical
  exact (Icc (⌈x⌉:ℤ) (⌊y⌋:ℤ)).filter (fun m:ℤ => x < (m:ℝ) ∧ (m:ℝ) < y ∧
    ∃ ell : ℕ, ell.Prime ∧ P < (ell:ℝ) ∧ (m=(d:ℤ)*ell ∨ m= -((d:ℤ)*ell)))

lemma mem_primeMultiplesIn (d : ℕ) (P x y : ℝ) (m : ℤ) :
    m ∈ primeMultiplesIn d P x y ↔ x < (m:ℝ) ∧ (m:ℝ) < y ∧
      ∃ ell : ℕ, ell.Prime ∧ P < (ell:ℝ) ∧ (m=(d:ℤ)*ell ∨ m= -((d:ℤ)*ell)) := by
  classical
  constructor
  · intro hm
    exact (mem_filter.mp hm).2
  · intro hm
    apply mem_filter.mpr
    exact ⟨mem_Icc.mpr ⟨Int.ceil_le.mpr hm.1.le,Int.le_floor.mpr hm.2.1.le⟩,hm⟩

lemma prime_multiple_pos_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (fun ell:ℕ => (d:ℤ)*(ell:ℤ)) := by
  intro a b hab
  have hd0 : (d:ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have he := mul_left_cancel₀ hd0 hab
  exact_mod_cast he

lemma prime_multiple_neg_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (fun ell:ℕ => -((d:ℤ)*(ell:ℤ))) := by
  intro a b hab
  exact prime_multiple_pos_injective hd (neg_injective hab)

lemma signed_prime_sets_card_le {d : ℕ} (hd : 0 < d) {P x y : ℝ} (A B : Finset ℕ)
    (hA : ∀ ell ∈ A, ell.Prime ∧ P < (ell:ℝ) ∧ x < (d:ℝ)*ell ∧ (d:ℝ)*ell < y)
    (hB : ∀ ell ∈ B, ell.Prime ∧ P < (ell:ℝ) ∧ x < -((d:ℝ)*ell) ∧ -((d:ℝ)*ell) < y) :
    A.card+B.card ≤ (primeMultiplesIn d P x y).card := by
  classical
  let pos : ℕ → ℤ := fun ell => (d:ℤ)*ell
  let neg : ℕ → ℤ := fun ell => -((d:ℤ)*ell)
  have hsub : A.image pos ∪ B.image neg ⊆ primeMultiplesIn d P x y := by
    intro m hm
    rcases mem_union.mp hm with hm|hm
    · obtain ⟨ell,he,rfl⟩ := mem_image.mp hm
      obtain ⟨hp,hP,hlo,hhi⟩ := hA ell he
      apply (mem_primeMultiplesIn _ _ _ _ _).mpr
      refine ⟨?_,?_,ell,hp,hP,Or.inl rfl⟩
      · simpa [pos] using hlo
      · simpa [pos] using hhi
    · obtain ⟨ell,he,rfl⟩ := mem_image.mp hm
      obtain ⟨hp,hP,hlo,hhi⟩ := hB ell he
      apply (mem_primeMultiplesIn _ _ _ _ _).mpr
      refine ⟨?_,?_,ell,hp,hP,Or.inr rfl⟩
      · simpa [neg] using hlo
      · simpa [neg] using hhi
  have hdisj : Disjoint (A.image pos) (B.image neg) := by
    apply disjoint_left.mpr
    intro m hmA hmB
    obtain ⟨a,ha,ham⟩ := mem_image.mp hmA
    obtain ⟨b,hb,hbm⟩ := mem_image.mp hmB
    have hdZ : (0:ℤ) < d := by exact_mod_cast hd
    have hapos : 0 < pos a := mul_pos hdZ (by exact_mod_cast (hA a ha).1.pos)
    have hbpos : 0 < (d:ℤ)*(b:ℤ) := mul_pos hdZ (by exact_mod_cast (hB b hb).1.pos)
    have he : pos a = -((d:ℤ)*(b:ℤ)) := ham.trans hbm.symm
    linarith
  have he := card_le_card hsub
  rw [card_union_of_disjoint hdisj,card_image_of_injective _ (prime_multiple_pos_injective hd),
    card_image_of_injective _ (prime_multiple_neg_injective hd)] at he
  exact he

end Erdos970Dependency.SiegelWalfisz



namespace ErdosStoppedArithmetic
open Erdos970Dependency.SiegelWalfisz
attribute [local instance] Classical.propDecidable

theorem large_prime_factor_unique (d e p q : ℕ) (he : 0 < e) (hp : p.Prime) (hq : q.Prime)
    (hep : e < p) (heq : d*p=e*q) : d=e ∧ p=q := by
  have hpd : p ∣ e*q := heq ▸ Nat.dvd_mul_left p d
  have hpeq : p=q := by
    rcases hp.dvd_mul.mp hpd with hpe | hpq
    · have hh := Nat.le_of_dvd he hpe
      omega
    · rcases (Nat.dvd_prime hq).mp hpq with h | h
      · exact (hp.ne_one h).elim
      · exact h
  refine ⟨?_,hpeq⟩
  rw [hpeq] at heq
  exact mul_right_cancel₀ hq.ne_zero heq

theorem prime_multiple_natAbs (d : ℕ) (P x y : ℝ) (m : ℤ)
    (hm : m ∈ primeMultiplesIn d P x y) :
    ∃ p : ℕ,p.Prime ∧ P < (p : ℝ) ∧ m.natAbs=d*p := by
  obtain ⟨_hx,_hy,p,hp,hP,hpos|hneg⟩ := (mem_primeMultiplesIn d P x y m).mp hm
  · exact ⟨p,hp,hP,by rw [hpos,Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_natCast]⟩
  · exact ⟨p,hp,hP,by rw [hneg,Int.natAbs_neg,Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_natCast]⟩

theorem prime_multiple_factors_disjoint (P x y : ℝ) (d e : ℕ) (he : 0 < e)
    (heP : (e : ℝ) ≤ P) (hne : d ≠ e) :
    Disjoint (primeMultiplesIn d P x y) (primeMultiplesIn e P x y) := by
  apply Finset.disjoint_left.mpr
  intro m hmd hme
  obtain ⟨p,hp,hP,hd⟩ := prime_multiple_natAbs d P x y m hmd
  obtain ⟨q,hq,_hQ,heq⟩ := prime_multiple_natAbs e P x y m hme
  have hep : e < p := by exact_mod_cast heP.trans_lt hP
  exact hne (large_prime_factor_unique d e p q he hp hq hep (hd.symm.trans heq)).1

end ErdosStoppedArithmetic



namespace Erdos970Dependency.SiegelWalfisz

lemma prime_multiple_d_le_P {P d : ℝ} (hP : 1 ≤ P) (hd : d ≤ P^(19/20:ℝ)) : d ≤ P := by
  calc
    _ ≤ P^(19/20:ℝ) := hd
    _ ≤ P^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
    _ = P := Real.rpow_one P

lemma prime_multiple_P_sq_le {P s : ℝ} (hP : 1 ≤ P) (hs : 2 ≤ s) : P^2 ≤ P^s := by
  calc
    _ = P^(2:ℝ) := (Real.rpow_natCast P 2).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP hs

lemma prime_multiple_interval_height {Cs w P s x y : ℝ} (hP : 0 < P)
    (hheight : 2*w^(Cs+2) ≤ P^(1/50:ℝ))
    (hxy : max |x| |y| ≤ 2*w^(Cs+2)*P^s) : max |x| |y| ≤ P^(s+1/50) := by
  calc
    _ ≤ 2*w^(Cs+2)*P^s := hxy
    _ ≤ P^(1/50:ℝ)*P^s := mul_le_mul_of_nonneg_right hheight (Real.rpow_pos_of_pos hP _).le
    _ = _ := by rw [← Real.rpow_add hP]; congr 1; ring

lemma prime_multiple_piece_bounds {Cs w P s H d a b : ℝ}
    (hCs : 0 ≤ Cs) (hw : 4 ≤ w) (hP : 3 ≤ P) (hs : 203/100 ≤ s)
    (hd1 : 1 ≤ d) (hd : d ≤ P^(19/20:ℝ))
    (hH : P^s/2 ≤ H) (hheight : 2*w^(Cs+2) ≤ P^(1/50:ℝ))
    (ha : H/w ≤ a) (hlen : H/w ≤ b-a) (hb : b ≤ 2*w^(Cs+2)*P^s) :
    P ≤ a/d ∧ a/d ≤ b/d ∧ b/d ≤ P^(s+1/50) ∧
      (b/d)/w^(Cs+4) ≤ b/d-a/d ∧ Real.log (b/d) ≤ (s+1/50)*Real.log P := by
  have hw0 : 0 < w := by linarith
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hd0 : 0 < d := by linarith
  have hPs : 0 < P^s := Real.rpow_pos_of_pos hP0 _
  have hH0 : 0 < H := by linarith
  have ht0 : 0 < H/w := div_pos hH0 hw0
  have ha0 : 0 < a := ht0.trans_le ha
  have hlen0 : 0 < b-a := ht0.trans_le hlen
  have hb0 : 0 < b := by linarith
  have hwp : 0 < w^(Cs+2) := Real.rpow_pos_of_pos hw0 _
  have hW : 0 < w^(Cs+4) := Real.rpow_pos_of_pos hw0 _
  have hwle : w ≤ w^(Cs+2) := by
    calc
      _ = w^(1:ℝ) := (Real.rpow_one w).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2w : 2*w ≤ P^(1/20:ℝ) := by
    calc
      _ ≤ 2*w^(Cs+2) := mul_le_mul_of_nonneg_left hwle (by norm_num)
      _ ≤ P^(1/50:ℝ) := hheight
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num)
  have h2wd : 2*w*d ≤ P := by
    calc
      _ ≤ P^(1/20:ℝ)*P^(19/20:ℝ) := mul_le_mul h2w hd hd0.le (by positivity)
      _ = P := by rw [← Real.rpow_add hP0]; norm_num
  have hP2 : P^2 ≤ P^s := prime_multiple_P_sq_le hP1 (by linarith)
  have hPd : P*d ≤ H/w := by
    apply (le_div_iff₀ hw0).mpr
    calc
      _ = (P/2)*(2*w*d) := by ring
      _ ≤ (P/2)*P := mul_le_mul_of_nonneg_left h2wd (by positivity)
      _ = P^2/2 := by ring
      _ ≤ P^s/2 := div_le_div_of_nonneg_right hP2 (by norm_num)
      _ ≤ H := hH
  have hlo : P ≤ a/d := (le_div_iff₀ hd0).mpr (hPd.trans ha)
  have hab : a/d ≤ b/d := div_le_div_of_nonneg_right (by linarith) hd0.le
  have hhi : b/d ≤ P^(s+1/50) := by
    calc
      _ ≤ b := div_le_self hb0.le hd1
      _ ≤ 2*w^(Cs+2)*P^s := hb
      _ ≤ P^(1/50:ℝ)*P^s := mul_le_mul_of_nonneg_right hheight hPs.le
      _ = _ := by rw [← Real.rpow_add hP0]; congr 1; ring
  have hHlen : H ≤ w*(b-a) := by
    have he := (div_le_iff₀ hw0).mp hlen
    simpa only [mul_comm] using he
  have hpower : w^(Cs+4) = w^(Cs+2)*w^2 := by
    rw [← Real.rpow_natCast w 2,← Real.rpow_add hw0]
    congr 1
    ring
  have hwidth : b ≤ w^(Cs+4)*(b-a) := by
    calc
      _ ≤ 2*w^(Cs+2)*P^s := hb
      _ ≤ 2*w^(Cs+2)*(2*H) := mul_le_mul_of_nonneg_left (by linarith : P^s≤2*H) (by positivity)
      _ = 4*w^(Cs+2)*H := by ring
      _ ≤ 4*w^(Cs+2)*(w*(b-a)) := mul_le_mul_of_nonneg_left hHlen (by positivity)
      _ = (4*w)*(w^(Cs+2)*(b-a)) := by ring
      _ ≤ w^2*(w^(Cs+2)*(b-a)) := mul_le_mul_of_nonneg_right (by nlinarith : 4*w≤w^2) (by positivity)
      _ = _ := by rw [hpower]; ring
  have hrel : (b/d)/w^(Cs+4) ≤ b/d-a/d := by
    apply (div_le_iff₀ hW).mpr
    calc
      _ ≤ (w^(Cs+4)*(b-a))/d := div_le_div_of_nonneg_right hwidth hd0.le
      _ = _ := by ring
  have hlog := Real.log_le_log (hP0.trans_le (hlo.trans hab)) hhi
  rw [Real.log_rpow hP0] at hlog
  exact ⟨hlo,hab,hhi,hrel,hlog⟩

end Erdos970Dependency.SiegelWalfisz



namespace ErdosStoppedArithmetic
open Erdos970Dependency.SiegelWalfisz
attribute [local instance] Classical.propDecidable

noncomputable def admissiblePairs (T : Finset ℕ) (M : Finset ℤ) (good : ℕ → ℤ → Prop) :
    Finset (ℕ × ℤ) := (T.product M).filter (fun pm => good pm.1 pm.2)

theorem admissible_pair_card_rows (T : Finset ℕ) (M : Finset ℤ) (good : ℕ → ℤ → Prop) :
    (admissiblePairs T M good).card = ∑ p ∈ T,(M.filter (good p)).card := by
  simp only [admissiblePairs,Finset.card_filter,Finset.product_eq_sprod,Finset.sum_product]

theorem admissible_pair_card_columns (T : Finset ℕ) (M : Finset ℤ) (good : ℕ → ℤ → Prop) :
    (admissiblePairs T M good).card = ∑ m ∈ M,(T.filter (fun p => good p m)).card := by
  rw [admissible_pair_card_rows]
  simp only [Finset.card_filter]
  exact Finset.sum_comm

theorem prime_multiple_pair_sum (P x y : ℝ) (D T : Finset ℕ) (good : ℕ → ℤ → Prop)
    (hD : ∀ d ∈ D,0 < d ∧ (d : ℝ) ≤ P) :
    (admissiblePairs T (D.biUnion (fun d => primeMultiplesIn d P x y)) good).card =
      ∑ d ∈ D,∑ m ∈ primeMultiplesIn d P x y,(T.filter (fun p => good p m)).card := by
  rw [admissible_pair_card_columns]
  apply Finset.sum_biUnion
  intro d hd e he hne
  exact prime_multiple_factors_disjoint P x y d e (hD e he).1 (hD e he).2 hne

theorem prime_multiple_pair_lower (P x y A B : ℝ) (D T : Finset ℕ)
    (good : ℕ → ℤ → Prop) (W : ℕ → ℝ)
    (hD : ∀ d ∈ D,0 < d ∧ (d : ℝ) ≤ P) (hB : 0 ≤ B)
    (hW : ∀ d ∈ D,0 ≤ W d)
    (hM : ∀ d ∈ D,A/(d : ℝ) ≤ ((primeMultiplesIn d P x y).card : ℝ))
    (hTag : ∀ d ∈ D,∀ m ∈ primeMultiplesIn d P x y,
      B*W d ≤ ((T.filter (fun p => good p m)).card : ℝ)) :
    A*B*(∑ d ∈ D,W d/(d : ℝ)) ≤
      ((admissiblePairs T (D.biUnion (fun d => primeMultiplesIn d P x y)) good).card : ℝ) := by
  rw [prime_multiple_pair_sum P x y D T good hD,Nat.cast_sum]
  have hEach (d : ℕ) (hd : d ∈ D) :
      A*B*(W d/(d : ℝ)) ≤
        ((∑ m ∈ primeMultiplesIn d P x y,(T.filter (fun p => good p m)).card : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    calc
      _ = (A/(d : ℝ))*(B*W d) := by ring
      _ ≤ ((primeMultiplesIn d P x y).card : ℝ)*(B*W d) :=
        mul_le_mul_of_nonneg_right (hM d hd) (mul_nonneg hB (hW d hd))
      _ = ∑ _m ∈ primeMultiplesIn d P x y,B*W d := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun m hm => hTag d hd m hm)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum hEach

end ErdosStoppedArithmetic



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma prime_multiple_height_eventually {Cs K : ℝ} (_hCs : 0 ≤ Cs) (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop, 4 ≤ w ∧ ∀ P : ℝ,
      Real.exp (K*(Real.log w)^3) ≤ P → 3 ≤ P ∧ 2*w^(Cs+2) ≤ P^(1/50:ℝ) := by
  let a : ℝ := K/50
  let B : ℝ := Real.log 2+Cs+2
  have ha : 0 < a := by dsimp [a]; positivity
  filter_upwards [eventually_ge_atTop (4:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (B/a))),
    (exponential_log_cube_tendsto hK).eventually (eventually_ge_atTop (3:ℝ))]
    with w hw hh hlarge
  refine ⟨hw,?_⟩
  intro P hP
  have hP3 : 3 ≤ P := hlarge.trans hP
  have hP0 : 0 < P := by linarith
  have hw0 : 0 < w := by linarith
  let h := Real.log w
  have hh1 : 1 ≤ h := (le_max_left _ _).trans hh
  have hhb : B/a ≤ h := (le_max_right _ _).trans hh
  have hB : B ≤ a*h := by
    have he := (div_le_iff₀ ha).mp hhb
    simpa only [mul_comm] using he
  have hhsq : h ≤ h^2 := by nlinarith
  have hBsq : B ≤ a*h^2 := hB.trans (mul_le_mul_of_nonneg_left hhsq ha.le)
  have hBcube := mul_le_mul_of_nonneg_right hBsq (show 0 ≤ h by linarith)
  have hlog2 : Real.log 2 ≤ Real.log 2*h := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh1 (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hlin : Real.log 2+(Cs+2)*h ≤ a*h^3 := by dsimp [B] at hBcube; nlinarith
  have hlogP : K*h^3 ≤ Real.log P := by
    have he := Real.log_le_log (Real.exp_pos _) hP
    simpa only [Real.log_exp] using he
  have he : Real.log 2+(Cs+2)*h ≤ Real.log P*(1/50) := by
    dsimp [a] at hlin
    nlinarith
  refine ⟨hP3,?_⟩
  calc
    _ = Real.exp (Real.log 2+(Cs+2)*h) := by
      rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2),Real.rpow_def_of_pos hw0]
      congr 1
      congr 1
      ring
    _ ≤ Real.exp (Real.log P*(1/50)) := Real.exp_le_exp.mpr he
    _ = _ := (Real.rpow_def_of_pos hP0 _).symm

lemma prime_multiple_endpoint_loss {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ P : ℝ in atTop, 3 ≤ P ∧ ∀ s d H : ℝ,
      203/100 ≤ s → s ≤ 219/100 → 1 ≤ d → d ≤ P^(19/20:ℝ) → P^s/2 ≤ H →
      2 ≤ (eps/2)*H/(d*(s+1/50)*Real.log P) := by
  filter_upwards [eventually_ge_atTop (3:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_polynomial_le_exp (24/eps) 1 (by norm_num : (0:ℝ)<1))]
    with P hP hp
  refine ⟨hP,?_⟩
  intro s d H hs hsUpper hd1 hd hH
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hd0 : 0 < d := by linarith
  have hs0 : 0 < s+1/50 := by linarith
  have hlog : 0 < Real.log P := Real.log_pos (by linarith)
  have h24 : 24*Real.log P ≤ eps*P := by
    have he := mul_le_mul_of_nonneg_right hp.2 heps.le
    rw [one_mul,pow_one,Real.exp_log hP0] at he
    calc
      _ = ((24/eps)*Real.log P)*eps := by field_simp
      _ ≤ P*eps := he
      _ = _ := mul_comm _ _
  have hdP := prime_multiple_d_le_P hP1 hd
  have hP2 := prime_multiple_P_sq_le hP1 (show 2 ≤ s by linarith)
  have hden : d*(s+1/50)*Real.log P ≤ 3*P*Real.log P := by
    have hm := mul_le_mul hdP (show s+1/50≤3 by linarith) hs0.le hP0.le
    have hn := mul_le_mul_of_nonneg_right hm hlog.le
    nlinarith only [hn]
  have hm := mul_le_mul_of_nonneg_right h24 (show 0≤P/4 by positivity)
  have hl := mul_le_mul_of_nonneg_left (show P^2≤2*H by linarith) (show 0≤eps/4 by positivity)
  apply (le_div_iff₀ (by positivity : 0<d*(s+1/50)*Real.log P)).mpr
  nlinarith only [hden,hm,hl]

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Finset

noncomputable def retainedPrimes (d : ℕ) (a b t : ℝ) : Finset ℕ :=
  if t ≤ b-a then primeIntervalFlags false false (a/(d:ℝ)) (b/(d:ℝ)) else ∅

lemma mem_retainedPrimes (d : ℕ) (a b t : ℝ) (ell : ℕ) :
    ell ∈ retainedPrimes d a b t ↔ t ≤ b-a ∧ ell.Prime ∧ a/(d:ℝ) < ell ∧ (ell:ℝ) < b/(d:ℝ) := by
  unfold retainedPrimes
  by_cases h : t ≤ b-a
  · simp [h,mem_primeIntervalFlags]
  · simp [h]

lemma retained_positive_data {d : ℕ} (hd : 0 < d) {P x y t : ℝ}
    (hstart : t ≤ y-max x t → P ≤ (max x t)/(d:ℝ)) :
    ∀ ell ∈ retainedPrimes d (max x t) y t,
      ell.Prime ∧ P < (ell:ℝ) ∧ x < (d:ℝ)*ell ∧ (d:ℝ)*ell < y := by
  intro ell he
  obtain ⟨hret,hpr,hlo,hhi⟩ := (mem_retainedPrimes _ _ _ _ _).mp he
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have h1 := (div_lt_iff₀ hd0).mp hlo
  have h2 := (lt_div_iff₀ hd0).mp hhi
  refine ⟨hpr,(hstart hret).trans_lt hlo,?_,?_⟩
  · have hx := le_max_left x t
    nlinarith
  · nlinarith

lemma retained_negative_data {d : ℕ} (hd : 0 < d) {P x y t : ℝ}
    (hstart : t ≤ -x-max (-y) t → P ≤ (max (-y) t)/(d:ℝ)) :
    ∀ ell ∈ retainedPrimes d (max (-y) t) (-x) t,
      ell.Prime ∧ P < (ell:ℝ) ∧ x < -((d:ℝ)*ell) ∧ -((d:ℝ)*ell) < y := by
  intro ell he
  obtain ⟨hret,hpr,hlo,hhi⟩ := (mem_retainedPrimes _ _ _ _ _).mp he
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have h1 := (div_lt_iff₀ hd0).mp hlo
  have h2 := (lt_div_iff₀ hd0).mp hhi
  refine ⟨hpr,(hstart hret).trans_lt hlo,?_,?_⟩
  · nlinarith
  · have hy := le_max_left (-y) t
    nlinarith

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter _root_.Finset
open scoped Topology


private lemma retained_count_lower {eps delta H t len den count : ℝ}
    (hdelta : delta = eps / 4) (hdelta1 : delta < 1)
    (hH : 0 ≤ H) (hden : 0 < den)
    (htrim : 4 * t ≤ delta * H) (hretained : H - 4 * t ≤ len)
    (hsum : (1 - delta) * len / den - 2 ≤ count)
    (hLoss : 2 ≤ (eps / 2) * H / den) :
    (1 - eps) * H / den ≤ count := by
  have hkeep : H * (1 - delta) ≤ len := by nlinarith
  have hfactor : 1 - eps / 2 ≤ (1 - delta) ^ 2 := by
    rw [hdelta]
    nlinarith [sq_nonneg eps]
  have hmass : (1 - eps / 2) * H ≤ (1 - delta) * len := by
    calc
      _ ≤ (1 - delta) ^ 2 * H := mul_le_mul_of_nonneg_right hfactor hH
      _ = (1 - delta) * (H * (1 - delta)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hkeep (by linarith)
  calc
    _ = (1 - eps / 2) * H / den - (eps / 2) * H / den := by ring
    _ ≤ (1 - eps / 2) * H / den - 2 := sub_le_sub_left hLoss _
    _ ≤ (1 - delta) * len / den - 2 :=
      sub_le_sub_right (div_le_div_of_nonneg_right hmass hden.le) 2
    _ ≤ _ := hsum

theorem moving_signed_prime_multiple_lower (Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∃ K : ℝ, 0 < K ∧ ∀ rho : ℝ, 1 < rho → ∀ eps : ℝ, 0 < eps → eps < 1 →
      ∃ w₀ : ℝ, 4 ≤ w₀ ∧ ∀ w : ℝ, w₀ ≤ w → ∀ P s x y : ℝ, ∀ d : ℕ,
        Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp (rho*K*(Real.log w)^3) →
        203/100 ≤ s → s ≤ 219/100 → P^s/2 ≤ y-x →
        max |x| |y| ≤ 2*w^(Cs+2)*P^s → 0 < d → (d:ℝ) ≤ P^(19/20:ℝ) →
        (1-eps)*(y-x)/((d:ℝ)*(s+1/50)*Real.log P) ≤ ((primeMultiplesIn d P x y).card:ℝ) := by
  obtain ⟨K,hK,hFamily⟩ := moving_prime_interval_lower_flags (Cs+4) (by linarith)
  refine ⟨K,hK,?_⟩
  intro rho hrho eps heps heps1
  let delta : ℝ := eps/4
  let L : ℝ := 3*rho*K
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdelta1 : delta < 1 := by dsimp [delta]; linarith
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨wF,hwF,hF⟩ := hFamily L hL delta hdelta
  obtain ⟨P0,hP0⟩ := eventually_atTop.mp (prime_multiple_endpoint_loss heps)
  have hev : ∀ᶠ w : ℝ in atTop, 4 ≤ w ∧ ∀ P s x y : ℝ, ∀ d : ℕ,
      Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp (rho*K*(Real.log w)^3) →
      203/100 ≤ s → s ≤ 219/100 → P^s/2 ≤ y-x →
      max |x| |y| ≤ 2*w^(Cs+2)*P^s → 0 < d → (d:ℝ) ≤ P^(19/20:ℝ) →
      (1-eps)*(y-x)/((d:ℝ)*(s+1/50)*Real.log P) ≤ ((primeMultiplesIn d P x y).card:ℝ) := by
    filter_upwards [prime_multiple_height_eventually hCs hK,eventually_ge_atTop wF,
      eventually_ge_atTop (16/eps),
      (exponential_log_cube_tendsto hK).eventually (eventually_ge_atTop P0)]
      with w hwHeight hwFamily hwBudget hwP
    refine ⟨hwHeight.1,?_⟩
    intro P s x y d hPlower hPupper hs hsUpper hH hMax hd hdSmall
    obtain ⟨hP3,hheight⟩ := hwHeight.2 P hPlower
    have hPpos : 0 < P := by linarith
    have hP1 : 1 ≤ P := by linarith
    have hw0 : 0 < w := by linarith [hwHeight.1]
    have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
    have hd0 : (0:ℝ) < d := by exact_mod_cast hd
    have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
    let H : ℝ := y-x
    let t : ℝ := H/w
    let Den : ℝ := (s+1/50)*Real.log P
    let A := retainedPrimes d (max x t) y t
    let B := retainedPrimes d (max (-y) t) (-x) t
    have hPs : 0 < P^s := Real.rpow_pos_of_pos hPpos _
    have hH0 : 0 < H := by dsimp [H]; linarith
    have ht0 : 0 < t := div_pos hH0 hw0
    have hDen : 0 < Den := by dsimp [Den]; positivity
    have hden : 0 < (d:ℝ)*Den := mul_pos hd0 hDen
    have hy : y ≤ 2*w^(Cs+2)*P^s := (le_abs_self y).trans ((le_max_right _ _).trans hMax)
    have hnx : -x ≤ 2*w^(Cs+2)*P^s := (neg_le_abs x).trans ((le_max_left _ _).trans hMax)
    have hlogUpper : Real.log P ≤ rho*K*(Real.log w)^3 := by
      have he := Real.log_le_log hPpos hPupper
      simpa only [Real.log_exp] using he
    have htop : P^(3:ℝ) ≤ Real.exp (L*(Real.log w)^3) := by
      rw [Real.rpow_def_of_pos hPpos]
      apply Real.exp_le_exp.mpr
      dsimp [L]
      nlinarith
    have hEach (a b : ℝ) (ha : t ≤ a) (hb : b ≤ 2*w^(Cs+2)*P^s) :
        (1-delta)*retainedLength a b t/((d:ℝ)*Den)-1 ≤ ((retainedPrimes d a b t).card:ℝ) := by
      by_cases hret : t ≤ b-a
      · obtain ⟨hlo,hab,hhi,hrel,hlog⟩ := prime_multiple_piece_bounds hCs hwHeight.1 hP3 hs
          hd1 hdSmall hH hheight ha hret hb
        have hV : b/(d:ℝ) ≤ Real.exp (L*(Real.log w)^3) := hhi.trans
          ((Real.rpow_le_rpow_of_exponent_le hP1 (show s+1/50 ≤ (3:ℝ) by linarith)).trans htop)
        have hprime := hF w hwFamily (a/(d:ℝ)) (b/(d:ℝ)) hab (hPlower.trans hlo) hV hrel false false
        have hlogv : 0 < Real.log (b/(d:ℝ)) := Real.log_pos (by linarith)
        have hlen : 0 ≤ b-a := by linarith
        have hrat : (1-delta)*(b-a)/((d:ℝ)*Den) ≤
            (1-delta)*(b/(d:ℝ)-a/(d:ℝ))/Real.log (b/(d:ℝ)) := by
          calc
            _ = ((1-delta)*((b-a)/(d:ℝ)))/Den := by ring_nf
            _ ≤ ((1-delta)*((b-a)/(d:ℝ)))/Real.log (b/(d:ℝ)) :=
              div_le_div_of_nonneg_left (by positivity) hlogv hlog
            _ = _ := by ring
        simpa only [retainedPrimes,retainedLength,hret,ite_true] using
          (sub_le_sub_right hrat 1).trans hprime
      · norm_num [retainedPrimes,retainedLength,hret]
    have hpCount := hEach (max x t) y (le_max_right _ _) hy
    have hnCount := hEach (max (-y) t) (-x) (le_max_right _ _) hnx
    have hA := retained_positive_data (P:=P) (x:=x) (y:=y) (t:=t) hd (fun hret =>
      (prime_multiple_piece_bounds hCs hwHeight.1 hP3 hs hd1 hdSmall hH hheight (le_max_right _ _) hret hy).1)
    have hB := retained_negative_data (P:=P) (x:=x) (y:=y) (t:=t) hd (fun hret =>
      (prime_multiple_piece_bounds hCs hwHeight.1 hP3 hs hd1 hdSmall hH hheight (le_max_right _ _) hret hnx).1)
    have hcard : (A.card:ℝ)+(B.card:ℝ) ≤ ((primeMultiplesIn d P x y).card:ℝ) := by
      exact_mod_cast signed_prime_sets_card_le hd A B hA hB
    let len : ℝ := retainedLength (max x t) y t+retainedLength (max (-y) t) (-x) t
    have hsum : (1-delta)*len/((d:ℝ)*Den)-2 ≤ ((primeMultiplesIn d P x y).card:ℝ) := by
      calc
        _ = ((1-delta)*retainedLength (max x t) y t/((d:ℝ)*Den)-1)+
            ((1-delta)*retainedLength (max (-y) t) (-x) t/((d:ℝ)*Den)-1) := by dsimp [len]; ring
        _ ≤ (A.card:ℝ)+(B.card:ℝ) := add_le_add hpCount hnCount
        _ ≤ _ := hcard
    have htrim : 4*t ≤ delta*H := by
      have hweps := (div_le_iff₀ heps).mp hwBudget
      have hfrac : 4/w ≤ delta := (div_le_iff₀ hw0).mpr (by dsimp [delta]; nlinarith)
      calc
        _ = (4/w)*H := by dsimp [t]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hfrac hH0.le
    have hretained := signed_retained_length (show x ≤ y by dsimp [H] at hH0; linarith) ht0.le
    change H-4*t ≤ len at hretained
    have hLoss := (hP0 P (hwP.trans hPlower)).2 s (d:ℝ) H hs hsUpper hd1 hdSmall hH
    have hLoss' : 2 ≤ (eps/2)*H/((d:ℝ)*Den) := by simpa only [Den,mul_assoc] using hLoss
    simpa only [H, Den, mul_assoc] using
      retained_count_lower (show delta = eps / 4 from rfl) hdelta1 hH0.le hden
        htrim hretained hsum hLoss'
  obtain ⟨b,hb⟩ := eventually_atTop.mp hev
  refine ⟨max 4 b,le_max_left _ _,?_⟩
  intro w hw P s x y d hPlower hPupper hs hsUpper hH hMax hd hdSmall
  exact (hb w ((le_max_right _ _).trans hw)).2 P s x y d hPlower hPupper hs hsUpper hH hMax hd hdSmall

end Erdos970Dependency.SiegelWalfisz



open _root_.Filter
namespace ErdosStoppedArithmetic
open Erdos970Dependency.SiegelWalfisz Erdos970.EulerWeightedLower
attribute [local instance] Classical.propDecidable

theorem supported_small_factor_bounds (P : ℝ) (hP : 1 < P) (E : Finset ℕ) (d : ℕ)
    (hd : d ∈ supportedIntegers E ⌊P^(95/100 : ℝ)⌋₊) :
    0 < d ∧ (d : ℝ) ≤ P^(19/20 : ℝ) ∧ (d : ℝ) ≤ P := by
  have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
  have hh : (d : ℝ) ≤ P^(95/100 : ℝ) := (Nat.le_floor_iff (Real.rpow_nonneg (by linarith) _)).mp hi.2
  have hexp : (95/100 : ℝ)=(19/20 : ℝ) := by norm_num
  refine ⟨hi.1,by simpa only [hexp] using hh,?_⟩
  exact hh.trans (Real.rpow_le_self_of_one_le hP.le (by norm_num))

theorem paper_weight_nonneg (E : Finset ℕ) (hE : ∀ p ∈ E,p.Prime) (d : ℕ) :
    0 ≤ paperWeight E d := by
  unfold paperWeight
  apply Finset.prod_nonneg
  intro p hp
  have hpr := hE p (Finset.mem_filter.mp hp).1
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
  have hden : 0 < (p : ℝ)-1 := by linarith
  have hrec : 1/((p : ℝ)-1) ≤ 1 := (div_le_one hden).mpr (by linarith)
  exact sub_nonneg.mpr hrec

theorem moving_weighted_pair_lower (Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∃ K : ℝ,0 < K ∧ ∀ rho : ℝ,1 < rho → ∀ eps : ℝ,0 < eps → eps < 1 →
      ∃ w0 : ℝ,4 ≤ w0 ∧ ∀ w : ℝ,w0 ≤ w → ∀ P s x y : ℝ,
      Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp (rho*K*(Real.log w)^3) →
      203/100 ≤ s → s ≤ 219/100 → P^s/2 ≤ y-x → max |x| |y| ≤ 2*w^(Cs+2)*P^s →
      ∀ (E T : Finset ℕ) (good : ℕ → ℤ → Prop) (B : ℝ),E ⊆ primesThrough P → 0 ≤ B →
      (∀ d ∈ supportedIntegers E ⌊P^(95/100 : ℝ)⌋₊,∀ m ∈ primeMultiplesIn d P x y,
        B*paperWeight E d ≤ ((T.filter (fun p => good p m)).card : ℝ)) →
      ((1-eps)*(y-x)/((s+1/50)*Real.log P))*B*
        (Real.exp (-Real.eulerMascheroniConstant)*(94/100-eps)) ≤
        ((admissiblePairs T ((supportedIntegers E ⌊P^(95/100 : ℝ)⌋₊).biUnion
          (fun d => primeMultiplesIn d P x y)) good).card : ℝ) := by
  obtain ⟨K,hK,hPrime⟩ := moving_signed_prime_multiple_lower Cs hCs
  refine ⟨K,hK,?_⟩
  intro rho hrho eps heps heps1
  obtain ⟨wS,hwS,hS⟩ := hPrime rho hrho eps heps heps1
  obtain ⟨P0,hP0⟩ := eventually_atTop.mp (weightedSmallSum_eventually_uniform heps)
  obtain ⟨wG,hwG⟩ := eventually_atTop.mp
    ((exponential_log_cube_tendsto hK).eventually_ge_atTop (max 2 P0))
  refine ⟨max wS wG,hwS.trans (le_max_left _ _),?_⟩
  intro w hw P s x y hPlower hPupper hs hsupper hLength hHeight E T good B hE hB hTag
  have hLarge : max 2 P0 ≤ P := (hwG w ((le_max_right _ _).trans hw)).trans hPlower
  have hP2 : 2 ≤ P := (le_max_left _ _).trans hLarge
  have hP : 1 < P := by linarith
  have hPpos : 0 < P := by linarith
  have hlog : 0 < Real.log P := Real.log_pos hP
  have hspos : 0 < s+1/50 := by linarith
  have hLengthPos : 0 < y-x := (by positivity : (0 : ℝ) < P^s/2).trans_le hLength
  let A := (1-eps)*(y-x)/((s+1/50)*Real.log P)
  have hA : 0 ≤ A := by dsimp [A];positivity
  let D := supportedIntegers E ⌊P^(95/100 : ℝ)⌋₊
  have hD (d : ℕ) (hd : d ∈ D) := supported_small_factor_bounds P hP E d hd
  have hpr (p : ℕ) (hp : p ∈ E) : p.Prime := primesThrough_prime (hE hp)
  have hM (d : ℕ) (hd : d ∈ D) : A/(d : ℝ) ≤ ((primeMultiplesIn d P x y).card : ℝ) := by
    have hh := hS w ((le_max_left _ _).trans hw) P s x y d hPlower hPupper hs hsupper
      hLength hHeight (hD d hd).1 (hD d hd).2.1
    have he : A/(d : ℝ)=(1-eps)*(y-x)/((d : ℝ)*(s+1/50)*Real.log P) := by
      dsimp [A]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    exact he.trans_le hh
  have hPairs := prime_multiple_pair_lower P x y A B D T good (paperWeight E)
    (fun d hd => ⟨(hD d hd).1,(hD d hd).2.2⟩) hB (fun d _ => paper_weight_nonneg E hpr d) hM hTag
  have hWeighted := hP0 P ((le_max_right _ _).trans hLarge) E hE
  change A*B*(Real.exp (-Real.eulerMascheroniConstant)*(94/100-eps)) ≤ _
  have hh := mul_le_mul_of_nonneg_left hWeighted (mul_nonneg hA hB)
  exact hh.trans hPairs

end ErdosStoppedArithmetic


end Erdos970

end OAI
