import OAI.NumberTheory.GaussianMoat.SieveCertificate

namespace OAI

namespace GaussianMoat

section
open scoped BigOperators Classical

noncomputable def bandConstant (D : ℝ) : ℝ :=
  10000+100*|Real.log D|+100*|Real.log (max D ((latticeBall (4*D)).card:ℝ))|

lemma bandConstant_pos (D : ℝ) : 0<bandConstant D := by
  unfold bandConstant
  positivity

theorem entropyBand_from_margin (s : SplitSieve) (pre post : List ℕ) (N l : ℕ)
    {D g U δ : ℝ} (hD : 1≤D) (hg : 0<g) (hg1 : g≤1/200) (hU : 0<U)
    (hL : 1≤ s.meanLog)
    (hmargin : bandConstant D*s.meanLog≤g^5*bandScale g U l)
    (hcap : ⌊U/s.meanLog⌋₊≤ s.primes.card)
    (hpost : ∀ n∈post, (n:ℝ)≤Real.exp (g*bandScale g U l))
    (hN : (N:ℝ)≤Real.exp (g*bandScale g U l))
    (hlen : (post.length+2:ℝ)≤Real.exp (g*bandScale g U l))
    (hδ : (1/2:ℝ)^l+90*g≤δ) :
    Nonempty (EntropyBand s D
      (pre++List.ofFn (fun i : Fin l => bandLength g U i.val)++post)
      N (bandSize s g U l) δ) := by
  let V := bandScale g U l
  have hV : 0<V := bandScale_pos hg hU l
  have hg01 : g≤1 := by linarith only [hg1]
  have hg5 : g^5≤g := by
    have hh : g^4≤1 := pow_le_one₀ hg.le hg01
    calc g^5=g^4*g := by ring
         _ ≤ 1*g := mul_le_mul_of_nonneg_right hh hg.le
         _ = g := one_mul _
  have hg52 : g^5≤g^2 := by
    have hh : g^3≤1 := pow_le_one₀ hg.le hg01
    calc g^5=g^3*g^2 := by ring
         _ ≤ 1*g^2 := mul_le_mul_of_nonneg_right hh (sq_nonneg _)
         _ = g^2 := one_mul _
  have hC : bandConstant D≤g^5*V := by
    have hh := mul_le_mul_of_nonneg_left hL (bandConstant_pos D).le
    simp only [mul_one] at hh
    exact hh.trans hmargin
  have hCg := hC.trans (mul_le_mul_of_nonneg_right hg5 hV.le)
  have hCg2 := hC.trans (mul_le_mul_of_nonneg_right hg52 hV.le)
  have hCV := hCg.trans (by nlinarith only [hg01,hV] : g*V≤V)
  have hl16 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<16)
  have hl18 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<18)
  have hl36 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<36)
  have hld := le_abs_self (Real.log D)
  have hla := le_abs_self (Real.log (max D ((latticeBall (4*D)).card:ℝ)))
  have ha := abs_nonneg (Real.log D)
  have hb := abs_nonneg (Real.log (max D ((latticeBall (4*D)).card:ℝ)))
  have hC640 : 640≤bandConstant D := by unfold bandConstant; linarith only [ha,hb]
  apply entropyBand_from_suffix s pre post N l hD hg hg1 hU hL
  · dsimp only [bandConstant] at hCg
    linarith only [hCg,hl18,ha,hb]
  · exact (mul_le_mul_of_nonneg_right hC640 (by linarith only [hL])).trans hmargin
  · dsimp only [bandConstant] at hCg2
    linarith only [hCg2,hl16,hla,ha,hb]
  · dsimp only [bandConstant] at hCg
    nlinarith only [hCg,hl36,hld,ha,hb]
  · dsimp only [bandConstant] at hCV
    linarith only [hCV,hl16,hld,ha,hb]
  · exact hcap
  · exact hpost
  · exact hN
  · exact hlen
  · dsimp only [bandConstant] at hCg
    linarith only [hCg,hl36,hld,ha,hb]
  · exact hδ

open scoped BigOperators Classical
open Filter

theorem eventually_poly_le_exp (C : ℝ) {a : ℝ} (ha : 0<a) (d : ℕ) :
    ∀ᶠ y : ℝ in atTop, C*y^d≤a*Real.exp y := by
  by_cases hC : 0<C
  · have hh := (Real.isLittleO_pow_exp_atTop (n := d)).bound (div_pos ha hC)
    filter_upwards [hh,eventually_ge_atTop (0:ℝ)] with y hy hy0
    rw [Real.norm_of_nonneg (pow_nonneg hy0 _),Real.norm_of_nonneg (Real.exp_nonneg _)] at hy
    have hm := mul_le_mul_of_nonneg_left hy hC.le
    rwa [←mul_assoc,mul_div_cancel₀ _ hC.ne'] at hm
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
    exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hC) (pow_nonneg hy _)).trans
      (mul_nonneg ha.le (Real.exp_nonneg _))

theorem eventually_linear_le_square (A B : ℝ) :
    ∀ᶠ y : ℝ in atTop, A*y+B≤y^2 := by
  filter_upwards [eventually_ge_atTop (max (|A|+|B|+1) 1)] with y hy
  have h1 : 1≤y := (le_max_right _ _).trans hy
  have h2 : |A|+|B|+1≤y := (le_max_left _ _).trans hy
  have h3 : A≤|A| := le_abs_self _
  have h4 : B≤|B| := le_abs_self _
  nlinarith only [h1,h2,h3,h4,abs_nonneg A,abs_nonneg B]

noncomputable def accurateGrid (m : ℕ) : ℝ := Real.exp (-((m:ℝ)^2))
def accurateIterations (m : ℕ) : ℕ := 4*m^2

lemma accurateGrid_pos (m : ℕ) : 0<accurateGrid m := Real.exp_pos _

lemma accurateGrid_le_one (m : ℕ) : accurateGrid m≤1 := by
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))

lemma accurateIterations_error (m : ℕ) :
    (1/2:ℝ)^(accurateIterations m)+90*accurateGrid m≤91*accurateGrid m := by
  have hl : (1/2:ℝ)≤Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  have he : (1/2:ℝ)^(accurateIterations m)≤accurateGrid m := by
    rw [show (1/2:ℝ)=Real.exp (-Real.log 2) by rw [Real.exp_neg,Real.exp_log (by norm_num)]; norm_num]
    rw [←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    simp only [accurateIterations,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    nlinarith only [sq_nonneg (m:ℝ),hl]
  linarith only [he]

lemma accurateGrid_scale (m : ℕ) (a : ℝ) :
    bandScale (accurateGrid m) (Real.exp (a*Real.exp m)) (accurateIterations m)=
      Real.exp (a*Real.exp m-8*(m:ℝ)^4) := by
  unfold bandScale accurateGrid accurateIterations
  rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]
  congr 1
  push_cast
  ring

theorem eventually_accurate_scale {a : ℝ} (ha : 0<a) (k : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      Real.exp ((a/2)*Real.exp m)≤(accurateGrid m)^k *
        bandScale (accurateGrid m) (Real.exp (a*Real.exp m)) (accurateIterations m) := by
  have h4 := eventually_poly_le_exp 8 (a := a/4) (by positivity) 4
  have h2 := eventually_poly_le_exp (k:ℝ) (a := a/4) (by positivity) 2
  have hh := (h4.and h2).filter_mono (show Filter.map ((↑) : ℕ → ℝ) atTop≤atTop from tendsto_natCast_atTop_atTop)
  change ∀ᶠ m : ℕ in atTop, _ at hh
  filter_upwards [hh] with m hm
  rw [accurateGrid_scale]
  unfold accurateGrid
  rw [←Real.exp_nat_mul,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hm.1,hm.2]

theorem eventually_accurate_error (C : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ m : ℕ in atTop, 91*accurateGrid m*(C*Real.exp m)≤ε := by
  by_cases hC : 0<C
  · have hh := eventually_linear_le_square 1 (Real.log (91*C/ε))
    have hh' := hh.filter_mono (show Filter.map ((↑) : ℕ → ℝ) atTop≤atTop from tendsto_natCast_atTop_atTop)
    filter_upwards [hh'] with m hm
    change 1*(m:ℝ)+Real.log (91*C/ε)≤(m:ℝ)^2 at hm
    have he : Real.exp ((m:ℝ)-(m:ℝ)^2)≤ε/(91*C) := by
      rw [←Real.exp_log (show 0<ε/(91*C) by positivity)]
      apply Real.exp_le_exp.mpr
      rw [Real.log_div (by positivity) (by positivity)]
      rw [Real.log_div (by positivity) hε.ne'] at hm
      linarith only [hm]
    have hmul := (le_div_iff₀ (show 0<91*C by positivity)).mp he
    unfold accurateGrid
    rw [show 91*Real.exp (-((m:ℝ)^2))*(C*Real.exp m)=
      Real.exp ((m:ℝ)-(m:ℝ)^2)*(91*C) by rw [Real.exp_sub,Real.exp_neg]; ring]
    exact hmul
  · filter_upwards [] with m
    have : C*Real.exp (m:ℝ)≤0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hC) (Real.exp_nonneg _)
    exact (mul_nonpos_of_nonneg_of_nonpos (by exact mul_nonneg (by norm_num) (accurateGrid_pos m).le : 0≤91*accurateGrid m) this).trans hε.le

end

section
open scoped BigOperators Classical
open Filter

lemma eventually_const_le_exp_mul {a : ℝ} (ha : 0<a) (C : ℝ) :
    ∀ᶠ m : ℕ in atTop, C≤a*Real.exp m := by
  have hh : Tendsto (fun m : ℕ => Real.exp (m:ℝ)*a) atTop atTop :=
    (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop).atTop_mul_const ha
  simpa only [mul_comm] using hh.eventually (eventually_ge_atTop C)

lemma eventually_mul_le_double_exp {a : ℝ} (ha : 0<a) (C : ℝ) :
    ∀ᶠ m : ℕ in atTop, C*Real.exp m≤Real.exp (a*Real.exp m) := by
  have hh := eventually_poly_le_exp (C/a) (a := 1) (by norm_num) 1
  have ht : Tendsto (fun m : ℕ => a*Real.exp m) atTop atTop := by
    simpa only [Function.comp_apply] using Filter.Tendsto.const_mul_atTop ha
      (Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [ht.eventually hh] with m hm
  simpa only [pow_one,one_mul,←mul_assoc,div_mul_cancel₀ _ ha.ne'] using hm

lemma eventually_accurate_small {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ m : ℕ in atTop, accurateGrid m≤ε := by
  have hh := eventually_linear_le_square 0 (-Real.log ε)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hh] with m hm
  change 0*(m:ℝ)-Real.log ε≤(m:ℝ)^2 at hm
  unfold accurateGrid
  rw [←Real.exp_log hε]
  apply Real.exp_le_exp.mpr
  linarith only [hm]

lemma dense_sieve_cap (s : SplitSieve) (hne : s.primes.Nonempty) {T δ U : ℝ}
    (hT : 2≤T)
    (hp : ∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T)
    (hdense : δ*T/Real.log (2*T)≤ s.primes.card)
    (hsize : 2*U≤δ*T) : ⌊U/s.meanLog⌋₊≤ s.primes.card := by
  have hT0 : 0<T := by linarith only [hT]
  have hlogT : 0<Real.log T := Real.log_pos (by linarith only [hT])
  have hm := s.meanLog_bounds hne hT0 hp
  have hmean : 0<s.meanLog := hlogT.trans_le hm.1
  have hl2 : Real.log 2≤Real.log T := Real.log_le_log (by norm_num) hT
  have hhlog : Real.log (2*T)≤2*s.meanLog := by
    rw [Real.log_mul (by norm_num) hT0.ne']
    linarith only [hl2,hm.1]
  have hlo : 0<Real.log (2*T) := Real.log_pos (by linarith only [hT])
  have hd : δ*T≤(s.primes.card:ℝ)*Real.log (2*T) := (div_le_iff₀ hlo).mp hdense
  have hk : δ*T≤(s.primes.card:ℝ)*(2*s.meanLog) := hd.trans
    (mul_le_mul_of_nonneg_left hhlog (Nat.cast_nonneg _))
  apply Nat.floor_le_of_le
  apply (div_le_iff₀ hmean).mpr
  nlinarith only [hsize,hk]

theorem eventually_accurate_band {D A B a b δ : ℝ}
    (hD : 1≤D) (hA : 0<A) (ha : 0<a) (haA : a<A)
    (hba : b≤a/2) (hδ : 0<δ) :
    ∀ᶠ m : ℕ in atTop, ∀ (s : SplitSieve) (T : ℝ) (pre post : List ℕ) (N : ℕ),
      s.primes.Nonempty →
      (∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T) →
      δ*T/Real.log (2*T)≤ s.primes.card →
      Real.exp (A*Real.exp m)≤T → Real.log T≤B*Real.exp m →
      (∀ n∈post, (n:ℝ)≤Real.exp (Real.exp (b*Real.exp m))) →
      (N:ℝ)≤Real.exp (Real.exp (b*Real.exp m)) →
      (post.length+2:ℝ)≤Real.exp (Real.exp (b*Real.exp m)) →
      Nonempty (EntropyBand s D
        (pre++List.ofFn (fun i : Fin (accurateIterations m) =>
          bandLength (accurateGrid m) (Real.exp (a*Real.exp m)) i.val)++post)
        N (bandSize s (accurateGrid m) (Real.exp (a*Real.exp m)) (accurateIterations m))
        (91*accurateGrid m)) := by
  have hlarge := eventually_mul_le_double_exp (a := a/2) (by positivity)
    (bandConstant D*(B+1))
  have hgap := eventually_const_le_exp_mul (a := A-a) (by linarith only [haA]) (Real.log (2/δ))
  have htwo := eventually_const_le_exp_mul hA 2
  filter_upwards [eventually_accurate_scale ha 5,eventually_accurate_scale ha 1,
    eventually_accurate_small (show (0:ℝ)<1/200 by norm_num),hlarge,hgap,htwo]
    with m hm5 hm1 hsmall hlarge hgap htwo
  intro s T pre post N hne hp hdense hT hThi hpost hN hlen
  have he1 : 1≤Real.exp (m:ℝ) := Real.one_le_exp_iff.mpr (Nat.cast_nonneg _)
  have hT0 : 0<T := (Real.exp_pos _).trans_le hT
  have hT2 : 2≤T := by
    have hh := Real.add_one_le_exp (A*Real.exp m)
    linarith only [hh,htwo,hT]
  have hm := s.meanLog_bounds hne hT0 hp
  have hmean : 1≤ s.meanLog := by
    have hh := Real.log_le_log (Real.exp_pos _) hT
    rw [Real.log_exp] at hh
    linarith only [hh,hm.1,htwo]
  have hl2 : Real.log 2≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith only [hh]
  have hmean' : s.meanLog≤(B+1)*Real.exp m := by
    rw [Real.log_mul (by norm_num) hT0.ne'] at hm
    nlinarith only [hm.2,hThi,hl2,he1]
  have hmargin := (mul_le_mul_of_nonneg_left hmean' (bandConstant_pos D).le).trans
    (by simpa only [mul_assoc] using hlarge.trans hm5)
  have hsize : 2*Real.exp (a*Real.exp m)≤δ*T := by
    have he : Real.exp (a*Real.exp m+Real.log (2/δ))≤Real.exp (A*Real.exp m) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hgap]
    rw [Real.exp_add,Real.exp_log (div_pos (by norm_num) hδ)] at he
    have hh := mul_le_mul_of_nonneg_left (he.trans hT) hδ.le
    have heq : δ*(Real.exp (a*Real.exp m)*(2/δ))=2*Real.exp (a*Real.exp m) := by field_simp
    rwa [heq] at hh
  have hcap := dense_sieve_cap s hne hT2 hp hdense hsize
  have htail : Real.exp (b*Real.exp m)≤accurateGrid m*
      bandScale (accurateGrid m) (Real.exp (a*Real.exp m)) (accurateIterations m) := by
    simpa only [pow_one] using ((Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hba (Real.exp_nonneg _))).trans hm1)
  exact entropyBand_from_margin s pre post N (accurateIterations m) hD (accurateGrid_pos m)
    hsmall (Real.exp_pos _) hmean hmargin hcap
    (fun n hn => (hpost n hn).trans (Real.exp_le_exp.mpr htail))
    (hN.trans (Real.exp_le_exp.mpr htail)) (hlen.trans (Real.exp_le_exp.mpr htail))
    (accurateIterations_error m)

end

open scoped BigOperators Classical

lemma EntropyBand.size_cap {s : SplitSieve} {D δ : ℝ} {ns : List ℕ} {N b : ℕ}
    (q : EntropyBand s D ns N b δ) (hmean : 0< s.meanLog) : b≤ s.primes.card := by
  rw [q.size]
  apply le_trans _ q.cap
  apply Nat.floor_mono
  apply div_le_div_of_nonneg_right _ hmean.le
  have hh := bandScale_antitone q.positive.le (by linarith only [q.small]) q.scale.le (Nat.zero_le q.l)
  simpa only [bandScale,pow_zero,one_mul] using hh

lemma EntropyBand.size_lower {s : SplitSieve} {D δ : ℝ} {ns : List ℕ} {N b : ℕ}
    (q : EntropyBand s D ns N b δ) (hmean : 0< s.meanLog) :
    bandScale q.g q.U q.l/2≤(b:ℝ)*s.meanLog := by
  have hV := bandScale_pos q.positive q.scale q.l
  have hg5 : q.g^5≤1 := pow_le_one₀ q.positive.le (by linarith only [q.small])
  have hh := mul_le_mul_of_nonneg_right hg5 hV.le
  have hlarge := q.large
  have hVL : 2*s.meanLog≤bandScale q.g q.U q.l := by nlinarith only [hh,hlarge,hmean]
  have hf := Nat.lt_floor_add_one (bandScale q.g q.U q.l/s.meanLog)
  have hm := mul_lt_mul_of_pos_right hf hmean
  rw [div_mul_cancel₀ _ hmean.ne',add_mul,one_mul] at hm
  have ht : bandScale q.g q.U q.l/2≤(⌊bandScale q.g q.U q.l/s.meanLog⌋₊:ℝ)*s.meanLog := by
    linarith only [hm,hVL]
  simpa only [q.size,bandSize] using ht

lemma EntropyBand.size_pos {s : SplitSieve} {D δ : ℝ} {ns : List ℕ} {N b : ℕ}
    (q : EntropyBand s D ns N b δ) (hmean : 0< s.meanLog) : 0<b := by
  have hh := q.size_lower hmean
  have hV := bandScale_pos q.positive q.scale q.l
  by_contra h
  have hb : b=0 := by omega
  have he : (b:ℝ)=0 := by exact_mod_cast hb
  rw [he,zero_mul] at hh
  linarith only [hh,hV]

lemma bandSize_lower_of_scale {s : SplitSieve} {g U C T : ℝ} {l : ℕ}
    (hmean : 0< s.meanLog) (hlog : 0<Real.log T)
    (hm : s.meanLog≤2*Real.log T)
    (hV : 2*s.meanLog≤bandScale g U l)
    (hscale : C*T≤bandScale g U l) :
    C*T/(4*Real.log T)≤(bandSize s g U l:ℝ) := by
  have hf := Nat.lt_floor_add_one (bandScale g U l/s.meanLog)
  have hh := mul_lt_mul_of_pos_right hf hmean
  rw [div_mul_cancel₀ _ hmean.ne',add_mul,one_mul] at hh
  have hlo : bandScale g U l/2≤(bandSize s g U l:ℝ)*s.meanLog := by
    change _≤(⌊bandScale g U l/s.meanLog⌋₊:ℝ)*_
    linarith only [hh,hV]
  have hu := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (bandSize s g U l))
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hlo,hu,hscale]

end GaussianMoat

end OAI
