import OAI.NumberTheory.GaussianMoat.BatchParameters

namespace OAI

namespace GaussianMoat
open scoped BigOperators Classical
open Filter

lemma window_power_step {i w : ℕ} (hi : i<w) :
    (100:ℝ)^i≤(100:ℝ)^w/100 := by
  have hh : (100:ℝ)^(i+1)≤(100:ℝ)^w := pow_le_pow_right₀ (by norm_num) hi
  rw [pow_succ] at hh
  linarith only [hh]

lemma window_power_nonneg (w : ℕ) : (0:ℝ)≤100^w := by positivity
lemma window_power_one (w : ℕ) : (1:ℝ)≤100^w := one_le_pow₀ (by norm_num)

lemma smaller_window_operations {a : ℝ} (ha : 0≤a) (ha1 : a≤1)
    (m w : ℕ) (J : ℕ → Finset ℕ)
    (hJ : ∀ i<w, ∀ j∈J i, (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m)) :
    ∀ n∈windowBlocks a m J w,
      (n:ℝ)≤Real.exp (Real.exp (((100:ℝ)^w/50)*Real.exp m)) := by
  intro n hn
  obtain ⟨i,hi,hni⟩ := windowBlocks_mem a m J hn
  have hh := mul_le_mul_of_nonneg_right (window_power_step hi) (Real.exp_nonneg (m:ℝ))
  have hi0 : 0≤(100:ℝ)^i*Real.exp m := by positivity
  rcases hni with hni|hni
  · obtain ⟨j,hj,hnj⟩ := List.mem_flatMap.mp hni
    have hj' : j∈J i := (Finset.mem_sort (·≥·)).mp hj
    have hp : (2:ℝ)^j≤Real.exp (((100:ℝ)^w/50)*Real.exp m) := by
      rw [←Real.exp_log (by positivity : (0:ℝ)<2^j),Real.log_pow]
      apply Real.exp_le_exp.mpr
      nlinarith only [hJ i hi j hj',hh,hi0]
    apply topBlock_bound ha j _ n hnj
    have hc : topParameter*a≤1 := by
      have hg : topParameter≤1 := by norm_num [topParameter]
      exact (mul_le_mul_of_nonneg_left ha1 topParameter_pos.le).trans (by simpa only [mul_one] using hg)
    exact (mul_le_of_le_one_left (by positivity : (0:ℝ)≤2^j) hc).trans hp
  · apply accurateBlock_bound (accurateGrid_le_one m) _ n hni
    have he : Real.exp (((100:ℝ)^i/4)*Real.exp m)≤Real.exp (((100:ℝ)^w/50)*Real.exp m) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hh,hi0]
    exact (mul_le_of_le_one_left (Real.exp_nonneg _) (accurateGrid_le_one m)).trans he

lemma windowBlocks_length_bound {C : ℝ} {a : ℝ} (m W : ℕ)
    (J : ℕ → Finset ℕ) (hJ : ∀ w<W, ((J w).card:ℝ)≤C) :
    ((windowBlocks a m J W).length:ℝ)≤(W:ℝ)*(20*C+4*(m:ℝ)^2) := by
  induction W with
  | zero => simp [windowBlocks]
  | succ W ih =>
    have hi := ih (fun w hw => hJ w (by omega))
    rw [windowBlocks_succ,List.length_append,List.length_append]
    simp only [topBlocks_length,Nat.cast_add,Nat.cast_mul,topIterations,Nat.cast_ofNat,
      accurateBlock,List.length_ofFn,accurateIterations,Nat.cast_pow]
    have hh := hJ W (by omega)
    have hW : (W:ℝ)+1=(W+1:ℕ) := by push_cast; rfl
    push_cast
    nlinarith only [hi,hh]

lemma windowBlocks_length_bound_of_bins {a : ℝ} {m W : ℕ}
    (J : ℕ → Finset ℕ) (hm : 2≤Real.exp m)
    (hJ : ∀ w<W, ∀ j∈J w, (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) :
    ((windowBlocks a m J W).length:ℝ)≤
      (W:ℝ)*(60*(100:ℝ)^W*Real.exp m+4*(m:ℝ)^2) := by
  have hb : ∀ w<W, ((J w).card:ℝ)≤3*(100:ℝ)^W*Real.exp m := by
    intro w hw
    have hw1 := window_power_one w
    have hs : 2≤(100:ℝ)^w*Real.exp m := by nlinarith only [hw1,hm]
    have hh := narrow_bins_card hs (J w) (hJ w hw)
    have hp : (100:ℝ)^w≤(100:ℝ)^W := pow_le_pow_right₀ (by norm_num) hw.le
    have he := mul_le_mul_of_nonneg_right hp (Real.exp_nonneg (m:ℝ))
    nlinarith only [hh,he]
  have hh := windowBlocks_length_bound (a := a) m W J hb
  nlinarith only [hh]

lemma eventually_window_length (W : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      (W:ℝ)*(60*(100:ℝ)^W*Real.exp m+4*(m:ℝ)^2)+4*(m:ℝ)^2+2≤Real.exp (Real.exp m) := by
  have hp := eventually_poly_le_exp (4*((W:ℝ)+1)) (a := 1) (by norm_num) 2
  have ht := (eventually_mul_le_double_exp (a := 1) (by norm_num) (60*W*(100:ℝ)^W+3))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hp,ht] with m hm ht
  simp only [one_mul] at hm ht
  have he : 1≤Real.exp (m:ℝ) := Real.one_le_exp_iff.mpr (Nat.cast_nonneg _)
  nlinarith only [hm,ht,he]

noncomputable def windowSmoothing (W m : ℕ) : ℕ :=
  ⌈Real.exp (20*(100:ℝ)^W*Real.exp m)⌉₊

lemma windowSmoothing_pos (W m : ℕ) : 0<windowSmoothing W m :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

lemma windowSmoothing_bounds (W m : ℕ) :
    Real.exp (20*(100:ℝ)^W*Real.exp m)≤(windowSmoothing W m:ℝ) ∧
    (windowSmoothing W m:ℝ)+1≤Real.exp ((20*(100:ℝ)^W+2)*Real.exp m) := by
  refine ⟨Nat.le_ceil _,?_⟩
  have hh := (Nat.ceil_lt_add_one (Real.exp_nonneg (20*(100:ℝ)^W*Real.exp m))).le
  have he : 1≤Real.exp (m:ℝ) := Real.one_le_exp_iff.mpr (Nat.cast_nonneg _)
  have he' : 3≤Real.exp (2*Real.exp (m:ℝ)) := by
    have hh := Real.add_one_le_exp (2*Real.exp (m:ℝ))
    linarith only [hh,he]
  have hbase : 1≤Real.exp (20*(100:ℝ)^W*Real.exp m) := Real.one_le_exp_iff.mpr (by positivity)
  have hmul := mul_le_mul_of_nonneg_left he' (Real.exp_nonneg (20*(100:ℝ)^W*Real.exp m))
  rw [←Real.exp_add] at hmul
  change (⌈Real.exp (20*(100:ℝ)^W*Real.exp m)⌉₊:ℝ)+1≤_
  rw [show (20*(100:ℝ)^W+2)*Real.exp m=20*(100:ℝ)^W*Real.exp m+2*Real.exp m by ring]
  linarith only [hh,hbase,hmul]

theorem eventually_suffix_cost {D a b C : ℝ} (hD : 0<D) (ha : 0<a) (hab : a<b) :
    ∀ᶠ X : ℝ in atTop, ∀ ns : List ℕ, ∀ N : ℕ,
      1≤ns.sum+N → (ns.length+2:ℝ)≤Real.exp X →
      (∀ n∈ns, (n:ℝ)≤Real.exp (Real.exp (a*X))) →
      (N:ℝ)+1≤Real.exp (C*X) →
      Real.log 36+2*Real.log (D*(ns.sum+N))≤Real.exp (b*X) := by
  have hp := eventually_poly_le_exp_linear
    (|Real.log 36|+2*|Real.log D|+2*|1+C|) ha 1
  have hres := eventually_mul_exp_le_exp hab 3
  filter_upwards [hp,hres,eventually_ge_atTop (1:ℝ)] with X hp hres hX
  intro ns N hs hl ho hN
  have hlog := schedule_log_bound ns N (Real.exp_nonneg (a*X)) ho
  have hl' : Real.log ((ns.length:ℝ)+1)≤X := by
    have hh := Real.log_le_log (by positivity : 0<(ns.length:ℝ)+1) (by linarith only [hl] : (ns.length:ℝ)+1≤Real.exp X)
    rwa [Real.log_exp] at hh
  have hN' : Real.log ((N:ℝ)+1)≤C*X := by
    have hh := Real.log_le_log (by positivity : 0<(N:ℝ)+1) hN
    rwa [Real.log_exp] at hh
  have hspos : (0:ℝ)<(ns.sum+N:ℕ) := by exact_mod_cast (show 0<ns.sum+N by omega)
  have hs' : Real.log ((ns.sum+N:ℕ):ℝ)≤Real.log ((ns.sum+N:ℕ)+1) :=
    Real.log_le_log hspos (by push_cast; linarith)
  simp only [Nat.cast_add] at hspos hs' hlog
  rw [Real.log_mul hD.ne' hspos.ne']
  have hc : Real.log 36+2*Real.log D+2*(1+C)*X≤Real.exp (a*X) := by
    simp only [pow_one] at hp
    have h1 := le_abs_self (Real.log (36:ℝ))
    have h2 := le_abs_self (Real.log D)
    have h3 := le_abs_self (1+C)
    nlinarith only [hp,hX,h1,h2,h3,abs_nonneg (Real.log (36:ℝ)),abs_nonneg (Real.log D)]
  nlinarith only [hlog,hl',hN',hs',hc,hres]

noncomputable def coverageRepetitions (X : ℝ) : ℕ := ⌈Real.exp (X/100)⌉₊

lemma coverageRepetitions_pos (X : ℝ) : 0<coverageRepetitions X :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

lemma coverageRepetitions_bounds {X : ℝ} (hX : 0≤X) :
    Real.exp (X/100)≤(coverageRepetitions X:ℝ) ∧
    (coverageRepetitions X:ℝ)≤2*Real.exp (X/100) := by
  refine ⟨Nat.le_ceil _,?_⟩
  have hh := (Nat.ceil_lt_add_one (Real.exp_nonneg (X/100))).le
  have he : 1≤Real.exp (X/100) := Real.one_le_exp_iff.mpr (by positivity)
  change (⌈Real.exp (X/100)⌉₊:ℝ)≤2*Real.exp (X/100)
  linarith only [hh,he]

lemma eventually_coverage_hazard :
    ∀ᶠ X : ℝ in atTop, ∀ p : ℝ, 0<p → p≤2*Real.exp (21/20*X) →
      p*Real.exp (-(coverageRepetitions X:ℝ)*(1/64)^2*
        (p*Real.exp (-X/200))/(2*p))≤1/640000 := by
  have hp := eventually_poly_le_exp_linear (8192*(21/20+Real.log (1280000:ℝ)))
    (a := 1/200) (by norm_num) 1
  filter_upwards [hp,eventually_ge_atTop (1:ℝ)] with X hpoly hX
  intro p hp0 hp
  have hlog : 0≤Real.log (1280000:ℝ) := Real.log_nonneg (by norm_num)
  have hmargin : 8192*(21/20*X+Real.log (1280000:ℝ))≤Real.exp (X/200) := by
    simp only [pow_one,show (1:ℝ)/200*X=X/200 by ring] at hpoly
    nlinarith only [hpoly,hX,hlog]
  have hn := (coverageRepetitions_bounds (by linarith only [hX])).1
  have hn' := mul_le_mul_of_nonneg_right hn (Real.exp_nonneg (-X/200))
  rw [←Real.exp_add] at hn'
  have he : X/100+-X/200=X/200 := by ring
  rw [he] at hn'
  have harg : -(coverageRepetitions X:ℝ)*(1/64)^2*(p*Real.exp (-X/200))/(2*p)≤
      -(21/20*X)-Real.log (1280000:ℝ) := by
    have hEq : -(coverageRepetitions X:ℝ)*(1/64)^2*(p*Real.exp (-X/200))/(2*p)=
        -(coverageRepetitions X:ℝ)*Real.exp (-X/200)/8192 := by field_simp; ring
    rw [hEq]
    linarith only [hmargin,hn']
  have hh := mul_le_mul hp (Real.exp_le_exp.mpr harg) (Real.exp_nonneg _) (by positivity : 0≤2*Real.exp (21/20*X))
  simp only [mul_assoc,←Real.exp_add] at hh
  have he' : 21/20*X+(-(21/20*X)-Real.log (1280000:ℝ))=-Real.log (1280000:ℝ) := by ring
  rw [he',Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<1280000)] at hh
  norm_num at hh ⊢
  simpa only [mul_assoc] using hh

lemma eventually_coverage_data_cost :
    ∀ᶠ X : ℝ in atTop, ∀ H b : ℝ,
      H≤Real.exp (3/50*X) → Real.exp (X/8)/(4*X)≤b →
      (coverageRepetitions X:ℝ)*H/b≤1/1024 := by
  have hp := eventually_poly_le_exp_linear (8192:ℝ) (a := 11/200) (by norm_num) 1
  filter_upwards [hp,eventually_ge_atTop (1:ℝ)] with X hpoly hX
  intro H b hH hb
  have hXp : 0<X := by linarith only [hX]
  have hbp : 0<b := (div_pos (Real.exp_pos _) (by positivity)).trans_le hb
  have hn := (coverageRepetitions_bounds hXp.le).2
  have hmul := (mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg (coverageRepetitions X))).trans
    (mul_le_mul_of_nonneg_right hn (Real.exp_nonneg (3/50*X)))
  simp only [mul_assoc,←Real.exp_add] at hmul
  have hEq : X/100+3/50*X=7/100*X := by ring
  rw [hEq] at hmul
  have hb' := (div_le_iff₀ (show 0<4*X by positivity)).mp hb
  simp only [pow_one] at hpoly
  have hh := mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg (7/100*X))
  rw [←Real.exp_add] at hh
  have he : 11/200*X+7/100*X=X/8 := by ring
  rw [he] at hh
  have hnH : (coverageRepetitions X:ℝ)*H*(4096*X)≤b*(4*X) := by
    have hh' := mul_le_mul_of_nonneg_right hmul (show 0≤4096*X by positivity)
    nlinarith only [hh',hh,hb']
  apply (div_le_iff₀ hbp).mpr
  nlinarith only [hnH,hXp]

lemma eventually_package_displacement {c : ℝ} (hc : 0<c) :
    ∀ᶠ X : ℝ in atTop, ∀ n H T : ℝ,
      0≤n → n≤Real.exp (7/10*X) → H≤Real.exp (13/50*X) → Real.exp X≤T →
      2*n*H≤c*T/5000 := by
  have hh := eventually_mul_exp_le_exp (a := 24/25) (b := 1) (by norm_num) (10000/c)
  filter_upwards [hh] with X hX
  intro n H T hn0 hn hH hT
  have hmul := (mul_le_mul_of_nonneg_left hH hn0).trans
    (mul_le_mul_of_nonneg_right hn (Real.exp_nonneg (13/50*X)))
  rw [←Real.exp_add] at hmul
  have he : 7/10*X+13/50*X=24/25*X := by ring
  rw [he] at hmul
  simp only [one_mul] at hX
  have hh' := mul_le_mul_of_nonneg_left (hX.trans hT) hc.le
  rw [←mul_assoc,mul_div_cancel₀ _ hc.ne'] at hh'
  nlinarith only [hmul,hh']

theorem coverage_from_scalar_guards (s : SplitSieve) (D X : ℝ) (N : ℕ)
    (mid bot : List ℕ) (b q : ℕ) (e : ℝ)
    (hm : EntropyBand s D mid 0 b e) (hb : EntropyBand s D bot N q e)
    (hmean : 0< s.meanLog) (hN : 1≤bot.sum+N)
    (hX : 100≤X)
    (hp : ∀ i, Real.exp X≤(s.signedPrime i:ℝ) ∧
      (s.signedPrime i:ℝ)≤2*Real.exp (21/20*X))
    (hbase : e*s.meanLog≤Real.exp (-100)/(512*640000))
    (hmid : e*s.meanLog≤1/1024)
    (hcost : (coverageRepetitions X:ℝ)*(Real.log 36+2*Real.log (D*(bot.sum+N)))/b≤1/1024)
    (hhazard : ∀ i, (s.signedPrime i:ℝ)*Real.exp
      (-(coverageRepetitions X:ℝ)*(1/64)^2*
        ((s.signedPrime i:ℝ)*Real.exp (-X/200))/(2*(s.signedPrime i:ℝ)))≤1/640000) :
    CoverageDerivation s D N (mid++bot) (1/4)
      (fun i => (s.signedPrime i:ℝ)*Real.exp (-X/200)) (1/100) := by
  exact one_step_coverage s D N mid bot b q (coverageRepetitions X) e e _ hm hb
    (hm.size_pos hmean) (hm.size_cap hmean) (hb.size_pos hmean) (hb.size_cap hmean)
    hN (coverageRepetitions_pos X)
    (fun i => (Real.exp_le_exp.mpr hX).trans (hp i).1)
    (fun i => mul_pos ((Real.exp_pos X).trans_le (hp i).1) (Real.exp_pos _)) hbase
    (by linarith only [hmid,hcost]) hhazard

lemma binEntropy_small_exp {t Y : ℝ} (ht : 0≤t) (hY : 1≤Y)
    (htY : t≤Real.exp (-Y)) :
    Real.binEntropy t≤(Y+1)*Real.exp (-Y) := by
  have heY : 2≤Real.exp Y := by linarith only [Real.add_one_le_exp Y,hY]
  have hu : Real.exp (-Y)≤(1/2:ℝ) := by
    rw [Real.exp_neg]
    exact inv_le_of_inv_le₀ (by norm_num) (by simpa using heY)
  have hm := Real.binEntropy_strictMonoOn.monotoneOn
    (show t∈Set.Icc 0 (2:ℝ)⁻¹ by norm_num; exact ⟨ht,htY.trans hu⟩)
    (show Real.exp (-Y)∈Set.Icc 0 (2:ℝ)⁻¹ by norm_num; exact ⟨(Real.exp_pos _).le,hu⟩) htY
  have hn := Real.negMulLog_le_one_sub_self (show 0≤1-Real.exp (-Y) by linarith only [hu])
  simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    Real.negMulLog,Real.log_exp] at hm ⊢
  have hh : -(1-Real.exp (-Y))*Real.log (1-Real.exp (-Y))≤Real.exp (-Y) := by
    simpa only [Real.negMulLog,sub_sub_cancel] using hn
  nlinarith only [hm,hh]

lemma exp_ratio_bound {a N X A : ℝ} (ha : a≤Real.exp (A*X))
    (hN : Real.exp (10*A*X)≤N) :
    a/(N+1)≤Real.exp (-9*A*X) := by
  have hNp : 0<N+1 := by linarith only [hN,Real.exp_pos (10*A*X)]
  apply (div_le_iff₀ hNp).mpr
  have hh := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg (-9*A*X))
  rw [←Real.exp_add] at hh
  rw [show -9*A*X+10*A*X=A*X by ring] at hh
  nlinarith only [ha,hh,Real.exp_nonneg (-9*A*X)]

theorem eventually_smoothing_guard {A H : ℝ} (hA : 1≤A) :
    ∀ᶠ X : ℝ in atTop, ∀ a L E N : ℝ,
      0≤a → a≤Real.exp (A*X) → 0≤L → L≤Real.exp (A*X) →
      E≤Real.exp (A*X) → Real.exp (10*A*X)≤N →
      2*Real.binEntropy (a/(N+1))+(a/(N+1))*(L*H+2*E)≤Real.exp (-X) := by
  have hpoly := eventually_poly_le_exp_linear (4*(9*A+1))
    (a := 9*A-1) (by linarith only [hA]) 1
  have hcost := eventually_poly_le_exp_linear (2*(max H 0+2))
    (a := 8*A-1) (by linarith only [hA]) 0
  filter_upwards [hpoly,hcost,eventually_ge_atTop (1:ℝ)] with X hpoly hcost hX
  intro a L E N ha0 ha hL0 hL hE hN
  have hNpos : 0<N+1 := by linarith only [hN,Real.exp_pos (10*A*X)]
  have ht0 : 0≤a/(N+1) := div_nonneg ha0 hNpos.le
  have ht := exp_ratio_bound ha hN
  have hAX : 1≤A*X := by nlinarith only [hA,hX]
  have hbin := binEntropy_small_exp ht0 (by nlinarith only [hAX] : 1≤9*A*X)
    (by simpa only [neg_mul] using ht)
  have hbin' : 2*Real.binEntropy (a/(N+1))≤Real.exp (-X)/2 := by
    simp only [pow_one] at hpoly
    have hc : 4*(9*A*X+1)≤Real.exp ((9*A-1)*X) := by nlinarith only [hpoly,hX]
    have hh := mul_le_mul_of_nonneg_right hc (Real.exp_nonneg (-(9*A*X)))
    rw [←Real.exp_add,show (9*A-1)*X+-(9*A*X)= -X by ring] at hh
    linarith only [hh,hbin]
  have hK : L*H+2*E≤(max H 0+2)*Real.exp (A*X) := by
    have hh := mul_le_mul_of_nonneg_left (le_max_left H 0) hL0
    have hh' := mul_le_mul_of_nonneg_right hL (le_max_right H 0)
    nlinarith only [hh,hh',hE]
  have hKt := (mul_le_mul_of_nonneg_left hK ht0).trans
    (mul_le_mul_of_nonneg_right ht (show 0≤(max H 0+2)*Real.exp (A*X) by positivity))
  have hprod : Real.exp (-9*A*X)*((max H 0+2)*Real.exp (A*X))=
      (max H 0+2)*Real.exp (-8*A*X) := by
    rw [mul_left_comm,←Real.exp_add]
    congr 1
    ring_nf
  rw [hprod] at hKt
  have hlast : (max H 0+2)*Real.exp (-8*A*X)≤Real.exp (-X)/2 := by
    simp only [pow_zero,mul_one] at hcost
    have hh := mul_le_mul_of_nonneg_right hcost (Real.exp_nonneg (-8*A*X))
    rw [←Real.exp_add,show (8*A-1)*X+-8*A*X= -X by ring] at hh
    linarith only [hh]
  linarith only [hbin',hKt,hlast]

lemma eventually_smoothing_total (C : ℝ) :
    ∀ᶠ X : ℝ in atTop, C*X*Real.exp (-X)≤1 := by
  have hh := eventually_poly_le_exp C (a := 1) (by norm_num) 1
  filter_upwards [hh] with X hX
  simp only [pow_one,one_mul] at hX
  have hm := mul_le_mul_of_nonneg_right hX (Real.exp_nonneg (-X))
  simpa only [←Real.exp_add,add_neg_cancel,Real.exp_zero] using hm

end GaussianMoat

end OAI
