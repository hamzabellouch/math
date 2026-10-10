import OAI.NumberTheory.GaussianMoat.Smoothing

namespace OAI

namespace GaussianMoat
open scoped BigOperators Classical
open Filter

noncomputable def commonBlocks (a : ℝ) (m W : ℕ) (J : ℕ → Finset ℕ) : List ℕ :=
  windowBlocks a m J W++accurateBlock m (1/20)

noncomputable def middleBlocks (a : ℝ) (m w : ℕ) (J : ℕ → Finset ℕ) : List ℕ :=
  accurateBlock m ((100:ℝ)^w/4)++windowBlocks a m J w

lemma windowScale_tendsto (w : ℕ) :
    Tendsto (fun m : ℕ => (100:ℝ)^w*Real.exp m) atTop atTop :=
  (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)

lemma dyadic_prime_bounds (j : ℕ) :
    ∀ p∈(dyadicSieve j).primes, (2:ℝ)^j≤(p:ℝ) ∧ (p:ℝ)≤2*(2:ℝ)^j := by
  intro p hp
  have hh := (PrimeLogMass.mem_dyadicBatch j p).mp hp
  constructor
  · exact_mod_cast hh.1
  · have hh' : p≤2^(j+1) := hh.2.1.le
    rw [pow_succ] at hh'
    exact_mod_cast (by simpa only [mul_comm] using hh' : p≤2*2^j)

lemma dyadic_dense_nonempty {δ : ℝ} (hδ : 0<δ) {j : ℕ}
    (hd : δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(PrimeLogMass.dyadicBatch j).card) :
    (dyadicSieve j).primes.Nonempty := by
  apply Finset.card_pos.mp
  have hp : 0<δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1)) := by rw [Real.log_pow]; positivity
  exact_mod_cast hp.trans_le hd

lemma dyadic_mean_bounds {X : ℝ} (hX : 2≤X) {j : ℕ}
    (hne : (dyadicSieve j).primes.Nonempty)
    (hlo : X≤j*Real.log 2) (hhi : j*Real.log 2≤21/20*X) :
    1≤(dyadicSieve j).meanLog ∧ (dyadicSieve j).meanLog≤2*X := by
  have hh := (dyadicSieve j).meanLog_bounds hne (by positivity) (dyadic_prime_bounds j)
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hh
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  constructor <;> linarith only [hh.1,hh.2,hlo,hhi,hX,hl2]

lemma commonBlocks_length {a : ℝ} {m W : ℕ} (J : ℕ → Finset ℕ) (hm : 2≤Real.exp m)
    (hJ : ∀ w<W, ∀ j∈J w, (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) :
    ((commonBlocks a m W J).length:ℝ)+2≤
      (W:ℝ)*(60*(100:ℝ)^W*Real.exp m+4*(m:ℝ)^2)+4*(m:ℝ)^2+2 := by
  have hh := windowBlocks_length_bound_of_bins (a := a) J hm hJ
  simp only [commonBlocks,List.length_append,accurateBlock,List.length_ofFn,
    accurateIterations,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  linarith only [hh]

lemma middleBlocks_length_le {a : ℝ} {m W w : ℕ} (J : ℕ → Finset ℕ) (hw : w<W) :
    (middleBlocks a m w J).length≤(windowBlocks a m J W).length := by
  obtain ⟨pre,he⟩ := windowBlocks_split a m J hw
  simp only [middleBlocks,he,List.length_append]
  omega

theorem eventually_window_tail_bounds {D a : ℝ} (hD : 1≤D) (ha : 0≤a) (ha1 : a≤1)
    (W w : ℕ) (hw : w<W) :
    ∀ᶠ m : ℕ in atTop, ∀ J : ℕ → Finset ℕ,
      (∀ i<W, ∀ j∈J i, (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m)) →
      ((commonBlocks a m W J).length:ℝ)+2≤Real.exp (Real.exp m) ∧
      (windowSmoothing W m:ℝ)≤Real.exp (Real.exp ((1/100)*Real.exp m)) ∧
      ((windowBlocks a m J w).length+2:ℝ)≤Real.exp (Real.exp (((100:ℝ)^w/50)*Real.exp m)) ∧
      Real.log 36+2*Real.log (D*((accurateBlock m (1/20)).sum+windowSmoothing W m))≤
        Real.exp (3/50*((100:ℝ)^w*Real.exp m)) ∧
      Real.log 36+2*Real.log (D*((middleBlocks a m w J++accurateBlock m (1/20)).sum+windowSmoothing W m))≤
        Real.exp (13/50*((100:ℝ)^w*Real.exp m)) := by
  have hN := eventually_mul_le_double_exp (a := 1/100) (by norm_num) (20*(100:ℝ)^W+2)
  have hlen := eventually_mul_le_double_exp (a := 1/100) (by norm_num) 1
  have ht := windowScale_tendsto w
  have hbot := ht.eventually (eventually_suffix_cost (D := D) (a := 1/20) (b := 3/50)
    (C := 20*(100:ℝ)^W+2) (by linarith only [hD]) (by norm_num) (by norm_num))
  have hrest := ht.eventually (eventually_suffix_cost (D := D) (a := 1/4) (b := 13/50)
    (C := 20*(100:ℝ)^W+2) (by linarith only [hD]) (by norm_num) (by norm_num))
  have hm2 := (windowScale_tendsto 0).eventually (eventually_ge_atTop (2:ℝ))
  filter_upwards [eventually_window_length W,hN,hlen,hbot,hrest,hm2] with m hm hN hlen hbot hrest hm2
  intro J hJ
  simp only [one_mul] at hlen
  simp only [pow_zero,one_mul] at hm2
  have hl := (commonBlocks_length (a := a) J hm2 hJ).trans hm
  have hpow := window_power_one w
  have hX : Real.exp (m:ℝ)≤(100:ℝ)^w*Real.exp m := by nlinarith only [hpow,Real.exp_pos (m:ℝ)]
  have hNsmall : (windowSmoothing W m:ℝ)≤Real.exp (Real.exp ((1/100)*Real.exp m)) := by
    have hN' := (windowSmoothing_bounds W m).2.trans (Real.exp_le_exp.mpr hN)
    linarith only [hN']
  have hlw : ((windowBlocks a m J w).length+2:ℝ)≤Real.exp (Real.exp (((100:ℝ)^w/50)*Real.exp m)) := by
    have hh : (windowBlocks a m J w).length≤(commonBlocks a m W J).length := by
      obtain ⟨pre,he⟩ := windowBlocks_split a m J hw
      simp only [commonBlocks,he,List.length_append]; omega
    have harg : Real.exp (m:ℝ)≤Real.exp (((100:ℝ)^w/50)*Real.exp m) := by
      apply hlen.trans (Real.exp_le_exp.mpr _)
      nlinarith only [hpow,Real.exp_pos (m:ℝ)]
    exact (add_le_add (by exact_mod_cast hh : ((windowBlocks a m J w).length:ℝ)≤(commonBlocks a m W J).length) (le_refl (2:ℝ))) |>.trans (hl.trans (Real.exp_le_exp.mpr harg))
  have hNs : (windowSmoothing W m:ℝ)+1≤Real.exp ((20*(100:ℝ)^W+2)*((100:ℝ)^w*Real.exp m)) :=
    (windowSmoothing_bounds W m).2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hX (by positivity)))
  have hbLen : ((accurateBlock m (1/20)).length+2:ℝ)≤Real.exp ((100:ℝ)^w*Real.exp m) := by
    have hh : (accurateBlock m (1/20)).length≤(commonBlocks a m W J).length := by simp [commonBlocks]
    exact (add_le_add (by exact_mod_cast hh : ((accurateBlock m (1/20)).length:ℝ)≤(commonBlocks a m W J).length) (le_refl (2:ℝ))) |>.trans (hl.trans (Real.exp_le_exp.mpr hX))
  have hrLen : ((middleBlocks a m w J++accurateBlock m (1/20)).length+2:ℝ)≤Real.exp ((100:ℝ)^w*Real.exp m) := by
    have hh := middleBlocks_length_le (a := a) (m := m) J hw
    have hh' : (middleBlocks a m w J++accurateBlock m (1/20)).length≤(commonBlocks a m W J).length := by
      simp only [commonBlocks,List.length_append]; omega
    exact (add_le_add (by exact_mod_cast hh' : ((middleBlocks a m w J++accurateBlock m (1/20)).length:ℝ)≤(commonBlocks a m W J).length) (le_refl (2:ℝ))) |>.trans (hl.trans (Real.exp_le_exp.mpr hX))
  have hbOps : ∀ n∈accurateBlock m (1/20), (n:ℝ)≤Real.exp (Real.exp ((1/20)*((100:ℝ)^w*Real.exp m))) := by
    apply accurateBlock_bound (accurateGrid_le_one m)
    exact (mul_le_of_le_one_left (Real.exp_nonneg _) (accurateGrid_le_one m)).trans
      (Real.exp_le_exp.mpr (by linarith only [hX]))
  have hrOps : ∀ n∈middleBlocks a m w J++accurateBlock m (1/20), (n:ℝ)≤Real.exp (Real.exp ((1/4)*((100:ℝ)^w*Real.exp m))) := by
    intro n hn
    rcases List.mem_append.mp hn with hn|hn
    · rcases List.mem_append.mp hn with hn|hn
      · apply accurateBlock_bound (accurateGrid_le_one m) _ n hn
        simpa only [div_mul_eq_mul_div,mul_assoc,one_mul] using
          (mul_le_of_le_one_left (Real.exp_nonneg (((100:ℝ)^w/4)*Real.exp m)) (accurateGrid_le_one m))
      · exact (smaller_window_operations ha ha1 m w J (fun i hi => hJ i (hi.trans hw)) n hn).trans
          (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith only [show 0≤(100:ℝ)^w*Real.exp m by positivity] : ((100:ℝ)^w/50)*Real.exp m≤(1/4)*((100:ℝ)^w*Real.exp m))))
    · exact (hbOps n hn).trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith only [show 0≤(100:ℝ)^w*Real.exp m by positivity] : (1/20)*((100:ℝ)^w*Real.exp m)≤(1/4)*((100:ℝ)^w*Real.exp m))))
  exact ⟨hl,hNsmall,hlw,
    hbot _ _ (by have := windowSmoothing_pos W m; omega) hbLen hbOps hNs,
    hrest _ _ (by have := windowSmoothing_pos W m; omega) hrLen hrOps hNs⟩

lemma floor_size_lower {s : SplitSieve} {g U X : ℝ} {l : ℕ}
    (hX : 0<X) (hm : 0<s.meanLog) (hm' : s.meanLog≤2*X)
    (hscale : Real.exp (X/8)≤bandScale g U l) (hlarge : 4*X≤Real.exp (X/8)) :
    Real.exp (X/8)/(4*X)≤(bandSize s g U l:ℝ) := by
  have hf := Nat.lt_floor_add_one (bandScale g U l/s.meanLog)
  have hh := mul_lt_mul_of_pos_right hf hm
  rw [div_mul_cancel₀ _ hm.ne',add_mul,one_mul] at hh
  have hb := mul_le_mul_of_nonneg_left hm' (Nat.cast_nonneg (bandSize s g U l))
  change (bandScale g U l)<((bandSize s g U l:ℝ)*s.meanLog)+s.meanLog at hh
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hf,hh,hb,hscale,hlarge,hm']

theorem eventually_window_bands {D a δ : ℝ} (hD : 1≤D) (ha : 0≤a) (ha1 : a≤1)
    (hδ : 0<δ) (W w : ℕ) (hw : w<W) :
    ∀ᶠ m : ℕ in atTop, ∀ J : ℕ → Finset ℕ,
      (∀ i<W, ∀ j∈J i, ((100:ℝ)^i*Real.exp m)≤j*Real.log 2 ∧
        j*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m) ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(PrimeLogMass.dyadicBatch j).card) →
      ∀ j∈J w,
        Nonempty (EntropyBand (dyadicSieve j) D (middleBlocks a m w J) 0
          (bandSize (dyadicSieve j) (accurateGrid m) (Real.exp (((100:ℝ)^w/4)*Real.exp m)) (accurateIterations m))
          (91*accurateGrid m)) ∧
        Nonempty (EntropyBand (dyadicSieve j) D (accurateBlock m (1/20)) (windowSmoothing W m)
          (bandSize (dyadicSieve j) (accurateGrid m) (Real.exp ((1/20)*Real.exp m)) (accurateIterations m))
          (91*accurateGrid m)) ∧
        Real.exp (((100:ℝ)^w*Real.exp m)/8)/(4*((100:ℝ)^w*Real.exp m))≤
          (bandSize (dyadicSieve j) (accurateGrid m) (Real.exp (((100:ℝ)^w/4)*Real.exp m)) (accurateIterations m):ℝ) := by
  have hwp := window_power_one w
  have hp : (0:ℝ)<100^w := by positivity
  have hmid := eventually_accurate_band (D := D) (A := (100:ℝ)^w) (B := 2*(100:ℝ)^w)
    (a := (100:ℝ)^w/4) (b := (100:ℝ)^w/50) hD hp (by positivity) (by linarith only [hp])
    (by linarith only [hp]) hδ
  have hbot := eventually_accurate_band (D := D) (A := 1) (B := 2*(100:ℝ)^w)
    (a := 1/20) (b := 1/100) hD (by norm_num) (by norm_num) (by norm_num) (by norm_num) hδ
  have hscale := eventually_accurate_scale (a := (100:ℝ)^w/4) (by positivity) 0
  have hlarge := eventually_mul_le_double_exp (a := (100:ℝ)^w/8) (by positivity) (4*(100:ℝ)^w)
  have hm2 := (windowScale_tendsto 0).eventually (eventually_ge_atTop (2:ℝ))
  filter_upwards [hmid,hbot,hscale,hlarge,eventually_window_tail_bounds hD ha ha1 W w hw,hm2]
    with m hmid hbot hscale hlarge htail hm2
  intro J hJ j hj
  simp only [pow_zero,one_mul] at hm2
  have hdata := hJ w hw j hj
  have hne := dyadic_dense_nonempty hδ hdata.2.2
  have hX2 : 2≤(100:ℝ)^w*Real.exp m := by nlinarith only [hm2,hwp]
  have hm := dyadic_mean_bounds hX2 hne hdata.1 hdata.2.1
  have hpj := dyadic_prime_bounds j
  have hdense : δ*(2:ℝ)^j/Real.log (2*(2:ℝ)^j)≤(dyadicSieve j).primes.card := by
    change δ*(2:ℝ)^j/Real.log (2*(2:ℝ)^j)≤(PrimeLogMass.dyadicBatch j).card
    simpa only [pow_succ,mul_comm] using hdata.2.2
  have hT : Real.exp ((100:ℝ)^w*Real.exp m)≤(2:ℝ)^j := by
    rw [←Real.exp_log (by positivity : (0:ℝ)<2^j),Real.log_pow]
    exact Real.exp_le_exp.mpr hdata.1
  have hThi : Real.log ((2:ℝ)^j)≤(2*(100:ℝ)^w)*Real.exp m := by
    rw [Real.log_pow]
    nlinarith only [hdata.2.1,hX2]
  obtain ⟨_,hN,hlen,_,_⟩ := htail J (fun i hi k hk => (hJ i hi k hk).2.1)
  have hmid' := hmid (dyadicSieve j) ((2:ℝ)^j) [] (windowBlocks a m J w) 0
    hne hpj hdense hT hThi
    (smaller_window_operations ha ha1 m w J (fun i hi k hk => (hJ i (hi.trans hw) k hk).2.1))
    (by simp only [Nat.cast_zero]; positivity) hlen
  have hTwo : (2:ℝ)≤Real.exp (Real.exp ((1/100)*Real.exp m)) := by
    have he : 1≤Real.exp ((1/100)*Real.exp (m:ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
    linarith only [Real.add_one_le_exp (Real.exp ((1/100)*Real.exp (m:ℝ))),he]
  have hbot' := hbot (dyadicSieve j) ((2:ℝ)^j) [] [] (windowSmoothing W m)
    hne hpj hdense
    ((Real.exp_le_exp.mpr (by nlinarith only [hwp,Real.exp_pos (m:ℝ)] : 1*Real.exp m≤(100:ℝ)^w*Real.exp m)).trans hT)
    hThi (by simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true]) hN
    (by simpa only [List.length_nil,Nat.cast_zero,zero_add] using hTwo)
  refine ⟨?_,?_,?_⟩
  · simpa only [List.nil_append,accurateBlock,middleBlocks] using hmid'
  · simpa only [List.nil_append,List.append_nil,accurateBlock] using hbot'
  · apply floor_size_lower (by linarith only [hX2]) (by linarith only [hm.1]) hm.2
    · simpa only [pow_zero,one_mul,div_div,show (4:ℝ)*2=8 by norm_num,div_mul_eq_mul_div] using hscale
    · simpa only [mul_assoc,div_mul_eq_mul_div] using hlarge

end GaussianMoat

end OAI
