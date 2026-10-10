import OAI.NumberTheory.GaussianMoat.CommonBlocks

namespace OAI

namespace GaussianMoat
open scoped BigOperators Classical
open Filter

lemma eventually_length_smoothing :
    ∀ᶠ X : ℝ in atTop, ∀ p L N : ℝ,
      0<p → p≤2*Real.exp (21/20*X) → 0≤L → L≤Real.exp (21/50*X) →
      Real.exp (20*X)≤N → L≤N ∧ L/(N+1)≤((1/4)/p)/2 := by
  have hh := eventually_mul_exp_le_exp (a := 147/100) (b := 20) (by norm_num) 16
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with X hh hX
  intro p L N hp hp' hL hL' hN
  have hNpos : 0<N+1 := by linarith only [hN,Real.exp_pos (20*X)]
  have hm := mul_le_mul hp' hL' hL (by positivity : 0≤2*Real.exp (21/20*X))
  rw [mul_assoc,←Real.exp_add,show 21/20*X+21/50*X=147/100*X by ring] at hm
  refine ⟨hL'.trans ((Real.exp_le_exp.mpr (by linarith only [hX])).trans hN),?_⟩
  apply (div_le_iff₀ hNpos).mpr
  have he : ((1/4:ℝ)/p)/2=(1/8)/p := by ring
  rw [he]
  apply (mul_le_mul_iff_left₀ hp).mp
  have heq : (1/8/p)*(N+1)*p=(N+1)/8 := by field_simp
  rw [heq]
  nlinarith only [hm,hh,hN]

theorem eventually_window_batch {D a δ : ℝ} {K : ℕ}
    (hD : 1≤D) (ha : 0<a) (ha1 : a≤1) (haδ : 2*a≤δ)
    (hgap : a≤(2:ℝ)^K*topCoefficient a) (W w : ℕ) (hw : w<W) :
    ∀ᶠ m : ℕ in atTop, ∀ J : ℕ → Finset ℕ,
      (∀ i<W, ∀ j∈J i, ((100:ℝ)^i*Real.exp m)≤j*Real.log 2 ∧
        j*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m) ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(PrimeLogMass.dyadicBatch j).card) →
      (∀ i∈J w, ∀ j∈J w, i<j → i+K≤j) →
      ∀ j∈J w, ∀ E : ℝ, E≤(topCoefficient a/4)*(2:ℝ)^j/10000 →
        Nonempty (BatchCertificate D (commonBlocks a m W J) (windowSmoothing W m)
          (dyadicSieve j) (batchWordLength j) E
          ((topCoefficient a/4)/(10000000*Real.log ((2:ℝ)^j)))) := by
  have hδ : 0<δ := by linarith only [ha,haδ]
  have hc : 0<topCoefficient a/4 := by exact div_pos (topCoefficient_pos ha) (by norm_num)
  have ht := windowScale_tendsto w
  have hε : 0 < min (1/1024:ℝ) (Real.exp (-100)/(512*640000)) := by positivity
  have herr := eventually_accurate_error (2*(100:ℝ)^w) hε
  filter_upwards [eventually_window_bands hD ha.le ha1 hδ W w hw,
    eventually_window_tail_bounds hD ha.le ha1 W w hw,
    ht.eventually (eventually_window_top hD ha haδ hgap),
    ht.eventually (eventually_integer_batch_bounds hD),
    ht.eventually eventually_coverage_hazard,ht.eventually eventually_coverage_data_cost,
    ht.eventually (eventually_package_displacement hc),
    ht.eventually eventually_length_smoothing,herr,ht.eventually (eventually_ge_atTop (1600:ℝ))]
    with m hbands htail htop hint hhazard hccost hpcost hsmooth herr hX
  intro J hJ hsep j hj E hE
  let X : ℝ := (100:ℝ)^w*Real.exp m
  let s := dyadicSieve j
  have hdata := hJ w hw j hj
  have hne : s.primes.Nonempty := dyadic_dense_nonempty hδ hdata.2.2
  have hpj := dyadic_prime_bounds j
  have hm := dyadic_mean_bounds (by linarith only [hX]) hne hdata.1 hdata.2.1
  have hTpos : (0:ℝ)<2^j := by positivity
  have hT : Real.exp X≤(2:ℝ)^j := by
    rw [←Real.exp_log hTpos,Real.log_pow]
    exact Real.exp_le_exp.mpr hdata.1
  have hprime : ∀ i : s.SignedIndex, Real.exp X≤(s.signedPrime i:ℝ) ∧
      (s.signedPrime i:ℝ)≤2*Real.exp (21/20*X) := by
    intro i
    have hp := hpj _ (s.enumeration i.2).property
    refine ⟨hT.trans hp.1,hp.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [←Real.exp_log hTpos,Real.log_pow]
    exact Real.exp_le_exp.mpr hdata.2.1
  obtain ⟨pre,hpre⟩ := windowBlocks_split a m J hw
  obtain ⟨hband,hbsize⟩ := htop (J w) pre hsep (hJ w hw) j hj
  obtain ⟨qtop⟩ := hband
  obtain ⟨hmid,hbot,hbmid⟩ := hbands J hJ j hj
  obtain ⟨qmid⟩ := hmid
  obtain ⟨qbot⟩ := hbot
  obtain ⟨_,_,_,hbotcost,hrestcost⟩ := htail J (fun i hi k hk => (hJ i hi k hk).2.1)
  have herrors : (91*accurateGrid m)*s.meanLog≤ min (1/1024:ℝ) (Real.exp (-100)/(512*640000)) := by
    have hh := mul_le_mul_of_nonneg_left hm.2 (by have := accurateGrid_pos m; positivity : 0≤91*accurateGrid m)
    exact hh.trans (by simpa only [mul_assoc] using herr)
  have hcoverage := coverage_from_scalar_guards s D X (windowSmoothing W m)
    (middleBlocks a m w J) (accurateBlock m (1/20)) _ _ _ qmid qbot
    (by linarith only [hm.1]) (by have := windowSmoothing_pos W m; omega)
    (by linarith only [hX]) hprime
    (herrors.trans (min_le_right _ _)) (herrors.trans (min_le_left _ _))
    (hccost _ _ hbotcost hbmid) (fun i => hhazard _ ((Real.exp_pos X).trans_le (hprime i).1) (hprime i).2)
  obtain ⟨hn,hshort,hnL,hnL',hnmax,hLmax⟩ := hint j hdata.1 hdata.2.1
  have hN : Real.exp (20*X)≤(windowSmoothing W m:ℝ) := by
    apply le_trans _ (windowSmoothing_bounds W m).1
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤100) hw.le) (Real.exp_nonneg (m:ℝ))
    dsimp only [X]
    nlinarith only [hh]
  have hNLength : batchWordLength j≤windowSmoothing W m := by
    have h := hsmooth ((2:ℝ)^j) (batchWordLength j) (windowSmoothing W m) hTpos
      (by
        have hh : (2:ℝ)^j≤Real.exp (21/20*X) := by
          rw [←Real.exp_log hTpos,Real.log_pow]
          exact Real.exp_le_exp.mpr hdata.2.1
        linarith only [hh,Real.exp_nonneg (21/20*X)])
      (Nat.cast_nonneg _) hLmax hN
    exact_mod_cast h.1
  refine ⟨{
    pre := pre++topBlocks a (J w)
    rest := middleBlocks a m w J++accurateBlock m (1/20)
    schedule := by simp only [commonBlocks,middleBlocks,hpre,List.append_assoc]
    T := (2:ℝ)^j
    nonempty := hne
    prime_scale := hpj
    large := by linarith only [hT,Real.add_one_le_exp X,hX]
    mean := hm.1
    b := bandSize s topParameter (a*(2:ℝ)^j) topIterations
    n := packageRepetitions j
    τ := 1/4
    A := X/400
    η := 1/100
    δ := 1/10000
    u := fun i => (s.signedPrime i:ℝ)*Real.exp (-X/200)
    band := qtop
    coverage := hcoverage
    cap := qtop.size_cap (by linarith only [hm.1])
    repetitions := hn
    length := batchWordLength_pos j
    floor := by norm_num
    gain := by linarith only [hX]
    exceptions := fun i => by positivity
    short := fun i => hshort.trans_le (hpj _ (s.enumeration i.2).property).1
    smooth_length := hNLength
    smooth_error := fun i => (hsmooth _ _ _ ((Real.exp_pos X).trans_le (hprime i).1)
      (hprime i).2 (Nat.cast_nonneg _) hLmax hN).2
    list := ?_
    rate := ?_
  }⟩
  · intro i
    have hh := package_list_arithmetic hX hT ((Real.exp_pos X).trans_le (hprime i).1)
      (hpj _ (s.enumeration i.2).property).2 hnL
    dsimp only [s] at hh
    convert hh using 1; congr 2; ring_nf
  · apply package_rate_arithmetic (by linarith only [hX]) hTpos hc
      (by simpa only [Real.log_pow] using hdata.1)
      (by simpa only [Real.log_pow] using hdata.2.1) hm.2
      (by convert hbsize using 1; ring) hnL'
      (hpcost _ _ _ (Nat.cast_nonneg _) hnmax hrestcost hT) hE

end GaussianMoat

end OAI
