import OAI.NumberTheory.GaussianMoat.SieveSmoothing

namespace OAI

namespace GaussianMoat
open scoped BigOperators Classical
open Filter

theorem exists_sieveCertificate (D : ℝ) (hD : 1≤D) : Nonempty (SieveCertificate D) := by
  obtain ⟨a,δ,t,K,ha,ha1,haδ,ht,hK,hgap,hcost,hdensity⟩ := exists_separated_parameters
  let c := topCoefficient a/4
  have hc : 0<c := div_pos (topCoefficient_pos ha) (by norm_num)
  let rate := c*t/10500000
  have hrate : 0<rate := by dsimp only [rate]; positivity
  obtain ⟨W,hW⟩ := exists_nat_gt (max 0 ((Real.log (latticeBall D).card+1)/rate))
  have hW0 : 0<W := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hW)
  have hWrate : Real.log (latticeBall D).card+1<(W:ℝ)*rate :=
    (div_lt_iff₀ hrate).mp ((le_max_right _ _).trans_lt hW)
  have hbatch : ∀ᶠ m : ℕ in atTop, ∀ w∈Finset.range W, ∀ J : ℕ → Finset ℕ,
      (∀ i<W, ∀ j∈J i, ((100:ℝ)^i*Real.exp m)≤j*Real.log 2 ∧
        j*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m) ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(PrimeLogMass.dyadicBatch j).card) →
      (∀ i∈J w, ∀ j∈J w, i<j → i+K≤j) →
      ∀ j∈J w, ∀ E : ℝ, E≤c*(2:ℝ)^j/10000 →
        Nonempty (BatchCertificate D (commonBlocks a m W J) (windowSmoothing W m)
          (dyadicSieve j) (batchWordLength j) E (c/(10000000*Real.log ((2:ℝ)^j)))) := by
    apply (Finset.eventually_all (Finset.range W)).mpr
    intro w hw
    exact eventually_window_batch hD ha ha1 haδ hgap W w (Finset.mem_range.mp hw)
  obtain ⟨X0,hX0⟩ := eventually_atTop.mp hdensity
  have hexp : Tendsto (fun m : ℕ => Real.exp (m:ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨m,hbatch,hsmooth,hm⟩ :=
    (hbatch.and ((eventually_allBins_smoothing D W).and
      (hexp.eventually (eventually_ge_atTop (max X0 (K*Real.log 2)))))).exists
  have hmX : X0≤Real.exp (m:ℝ) := (le_max_left _ _).trans hm
  have hmK : K*Real.log 2≤Real.exp (m:ℝ) := (le_max_right _ _).trans hm
  have hbexists : ∀ w : ℕ, ∃ J : Finset ℕ,
      t*((100:ℝ)^w*Real.exp m)≤J.card ∧
      (∀ i∈J, ∀ j∈J, i<j → i+K≤j) ∧
      ∀ j∈J, (100:ℝ)^w*Real.exp m≤j*Real.log 2 ∧
        j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m) ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(PrimeLogMass.dyadicBatch j).card := by
    intro w
    apply hX0 _ (hmX.trans _)
    have := window_power_one w
    nlinarith only [this,Real.exp_pos (m:ℝ)]
  choose J hdense hsep hbounds using hbexists
  let U := allBins W J
  have hJ : ∀ w<W, ∀ j∈J w, (100:ℝ)^w*Real.exp m≤j*Real.log 2 ∧
      j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m) := by
    intro w _ j hj; exact ⟨(hbounds w j hj).1,(hbounds w j hj).2.1⟩
  have hU : U.Nonempty := by
    have hCard0 : 0<(J 0).card := by
      have hpos : 0<t*((100:ℝ)^0*Real.exp m) := by positivity
      exact_mod_cast hpos.trans_le (hdense 0)
    obtain ⟨j,hj⟩ := Finset.card_pos.mp hCard0
    exact ⟨j,Finset.mem_biUnion.mpr ⟨0,Finset.mem_range.mpr hW0,hj⟩⟩
  have hUcard : 0<U.card := Finset.card_pos.mpr hU
  have hUlast : U.card-1+1=U.card := by omega
  have hUsep := allBins_separated J (Real.exp_pos (m:ℝ)) hmK hJ (fun w _ => hsep w)
  obtain ⟨hsmooth,htotal⟩ := hsmooth J (fun w hw j hj => (hJ w hw j hj).2)
  refine ⟨{
    schedule := commonBlocks a m W J
    smoothing := windowSmoothing W m
    batches := binEnum U
    last := U.card-1
    lengths := fun n => batchWordLength (binEnum U n)
    rates := fun n => c/(10000000*Real.log ((2:ℝ)^(binEnum U n)))
    error := Real.exp (-Real.exp m)
    batch := ?_
    divides := ?_
    nonneg := (Real.exp_pos _).le
    smooth := ?_
    excess := ?_
  }⟩
  · intro n hn
    apply Classical.choice
    have hn' : n<U.card := by omega
    have hmem := binEnum_mem U hn'
    obtain ⟨w,hw,hjw⟩ := Finset.mem_biUnion.mp hmem
    apply (hbatch w hw J (fun w _ => hbounds w) (hsep w) _ hjw _)
    have hh := precedingFactors_enum_cost U hK hn' hUsep
    have hm := mul_le_mul_of_nonneg_right hcost (show (0:ℝ)≤2^(binEnum U n) by positivity)
    exact hh.trans (by convert hm using 1; ring)
  · intro n hn
    exact batchWordLength_dvd (binEnum_strictMono U (Nat.lt_succ_self n) (by omega)).le
  · intro n hn a ha'
    rw [hUlast,precedingFactors_enum_all]
    exact hsmooth _ (binEnum_mem U (by omega)) _ (binEnum_mem U (by omega)) a ha'
  · rw [hUlast,binEnum_sum U (fun j => c/(10000000*Real.log ((2:ℝ)^j)))]
    have hsum := allBins_rate J (Real.exp_pos (m:ℝ)) hc hJ (fun w _ => hdense w)
    have hcost' : ((U.card-1:ℕ):ℝ)*Real.exp (-Real.exp m)≤1 :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le U.card 1 : ((U.card-1:ℕ):ℝ)≤U.card)
        (Real.exp_nonneg _)).trans htotal
    have hh := hWrate.trans_le hsum
    linarith only [hcost',hh]

theorem finiteSieveEndpoint_proved : FiniteSieveEndpoint :=
  finiteSieve_of_certificates exists_sieveCertificate

theorem fullMain : MainEndpoint ∧ UniformEndpoint :=
  endpoints_of_finiteSieve finiteSieveEndpoint_proved

end GaussianMoat

end OAI
