import OAI.NumberTheory.GaussianMoat.AccurateScales

namespace OAI

universe uIota

namespace GaussianMoat

section
open scoped BigOperators Classical
open Filter

noncomputable def topParameter : ℝ := 1/1000000
def topIterations : ℕ := 20
noncomputable def topCoefficient (a : ℝ) : ℝ := (topParameter^2)^topIterations*a

lemma topParameter_pos : 0<topParameter := by norm_num [topParameter]
lemma topParameter_small : topParameter≤1/200 := by norm_num [topParameter]
lemma topCoefficient_pos {a : ℝ} (ha : 0<a) : 0<topCoefficient a := by
  unfold topCoefficient; exact mul_pos (pow_pos (sq_pos_of_pos topParameter_pos) _) ha
lemma top_deficit : (1/2:ℝ)^topIterations+90*topParameter≤1/10000 := by
  norm_num [topParameter,topIterations]

theorem eventually_top_band {D a δ : ℝ} (hD : 1≤D) (ha : 0<a)
    (haδ : 2*a≤δ) :
    ∀ᶠ x : ℝ in atTop, ∀ (s : SplitSieve) (pre post : List ℕ),
      s.primes.Nonempty →
      (∀ p∈s.primes, Real.exp x≤(p:ℝ) ∧ (p:ℝ)≤2*Real.exp x) →
      δ*Real.exp x/Real.log (2*Real.exp x)≤ s.primes.card →
      (∀ n∈post, (n:ℝ)≤Real.exp (topParameter*topCoefficient a*Real.exp x)) →
      (post.length+2:ℝ)≤Real.exp (topParameter*topCoefficient a*Real.exp x) →
      Nonempty (EntropyBand s D
        (pre++List.ofFn (fun i : Fin topIterations =>
          bandLength topParameter (a*Real.exp x) i.val)++post)
        0 (bandSize s topParameter (a*Real.exp x) topIterations) (1/10000)) ∧
      topCoefficient a*Real.exp x/(4*x)≤
        (bandSize s topParameter (a*Real.exp x) topIterations:ℝ) := by
  have hc := topCoefficient_pos ha
  have hlarge := eventually_poly_le_exp (2*bandConstant D)
    (a := topParameter^5*topCoefficient a) (mul_pos (pow_pos topParameter_pos _) hc) 1
  filter_upwards [hlarge,eventually_ge_atTop (2:ℝ)] with x hlarge hx
  intro s pre post hne hp hdense hpost hlen
  have hT2 : 2≤Real.exp x := by linarith only [Real.add_one_le_exp x,hx]
  have hm := s.meanLog_bounds hne (Real.exp_pos x) hp
  rw [Real.log_exp] at hm
  have hmean : 1≤ s.meanLog := by linarith only [hm.1,hx]
  have hmean0 : 0< s.meanLog := by linarith only [hmean]
  have hlog2 : Real.log 2≤x := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith only [hh,hx]
  have hmean' : s.meanLog≤2*x := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp] at hm
    linarith only [hm.2,hlog2]
  have hscale : bandScale topParameter (a*Real.exp x) topIterations=topCoefficient a*Real.exp x := by
    unfold bandScale topCoefficient; ring
  have hmargin : bandConstant D*s.meanLog≤topParameter^5*
      bandScale topParameter (a*Real.exp x) topIterations := by
    have hh := mul_le_mul_of_nonneg_left hmean' (bandConstant_pos D).le
    rw [hscale]
    simp only [pow_one] at hlarge
    nlinarith only [hh,hlarge]
  have hcap := dense_sieve_cap s hne hT2 hp hdense
    (by nlinarith only [haδ,Real.exp_pos x] : 2*(a*Real.exp x)≤δ*Real.exp x)
  have hband := entropyBand_from_margin s pre post 0 topIterations hD topParameter_pos
    topParameter_small (mul_pos ha (Real.exp_pos _)) hmean hmargin hcap
    (by simpa only [hscale,mul_assoc] using hpost)
    (by simp only [Nat.cast_zero]; positivity)
    (by simpa only [hscale,mul_assoc] using hlen) top_deficit
  refine ⟨hband,?_⟩
  have hg5 : topParameter^5≤1 := pow_le_one₀ topParameter_pos.le (by norm_num [topParameter])
  have hVpos := bandScale_pos topParameter_pos (mul_pos ha (Real.exp_pos x)) topIterations
  have hn := mul_le_mul_of_nonneg_right hg5 hVpos.le
  have hC : 2≤bandConstant D := by
    unfold bandConstant
    linarith only [abs_nonneg (Real.log D),abs_nonneg (Real.log (max D ((latticeBall (4*D)).card:ℝ)))]
  have hm2 := mul_le_mul_of_nonneg_right hC hmean0.le
  have hV : 2*s.meanLog≤bandScale topParameter (a*Real.exp x) topIterations := by
    nlinarith only [hmargin,hn,hm2]
  have hh := bandSize_lower_of_scale hmean0
    (show 0<Real.log (Real.exp x) by rw [Real.log_exp]; linarith only [hx])
    (by simpa only [Real.log_exp] using hmean') hV (le_of_eq hscale.symm)
  simpa only [Real.log_exp] using hh

end

open scoped BigOperators Classical

noncomputable def topBlock (a : ℝ) (j : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin topIterations => bandLength topParameter (a*(2:ℝ)^j) i.val)

noncomputable def topBlocks (a : ℝ) (J : Finset ℕ) : List ℕ :=
  (J.sort (·≥·)).flatMap (topBlock a)

noncomputable def accurateBlock (m : ℕ) (a : ℝ) : List ℕ :=
  List.ofFn (fun i : Fin (accurateIterations m) =>
    bandLength (accurateGrid m) (Real.exp (a*Real.exp m)) i.val)

lemma topBlocks_length (a : ℝ) (J : Finset ℕ) :
    (topBlocks a J).length=J.card*topIterations := by
  unfold topBlocks
  rw [List.length_flatMap]
  simp only [topBlock,List.length_ofFn,List.map_const',List.sum_replicate,Finset.length_sort,
    smul_eq_mul]

lemma topBlock_bound {a H : ℝ} (ha : 0≤a) (j : ℕ)
    (h : topParameter*a*(2:ℝ)^j≤H) :
    ∀ n∈topBlock a j, (n:ℝ)≤Real.exp H := by
  intro n hn
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hn
  exact (bandLength_le_exp_start topParameter_pos.le
    (by norm_num [topParameter]) (mul_nonneg ha (by positivity)) i.val).trans
    (Real.exp_le_exp.mpr (by simpa only [mul_assoc] using h))

lemma accurateBlock_bound {a H : ℝ} {m : ℕ} (hg : accurateGrid m≤1)
    (h : accurateGrid m*Real.exp (a*Real.exp m)≤H) :
    ∀ n∈accurateBlock m a, (n:ℝ)≤Real.exp H := by
  intro n hn
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hn
  exact (bandLength_le_exp_start (accurateGrid_pos m).le hg (Real.exp_nonneg _) i.val).trans
    (Real.exp_le_exp.mpr h)

lemma sorted_split {J : Finset ℕ} {j : ℕ} (hj : j∈J) :
    ∃ pre post : List ℕ, J.sort (·≥·)=pre++j::post ∧
      (∀ i∈post, i∈J ∧ i < j) ∧ (∀ i∈pre, i∈J ∧ j < i) := by
  have hm : j∈J.sort (·≥·) := (Finset.mem_sort (·≥·)).mpr hj
  obtain ⟨pre,post,he⟩ := List.mem_iff_append.mp hm
  have hp : (J.sort (·≥·)).Pairwise (·>·) := by
    exact (Finset.sortedGT_sort J).pairwise
  rw [he,List.pairwise_append,List.pairwise_cons] at hp
  refine ⟨pre,post,he,?_,?_⟩
  · intro i hi
    refine ⟨(Finset.mem_sort (·≥·)).mp ?_,hp.2.1.1 i hi⟩
    rw [he]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hi)
  · intro i hi
    refine ⟨(Finset.mem_sort (·≥·)).mp ?_,hp.2.2 i hi j (List.mem_cons_self ..)⟩
    rw [he]; exact List.mem_append_left _ hi

lemma topBlocks_split {a : ℝ} {J : Finset ℕ} {j : ℕ} (hj : j∈J) :
    ∃ pre post : List ℕ, topBlocks a J=pre++topBlock a j++post ∧
      post.length≤J.card*topIterations ∧
      (∀ n∈post, ∃ i∈J, i<j ∧ n∈topBlock a i) := by
  obtain ⟨A,B,he,hB,_⟩ := sorted_split hj
  refine ⟨A.flatMap (topBlock a),B.flatMap (topBlock a),?_,?_,?_⟩
  · simp only [topBlocks,he,List.flatMap_append,List.flatMap_cons,List.append_assoc]
  · have hh : (B.flatMap (topBlock a)).length≤(topBlocks a J).length := by
      simp only [topBlocks,he,List.flatMap_append,List.flatMap_cons,List.length_append]
      omega
    simpa only [topBlocks_length] using hh
  · intro n hn
    obtain ⟨i,hi,hn⟩ := List.mem_flatMap.mp hn
    exact ⟨i,(hB i hi).1,(hB i hi).2,hn⟩

noncomputable def windowBlocks (a : ℝ) (m : ℕ) (J : ℕ → Finset ℕ) (W : ℕ) : List ℕ :=
  ((List.range W).reverse).flatMap (fun w =>
    topBlocks a (J w)++accurateBlock m ((100:ℝ)^w/4))

lemma windowBlocks_succ (a : ℝ) (m : ℕ) (J : ℕ → Finset ℕ) (W : ℕ) :
    windowBlocks a m J (W+1)=topBlocks a (J W)++accurateBlock m ((100:ℝ)^W/4)++
      windowBlocks a m J W := by
  simp only [windowBlocks,List.range_succ,List.reverse_append,List.reverse_singleton,
    List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]

lemma windowBlocks_split (a : ℝ) (m : ℕ) (J : ℕ → Finset ℕ) {W w : ℕ} (hw : w<W) :
    ∃ pre, windowBlocks a m J W=pre++topBlocks a (J w)++
      accurateBlock m ((100:ℝ)^w/4)++windowBlocks a m J w := by
  induction W with
  | zero => omega
  | succ W ih =>
    rw [windowBlocks_succ]
    by_cases he : w=W
    · subst w; exact ⟨[],by simp only [List.nil_append]⟩
    · obtain ⟨pre,hp⟩ := ih (by omega)
      rw [hp]
      exact ⟨topBlocks a (J W)++accurateBlock m ((100:ℝ)^W/4)++pre,by simp only [List.append_assoc]⟩

lemma windowBlocks_mem (a : ℝ) (m : ℕ) (J : ℕ → Finset ℕ) {W n : ℕ}
    (hn : n∈windowBlocks a m J W) :
    ∃ w<W, n∈topBlocks a (J w) ∨ n∈accurateBlock m ((100:ℝ)^w/4) := by
  obtain ⟨w,hw,hn⟩ := List.mem_flatMap.mp hn
  exact ⟨w,List.mem_range.mp (List.mem_reverse.mp hw),List.mem_append.mp hn⟩

theorem separated_power_sum (J : Finset ℕ) {K j : ℕ} (hK : 0<K)
    (hsep : ∀ a∈J, ∀ b∈J, a<b → a+K≤b)
    (hcap : ∀ a∈J, a+K≤j) :
    (∑ a∈J, (2:ℝ)^a)≤(2:ℝ)^j/((2:ℝ)^K-1) := by
  have hden : 0<(2:ℝ)^K-1 := by
    have hh := one_lt_pow₀ (by norm_num : (1:ℝ)<2) (by omega : K≠0)
    linarith only [hh]
  induction J using Finset.induction_on_max generalizing j with
  | empty => simp only [Finset.sum_empty]; positivity
  | @insert a J hmax ih =>
    have ha : a∉J := fun h => (lt_irrefl a) (hmax a h)
    have hci : ∀ b∈J, b+K≤a := by
      intro b hb
      exact hsep b (Finset.mem_insert_of_mem hb) a (Finset.mem_insert_self ..)
        (hmax b hb)
    have hi := ih (fun b hb c hc hbc => hsep b (Finset.mem_insert_of_mem hb)
      c (Finset.mem_insert_of_mem hc) hbc) hci
    rw [Finset.sum_insert ha]
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (hcap a (Finset.mem_insert_self ..))
    have hd := (div_le_div_iff_of_pos_right hden).mpr hp
    rw [pow_add] at hd
    have he : (2:ℝ)^a+(2:ℝ)^a/((2:ℝ)^K-1)=(2:ℝ)^a*2^K/(2^K-1) := by
      field_simp; ring
    exact (add_le_add (le_refl ((2:ℝ)^a)) hi).trans (he ▸ hd)

lemma residueWeight_union_le (F G : Finset GaussianInt) :
    residueWeight (F∪G)≤residueWeight F+residueWeight G := by
  classical
  have hh := Finset.sum_union_inter (s₁ := F) (s₂ := G) (f := fun f : GaussianInt => Real.log f.norm.natAbs)
  change residueWeight (F∪G)+residueWeight (F∩G)=residueWeight F+residueWeight G at hh
  linarith only [hh,residueWeight_nonneg (F∩G)]

lemma residueWeight_biUnion_le {ι : Type uIota} (J : Finset ι) (F : ι → Finset GaussianInt) :
    residueWeight (J.biUnion F)≤∑ j∈J, residueWeight (F j) := by
  induction J using Finset.induction_on with
  | empty => simp [residueWeight]
  | @insert j J hj ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert hj]
    exact (residueWeight_union_le _ _).trans (add_le_add (le_refl _) ih)

lemma separated_factor_cost (J : Finset ℕ) {K j : ℕ} (hK : 0<K)
    (hsep : ∀ a∈J, ∀ b∈J, a<b → a+K≤b)
    (hcap : ∀ a∈J, a+K≤j) :
    residueWeight (J.biUnion (fun a => (dyadicSieve a).availableFactors))≤
      (4*Real.log 4/((2:ℝ)^K-1))*(2:ℝ)^j := by
  have hsum := Finset.sum_le_sum (fun a (_ : a∈J) => dyadicSieve_available_weight a)
  rw [←Finset.mul_sum] at hsum
  have hh := mul_le_mul_of_nonneg_left (separated_power_sum J hK hsep hcap)
    (show 0≤4*Real.log 4 by positivity)
  have ht := (residueWeight_biUnion_le J (fun a => (dyadicSieve a).availableFactors)).trans (hsum.trans hh)
  calc
    _ ≤ 4*Real.log 4*((2:ℝ)^j/(2^K-1)) := ht
    _ = _ := by ring

open scoped BigOperators Classical
open Filter

lemma log_two_lower : (1/2:ℝ)≤Real.log 2 := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at hh
  exact hh

lemma narrow_bins_card {X : ℝ} (hX : 2≤X) (J : Finset ℕ)
    (hJ : ∀ j∈J, (j:ℝ)*Real.log 2≤21/20*X) :
    (J.card:ℝ)≤3*X := by
  have hj : ∀ j∈J, (j:ℝ)≤21/10*X := by
    intro j hj
    have hh := mul_le_mul_of_nonneg_left log_two_lower (Nat.cast_nonneg j)
    linarith only [hh,hJ j hj]
  have hs : J⊆Finset.range (⌊21/10*X⌋₊+1) := by
    intro j hj'
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le ((Nat.le_floor_iff (by positivity)).mpr (hj j hj'))
  have hc : (J.card:ℝ)≤(⌊21/10*X⌋₊:ℝ)+1 := by
    exact_mod_cast (Finset.card_le_card hs).trans_eq (Finset.card_range _)
  have hf := Nat.floor_le (show 0≤21/10*X by linarith only [hX])
  linarith only [hc,hf,hX]

lemma topBlock_separated {a : ℝ} (ha : 0<a) {i j K : ℕ}
    (hgap : a≤(2:ℝ)^K*topCoefficient a) (hij : i+K≤j) :
    ∀ n∈topBlock a i, (n:ℝ)≤Real.exp (topParameter*topCoefficient a*(2:ℝ)^j) := by
  apply topBlock_bound ha.le
  have hh := mul_le_mul_of_nonneg_left hgap (show 0≤(2:ℝ)^i by positivity)
  rw [←mul_assoc,←pow_add] at hh
  have hp : (2:ℝ)^(i+K)≤(2:ℝ)^j := pow_le_pow_right₀ (by norm_num) hij
  have hp' := mul_le_mul_of_nonneg_right hp (topCoefficient_pos ha).le
  have hg := mul_le_mul_of_nonneg_left (hh.trans hp') topParameter_pos.le
  nlinarith only [hg]

theorem eventually_window_top {D a δ : ℝ} {K : ℕ}
    (hD : 1≤D) (ha : 0<a) (haδ : 2*a≤δ)
    (hgap : a≤(2:ℝ)^K*topCoefficient a) :
    ∀ᶠ X : ℝ in atTop, ∀ (J : Finset ℕ) (initial : List ℕ),
      (∀ i∈J, ∀ j∈J, i<j → i+K≤j) →
      (∀ j∈J, X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*X ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(PrimeLogMass.dyadicBatch j).card) →
      ∀ j∈J, Nonempty (EntropyBand (dyadicSieve j) D (initial++topBlocks a J)
        0 (bandSize (dyadicSieve j) topParameter (a*(2:ℝ)^j) topIterations) (1/10000)) ∧
        topCoefficient a*(2:ℝ)^j/(4*Real.log ((2:ℝ)^j))≤
          (bandSize (dyadicSieve j) topParameter (a*(2:ℝ)^j) topIterations:ℝ) := by
  have hδ : 0<δ := by linarith only [ha,haδ]
  have htop := eventually_top_band hD ha haδ
  have hlen := eventually_poly_le_exp (100:ℝ)
    (a := topParameter*topCoefficient a) (mul_pos topParameter_pos (topCoefficient_pos ha)) 1
  obtain ⟨x0,h0⟩ := eventually_atTop.mp (htop.and hlen)
  filter_upwards [eventually_ge_atTop (max x0 2)] with X hX
  intro J initial hsep hJ j hj
  have hX2 : 2≤X := (le_max_right _ _).trans hX
  have hX0 : x0≤X := (le_max_left _ _).trans hX
  have hlog := (hJ j hj).1
  have hlog' := (hJ j hj).2.1
  obtain ⟨hband,hlen⟩ := h0 (j*Real.log 2) (hX0.trans hlog)
  have hn : (dyadicSieve j).primes.Nonempty := by
    apply Finset.card_pos.mp
    have hlogp : 0<Real.log ((2:ℝ)^(j+1)) := by
      rw [Real.log_pow]
      positivity
    have hh := (hJ j hj).2.2
    have hp : 0<δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1)) := div_pos (by positivity) hlogp
    have hc : (0:ℝ)<(PrimeLogMass.dyadicBatch j).card := hp.trans_le hh
    exact_mod_cast hc
  obtain ⟨pre,post,he,hpl,hpm⟩ := topBlocks_split (a := a) hj
  have hT : Real.exp (j*Real.log 2)=(2:ℝ)^j := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  have hcard := narrow_bins_card hX2 J (fun i hi => (hJ i hi).2.1)
  have hlen' : (post.length+2:ℝ)≤Real.exp (topParameter*topCoefficient a*(2:ℝ)^j) := by
    have hp : (post.length:ℝ)≤(J.card:ℝ)*topIterations := by exact_mod_cast hpl
    simp only [pow_one,hT] at hlen
    have he := Real.add_one_le_exp (topParameter*topCoefficient a*(2:ℝ)^j)
    norm_num only [topIterations,Nat.cast_ofNat] at hp
    nlinarith only [hp,hcard,hlen,he,hlog,hX2]
  have hprime : ∀ p∈(dyadicSieve j).primes, Real.exp (j*Real.log 2)≤(p:ℝ) ∧
      (p:ℝ)≤2*Real.exp (j*Real.log 2) := by
    intro p hp
    rw [hT]
    have hh := (PrimeLogMass.mem_dyadicBatch j p).mp hp
    constructor
    · exact_mod_cast hh.1
    · have hh' : p≤2^(j+1) := hh.2.1.le
      rw [pow_succ] at hh'
      exact_mod_cast (by simpa only [mul_comm] using hh' : p≤2*2^j)
  have hdense : δ*Real.exp (j*Real.log 2)/Real.log (2*Real.exp (j*Real.log 2))≤
      (dyadicSieve j).primes.card := by
    change δ*Real.exp (j*Real.log 2)/Real.log (2*Real.exp (j*Real.log 2))≤
      (PrimeLogMass.dyadicBatch j).card
    simpa only [hT,pow_succ,mul_comm] using (hJ j hj).2.2
  have hpst : ∀ n∈post, (n:ℝ)≤Real.exp (topParameter*topCoefficient a*Real.exp (j*Real.log 2)) := by
    intro n hnp
    obtain ⟨i,hi,hij,hni⟩ := hpm n hnp
    rw [hT]
    exact topBlock_separated ha hgap (hsep i hi j hj hij) n hni
  obtain ⟨hb,hbsize⟩ := hband (dyadicSieve j) (initial++pre) post hn hprime hdense hpst
    (by simpa only [hT] using hlen')
  refine ⟨?_,?_⟩
  · simpa only [hT,he,topBlock,List.append_assoc] using hb
  · simpa only [hT,Real.log_pow] using hbsize

end GaussianMoat

end OAI
