import OAI.NumberTheory.GaussianMoat.WindowBatch

namespace OAI

namespace GaussianMoat

section
open scoped BigOperators Classical

noncomputable def binEnum (J : Finset ℕ) (n : ℕ) : ℕ :=
  if h : n<J.card then J.orderEmbOfFin rfl ⟨n,h⟩ else 0

lemma binEnum_eq (J : Finset ℕ) {n : ℕ} (hn : n<J.card) :
    binEnum J n=J.orderEmbOfFin rfl ⟨n,hn⟩ := by simp only [binEnum,dite_eq_left hn]

lemma binEnum_mem (J : Finset ℕ) {n : ℕ} (hn : n<J.card) : binEnum J n∈J := by
  rw [binEnum_eq J hn]
  exact J.orderEmbOfFin_mem rfl _

lemma binEnum_strictMono (J : Finset ℕ) {n k : ℕ} (hnk : n<k) (hk : k<J.card) :
    binEnum J n<binEnum J k := by
  rw [binEnum_eq J (hnk.trans hk),binEnum_eq J hk]
  exact (J.orderEmbOfFin rfl).strictMono hnk

lemma binEnum_surj (J : Finset ℕ) {j : ℕ} (hj : j∈J) :
    ∃ n<J.card, binEnum J n=j := by
  have hh : j∈Set.range (J.orderEmbOfFin rfl) := by rw [J.range_orderEmbOfFin rfl]; exact hj
  obtain ⟨i,hi⟩ := hh
  exact ⟨i.val,i.isLt,(binEnum_eq J i.isLt).trans hi⟩

lemma binEnum_sum (J : Finset ℕ) (f : ℕ → ℝ) :
    (∑ n∈Finset.range J.card, f (binEnum J n))=∑ j∈J, f j := by
  apply Finset.sum_bij (fun n _ => binEnum J n)
  · intro n hn; exact binEnum_mem J (Finset.mem_range.mp hn)
  · intro n hn k hk he
    have hn' := Finset.mem_range.mp hn
    have hk' := Finset.mem_range.mp hk
    rcases lt_trichotomy n k with h|h|h
    · exact (ne_of_lt (binEnum_strictMono J h hk') he).elim
    · exact h
    · exact (ne_of_lt (binEnum_strictMono J h hn') he.symm).elim
  · intro j hj
    obtain ⟨n,hn,he⟩ := binEnum_surj J hj
    exact ⟨n,Finset.mem_range.mpr hn,he⟩
  · intro n hn; rfl

lemma precedingFactors_enum_subset (J : Finset ℕ) {n : ℕ} (hn : n<J.card) :
    precedingFactors (fun k => dyadicSieve (binEnum J k)) n⊆
      (J.filter (·<binEnum J n)).biUnion (fun j => (dyadicSieve j).availableFactors) := by
  intro f hf
  obtain ⟨k,hk,hf⟩ := Finset.mem_biUnion.mp hf
  have hk' := Finset.mem_range.mp hk
  apply Finset.mem_biUnion.mpr
  exact ⟨binEnum J k,Finset.mem_filter.mpr ⟨binEnum_mem J (hk'.trans hn),binEnum_strictMono J hk' hn⟩,hf⟩

lemma precedingFactors_enum_cost (J : Finset ℕ) {K n : ℕ} (hK : 0<K) (hn : n<J.card)
    (hsep : ∀ a∈J, ∀ b∈J, a<b → a+K≤b) :
    residueWeight (precedingFactors (fun k => dyadicSieve (binEnum J k)) n)≤
      (4*Real.log 4/((2:ℝ)^K-1))*(2:ℝ)^(binEnum J n) := by
  apply (residueWeight_mono (precedingFactors_enum_subset J hn)).trans
  apply separated_factor_cost _ hK
  · intro a ha b hb hab
    exact hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
  · intro a ha
    exact hsep a (Finset.mem_filter.mp ha).1 (binEnum J n) (binEnum_mem J hn) (Finset.mem_filter.mp ha).2

lemma precedingFactors_enum_all (J : Finset ℕ) :
    precedingFactors (fun k => dyadicSieve (binEnum J k)) J.card=
      J.biUnion (fun j => (dyadicSieve j).availableFactors) := by
  ext f
  constructor
  · intro hf
    obtain ⟨k,hk,hf⟩ := Finset.mem_biUnion.mp hf
    exact Finset.mem_biUnion.mpr ⟨binEnum J k,binEnum_mem J (Finset.mem_range.mp hk),hf⟩
  · intro hf
    obtain ⟨j,hj,hf⟩ := Finset.mem_biUnion.mp hf
    obtain ⟨n,hn,he⟩ := binEnum_surj J hj
    exact Finset.mem_biUnion.mpr ⟨n,Finset.mem_range.mpr hn,by simpa only [he] using hf⟩

open scoped BigOperators Classical
open Filter

noncomputable def allBins (W : ℕ) (J : ℕ → Finset ℕ) : Finset ℕ :=
  (Finset.range W).biUnion J

lemma bin_window_gap {X : ℝ} {K u v i j : ℕ} (hX : 0<X)
    (hK : K*Real.log 2≤X) (huv : u<v)
    (hi : i*Real.log 2≤21/20*((100:ℝ)^u*X))
    (hj : (100:ℝ)^v*X≤j*Real.log 2) : i+K≤j := by
  have hp := mul_le_mul_of_nonneg_right (window_power_step huv) hX.le
  have ho := window_power_one u
  have hu : X≤(100:ℝ)^u*X := by nlinarith only [ho,hX]
  have hh : ((i+K:ℕ):ℝ)*Real.log 2≤(j:ℝ)*Real.log 2 := by
    push_cast
    nlinarith only [hp,hu,hK,hi,hj,hX]
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hn : (i+K:ℕ)≤(j:ℝ) := (mul_le_mul_iff_left₀ hl).mp hh
  exact_mod_cast hn

lemma allBins_separated {X : ℝ} {K W : ℕ} (J : ℕ → Finset ℕ) (hX : 0<X)
    (hK : K*Real.log 2≤X)
    (hb : ∀ w<W, ∀ j∈J w, (100:ℝ)^w*X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*((100:ℝ)^w*X))
    (hsep : ∀ w<W, ∀ i∈J w, ∀ j∈J w, i<j → i+K≤j) :
    ∀ i∈allBins W J, ∀ j∈allBins W J, i<j → i+K≤j := by
  intro i hi j hj hij
  obtain ⟨u,hu,hi⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨v,hv,hj⟩ := Finset.mem_biUnion.mp hj
  have hu' := Finset.mem_range.mp hu
  have hv' := Finset.mem_range.mp hv
  rcases lt_trichotomy u v with huv|rfl|hvu
  · exact bin_window_gap hX hK huv (hb u hu' i hi).2 (hb v hv' j hj).1
  · exact hsep u hu' i hi j hj hij
  · have hh := bin_window_gap hX hK hvu (hb v hv' j hj).2 (hb u hu' i hi).1
    omega

lemma bins_disjoint {X : ℝ} {W : ℕ} (J : ℕ → Finset ℕ) (hX : 0<X)
    (hb : ∀ w<W, ∀ j∈J w, (100:ℝ)^w*X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*((100:ℝ)^w*X)) :
    (↑(Finset.range W) : Set ℕ).PairwiseDisjoint J := by
  intro u hu v hv hne
  apply Finset.disjoint_left.mpr
  intro j hju hjv
  have hp (i k : ℕ) (hik : i<k) (hji : j∈J i) (hjk : j∈J k) (hi : i<W) (hk : k<W) : False := by
    have hh := mul_le_mul_of_nonneg_right (window_power_step hik) hX.le
    have hlo := (hb k hk j hjk).1
    have hhi := (hb i hi j hji).2
    have hz : 0<(100:ℝ)^k*X := by positivity
    nlinarith only [hh,hlo,hhi,hz]
  rcases lt_or_gt_of_ne hne with h|h
  · exact hp u v h hju hjv (Finset.mem_range.mp hu) (Finset.mem_range.mp hv)
  · exact hp v u h hjv hju (Finset.mem_range.mp hv) (Finset.mem_range.mp hu)

lemma allBins_card_upper {m W : ℕ} (J : ℕ → Finset ℕ) (hm : 2≤Real.exp m)
    (hb : ∀ w<W, ∀ j∈J w, j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) :
    ((allBins W J).card:ℝ)≤3*(W:ℝ)*(100:ℝ)^W*Real.exp m := by
  have hh := Finset.card_biUnion_le (s := Finset.range W) (t := J)
  have hs : (∑ w∈Finset.range W, ((J w).card:ℝ))≤(W:ℝ)*(3*(100:ℝ)^W*Real.exp m) := by
    calc
      _ ≤ ∑ w∈Finset.range W, 3*(100:ℝ)^W*Real.exp m := by
        apply Finset.sum_le_sum
        intro w hw
        have hw' := Finset.mem_range.mp hw
        have hp := window_power_one w
        have he : 2≤(100:ℝ)^w*Real.exp m := by nlinarith only [hp,hm]
        have hc := narrow_bins_card he (J w) (hb w hw')
        have hp' := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤100) hw'.le) (Real.exp_nonneg (m:ℝ))
        nlinarith only [hc,hp']
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hh' : ((allBins W J).card:ℝ)≤∑ w∈Finset.range W, ((J w).card:ℝ) := by exact_mod_cast hh
  nlinarith only [hh',hs]

lemma allBins_rate {X c t : ℝ} {W : ℕ} (J : ℕ → Finset ℕ) (hX : 0<X) (hc : 0<c)
    (hb : ∀ w<W, ∀ j∈J w, (100:ℝ)^w*X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*((100:ℝ)^w*X))
    (hdense : ∀ w<W, t*((100:ℝ)^w*X)≤(J w).card) :
    (W:ℝ)*(c*t/10500000)≤∑ j∈allBins W J, c/(10000000*Real.log ((2:ℝ)^j)) := by
  rw [allBins,Finset.sum_biUnion (bins_disjoint J hX hb)]
  have hs : ∀ w<W, c*t/10500000≤∑ j∈J w, c/(10000000*Real.log ((2:ℝ)^j)) := by
    intro w hw
    have hwX : 0<(100:ℝ)^w*X := by positivity
    have hl : ∀ j∈J w, 0<Real.log ((2:ℝ)^j) := by
      intro j hj; rw [Real.log_pow]; exact hwX.trans_le (hb w hw j hj).1
    have ht' := hdense w hw
    have hh : (J w).card*(c/(10500000*((100:ℝ)^w*X)))≤∑ j∈J w, c/(10000000*Real.log ((2:ℝ)^j)) := by
      calc
        _ = ∑ _j∈J w, c/(10500000*((100:ℝ)^w*X)) := by simp only [Finset.sum_const,nsmul_eq_mul]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j hj
          apply div_le_div_of_nonneg_left hc.le (by have := hl j hj; positivity : 0<10000000*Real.log ((2:ℝ)^j))
          rw [Real.log_pow]
          nlinarith only [(hb w hw j hj).2]
    have hm := mul_le_mul_of_nonneg_right ht' (show 0≤c/(10500000*((100:ℝ)^w*X)) by positivity)
    have he : t*((100:ℝ)^w*X)*(c/(10500000*((100:ℝ)^w*X)))=c*t/10500000 := by field_simp
    rw [he] at hm
    exact hm.trans hh
  have hh := Finset.sum_le_sum (s := Finset.range W) (fun w hw => hs w (Finset.mem_range.mp hw))
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using hh

end

open scoped BigOperators Classical
open Filter

lemma exists_separated_parameters : ∃ a δ t : ℝ, ∃ K : ℕ,
    0<a ∧ a≤1 ∧ 2*a≤δ ∧ 0<t ∧ 0<K ∧
    a≤(2:ℝ)^K*topCoefficient a ∧
    4*Real.log 4/((2:ℝ)^K-1)≤(topCoefficient a/4)/10000 ∧
    ∀ᶠ X : ℝ in atTop, ∃ J : Finset ℕ,
      t*X≤J.card ∧ (∀ i∈J, ∀ j∈J, i<j → i+K≤j) ∧
      ∀ j∈J, X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*X ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(PrimeLogMass.dyadicBatch j).card := by
  obtain ⟨c,δ,hc,hδ,he⟩ := PrimeLogMass.eventually_dense_split_bins
  let a := min (δ/4) 1
  have ha : 0<a := lt_min (by positivity) (by norm_num)
  have ha1 : a≤1 := min_le_right _ _
  have haδ : 2*a≤δ := by have := min_le_left (δ/4) 1; dsimp only [a]; linarith only [this,hδ]
  have hv : 0<topCoefficient a := topCoefficient_pos ha
  have powtop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)
  have hn := powtop.eventually (eventually_ge_atTop (max (a/topCoefficient a) (1+160000*Real.log 4/topCoefficient a)))
  obtain ⟨K,hK,hpow⟩ := (eventually_gt_atTop 0 |>.and hn).exists
  have hlo := (le_max_left _ _).trans hpow
  have hhi := (le_max_right _ _).trans hpow
  have hgap : a≤(2:ℝ)^K*topCoefficient a := (div_le_iff₀ hv).mp hlo
  have hden : 0<(2:ℝ)^K-1 := by
    have := one_lt_pow₀ (by norm_num : (1:ℝ)<2) (by omega : K≠0)
    linarith only [this]
  have hcost : 4*Real.log 4/((2:ℝ)^K-1)≤(topCoefficient a/4)/10000 := by
    have hh : 160000*Real.log 4≤((2:ℝ)^K-1)*topCoefficient a := by
      apply (div_le_iff₀ hv).mp
      linarith only [hhi]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hh]
  refine ⟨a,δ,c/K,K,ha,ha1,haδ,div_pos hc (by exact_mod_cast hK),hK,hgap,hcost,?_⟩
  filter_upwards [he] with X hX
  obtain ⟨J,hJ,hp⟩ := hX
  obtain ⟨b,_,hcard,hsep⟩ := thin_bins J hK
  refine ⟨J.filter (fun j => j%K=b),?_,hsep,?_⟩
  · have hh := (div_le_div_of_nonneg_right hJ (Nat.cast_nonneg K)).trans hcard
    simpa only [div_mul_eq_mul_div] using hh
  · intro j hj
    exact hp j (Finset.mem_filter.mp hj).1

end GaussianMoat

end OAI
