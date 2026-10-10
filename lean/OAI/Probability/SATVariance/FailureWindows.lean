import OAI.Probability.SATVariance.BystanderVariance

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma finiteSAT_probability {n k M m : ℕ} (hkn : k ≤ n) (hm : m ≤ M) :
    favg (fun w : Fin M → Clause n k => if finiteSAT w m then (1:ℝ) else 0) =
      (streamLaw n k {ω | PrefixSAT ω m}).toReal := by
  have hp : Measurable (fun ω : Stream n k => fun j : Fin M => ω j) :=
    Measurable.of_eval (fun j => measurable_pi_apply j.val)
  have he : favg (fun w : Fin M → Clause n k => if finiteSAT w m then (1:ℝ) else 0) =
      (uniformOn Set.univ {w : Fin M → Clause n k | finiteSAT w m}).toReal := by
    simpa only [Set.mem_ofPred_eq] using
      (uniformOn_real {w : Fin M → Clause n k | finiteSAT w m}).symm
  rw [he,← prefixLaw hkn M,Measure.map_apply hp (Set.toFinite _).measurableSet]
  congr 2
  ext ω
  exact finiteSAT_stream ω hm

lemma finiteNotSAT_probability {n k M m : ℕ} (hkn : k ≤ n) (hm : m ≤ M) :
    favg (fun w : Fin M → Clause n k => if ¬finiteSAT w m then (1:ℝ) else 0) =
      (streamLaw n k {ω | ¬PrefixSAT ω m}).toReal := by
  have hp : Measurable (fun ω : Stream n k => fun j : Fin M => ω j) :=
    Measurable.of_eval (fun j => measurable_pi_apply j.val)
  have he : favg (fun w : Fin M → Clause n k => if ¬finiteSAT w m then (1:ℝ) else 0) =
      (uniformOn Set.univ {w : Fin M → Clause n k | ¬finiteSAT w m}).toReal := by
    rw [uniformOn_real]
    congr 1
    funext w
    by_cases h : finiteSAT w m <;> simp [h]
  rw [he,← prefixLaw hkn M,Measure.map_apply hp (Set.toFinite _).measurableSet]
  congr 2
  ext ω
  exact not_congr (finiteSAT_stream ω hm)

lemma finiteSAT_high_tail {n k M m : ℕ} (hkn : k ≤ n) (hm : m ≤ M) :
    favg (fun w : Fin M → Clause n k => if finiteSAT w m then (1:ℝ) else 0) ≤
      (2:ℝ)^n*(1-((2:ℝ)^k)⁻¹)^m := by
  rw [finiteSAT_probability hkn hm]
  have hh := ENNReal.toReal_mono (by finiteness) (first_moment_tail hkn m)
  simpa only [lt_firstFailure_iff,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofNat,rate_toReal] using hh

lemma finiteSAT_low_tail {n k M m : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (hm : m ≤ M)
    {a : ℝ} (ha : 0 ≤ a) (ha' : Real.exp 2*a ≤ 1/2) (hm' : (m:ℝ) ≤ a*n) :
    favg (fun w : Fin M → Clause n k => if ¬finiteSAT w m then (1:ℝ) else 0) ≤ 2*a := by
  rw [finiteNotSAT_probability hkn hm,← finiteNotSAT_probability hkn (le_refl m)]
  exact hall_probability_bound hk hkn ha ha' hm'

lemma cap_variance_finite {n k : ℕ} (hkn : k ≤ n) (B : ℝ) :
    variance (T B : Stream n k → ℝ) (streamLaw n k) =
      fvariance (finiteTime (n := n) (k := k) (L := cap n B)) := by
  let := clause_nonempty n k hkn
  have hm : Measurable (fun ω : Stream n k => fun j : Fin (cap n B) => ω j) :=
    Measurable.of_eval (fun j => measurable_pi_apply j.val)
  have he : (T B : Stream n k → ℝ) =
      finiteTime ∘ (fun ω : Stream n k => fun j : Fin (cap n B) => ω j) := by
    funext ω
    exact (finiteTime_stream ω).symm
  rw [he, ← variance_map (measurable_of_countable finiteTime).aemeasurable hm.aemeasurable,
    prefixLaw hkn,variance_uniform]

lemma outsideWindow_bound {n k M Q V : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (hQ : 2*Q ≤ M) (hV : V ≤ M) {a : ℝ} (ha : 0 ≤ a)
    (ha' : Real.exp 2*a ≤ 1/2) (hQa : (2*Q:ℕ) ≤ a*n) :
    favg (fun w : Fin M → Clause n k => outsideWindow Q V (List.ofFn w)) ≤
      2*a+(2:ℝ)^n*(1-((2:ℝ)^k)⁻¹)^V := by
  have hh (w : Fin M → Clause n k) : outsideWindow Q V (List.ofFn w) ≤
      (if ¬finiteSAT w (2*Q) then (1:ℝ) else 0)+(if finiteSAT w V then 1 else 0) := by
    have hlow := lt_listStop_ofFn_iff w hQ
    have hhigh := lt_listStop_ofFn_iff w hV
    by_cases ha : finiteSAT w (2*Q) <;> by_cases hb : finiteSAT w V <;>
      simp only [outsideWindow,ha,hb,not_true_eq_false,not_false_eq_true,ite_true,ite_false] <;>
      split_ifs <;> norm_num
    simp_all
    omega
  have havg := favg_mono hh
  rw [favg_add] at havg
  exact havg.trans (add_le_add (finiteSAT_low_tail hk hkn hQ ha ha' hQa)
    (finiteSAT_high_tail hkn hV))

lemma floor_window_bounds {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {n R : ℕ} (hR : 1 ≤ R) (hn : 8 ≤ a*n) :
    let Q := ⌊a*n/4⌋₊
    (a*n/8 ≤ (Q:ℝ)) ∧ ((Q:ℝ) ≤ a*n/4) ∧
      2*Q ≤ 2*R*n ∧ Q+R*n ≤ 2*R*n+1 ∧ Q ≤ 2*R*n ∧
      a/(16*((2*R:ℕ)+1:ℝ)^2) ≤
        (Q:ℝ)*((2*R*n:ℕ)+1-Q-R*n:ℝ)/((2*R*n:ℕ)+1:ℝ)^2 := by
  dsimp only
  let Q := ⌊a*n/4⌋₊
  have hn0 : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    norm_num [this] at hn
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hRR : (1:ℝ) ≤ R := by exact_mod_cast hR
  have hQup : (Q:ℝ) ≤ a*n/4 := Nat.floor_le (by positivity)
  have hQlo : a*n/8 ≤ (Q:ℝ) := by
    have hh := Nat.lt_floor_add_one (a*n/4)
    change a*n/4 < (Q:ℝ)+1 at hh
    linarith
  have haN := mul_le_mul_of_nonneg_right ha1 hnR.le
  have hRn : (n:ℝ) ≤ R*n := by nlinarith
  have h2Q : 2*Q ≤ 2*R*n := by
    have : 2*(Q:ℝ) ≤ 2*R*n := by nlinarith
    exact_mod_cast this
  have hQV : Q+R*n ≤ 2*R*n+1 := by
    have : (Q:ℝ)+R*n ≤ 2*R*n+1 := by nlinarith
    exact_mod_cast this
  refine ⟨hQlo,hQup,h2Q,hQV,by omega,?_⟩
  have hgap : (n:ℝ)/2 ≤ (2*R*n:ℕ)+1-Q-R*n := by
    push_cast
    nlinarith
  have hden : (2*R*n:ℕ)+1 ≤ ((2*R:ℕ)+1:ℝ)*n := by
    push_cast
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn0
    nlinarith
  have hd0 : (0:ℝ) < (2*R*n:ℕ)+1 := by positivity
  have hd1 : (0:ℝ) < ((2*R:ℕ)+1:ℝ) := by positivity
  have hnum : a*n^2/16 ≤ (Q:ℝ)*((2*R*n:ℕ)+1-Q-R*n:ℝ) := by
    have hh := mul_le_mul hQlo hgap (by positivity) (by positivity : (0:ℝ) ≤ Q)
    nlinarith
  have hsden : ((2*R*n:ℕ)+1:ℝ)^2 ≤ (((2*R:ℕ)+1:ℝ)*n)^2 :=
    pow_le_pow_left₀ hd0.le hden 2
  apply (le_div_iff₀ (sq_pos_of_pos hd0)).mpr
  have hcoef0 : 0 ≤ a/(16*((2*R:ℕ)+1:ℝ)^2) := by positivity
  apply le_trans (mul_le_mul_of_nonneg_left hsden hcoef0)
  calc
    a/(16*((2*R:ℕ)+1:ℝ)^2)*(((2*R:ℕ)+1:ℝ)*n)^2 = a*n^2/16 := by field_simp
    _ ≤ _ := hnum

lemma positive_linear_absorb (d : ℝ) (hd : 0 < d) (K : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K ≤ d*n := by
  obtain ⟨N,hN⟩ := exists_nat_gt (K/d)
  refine ⟨N,fun n hn => ?_⟩
  have hN' : (N:ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [(div_lt_iff₀ hd).mp (hN.trans_le hN')]

lemma eventual_geometric_small {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → r^n ≤ ε := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1
  have he : ∀ᶠ n : ℕ in Filter.atTop, r^n < ε := ht.eventually (gt_mem_nhds hε)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp he
  exact ⟨N,fun n hn => (hN n hn).le⟩

lemma exists_lower_scale (k : ℕ) (hk : 1 ≤ k) :
    ∃ R : ℕ, 1 ≤ R ∧ U k ≤ 2*(R:ℝ) ∧ 2*(1-((2:ℝ)^k)⁻¹)^R < 1 := by
  obtain ⟨N,hN⟩ := eventual_geometric_small (real_rate_pos hk).le
    (real_rate_lt_one k) (by norm_num : (0:ℝ) < 1/4)
  obtain ⟨L,hL⟩ := exists_nat_gt (U k)
  let R := max N (max L 1)
  have hRN : N ≤ R := le_max_left _ _
  have hRL : L ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hR1 : 1 ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨R,hR1,?_,by linarith [hN R hRN]⟩
  have hLR : (L:ℝ) ≤ R := by exact_mod_cast hRL
  have hRR : (0:ℝ) ≤ R := by positivity
  linarith

lemma exists_lower_density {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ Real.exp 2*a ≤ 1/2 ∧ 2*a ≤ β/4 := by
  let a := β/(16*Real.exp 2)
  have he : 0 < Real.exp (2:ℝ) := Real.exp_pos _
  have he1 : 1 ≤ Real.exp (2:ℝ) := Real.one_le_exp (by norm_num)
  have ha : 0 < a := by dsimp [a]; positivity
  have hA : a ≤ β/16 := by
    change β/(16*Real.exp 2) ≤ β/16
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 16*Real.exp 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_left he1 hβ.le]
  have hE : Real.exp 2*a = β/16 := by dsimp [a]; field_simp
  refine ⟨a,ha,by linarith,by rw [hE]; linarith,by linarith⟩

lemma sentinel_linear_lower {n k R : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (hR : 1 ≤ R) (hn : 2*k^2 ≤ n) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (haHall : Real.exp 2*a ≤ 1/2) (haβ : 2*a ≤ Real.exp (-4*(R:ℝ)*k^2)/4)
    (hlarge : 8 ≤ a*n)
    (hhigh : (2*(1-((2:ℝ)^k)⁻¹)^R)^n ≤ Real.exp (-4*(R:ℝ)*k^2)/4) :
    (a/(16*((2*R:ℕ)+1:ℝ)^2))*a*Real.exp (-4*(R:ℝ)*k^2)/16*n ≤
      fvariance (fun w : Fin (2*R*n) → Clause n k => (listStop (List.ofFn w):ℝ)) := by
  let M := 2*R*n
  let V := R*n
  let Q := ⌊a*n/4⌋₊
  let β := Real.exp (-4*(R:ℝ)*k^2)
  let γ := a/(16*((2*R:ℕ)+1:ℝ)^2)
  let p := (Q:ℝ)*((M:ℝ)+1-Q-V)/((M:ℝ)+1)^2
  have hβ : 0 < β := Real.exp_pos _
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨hQlo,hQup,h2Q,hQV,hQM,hcoef⟩ := floor_window_bounds ha ha1 hR hlarge
  change a*n/8 ≤ (Q:ℝ) at hQlo
  change (Q:ℝ) ≤ a*n/4 at hQup
  change 2*Q ≤ M at h2Q
  change Q+V ≤ M+1 at hQV
  change Q ≤ M at hQM
  have hcoef' : γ ≤ p := by simpa only [γ,p,M,V,Nat.cast_mul,Nat.cast_ofNat] using hcoef
  have hp : 0 ≤ p := hγ.le.trans hcoef'
  have hn0 : 0 < n := by omega
  have hM0 : 0 < M := by dsimp [M]; positivity
  have hV : V ≤ M := by dsimp [V,M]; nlinarith
  have hsel := selected_variance (by omega : 1 ≤ k) hkn Q V hQV
  change p*favg (fun w : Fin M → Clause n k => (min Q (isolateSet w).card:ℝ)) ≤
    fvariance (fun w : Fin M → Clause n k => (listStop (List.ofFn w):ℝ))+
      p*Q*favg (fun w : Fin M → Clause n k => outsideWindow Q V (List.ofFn w)) at hsel
  have hmean := isolate_count_lower (by omega : 1 ≤ k) hkn hn (R := R) (M := M) (le_refl M)
  have hmin := min_isolate_mean_lower hM0 hQM hmean
  change (Q:ℝ)*β ≤ favg (fun w : Fin M → Clause n k => (min Q (isolateSet w).card:ℝ)) at hmin
  have hout := outsideWindow_bound hk hkn h2Q hV ha.le haHall (by
    push_cast
    nlinarith [mul_nonneg ha.le (show (0:ℝ) ≤ n by positivity)])
  have hpow : (2:ℝ)^n*(1-((2:ℝ)^k)⁻¹)^V = (2*(1-((2:ℝ)^k)⁻¹)^R)^n := by
    dsimp [V]
    rw [pow_mul,mul_pow]
  rw [hpow] at hout
  have hbad : favg (fun w : Fin M → Clause n k => outsideWindow Q V (List.ofFn w)) ≤ β/2 := by
    dsimp only [β]
    linarith
  have htotal := mul_le_mul_of_nonneg_left hmin hp
  have herror := mul_le_mul_of_nonneg_left hbad (mul_nonneg hp (show (0:ℝ) ≤ Q by positivity))
  have hs : p*Q*β/2 ≤ fvariance (fun w : Fin M → Clause n k => (listStop (List.ofFn w):ℝ)) := by
    nlinarith
  have hl := mul_le_mul hcoef' hQlo (by positivity) hp
  have hl' := mul_le_mul_of_nonneg_right hl (div_nonneg hβ.le (by norm_num : (0:ℝ) ≤ 2))
  calc
    _ = γ*(a*n/8)*(β/2) := by dsimp [γ,β]; ring
    _ ≤ p*Q*(β/2) := hl'
    _ = p*Q*β/2 := by ring
    _ ≤ _ := hs

end RandomKSAT

end

end OAI
