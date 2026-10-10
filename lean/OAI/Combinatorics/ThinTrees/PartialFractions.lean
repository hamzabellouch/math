import OAI.Combinatorics.ThinTrees.Stability

namespace OAI

section

noncomputable section
open Polynomial Filter Finset
open scoped Topology
namespace StrongThinTree.MSS.Rational

lemma upper_root_I {k : ℕ} (hk : 0 < k) :
    ∃w : ℂ, 0 < w.im ∧ w^k=Complex.I := by
  let θ : ℝ := Real.pi/(2*k)
  let w := Complex.exp ((θ:ℂ)*Complex.I)
  have hkp : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθπ : θ < Real.pi := by
    dsimp [θ]
    apply (div_lt_iff₀ (by positivity : (0:ℝ)<2*k)).mpr
    have hk1 : (1:ℝ)≤k := by exact_mod_cast hk
    nlinarith [Real.pi_pos]
  refine ⟨w,?_,?_⟩
  · simpa [w,Complex.exp_im] using Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  · rw [show w^k=Complex.exp ((k:ℂ)*((θ:ℂ)*Complex.I)) from (Complex.exp_nat_mul _ _).symm]
    have heq : (k:ℂ)*((θ:ℂ)*Complex.I)=(Real.pi:ℂ)/2*Complex.I := by
      dsimp [θ]
      push_cast
      have hkc : (k:ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      field_simp [hkc]
    rw [heq,Complex.exp_pi_div_two_mul_I]

lemma upper_root_neg_I {k : ℕ} (hk : 2 ≤ k) :
    ∃w : ℂ, 0 < w.im ∧ w^k= -Complex.I := by
  let θ : ℝ := 3*Real.pi/(2*k)
  let w := Complex.exp ((θ:ℂ)*Complex.I)
  have hkp : (0:ℝ)<k := by exact_mod_cast (by omega : 0 < k)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθπ : θ < Real.pi := by
    dsimp [θ]
    apply (div_lt_iff₀ (by positivity : (0:ℝ)<2*k)).mpr
    have hk2 : (2:ℝ)≤k := by exact_mod_cast hk
    nlinarith [Real.pi_pos]
  refine ⟨w,?_,?_⟩
  · simpa [w,Complex.exp_im] using Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  · rw [show w^k=Complex.exp ((k:ℂ)*((θ:ℂ)*Complex.I)) from (Complex.exp_nat_mul _ _).symm]
    have heq : (k:ℂ)*((θ:ℂ)*Complex.I)=(Real.pi:ℂ)*Complex.I+(Real.pi:ℂ)/2*Complex.I := by
      dsimp [θ]
      push_cast
      have hkc : (k:ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      field_simp [hkc]
      norm_num
    rw [heq,Complex.exp_add,Complex.exp_pi_mul_I,Complex.exp_pi_div_two_mul_I]
    simp

lemma principal_part_order {c : ℝ} (hc : c ≠ 0) {k : ℕ} (hk : 0 < k)
    (h : ∀w : ℂ, 0 < w.im → ((c:ℂ)/w^k).im ≤ 0) : k=1 ∧ 0<c := by
  obtain ⟨u,hu,huPow⟩ := upper_root_I hk
  have hc0 : 0 ≤ c := by
    have hh := h u hu
    rw [huPow] at hh
    simpa [Complex.div_im] using hh
  have hk1 : k=1 := by
    by_contra hn
    obtain ⟨v,hv,hvPow⟩ := upper_root_neg_I (by omega : 2 ≤ k)
    have hh := h v hv
    rw [hvPow] at hh
    have hc1 : c ≤ 0 := by simpa [Complex.div_im] using hh
    exact hc (le_antisymm hc1 hc0)
  exact ⟨hk1,lt_of_le_of_ne hc0 (Ne.symm hc)⟩

lemma polynomial_part_order {c : ℝ} (hc : c ≠ 0) {k : ℕ} (hk : 0 < k)
    (h : ∀w : ℂ, 0 < w.im → ((c:ℂ)*w^k).im ≤ 0) : k=1 ∧ c<0 := by
  obtain ⟨u,hu,huPow⟩ := upper_root_I hk
  have hc0 : c ≤ 0 := by simpa [huPow] using h u hu
  have hk1 : k=1 := by
    by_contra hn
    obtain ⟨v,hv,hvPow⟩ := upper_root_neg_I (by omega : 2 ≤ k)
    have hc1 : 0 ≤ c := by simpa [hvPow] using h v hv
    exact hc (le_antisymm hc0 hc1)
  exact ⟨hk1,lt_of_le_of_ne hc0 hc⟩

def cval (p : ℝ[X]) (z : ℂ) : ℂ := (p.map (algebraMap ℝ ℂ)).eval z

@[simp] lemma cval_real (p : ℝ[X]) (x : ℝ) : cval p x=((p.eval x:ℝ):ℂ) := by
  exact Polynomial.eval_map_apply (algebraMap ℝ ℂ) x

lemma continuous_cval (p : ℝ[X]) : Continuous (cval p) := (p.map (algebraMap ℝ ℂ)).continuous

lemma pole_test (a b : ℝ[X]) {x : ℝ} {k : ℕ} (hk : 0 < k)
    (ha : a.eval x ≠ 0) (hb : b.eval x ≠ 0)
    (h : ∀z : ℂ, 0 < z.im → (cval a z/((z-(x:ℂ))^k*cval b z)).im ≤ 0) :
    k=1 ∧ 0<a.eval x/b.eval x := by
  apply principal_part_order (div_ne_zero ha hb) hk
  intro w hw
  have hw0 : w ≠ 0 := by intro hh; simp [hh] at hw
  have hb0 : cval b x ≠ 0 := by simpa using hb
  have hd : w^k*cval b x ≠ 0 := mul_ne_zero (pow_ne_zero _ hw0) hb0
  have ht : Tendsto (fun r : ℝ => cval a ((x:ℂ)+r*w)/(w^k*cval b ((x:ℂ)+r*w)))
      (𝓝[>] 0) (𝓝 (((a.eval x/b.eval x:ℝ):ℂ)/w^k)) := by
    have hc : ContinuousAt (fun r : ℝ => (x:ℂ)+(r:ℂ)*w) 0 := by fun_prop
    have hta := (continuous_cval a).continuousAt.comp hc
    have htb := (continuous_cval b).continuousAt.comp hc
    have htt := hta.tendsto.div (htb.tendsto.const_mul (w^k)) (by simpa using hd)
    dsimp only [Function.comp_apply,Pi.div_apply] at htt
    simp only [Complex.ofReal_zero] at htt
    have heq : cval a ((x:ℂ)+(0:ℂ)*w)/(w^k*cval b ((x:ℂ)+(0:ℂ)*w))=
        ((a.eval x/b.eval x:ℝ):ℂ)/w^k := by simp only [zero_mul,add_zero,cval_real,Complex.ofReal_div]; ring
    rw [heq] at htt
    exact htt.mono_left nhdsWithin_le_nhds
  have him := Complex.continuous_im.continuousAt.tendsto.comp ht
  apply le_of_tendsto him
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrp : 0 < r := hr
  have hrc : (r:ℂ) ≠ 0 := by exact_mod_cast hrp.ne'
  have hzr : 0 < ((x:ℂ)+(r:ℂ)*w).im := by simpa using mul_pos hrp hw
  have hh := h _ hzr
  have heq : cval a ((x:ℂ)+r*w)/(w^k*cval b ((x:ℂ)+r*w))=
      (r:ℂ)^k * (cval a ((x:ℂ)+r*w)/(((x:ℂ)+r*w-x)^k*cval b ((x:ℂ)+r*w))) := by
    rw [add_sub_cancel_left,mul_pow]
    field_simp [hrc]
  dsimp only [Function.comp_apply]
  rw [heq,←Complex.ofReal_pow,Complex.mul_im]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hrp.le _) hh

@[simp] lemma cval_mul (p q : ℝ[X]) (z : ℂ) : cval (p*q) z=cval p z*cval q z := by
  simp [cval]
@[simp] lemma cval_pow (p : ℝ[X]) (n : ℕ) (z : ℂ) : cval (p^n) z=(cval p z)^n := by
  simp [cval]
@[simp] lemma cval_X_sub_C (x : ℝ) (z : ℂ) : cval (X-C x) z=z-x := by
  simp [cval]

lemma simple_roots (a b : ℝ[X]) (hb : b ≠ 0) (hab : IsCoprime a b)
    (h : ∀z : ℂ, 0 < z.im → (cval a z/cval b z).im ≤ 0) : b.roots.Nodup := by
  classical
  apply Multiset.nodup_iff_count_le_one.mpr
  intro x
  rw [count_roots]
  by_cases hx : b.IsRoot x
  · have ha : a.eval x ≠ 0 := by
      have ht := aeval_ne_zero_of_isCoprime hab x
      simpa [aeval_def,eval₂_at_apply,hx.eq_zero] using ht
    obtain ⟨q,hq,hq0⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd b hb x
    have hqx : q.eval x ≠ 0 := by simpa [dvd_iff_isRoot,IsRoot] using hq0
    have hh := pole_test a q ((rootMultiplicity_pos hb).mpr hx) ha hqx
      (fun z hz => by
        have he := congrArg (fun p => cval p z) hq
        simp only [cval_mul,cval_pow,cval_X_sub_C] at he
        rw [←he]
        exact h z hz)
    omega
  · have hh : rootMultiplicity x b = 0 := by
      exact Nat.eq_zero_of_not_pos (fun hp => hx ((rootMultiplicity_pos hb).mp hp))
    omega

lemma cval_ray (p : ℝ[X]) {w r : ℂ} (hw : w ≠ 0) (hr : r ≠ 0) :
    cval p (w/r) = cval p.reverse (r/w)*(w/r)^p.natDegree := by
  let : Invertible (w/r) := invertibleOfNonzero (div_ne_zero hw hr)
  have h := eval₂_reverse_mul_pow (algebraMap ℝ ℂ) (w/r) p
  simpa only [cval,eval_map,←eval₂_eq_eval_map,invOf_eq_inv,inv_div] using h.symm

lemma reverse_at_zero (p : ℝ[X]) : cval p.reverse 0=((p.leadingCoeff:ℝ):ℂ) := by
  simp [cval,eval_map,coeff_reverse]

lemma ray_limit (a b : ℝ[X]) (hb : b ≠ 0) (hdeg : b.natDegree ≤ a.natDegree)
    {w : ℂ} (hw : w ≠ 0) :
    Tendsto (fun r : ℝ => (r:ℂ)^(a.natDegree-b.natDegree)*
      (cval a (w/r)/cval b (w/r))) (𝓝[>] 0)
      (𝓝 (((a.leadingCoeff/b.leadingCoeff:ℝ):ℂ)*w^(a.natDegree-b.natDegree))) := by
  have hc : ContinuousAt (fun r : ℝ => (r:ℂ)/w) 0 := by fun_prop
  have ha := (continuous_cval a.reverse).continuousAt.comp hc
  have hb' := (continuous_cval b.reverse).continuousAt.comp hc
  have hlc : cval b.reverse ((0:ℂ)/w) ≠ 0 := by
    simp only [zero_div,reverse_at_zero,ne_eq,Complex.ofReal_eq_zero]
    exact leadingCoeff_ne_zero.mpr hb
  have ht := (ha.tendsto.div hb'.tendsto hlc).mul_const (w^(a.natDegree-b.natDegree))
  simp only [Function.comp_apply,zero_div,Complex.ofReal_zero,reverse_at_zero,←Complex.ofReal_div] at ht
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (r:ℂ) ≠ 0 := by exact_mod_cast (show r ≠ 0 from ne_of_gt hr)
  rw [cval_ray a hw hr0,cval_ray b hw hr0]
  rw [show a.natDegree=b.natDegree+(a.natDegree-b.natDegree) from (Nat.add_sub_of_le hdeg).symm]
  simp only [Nat.add_sub_cancel_left,pow_add,div_pow]
  field_simp
  rfl

lemma degree_le (a b : ℝ[X]) (hb : b ≠ 0)
    (h : ∀z : ℂ, 0 < z.im → (cval a z/cval b z).im ≤ 0)
    (hpos : ∀t : ℝ, 0 ≤ t → 0 ≤ a.eval t/b.eval t) : a.natDegree ≤ b.natDegree := by
  by_contra hdeg
  have hlt : b.natDegree < a.natDegree := Nat.lt_of_not_ge hdeg
  have ha : a ≠ 0 := by intro hh; simp [hh] at hlt
  have hc : a.leadingCoeff/b.leadingCoeff ≠ 0 :=
    div_ne_zero (leadingCoeff_ne_zero.mpr ha) (leadingCoeff_ne_zero.mpr hb)
  have ht := polynomial_part_order hc (Nat.sub_pos_of_lt hlt) (by
    intro w hw
    have hw0 : w ≠ 0 := by intro hh; simp [hh] at hw
    have hh := Complex.continuous_im.continuousAt.tendsto.comp (ray_limit a b hb hlt.le hw0)
    apply le_of_tendsto hh
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hrp : 0 < r := hr
    have hz : 0 < (w/(r:ℂ)).im := by
      simpa [Complex.div_ofReal_im] using div_pos hw hrp
    have hi := h _ hz
    dsimp only [Function.comp_apply]
    simp only [←Complex.ofReal_pow,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hrp.le _) hi)
  have hc0 : 0 ≤ a.leadingCoeff/b.leadingCoeff := by
    have hh := Complex.continuous_re.continuousAt.tendsto.comp (ray_limit a b hb hlt.le (one_ne_zero : (1:ℂ)≠0))
    simp only [one_pow,mul_one,Complex.ofReal_re] at hh
    apply ge_of_tendsto hh
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hrp : 0 < r := hr
    dsimp only [Function.comp_apply]
    have he : (1:ℂ)/(r:ℂ)=((1/r:ℝ):ℂ) := by push_cast; rfl
    rw [he,cval_real,cval_real,←Complex.ofReal_div,←Complex.ofReal_pow,←Complex.ofReal_mul,Complex.ofReal_re]
    exact mul_nonneg (pow_nonneg hrp.le _) (hpos _ (by positivity))
  linarith [ht.2]

lemma monic_eq_prod_roots (b : ℝ[X]) (hm : b.Monic) (hs : b.Splits)
    (hn : b.roots.Nodup) : b=∏x ∈ b.roots.toFinset, (X-C x) := by
  classical
  conv_lhs => rw [hs.eq_prod_roots,hm.leadingCoeff,C_1,one_mul,Finset.prod_multiset_map_count]
  apply Finset.prod_congr rfl
  intro x hx
  rw [Multiset.count_eq_one_of_mem hn (Multiset.mem_toFinset.mp hx),pow_one]

lemma simple_decomposition (a b : ℝ[X]) (hm : b.Monic) (hs : b.Splits)
    (hn : b.roots.Nodup) (hd : a.natDegree ≤ b.natDegree) :
    ∃c : ℝ, ∃d : ℝ → ℝ, a=C c*b+∑x ∈ b.roots.toFinset, C (d x)*∏y ∈ b.roots.toFinset.erase x, (X-C y) := by
  classical
  let s := b.roots.toFinset
  have hb : b=∏x ∈ s, (X-C x) := monic_eq_prod_roots b hm hs hn
  obtain ⟨q,r,hr,he⟩ := eq_quo_mul_prod_add_sum_rem_mul_prod (s:=s) a
    (g:=fun x : ℝ => X-C x) (fun _ _ => monic_X_sub_C _)
    (fun _ _ _ _ hxy => isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hxy)))
  have hrC : ∀x ∈ s, r x=C ((r x).coeff 0) := by
    intro x hx
    by_cases h0 : r x=0
    · simp [h0]
    apply eq_C_of_natDegree_eq_zero
    have hh := hr x hx
    rw [degree_X_sub_C,degree_eq_natDegree h0] at hh
    have hh' : (r x).natDegree < 1 := WithBot.coe_lt_coe.mp hh
    omega
  have hR : (∑x ∈ s, r x * ∏y ∈ s.erase x, (X-C y)).degree < b.degree := by
    apply (degree_sum_le _ _).trans_lt
    apply Finset.sup_lt_iff (by simpa only [bot_lt_iff_ne_bot,degree_ne_bot] using hm.ne_zero) |>.mpr
    intro x hx
    rw [hb,←Finset.mul_prod_erase s (fun x : ℝ => X-C x) hx]
    rw [degree_mul,degree_mul]
    apply WithBot.add_lt_add_right
    · rw [degree_ne_bot]
      exact (monic_prod_of_monic (s.erase x) _ (fun y _ => monic_X_sub_C y)).ne_zero
    · exact hr x hx
  have hq : q.natDegree=0 := by
    by_contra hq
    have hqp : 0 < q.degree := natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hq)
    have hqb : b.degree < (q*b).degree := by
      rw [degree_mul]
      simpa using WithBot.add_lt_add_right (by simpa [degree_ne_bot] using hm.ne_zero) hqp
    have hda : a.degree ≤ b.degree := by
      exact degree_le_of_natDegree_le hd |>.trans (le_of_eq (degree_eq_natDegree hm.ne_zero).symm)
    have he' : a=q*b+∑x ∈ s, r x*∏y ∈ s.erase x, (X-C y) := by simpa only [←hb] using he
    rw [he',degree_add_eq_left_of_degree_lt (hR.trans hqb)] at hda
    exact (not_le_of_gt hqb) hda
  refine ⟨q.coeff 0,fun x => (r x).coeff 0,?_⟩
  calc
    a=q*b+∑x ∈ s, r x*∏y ∈ s.erase x, (X-C y) := by simpa only [←hb] using he
    _=C (q.coeff 0)*b+∑x ∈ s, C ((r x).coeff 0)*∏y ∈ s.erase x, (X-C y) := by
      apply congrArg₂ (·+·)
      · exact congrArg (·*b) (eq_C_of_natDegree_eq_zero hq)
      · exact Finset.sum_congr rfl (fun x hx => congrArg (·*∏y ∈ s.erase x, (X-C y)) (hrC x hx))

lemma decomposition_value (a b : ℝ[X]) (s : Finset ℝ) (c : ℝ) (d : ℝ → ℝ)
    (hb : b=∏x ∈ s, (X-C x))
    (he : a=C c*b+∑x ∈ s, C (d x)*∏y ∈ s.erase x, (X-C y))
    {t : ℝ} (ht : ∀x ∈ s, t ≠ x) :
    a.eval t/b.eval t=c+∑x ∈ s, d x/(t-x) := by
  classical
  have hb0 : b.eval t ≠ 0 := by
    rw [hb,eval_prod]
    simp only [eval_sub,eval_X,eval_C]
    exact Finset.prod_ne_zero_iff.mpr (fun x hx => sub_ne_zero.mpr (ht x hx))
  have he' := congrArg (fun p : ℝ[X] => p.eval t) he
  simp only [eval_add,eval_mul,eval_C,eval_finsetSum,eval_prod,eval_sub,eval_X] at he'
  rw [he',add_div,mul_div_cancel_right₀ _ hb0,Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  have hh := congrArg (fun p : ℝ[X] => p.eval t) (hb.trans (Finset.mul_prod_erase s (fun y : ℝ => X-C y) hx).symm)
  simp only [eval_mul,eval_sub,eval_X,eval_C,eval_prod] at hh
  have hpr : (∏y ∈ s.erase x, (t-y)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun y hy => sub_ne_zero.mpr (ht y (mem_of_mem_erase hy)))
  rw [hh]
  field_simp

lemma residue_value (a b : ℝ[X]) (s : Finset ℝ) (c : ℝ) (d : ℝ → ℝ)
    (hb : b=∏x ∈ s, (X-C x))
    (he : a=C c*b+∑x ∈ s, C (d x)*∏y ∈ s.erase x, (X-C y))
    {x : ℝ} (hx : x ∈ s) :
    a.eval x/(∏y ∈ s.erase x, (X-C y)).eval x=d x := by
  classical
  have hb0 : b.eval x=0 := by
    rw [hb,eval_prod]
    exact Finset.prod_eq_zero hx (by simp)
  have he' := congrArg (fun p : ℝ[X] => p.eval x) he
  simp only [eval_add,eval_mul,eval_C,eval_finsetSum,hb0,mul_zero,zero_add] at he'
  rw [Finset.sum_eq_single x] at he'
  · rw [he',mul_div_cancel_right₀]
    rw [eval_prod]
    simp only [eval_sub,eval_X,eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro y hy
    exact sub_ne_zero.mpr (mem_erase.mp hy).1.symm
  · intro y hy hxy
    suffices h0 : (∏z ∈ s.erase y, (X-C z)).eval x=0 by rw [h0,mul_zero]
    rw [eval_prod]
    exact Finset.prod_eq_zero (mem_erase.mpr ⟨hxy.symm,hx⟩) (by simp)
  · exact fun hn => (hn hx).elim

lemma positive_decomposition_monic (a b : ℝ[X]) (hm : b.Monic) (hs : b.Splits)
    (hn : ∀x ∈ b.roots, x < 0) (hab : IsCoprime a b)
    (h : ∀z : ℂ, 0 < z.im → (cval a z/cval b z).im ≤ 0)
    (hpos : ∀t : ℝ, 0 ≤ t → 0 ≤ a.eval t/b.eval t) :
    ∃c : ℝ, ∃d : ℝ → ℝ, 0 ≤ c ∧ (∀x ∈ b.roots.toFinset, 0 < d x) ∧
      ∀t : ℝ, 0 ≤ t → a.eval t/b.eval t=c+∑x ∈ b.roots.toFinset, d x/(t-x) := by
  classical
  have hnodup := simple_roots a b hm.ne_zero hab h
  obtain ⟨c,d,he⟩ := simple_decomposition a b hm hs hnodup (degree_le a b hm.ne_zero h hpos)
  let s := b.roots.toFinset
  have hb : b=∏x ∈ s, (X-C x) := monic_eq_prod_roots b hm hs hnodup
  have hv : ∀t : ℝ, 0 ≤ t → a.eval t/b.eval t=c+∑x ∈ s, d x/(t-x) := by
    intro t ht
    exact decomposition_value a b s c d hb he (fun x hx => ne_of_gt ((hn x (Multiset.mem_toFinset.mp hx)).trans_le ht))
  have hd : ∀x ∈ s, 0 < d x := by
    intro x hx
    have hx0 : b.eval x=0 := (mem_roots hm.ne_zero).mp (Multiset.mem_toFinset.mp hx)
    have ha : a.eval x ≠ 0 := by
      simpa [aeval_def,eval₂_at_apply,hx0] using aeval_ne_zero_of_isCoprime hab x
    let q : ℝ[X] := ∏y ∈ s.erase x, (X-C y)
    have hqx : q.eval x ≠ 0 := by
      dsimp [q]
      rw [eval_prod]
      simp only [eval_sub,eval_X,eval_C]
      exact Finset.prod_ne_zero_iff.mpr (fun y hy => sub_ne_zero.mpr (mem_erase.mp hy).1.symm)
    have hbe : b=(X-C x)*q := hb.trans (Finset.mul_prod_erase s (fun y : ℝ => X-C y) hx).symm
    have hp := pole_test a q (k:=1) (by omega) ha hqx (by
      intro z hz
      simpa only [hbe,cval_mul,cval_X_sub_C,pow_one] using h z hz)
    have hr := residue_value a b s c d hb he hx
    exact hr ▸ hp.2
  have hc : 0 ≤ c := by
    have hlim : Tendsto (fun t : ℝ => c+∑x ∈ s, d x/(t-x)) atTop (𝓝 c) := by
      simpa using tendsto_const_nhds.add (tendsto_finsetSum s (fun x _ =>
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => d x) atTop (𝓝 (d x))).div_atTop (by simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-x) tendsto_id)))
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    rw [←hv t ht]
    exact hpos t ht
  exact ⟨c,d,hc,hd,hv⟩

lemma positive_decomposition (a b : ℝ[X]) (hb : b ≠ 0) (hs : b.Splits)
    (hreal : ∀t : ℝ, 0 ≤ t → b.eval t ≠ 0)
    (hupper : ∀z : ℂ, 0 < z.im → cval b z ≠ 0)
    (h : ∀z : ℂ, 0 < z.im → (cval a z/cval b z).im ≤ 0)
    (hpos : ∀t : ℝ, 0 ≤ t → 0 ≤ a.eval t/b.eval t) :
    ∃s : Finset ℝ, ∃c : ℝ, ∃d : ℝ → ℝ, 0 ≤ c ∧
      (∀x ∈ s, x < 0 ∧ 0 < d x) ∧
      ∀t : ℝ, 0 ≤ t → a.eval t/b.eval t=c+∑x ∈ s, d x/(t-x) := by
  classical
  let f : RatFunc ℝ := algebraMap ℝ[X] (RatFunc ℝ) a/algebraMap ℝ[X] (RatFunc ℝ) b
  have hf : f.num*b=a*f.denom := (RatFunc.num_mul_eq_mul_denom_iff hb).mpr rfl
  obtain ⟨g,hg⟩ := RatFunc.denom_div_dvd a b
  change b=f.denom*g at hg
  have hcf (z : ℂ) (hz : cval b z ≠ 0) : cval f.num z/cval f.denom z=cval a z/cval b z := by
    have hd : cval f.denom z ≠ 0 := by
      rw [hg,cval_mul] at hz
      exact (mul_ne_zero_iff.mp hz).1
    apply (div_eq_div_iff hd hz).mpr
    simpa only [cval_mul] using congrArg (fun p => cval p z) hf
  have hrf (t : ℝ) (ht : b.eval t ≠ 0) : f.num.eval t/f.denom.eval t=a.eval t/b.eval t := by
    have hh := hcf (t:ℂ) (by simpa using ht)
    simpa only [cval_real,←Complex.ofReal_div,Complex.ofReal_inj] using hh
  have hds : f.denom.Splits := hs.of_dvd hb ⟨g,hg⟩
  have hdn : ∀x ∈ f.denom.roots, x < 0 := by
    intro x hx
    by_contra hx0
    have hd0 : f.denom.eval x=0 := (mem_roots (RatFunc.denom_ne_zero f)).mp hx
    have hb0 : b.eval x=0 := by rw [hg,eval_mul,hd0,zero_mul]
    exact hreal x (le_of_not_gt hx0) hb0
  have hdh : ∀z : ℂ, 0 < z.im → (cval f.num z/cval f.denom z).im ≤ 0 := by
    intro z hz
    rw [hcf z (hupper z hz)]
    exact h z hz
  have hdp : ∀t : ℝ, 0 ≤ t → 0 ≤ f.num.eval t/f.denom.eval t := by
    intro t ht
    rw [hrf t (hreal t ht)]
    exact hpos t ht
  obtain ⟨c,d,hc,hd,hrep⟩ := positive_decomposition_monic f.num f.denom (RatFunc.monic_denom f)
    hds hdn (RatFunc.isCoprime_num_denom f) hdh hdp
  refine ⟨f.denom.roots.toFinset,c,d,hc,fun x hx => ⟨hdn x (Multiset.mem_toFinset.mp hx),hd x hx⟩,?_⟩
  intro t ht
  rw [←hrf t (hreal t ht)]
  exact hrep t ht

end StrongThinTree.MSS.Rational

end
end

end OAI
