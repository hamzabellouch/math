import OAI.NumberTheory.PrimeGaps.PairedDetectors

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem extra_cumulative_pair_limit {n p d : ℕ} {tau sigma lam : ℝ}
    (htau : 0≤tau) (hsigma : 0 ≤ sigma) (hbudget : 2*(tau+sigma)<1) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau)
    (w : (Fin (d+1) → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆positiveSimplex (d+1) sigma) :
    Tendsto (fun X : ℕ => (extraAverage X (blockLength lam X) (fun m =>
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) m*
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau g) (subsetCoefficient p) m)
      (cumulativeProfile sigma w):ℂ)) atTop
      (𝓝 ((lam:ℂ)^(d+1)*∑ r : Setoid (Fin (n+p)),
        (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*extraPairKernel tau sigma f g w hf hg hw hfs hgs hws r))) := by
  let P := extraPairProfile f g w
  have hPc : HasCompactSupport P := extraPairProfile_compact f g w hf hg hw
  have hPs : ContDiff ℝ ∞ P := extraPairProfile_smooth f g w hfs hgs hws
  have hPb : tsupport P⊆positiveSimplex _ ((tau+sigma)+(tau+sigma)) :=
    tensorProfile_tsupport _ _ (tensorProfile_tsupport f w hsf hsw) (tensorProfile_tsupport g w hsg hsw)
  let F := cumulativeProfile ((tau+sigma)+(tau+sigma)) P
  have hFc := cumulativeProfile_compact ((tau+sigma)+(tau+sigma)) P hPc
  have hFs := cumulativeProfile_smooth ((tau+sigma)+(tau+sigma)) P hPc hPs
  obtain ⟨M,hMb⟩ := hFs.continuous.bounded_above_of_compact_support hFc
  have hh := extra_labeled_limit (n:=n) (p:=p) (d:=d) hlam F ((tau+sigma)+(tau+sigma))
    (by positivity) (by linarith) (cumulativeProfile_budget _ P hPb)
    (realEuclidean_compact F hFc) (realEuclidean_smooth F hFs)
    (max 0 M) (le_max_left _ _) (fun v _ => by simpa only [Real.norm_eq_abs] using (hMb v).trans (le_max_right 0 M))
    (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p))
  have he : (∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+(d+1))*extraPairKernel tau sigma f g w hf hg hw hfs hgs hws r)) =
      (lam:ℂ)^(d+1)*∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*extraPairKernel tau sigma f g w hf hg hw hfs hgs hws r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [pow_add]
    ring
  change Tendsto _ _ (𝓝 (∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+(d+1))*extraPairKernel tau sigma f g w hf hg hw hfs hgs hws r))) at hh
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  exact (extra_block_expansion hX _ f g w hsf hsg hsw _ _).symm

theorem extra_cumulative_square_limit {n d : ℕ} {tau sigma lam : ℝ}
    (htau : 0≤tau) (hsigma : 0 ≤ sigma) (hbudget : 2*(tau+sigma)<1) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsym : SymmetricFunction f)
    (w : (Fin (d+1) → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆positiveSimplex (d+1) sigma) :
    Tendsto (fun X : ℕ => extraAverage X (blockLength lam X) (fun m =>
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) m^2)
      (cumulativeProfile sigma w)) atTop
      (𝓝 (lam^(d+1)*alpha lam n*l2Mass f*l2Mass w)) := by
  have hh := extra_cumulative_pair_limit htau hsigma hbudget hlam f f hf hf hfs hfs hsf hsf w hw hws hsw
  rw [extra_square_pattern_sum lam f hf hfs hsf hsym w hw hws hsw] at hh
  have hh' := Complex.continuous_re.continuousAt.tendsto.comp hh
  simpa [Function.comp_def,←Complex.ofReal_pow,Complex.mul_re,←pow_two,mul_assoc] using hh'

theorem extra_cumulative_cross_limit {n p d : ℕ} (hnp : n≠p) {tau sigma lam : ℝ}
    (htau : 0≤tau) (hsigma : 0 ≤ sigma) (hbudget : 2*(tau+sigma)<1) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau)
    (w : (Fin (d+1) → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆positiveSimplex (d+1) sigma) :
    Tendsto (fun X : ℕ => extraAverage X (blockLength lam X) (fun m =>
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) m*
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau g) (subsetCoefficient p) m)
      (cumulativeProfile sigma w)) atTop (𝓝 0) := by
  have hh := extra_cumulative_pair_limit htau hsigma hbudget hlam f g hf hg hfs hgs hsf hsg w hw hws hsw
  rw [extra_cross_pattern_sum hnp lam f g hf hg hfs hgs hsf hsg w hw hws hsw,mul_zero] at hh
  exact Complex.continuous_re.continuousAt.tendsto.comp hh

theorem orderedWeight_extra_limit {tau sigma lam : ℝ} {k d : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (hsigma : 0 ≤ sigma) (hbudget : 2*(tau+sigma)<1) (hlam : 0<lam)
    (w : (Fin (d+1) → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆positiveSimplex (d+1) sigma) :
    Tendsto (fun X : ℕ => extraAverage X (blockLength lam X) (fun m => orderedWeight tau lam k f X m^2)
      (cumulativeProfile sigma w)) atTop (𝓝 (lam^(d+1)*l2Mass w*familyW lam k f)) := by
  classical
  let H := fun (j : Fin (k+1)) X m => weightedBlock X (blockLength lam X) (blockLength lam X+1)
       (cumulativeProfile tau (f j)) (subsetCoefficient j) m
  have hp (i j : Fin (k+1)) :
      Tendsto (fun X : ℕ => extraAverage X (blockLength lam X) (fun m => H i X m*H j X m)
        (cumulativeProfile sigma w)) atTop
        (𝓝 (if i=j then lam^(d+1)*alpha lam i*l2Mass (f i)*l2Mass w else 0)) := by
    have hfi := hf.2.1 i (by omega : (i:ℕ)≤k)
    have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
    by_cases hij : i=j
    · subst j
      simp only [↓reduceIte]
      simpa only [H,pow_two] using extra_cumulative_square_limit htau hsigma hbudget hlam
        (f i) hfi.2.1 hfi.1 hfi.2.2.1 hfi.2.2.2 w hw hws hsw
    · simp only [ite_eq_right hij]
      have hne : (i:ℕ)≠(j:ℕ) := fun h => hij (Fin.ext h)
      exact extra_cumulative_cross_limit hne htau hsigma hbudget hlam
        (f i) (f j) hfi.2.1 hfj.2.1 hfi.1 hfj.1 hfi.2.2.1 hfj.2.2.1 w hw hws hsw
  have hs := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => hp i j
  have he (X : ℕ) : extraAverage X (blockLength lam X) (fun m => orderedWeight tau lam k f X m^2)
      (cumulativeProfile sigma w)=
      ∑ i : Fin (k+1),∑ j : Fin (k+1),extraAverage X (blockLength lam X) (fun m => H i X m*H j X m)
        (cumulativeProfile sigma w) := by
    unfold orderedWeight
    simp only [pow_two,Finset.sum_mul_sum,extraAverage_finset_sum]
    rfl
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte] at hs
  have hv : (∑ i : Fin (k+1),lam^(d+1)*alpha lam i*l2Mass (f i)*l2Mass w)=
      lam^(d+1)*l2Mass w*familyW lam k f := by
    have he : ∀ i : Fin (k+1),lam^(d+1)*alpha lam i*l2Mass (f i)*l2Mass w=
        (lam^(d+1)*l2Mass w)*(alpha lam i*l2Mass (f i)) := fun _ => by ring
    simp only [he,←Finset.mul_sum]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => alpha lam j*l2Mass (f j)) (k+1)
  rw [hv] at hs
  exact hs.congr' (Eventually.of_forall fun X => (he X).symm)

theorem distinctBox_pair_iff {h : ℕ} (b : Fin 2 → Fin h) :
    b∈distinctBox (fun _ => (1:ℤ)) ↔ b 0≠b 1 := by
  simp only [distinctBox,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hb he
    have hh : boxTuple (fun _ => (1:ℤ)) b 0=boxTuple (fun _ => (1:ℤ)) b 1 := by simp only [boxTuple,he]
    have hi := hb hh
    exact (by decide : (0:Fin 2)≠1) hi
  · intro hb i j hij
    have he : b i=b j := by
      apply Fin.ext
      exact_mod_cast (add_left_cancel (show (1:ℤ)+(b i:ℤ)=1+(b j:ℤ) from hij))
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (hb he)
    · exact False.elim (hb he.symm)
    · rfl

theorem sum_distinctBox_pair {h : ℕ} (F : Fin h → Fin h → ℝ) :
    (∑ v∈distinctBox (s:=2) (h:=h) (fun _ => (1:ℤ)),F (v 0) (v 1))=
      ∑ b : Fin h,∑ c : Fin h,if b≠c then F b c else 0 := by
  classical
  have he : distinctBox (s:=2) (h:=h) (fun _ => (1:ℤ))=Finset.univ.filter (fun b => b 0≠b 1) := by
    ext b
    simp only [distinctBox_pair_iff,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [he,Finset.sum_filter]
  calc
    _ = ∑ bc : Fin h × Fin h, if bc.1≠bc.2 then F bc.1 bc.2 else 0 :=
      Fintype.sum_equiv (finTwoArrowEquiv (Fin h)) _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_prod_type _

theorem sum_first_interval (h : ℕ) (F : ℕ → ℝ) :
    (∑ b∈Finset.Ioc 0 h,F b)=∑ b : Fin h,F (1+b) := by
  have he : Finset.Ioc 0 h=Finset.Ico 1 (h+1) := by
    ext b
    simp only [Finset.mem_Ioc,Finset.mem_Ico]
    omega
  rw [he,Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel,Finset.sum_range]

theorem sum_first_offdiagonal (h : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ b∈Finset.Ioc 0 h,∑ c∈(Finset.Ioc 0 h).erase b,F b c)=
      ∑ b : Fin h,∑ c : Fin h,if b≠c then F (1+b) (1+c) else 0 := by
  classical
  have he (b : ℕ) : (∑ c∈(Finset.Ioc 0 h).erase b,F b c)=
      ∑ c∈Finset.Ioc 0 h,if b≠c then F b c else 0 := by
    rw [←Finset.filter_ne,Finset.sum_filter]
  simp_rw [he,sum_first_interval]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simp only [ne_eq,Nat.add_left_cancel_iff,Fin.val_inj]

theorem extraAverage_pair_identity {tau : ℝ} {X : ℕ} (hX : 2≤X) (h : ℕ)
    (H : ℕ → ℝ) (g : (Fin 1 → ℝ) → ℝ)
    (hgs : tsupport g⊆positiveSimplex 1 tau) :
    extraAverage X h H (cumulativeProfile (tau+tau) (tensorProfile g g))=
      ∑ b∈Finset.Ioc 0 h,∑ c∈(Finset.Ioc 0 h).erase b,
        average X (fun m => H m*divisorSum X (cumulativeProfile tau g) m (fun _ => b)^2*
          divisorSum X (cumulativeProfile tau g) m (fun _ => c)^2) := by
  classical
  have hd (m : ℕ) (v : Fin 2 → Fin h) :
      divisorSum X (cumulativeProfile (tau+tau) (tensorProfile g g)) m (fun i => 1+(v i:ℕ))=
        divisorSum X (cumulativeProfile tau g) m (fun _ => 1+(v 0:ℕ))*
        divisorSum X (cumulativeProfile tau g) m (fun _ => 1+(v 1:ℕ)) := by
    convert divisorSum_cumulative_tensor g g hgs hgs hX m
      (fun _ => 1+(v 0:ℕ)) (fun _ => 1+(v 1:ℕ)) using 1
    congr 1
    funext i
    fin_cases i <;> rfl
  unfold extraAverage
  simp_rw [hd,mul_pow,←mul_assoc]
  rw [average_finset_sum]
  rw [sum_distinctBox_pair (fun b c : Fin h => average X (fun m =>
    H m*divisorSum X (cumulativeProfile tau g) m (fun _ => 1+(b:ℕ))^2*
      divisorSum X (cumulativeProfile tau g) m (fun _ => 1+(c:ℕ))^2)),
    sum_first_offdiagonal]

theorem unorderedWeight_extra_pair_limit {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (hbudget : 6*tau<1) (hlam : 0<lam)
    (g : (Fin 1 → ℝ) → ℝ) (hgc : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (hgt : tsupport g⊆positiveSimplex 1 tau) :
    Tendsto (fun X : ℕ => extraAverage X (blockLength lam X)
      (fun m => unorderedWeight tau lam k f X m^2)
      (cumulativeProfile (tau+tau) (tensorProfile g g)))
      atTop (𝓝 (lam^2*l2Mass g^2*familyW lam k f)) := by
  have hh := orderedWeight_extra_limit f hf htau (by linarith : 0≤tau+tau)
    (by linarith : 2*(tau+(tau+tau))<1) hlam (d:=1) (tensorProfile g g)
    (tensorProfile_compact g g hgc hgc) (tensorProfile_smooth g g hgs hgs)
    (tensorProfile_tsupport g g hgt hgt)
  rw [l2Mass_tensor,←pow_two] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  simp only [orderedWeight_eq_unordered f hf hX]

theorem unorderedWeight_detector_bound (hBV : BombieriVinogradov) {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (hbudget : 6*tau<1) (hlam : 0<lam)
    (hw : 0<familyW lam k f)
    (g : (Fin 1 → ℝ) → ℝ) (hgc : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (hgt : tsupport g⊆positiveSimplex 1 tau) (hg0 : cumulativeProfile tau g 0=1) :
    ∀ᶠ X : ℕ in atTop,
      average X (fun m => unorderedWeight tau lam k f X m^2*
        detector X (Finset.Ioc 0 (blockLength lam X)) m^2)≤
      (lam+lam^2*l2Mass g^2+1)*familyW lam k f := by
  let q := fun X : ℕ => Real.log (2*X+2*blockLength lam X)/Real.log X
  let Z := unorderedWeight tau lam k f
  let E := fun X : ℕ => extraAverage X (blockLength lam X) (fun m => Z X m^2)
    (cumulativeProfile (tau+tau) (tensorProfile g g))
  have hlim := ((detector_log_ratio_tendsto hlam.le).mul
    (unorderedWeight_external_marked_limit hBV f hf htau (by linarith) hlam)).add
    (((detector_log_ratio_tendsto hlam.le).pow 2).mul
      (unorderedWeight_extra_pair_limit f hf htau hbudget hlam g hgc hgs hgt))
  simp only [one_mul,one_pow] at hlim
  have hlim' : Tendsto (fun X : ℕ => q X*average X (fun m => Z X m^2*
      detector X (Finset.Ioc 0 (blockLength lam X)) m)+q X^2*E X)
      atTop (𝓝 ((lam+lam^2*l2Mass g^2)*familyW lam k f)) := by
    convert hlim using 1
    congr 1
    ring
  have hstrict : (lam+lam^2*l2Mass g^2)*familyW lam k f<
      (lam+lam^2*l2Mass g^2+1)*familyW lam k f := by nlinarith
  have hu := hlim'.eventually_lt_const hstrict
  filter_upwards [eventually_ge_atTop 2,hu] with X hX hU
  apply le_trans _ hU.le
  have hh := weighted_detector_square_majorant (X:=X) (Y:=2*X+2*blockLength lam X)
    hX (by omega) (Finset.Ioc 0 (blockLength lam X))
    (by intro m hm b hb; have := Finset.mem_Ioc.mp hm; have := Finset.mem_Ioc.mp hb; omega)
    (by intro m hm b hb; have := Finset.mem_Ioc.mp hm; have := Finset.mem_Ioc.mp hb; omega)
    (fun m => Z X m^2) (fun _ _ => sq_nonneg _) (cumulativeProfile tau g)
    (by linarith : tau<1) (cumulativeProfile_budget tau g hgt) hg0
  rw [←extraAverage_pair_identity hX (blockLength lam X) (fun m => Z X m^2) g hgt] at hh
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,q,E] using hh

theorem index_density_of_bombieriVinogradov (hBV : BombieriVinogradov)
    (C : ℝ) (hC : 0<C) :
    ∃ c : ℝ, 0<c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀≤N →
      c*(N:ℝ)≤((largeGapIndices C N).card:ℝ) := by
  let tau : ℝ := 1/8
  let lam : ℝ := C+1
  have htau : 0<tau := by norm_num [tau]
  have hlam : 0<lam := by dsimp [lam]; linarith
  obtain ⟨g,hgs,hgc,hgt,_hgb,_hGc,_hGcompact,hg0⟩ := exists_detector_profile htau
  let D := lam+lam^2*l2Mass g^2+1
  have hD : 0<D := by dsimp [D]; positivity
  let eps := lam^2/(16*D)
  have heps : 0<eps := by dsimp [eps]; positivity
  obtain ⟨k,f,hf,_hf0,hw,hv⟩ := exists_family_small_marked_ratio hlam htau heps
  let w := familyW lam k f
  have hw' : 0<w := hw
  let a := lam*w/2
  let K := D*w
  let b := 2*(eps*w)
  have ha : 0<a := by dsimp [a]; positivity
  have hK : 0<K := mul_pos hD hw'
  have hab : a^2/K=4*(eps*w) := by
    dsimp [a,K,eps]
    field_simp
    ring
  have hb : b<a^2/K := by
    rw [hab]
    dsimp [b]
    nlinarith [mul_pos heps hw']
  obtain ⟨M,hM,hfourth⟩ := unorderedWeight_fourth_bound f hf htau.le
    (by norm_num [tau] : 4*tau<1) hlam
  apply index_density_from_weight_estimates hC
    (fun X m => unorderedWeight tau lam k f X m^2) a K b M ha hK hM hb
  · exact Eventually.of_forall fun _ _ _ => sq_nonneg _
  · have hlim := unorderedWeight_external_marked_limit hBV f hf htau.le
      (by norm_num [tau] : 2*tau<1/2) hlam
    have hlt : a<lam*familyW lam k f := by
      change lam*w/2<lam*w
      nlinarith [mul_pos hlam hw']
    exact Eventually.mono ((tendsto_order.mp hlim).1 a hlt) fun _ h => h.le
  · exact unorderedWeight_detector_bound hBV f hf htau.le
      (by norm_num [tau] : 6*tau<1) hlam hw g hgc hgs hgt hg0
  · have hlim := unorderedWeight_internal_marked_limit hBV f hf htau.le
      (by norm_num [tau] : 2*tau<1/2) hlam
    have hV : familyV lam k f≤eps*w := (div_le_iff₀ hw).mp hv
    have hlt : familyV lam k f<b := by
      dsimp [b]
      nlinarith [mul_pos heps hw']
    exact Eventually.mono ((tendsto_order.mp hlim).2 b hlt) fun _ h => h.le
  · filter_upwards [hfourth] with X hX
    simpa only [←pow_mul] using hX

end LargePrimeGaps

end OAI
