import OAI.NumberTheory.PrimeGaps.MarkedMoments

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

theorem finiteSubsetWeight_eq_restricted_levels {tau : ℝ} {k X M h a : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f) (hk : k≤h)
    (B : Finset (Fin h)) :
    finiteSubsetWeight tau f X M h a B=
      ∑ j : Fin (k+1),restrictedUnorderedBlock X h a (cumulativeProfile tau (f j)) B M := by
  classical
  unfold finiteSubsetWeight
  have he : B.powerset=(Finset.univ.powerset : Finset (Finset (Fin h))).filter (fun S => S⊆B) := by
    ext S
    simp
  rw [he,Finset.sum_filter,Finset.sum_powerset]
  simp only [Finset.card_univ,Fintype.card_fin,setDivisor_subset_level_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => restrictedUnorderedBlock X h a (cumulativeProfile tau (f j)) B M) (k+1)]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega : k+1≤h+1))
  intro j _ hj
  have hjk : k<j := by simp only [Finset.mem_range,not_lt] at hj; omega
  rw [hf.2.2 j hjk,cumulativeProfile_zero,restrictedUnorderedBlock_zero]

noncomputable def restrictedWeight (tau lam : ℝ) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (X m : ℕ) (c : Fin (blockLength lam X)) : ℝ :=
  ∑ j : Fin (k+1),restrictedBlock X (blockLength lam X) (blockLength lam X+1)
    (cumulativeProfile tau (f j)) (subsetCoefficient j) (Finset.univ.erase c) m

theorem restrictedWeight_eq_finiteSubsetWeight {tau lam : ℝ} {k X m : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f)
    (hX : 2≤X) (hk : k≤blockLength lam X) (c : Fin (blockLength lam X)) :
    restrictedWeight tau lam k f X m c=
      finiteSubsetWeight tau f X m (blockLength lam X) (blockLength lam X+1) (Finset.univ.erase c) := by
  rw [finiteSubsetWeight_eq_restricted_levels hf hk]
  unfold restrictedWeight
  apply Finset.sum_congr rfl
  intro j _
  have hj := hf.all_properties j
  exact restrictedBlock_eq_unordered hX _ _ (cumulativeProfile_perm_orthant _ hj.2.2.1 hj.2.2.2)

theorem unorderedWeight_prime_delete {tau lam : ℝ} {k X m : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f)
    (htau : tau<1) (hX : 2≤X) (hk : k≤blockLength lam X) (hm : X < m)
    (c : Fin (blockLength lam X)) (hp : Nat.Prime (m+(blockLength lam X+1+(c:ℕ)))) :
    unorderedWeight tau lam k f X m=restrictedWeight tau lam k (deletedFamily f) X m c := by
  rw [unorderedWeight_eq_finiteSubsetWeight hf hk,
    restrictedWeight_eq_finiteSubsetWeight (deletedFamily_admissible hf) hX hk]
  exact finiteSubsetWeight_prime_delete hf htau hX c (by omega) hp

theorem coincident_double_sum {s h : ℕ} (a : ℤ) (F : (Fin (s+1) → Fin h) → ℂ) :
    (∑ u∈distinctBox (s:=s) (h:=h) (fun _ => a),∑ c : Fin h,
       if ∀ j,u j≠c then F (Fin.snoc u c) else 0)=
      ∑ v∈distinctBox (s:=s+1) (h:=h) (fun _ => a),F v := by
  classical
  simp only [distinctBox,Finset.sum_filter,constant_boxTuple_injective_iff]
  have he (u : Fin s → Fin h) :
      (if Function.Injective u then ∑ c : Fin h,if ∀ j,u j≠c then F (Fin.snoc u c) else 0 else 0)=
        ∑ c : Fin h,if Function.Injective u ∧ c∉Set.range u then F (Fin.snoc u c) else 0 := by
    by_cases hu : Function.Injective u <;> simp [hu,Set.mem_range]
  simp only [he]
  rw [Finset.sum_comm]
  calc
    _ = ∑ t : Fin h × (Fin s → Fin h),
        if Function.Injective t.2 ∧ t.1∉Set.range t.2 then F (Fin.snoc t.2 t.1) else 0 :=
      (Fintype.sum_prod_type _).symm
    _ = _ := by
      apply Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (s+1) => Fin h))
      intro t
      change (if Function.Injective t.2 ∧ t.1∉Set.range t.2 then F (Fin.snoc t.2 t.1) else 0)=
        (if Function.Injective (Fin.snoc t.2 t.1) then F (Fin.snoc t.2 t.1) else 0)
      exact if_congr Fin.snoc_injective_iff.symm rfl rfl

theorem patternTupleEquiv_avoid {n h : ℕ} (r : Setoid (Fin n)) (a : ℕ)
    (b : {b // b∈patternClass (α:=Fin h) r}) (c : Fin h) :
    (∀ i,b.val i≠c) ↔ ∀ j,(patternTupleEquiv r h a b).val j≠c := by
  constructor
  · intro hb j
    obtain ⟨i,hi⟩ := (patternLabels_surjective r) j
    have he := congrFun (patternTupleEquiv_labels r h a b) i
    simp only [patternBoxShifts,hi] at he
    have hv : (patternTupleEquiv r h a b).val j=b.val i := by
      apply Fin.ext
      omega
    simpa only [hv] using hb i
  · intro hb i
    have he := congrFun (patternTupleEquiv_labels r h a b) i
    simp only [patternBoxShifts] at he
    have hv : (patternTupleEquiv r h a b).val (patternLabels r i)=b.val i := by
      apply Fin.ext
      omega
    simpa only [hv] using hb (patternLabels r i)

theorem pattern_restricted_marked_sum_eq_box {n : ℕ} (r : Setoid (Fin n)) (h X : ℕ)
    (F : (Fin n → ℝ) → ℝ) :
    (∑ b∈patternClass (α:=Fin h) r,∑ c : Fin h,if ∀ i,b i≠c then
      (average X (fun m => divisorSum X F m (fun i => h+1+(b i:ℕ))*theta (m+(h+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ)
      else 0)=
    ∑ v∈distinctBox (s:=Fintype.card (Quotient r)+1) (h:=h) (fun _ => ((h+1:ℕ):ℤ)),
      (average X (fun m => divisorSum X F m
        (patternBoxShifts (patternLabels r) (fun _ => h+1) (fun j => v j.castSucc))*
        theta (m+(h+1+(v (Fin.last _):ℕ)))):ℂ)/(Real.log X:ℂ) := by
  classical
  rw [←coincident_double_sum]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]
  conv_lhs => rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Fintype.sum_equiv (patternTupleEquiv r h ((h+1:ℕ):ℤ))
  intro b
  rw [patternTupleEquiv_labels r h (h+1) b]
  apply Finset.sum_congr rfl
  intro c _
  simp only [←patternTupleEquiv_avoid r (h+1) b c]

theorem restricted_marked_pattern_limit (hBV : BombieriVinogradov) {n : ℕ}
    {lam : ℝ} (hlam : 0<lam) (r : Setoid (Fin n))
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ b∈patternClass (α:=Fin (blockLength lam X)) r,∑ c : Fin (blockLength lam X),
      if ∀ i,b i≠c then (average X (fun m => divisorSum X F m (fun i => blockLength lam X+1+(b i:ℕ))*
        theta (m+(blockLength lam X+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ) else 0) atTop
      (𝓝 ((lam:ℂ)^(Fintype.card (Quotient r)+1)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin n))
          (fun v => (F v.ofLp:ℂ)) hF hFs)
        (shiftFamily (fun i => (numericPattern r i:ℤ))))) := by
  have ha : ∀ᶠ X : ℕ in atTop,∀ _j : Fin (Fintype.card (Quotient r)+1),
      blockLength lam X+1≤2*blockLength lam X := by
    filter_upwards [blockOffset_eventually hlam] with X hX j
    exact hX
  have hh := marked_box_pattern_limit hBV hlam (patternLabels r) (patternLabels_surjective r)
    (fun X _ => blockLength lam X+1) ha F rho hrho hrhohalf hbudget hF hFs M hM hbound
  apply hh.congr'
  exact Eventually.of_forall fun X => (pattern_restricted_marked_sum_eq_box r _ X F).symm

noncomputable def internalMarked (X h : ℕ) (H : ℕ → Fin h → ℝ) : ℝ :=
  average X (fun m => ∑ c : Fin h,H m c*theta (m+(h+1+(c:ℕ)))/Real.log X)

theorem restrictedBlock_marked_expansion {n X h : ℕ}
    (F : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) :
    (internalMarked X h (fun m c => restrictedBlock X h (h+1) F k (Finset.univ.erase c) m):ℂ)=
      ∑ b : Fin n → Fin h,(k (Setoid.ker b):ℂ)*∑ c : Fin h,if ∀ i,b i≠c then
        (average X (fun m => divisorSum X F m (fun i => h+1+(b i:ℕ))*theta (m+(h+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ)
        else 0 := by
  classical
  unfold internalMarked restrictedBlock
  simp only [Finset.mem_erase,Finset.mem_univ,and_true,Finset.sum_mul,Finset.sum_div,
    average_finset_sum,Complex.ofReal_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hb : ∀ i,b i≠c
  · simp only [ite_eq_left hb]
    simp only [←mul_div_assoc,average_div]
    simp only [mul_assoc,average_const_mul,Complex.ofReal_div,Complex.ofReal_mul]
  · simp only [ite_eq_right hb,mul_zero,zero_mul,zero_div]
    simp [average]

theorem restrictedBlock_marked_limit (hBV : BombieriVinogradov) {n : ℕ}
    {lam : ℝ} (hlam : 0<lam)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (k : Setoid (Fin n) → ℝ) :
    Tendsto (fun X : ℕ => (internalMarked X (blockLength lam X) (fun m c =>
      restrictedBlock X (blockLength lam X) (blockLength lam X+1) F k (Finset.univ.erase c) m):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin n),(k r:ℂ)*((lam:ℂ)^(Fintype.card (Quotient r)+1)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin n))
          (fun v => (F v.ofLp:ℂ)) (realEuclidean_compact F hF) (realEuclidean_smooth F hFs))
        (equalityPatternFamily r)))) := by
  classical
  obtain ⟨M,hM⟩ := hFs.continuous.bounded_above_of_compact_support hF
  have hh := tendsto_finsetSum Finset.univ (fun r _ =>
    (restricted_marked_pattern_limit hBV hlam r F rho hrho hrhohalf hbudget
      (realEuclidean_compact F hF) (realEuclidean_smooth F hFs) M
      ((norm_nonneg (F 0)).trans (hM 0)) (fun v _ => by simpa only [Real.norm_eq_abs] using hM v)).const_mul (k r:ℂ))
  apply hh.congr'
  exact Eventually.of_forall (fun X => by
    dsimp only
    rw [restrictedBlock_marked_expansion]
    calc
      (∑ r : Setoid (Fin n), (k r:ℂ)*∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
        ∑ c : Fin (blockLength lam X),if ∀ i,b i≠c then
        (average X (fun m => divisorSum X F m (fun i => blockLength lam X+1+(b i:ℕ))*
          theta (m+(blockLength lam X+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ) else 0) =
        ∑ r : Setoid (Fin n),∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
          (k (Setoid.ker b):ℂ)*∑ c : Fin (blockLength lam X),if ∀ i,b i≠c then
            (average X (fun m => divisorSum X F m (fun i => blockLength lam X+1+(b i:ℕ))*
              theta (m+(blockLength lam X+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [(mem_patternClass r b).mp hb]
      _ = _ := sum_patterns _
    apply Finset.sum_congr (by ext b; simp)
    intro b _
    rfl)

theorem restrictedBlock_mul {n p : ℕ} (X h a m : ℕ)
    (F : (Fin n → ℝ) → ℝ) (G : (Fin p → ℝ) → ℝ)
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) (B : Finset (Fin h)) :
    restrictedBlock X h a F k B m*restrictedBlock X h a G l B m=
      restrictedBlock X h a (tensorProfile F G) (tensorCoefficient k l) B m := by
  classical
  unfold restrictedBlock
  rw [Finset.sum_mul_sum,←Finset.sum_product']
  apply Finset.sum_equiv (Fin.appendEquiv n p)
  · intro bc; simp
  intro bc _
  rw [show (Fin.appendEquiv n p) bc=Fin.append bc.1 bc.2 from rfl]
  simp only [tensorCoefficient,append_ker_left,append_ker_right]
  have he : (fun i => a+((Fin.append bc.1 bc.2 i :Fin h):ℕ))=
      Fin.append (fun i => a+(bc.1 i:ℕ)) (fun i => a+(bc.2 i:ℕ)) := by
    funext i
    cases i using Fin.addCases <;> simp
  rw [he,divisorSum_tensor]
  have hc : (∀ i,Fin.append bc.1 bc.2 i∈B) ↔ (∀ i,bc.1 i∈B) ∧ (∀ j,bc.2 j∈B) := by
    simp only [Fin.forall_fin_add,Fin.append_left,Fin.append_right]
  simp only [hc]
  split_ifs <;> simp_all
  all_goals ring

theorem restrictedBlock_congr_orthant {n X : ℕ} (hX : 2≤X) (h a m : ℕ)
    (F G : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) (B : Finset (Fin h))
    (hFG : ∀ v,(∀ i,0≤v i) → F v=G v) :
    restrictedBlock X h a F k B m=restrictedBlock X h a G k B m := by
  apply Finset.sum_congr rfl
  intro b _
  rw [divisorSum_congr_orthant hX m _ F G hFG]

theorem restrictedBlock_cumulative_mul {n p X : ℕ} (hX : 2≤X) (h a m : ℕ) {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : tsupport f⊆positiveSimplex n tau) (hg : tsupport g⊆positiveSimplex p tau)
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) (B : Finset (Fin h)) :
    restrictedBlock X h a (cumulativeProfile tau f) k B m*
      restrictedBlock X h a (cumulativeProfile tau g) l B m=
    restrictedBlock X h a (cumulativeProfile (tau+tau) (tensorProfile f g)) (tensorCoefficient k l) B m := by
  rw [restrictedBlock_mul]
  apply restrictedBlock_congr_orthant hX
  intro v hv
  let v1 := fun i : Fin n => v (i.castAdd p)
  let v2 := fun i : Fin p => v (i.natAdd n)
  have he : v=Fin.append v1 v2 := by
    funext i
    cases i using Fin.addCases <;> simp [v1,v2]
  rw [he,tensorProfile_append]
  exact (cumulativeProfile_tensor f g hf hg v1 v2 (fun i => hv _) (fun i => hv _)).symm

theorem internalMarked_congr {X h : ℕ} {H G : ℕ → Fin h → ℝ}
    (he : ∀ m c,H m c=G m c) : internalMarked X h H=internalMarked X h G := by
  unfold internalMarked
  congr 1
  funext m
  exact Finset.sum_congr rfl fun c _ => by rw [he]

theorem internalMarked_finset_sum {α : Type*} (X h : ℕ) (S : Finset α)
    (H : α → ℕ → Fin h → ℝ) :
    internalMarked X h (fun m c => ∑ i∈S,H i m c)=∑ i∈S,internalMarked X h (H i) := by
  unfold internalMarked
  simp only [Finset.sum_mul,Finset.sum_div,average_finset_sum]
  rw [Finset.sum_comm]

theorem restricted_cumulative_pair_limit (hBV : BombieriVinogradov) {n p : ℕ} {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau) :
    Tendsto (fun X : ℕ => (internalMarked X (blockLength lam X) (fun m c =>
      restrictedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) (Finset.univ.erase c) m*
      restrictedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau g) (subsetCoefficient p) (Finset.univ.erase c) m):ℂ))
      atTop (𝓝 ((lam:ℂ)*∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))) := by
  have hh := restrictedBlock_marked_limit hBV hlam
    (cumulativeProfile (tau+tau) (tensorProfile f g)) (tau+tau) (by positivity) (by linarith)
    (cumulativeProfile_budget _ _ (tensorProfile_tsupport f g hsf hsg))
    (cumulativeProfile_compact _ _ (tensorProfile_compact f g hf hg))
    (cumulativeProfile_smooth _ _ (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs))
    (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p))
  have he : (∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+1)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))=
      (lam:ℂ)*∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [pow_succ]
    ring
  change Tendsto _ _ (𝓝 (∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+1)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))) at hh
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  apply congrArg (fun z : ℝ => (z:ℂ))
  symm
  apply internalMarked_congr
  intro m c
  exact restrictedBlock_cumulative_mul hX _ _ m f g hsf hsg _ _ _

theorem restricted_cumulative_square_limit (hBV : BombieriVinogradov) {n : ℕ} {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsym : SymmetricFunction f) :
    Tendsto (fun X : ℕ => internalMarked X (blockLength lam X) (fun m c =>
      restrictedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) (Finset.univ.erase c) m^2))
      atTop (𝓝 (lam*alpha lam n*l2Mass f)) := by
  have hh := restricted_cumulative_pair_limit hBV htau htau2 hlam f f hf hf hfs hfs hsf hsf
  rw [cumulative_square_pattern_sum lam f hf hfs hsf hsym] at hh
  have hh' := Complex.continuous_re.continuousAt.tendsto.comp hh
  simpa [Function.comp_def,Complex.mul_re,←pow_two,mul_assoc] using hh'

theorem restricted_cumulative_cross_limit (hBV : BombieriVinogradov) {n p : ℕ} (hnp : n≠p) {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau) :
    Tendsto (fun X : ℕ => internalMarked X (blockLength lam X) (fun m c =>
      restrictedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) (Finset.univ.erase c) m*
      restrictedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau g) (subsetCoefficient p) (Finset.univ.erase c) m))
      atTop (𝓝 0) := by
  have hh := restricted_cumulative_pair_limit hBV htau htau2 hlam f g hf hg hfs hgs hsf hsg
  rw [cumulative_cross_pattern_sum hnp lam f g hf hg hfs hgs hsf hsg,mul_zero] at hh
  exact Complex.continuous_re.continuousAt.tendsto.comp hh

theorem restrictedWeight_marked_limit (hBV : BombieriVinogradov) {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam) :
    Tendsto (fun X : ℕ => internalMarked X (blockLength lam X) (fun m c => restrictedWeight tau lam k f X m c^2))
      atTop (𝓝 (lam*familyW lam k f)) := by
  classical
  let H := fun (j : Fin (k+1)) X m (c : Fin (blockLength lam X)) =>
    restrictedBlock X (blockLength lam X) (blockLength lam X+1)
      (cumulativeProfile tau (f j)) (subsetCoefficient j) (Finset.univ.erase c) m
  have hp (i j : Fin (k+1)) :
      Tendsto (fun X : ℕ => internalMarked X (blockLength lam X) (fun m c => H i X m c*H j X m c)) atTop
        (𝓝 (if i=j then lam*alpha lam i*l2Mass (f i) else 0)) := by
    have hfi := hf.2.1 i (by omega : (i:ℕ)≤k)
    have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
    by_cases hij : i=j
    · subst j
      simp only [↓reduceIte]
      simpa only [H,pow_two] using restricted_cumulative_square_limit hBV htau htau2 hlam
        (f i) hfi.2.1 hfi.1 hfi.2.2.1 hfi.2.2.2
    · simp only [ite_eq_right hij]
      have hne : (i:ℕ)≠(j:ℕ) := fun h => hij (Fin.ext h)
      exact restricted_cumulative_cross_limit hBV hne htau htau2 hlam
        (f i) (f j) hfi.2.1 hfj.2.1 hfi.1 hfj.1 hfi.2.2.1 hfj.2.2.1
  have hs := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => hp i j
  have he (X : ℕ) : internalMarked X (blockLength lam X) (fun m c => restrictedWeight tau lam k f X m c^2)=
      ∑ i : Fin (k+1),∑ j : Fin (k+1),internalMarked X (blockLength lam X) (fun m c => H i X m c*H j X m c) := by
    simp only [restrictedWeight,pow_two,Finset.sum_mul,Finset.mul_sum,internalMarked_finset_sum]
    rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte] at hs
  have hv : (∑ i : Fin (k+1),lam*alpha lam i*l2Mass (f i))=lam*familyW lam k f := by
    simp only [mul_assoc,←Finset.mul_sum]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => alpha lam j*l2Mass (f j)) (k+1)
  rw [hv] at hs
  exact hs.congr' (Eventually.of_forall fun X => (he X).symm)

theorem detector_I_eq (X h m : ℕ) :
    detector X (Finset.Ioc h (2*h)) m=
      (∑ c : Fin h,theta (m+(h+1+(c:ℕ))))/Real.log X := by
  unfold detector
  congr 1
  have he : Finset.Ioc h (2*h)=Finset.Ico (h+1) (h+1+h) := by
    ext i
    simp only [Finset.mem_Ioc,Finset.mem_Ico]
    omega
  rw [he,Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  symm
  exact Fin.sum_univ_eq_sum_range (fun c : ℕ => theta (m+(h+1+c))) h

theorem unorderedWeight_internal_delete_average {tau lam : ℝ} {k X : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : tau<1) (hX : 2≤X) (hk : k≤blockLength lam X) :
    average X (fun m => unorderedWeight tau lam k f X m^2*
      detector X (Finset.Ioc (blockLength lam X) (2*blockLength lam X)) m)=
      internalMarked X (blockLength lam X) (fun m c => restrictedWeight tau lam k (deletedFamily f) X m c^2) := by
  classical
  unfold internalMarked average
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  simp only [detector_I_eq,←mul_div_assoc,Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hp : Nat.Prime (m+(blockLength lam X+1+(c:ℕ)))
  · rw [unorderedWeight_prime_delete hf htau hX hk (Finset.mem_Ioc.mp hm).1 c hp]
  · simp [theta,hp]

theorem unorderedWeight_internal_marked_limit (hBV : BombieriVinogradov) {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam) :
    Tendsto (fun X : ℕ => average X (fun m => unorderedWeight tau lam k f X m^2*
      detector X (Finset.Ioc (blockLength lam X) (2*blockLength lam X)) m))
      atTop (𝓝 (familyV lam k f)) := by
  have hh := restrictedWeight_marked_limit hBV (deletedFamily f) (deletedFamily_admissible hf)
    htau htau2 hlam
  change Tendsto _ _ (𝓝 (familyV lam k f)) at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2,(blockLength_tendsto hlam).eventually_ge_atTop k] with X hX hk
  exact (unorderedWeight_internal_delete_average f hf (by linarith) hX hk).symm

theorem cumulative_tensor_permuted_kernel_invariant {n : ℕ} (e : Equiv.Perm (Fin n)) {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau) (hsym : ∀ y, f (y ∘ e)=f y)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+n)))
      (fun v => (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)) hF hFs)
      (fiberSubsetFamily (permutedLabels e) Finset.univ) = (l2Mass f:ℂ) := by
  rw [permuted_kernelConstant]
  have he : (∫ y, signedDirections (coordinateDirectionList (Fin (n+n)))
      (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
        (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)) (rayVector (permutedRay e) y)
      ∂positiveOrthantMeasure (Fin n)) =
      ∫ y, (f y^2:ℂ) ∂positiveOrthantMeasure (Fin n) := by
    apply integral_congr_ae
    rw [positiveOrthantMeasure_eq_restrict]
    filter_upwards [ae_restrict_mem (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioi))] with y hy
    rw [cumulativeProfile_signed_full (tau+tau) (tensorProfile f f)
      (tensorProfile_compact f f hf hf) (tensorProfile_smooth f f hfs hfs)
      (tensorProfile_tsupport f f hsupp hsupp)]
    · rw [rayVector_permuted,tensorProfile_append,hsym,pow_two]
      simp only [Complex.ofReal_mul]
    · intro i
      rw [rayVector_permuted]
      cases i using Fin.addCases with
      | left i => simpa using (hy i (Set.mem_univ i)).le
      | right i => simpa using (hy (e i) (Set.mem_univ (e i))).le
  rw [he]
  simp_rw [←Complex.ofReal_pow]
  rw [integral_complex_ofReal,positiveOrthantMeasure_eq_restrict]
  congr 1
  unfold l2Mass
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hfz : f y=0 := by
    by_contra hne
    exact hy (fun i _ => (hsupp (subset_tsupport f hne)).1 i)
  simp [hfz]

theorem l2Mass_tensor {n d : ℕ} (f : (Fin n → ℝ) → ℝ) (g : (Fin d → ℝ) → ℝ) :
    l2Mass (tensorProfile f g)=l2Mass f*l2Mass g := by
  unfold l2Mass
  rw [←(appendMeasurableEquiv_measurePreserving n d).integral_comp
    (appendMeasurableEquiv n d).measurableEmbedding]
  simp only [appendMeasurableEquiv_apply,tensorProfile_append,mul_pow]
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul (fun x => f x^2) (fun y => g y^2)

noncomputable def extendPerm {n : ℕ} (e : Equiv.Perm (Fin n)) (d : ℕ) : Equiv.Perm (Fin (n+d)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin d))).trans finSumFinEquiv)

@[simp] theorem extendPerm_left {n d : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    extendPerm e d (i.castAdd d)=(e i).castAdd d := by
  simp [extendPerm]

@[simp] theorem extendPerm_right {n d : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin d) :
    extendPerm e d (i.natAdd n)=i.natAdd n := by
  simp [extendPerm]

end LargePrimeGaps

end OAI
