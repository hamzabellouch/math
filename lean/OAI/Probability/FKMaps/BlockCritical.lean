import OAI.Probability.FKMaps.SeamLengths

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical

lemma stoppedWord_length_pos (T : (ℕ → Letter) → WithTop ℕ) (x : ℕ → Letter) :
    0<(stoppedWord T x).length := by simp [stoppedWord,revealed]
lemma rawSeamWord_seamWord (h : ℕ) (z : (ℕ → Letter) × (ℕ → Letter)) :
    rawSeamWord h z=seamWord (stoppedWord (firstUp h) z.1).length (stoppedWord (firstDown h) z.2).length z := by
  simp only [rawSeamWord,seamWord,stoppedWord,revealed,rawWord,rawPrefix,
    List.length_reverse,List.length_ofFn,List.reverse_reverse,Fin.val_cast]
lemma up_length_injective {x : ℕ → Letter} {a b : ℕ}
    (ha : firstUp a x≠⊤) (hb : firstUp b x≠⊤)
    (he : (stoppedWord (firstUp a) x).length=(stoppedWord (firstUp b) x).length) : a=b := by
  obtain ⟨i,hi⟩ := WithTop.ne_top_iff_exists.mp ha
  obtain ⟨j,hj⟩ := WithTop.ne_top_iff_exists.mp hb
  have hei := stoppedWord_length_of_hit hi.symm
  have hej := stoppedWord_length_of_hit hj.symm
  have hij : i=j := by omega
  subst j
  have h1 := (firstUp_of_hit_iff a x i).mp hi.symm |>.1
  have h2 := (firstUp_of_hit_iff b x i).mp hj.symm |>.1
  omega

def seamIntervals (K : ℕ) : Finset (ℕ×ℕ) := (Finset.range (K+1)).biUnion Finset.HasAntidiagonal.antidiagonal
lemma mem_seamIntervals (K : ℕ) (z : ℕ×ℕ) : z∈seamIntervals K ↔ z.1+z.2≤K := by
  simp only [seamIntervals,Finset.mem_biUnion,Finset.mem_range,Finset.HasAntidiagonal.mem_antidiagonal]
  constructor
  · rintro ⟨N,hN,he⟩
    omega
  · intro h
    exact ⟨z.1+z.2,by omega,rfl⟩
lemma sum_seamIntervals {α : Type*} [AddCommMonoid α] (K : ℕ) (f : ℕ×ℕ → α) :
    (∑ z∈seamIntervals K,f z)=∑ N∈Finset.range (K+1),∑ z∈Finset.HasAntidiagonal.antidiagonal N,f z := by
  apply Finset.sum_biUnion
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro z hi hj
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hi hj
  omega
lemma sum_ite_le_of_injection {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (P : α → Prop) (Q : β → Prop) (f : α → β)
    (hf : ∀ a∈s,P a → f a∈t ∧ Q (f a))
    (hinj : ∀ a∈s,P a → ∀ b∈s,P b → f a=f b → a=b) :
    (∑ a∈s,if P a then (1:ℝ) else 0)≤∑ b∈t,if Q b then (1:ℝ) else 0 := by
  rw [Finset.sum_boole,Finset.sum_boole]
  norm_cast
  apply Finset.card_le_card_of_injOn f
  · intro a ha
    obtain ⟨has,hpa⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr (hf a has hpa)
  · intro a ha b hb he
    obtain ⟨has,hpa⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbs,hpb⟩ := Finset.mem_filter.mp hb
    exact hinj a has hpa b hbs hpb he

def shortSeamSuccess (A h : ℕ) (z : (ℕ → Letter) × (ℕ → Letter)) : Prop :=
  EmptyReducing (rawSeamWord h z) ∧ (rawSeamWord h z).length≤2*A*h^2
lemma shortSeamSuccess_measurable (A h : ℕ) : MeasurableSet {z | shortSeamSuccess A h z} :=
  (Set.to_countable {w : List Letter | EmptyReducing w ∧ w.length≤2*A*h^2}).measurableSet.preimage (rawSeamWord_measurable h)
lemma seam_count_le (A H : ℕ) (z : (ℕ → Letter) × (ℕ → Letter))
    (hfinite : ∀ h : ℕ,0<h → firstUp h z.1≠⊤) :
    (∑ h∈Finset.Icc 1 H,if shortSeamSuccess A h z then (1:ℝ) else 0) ≤
      ∑ i∈seamIntervals (2*A*H^2),if EmptyReducing (seamWord (i.1+1) (i.2+1) z) then (1:ℝ) else 0 := by
  let f : ℕ → ℕ×ℕ := fun h => ((stoppedWord (firstUp h) z.1).length-1,(stoppedWord (firstDown h) z.2).length-1)
  apply sum_ite_le_of_injection _ _ _ _ f
  · intro h hh hs
    have hh' := Finset.mem_Icc.mp hh
    have hle : h^2≤H^2 := Nat.pow_le_pow_left hh'.2 2
    have hp1 := stoppedWord_length_pos (firstUp h) z.1
    have hp2 := stoppedWord_length_pos (firstDown h) z.2
    have hlen := hs.2
    rw [rawSeamWord_length] at hlen
    constructor
    · rw [mem_seamIntervals]
      dsimp [f]
      have := Nat.mul_le_mul_left (2*A) hle
      omega
    · change EmptyReducing (seamWord ((stoppedWord (firstUp h) z.1).length-1+1)
        ((stoppedWord (firstDown h) z.2).length-1+1) z)
      rw [Nat.sub_add_cancel hp1,Nat.sub_add_cancel hp2,← rawSeamWord_seamWord]
      exact hs.1
  · intro a ha _ b hb _ he
    have hab := congrArg Prod.fst he
    have hp1 := stoppedWord_length_pos (firstUp a) z.1
    have hp2 := stoppedWord_length_pos (firstUp b) z.1
    apply up_length_injective (hfinite a (by have := (Finset.mem_Icc.mp ha).1; omega))
      (hfinite b (by have := (Finset.mem_Icc.mp hb).1; omega))
    dsimp [f] at hab
    omega

lemma interval_expected_count (P : Parameters) (K : ℕ) :
    (∑ i∈seamIntervals K,((streamLaw P ℕ).prod (streamLaw P ℕ)).real
      {z | EmptyReducing (seamWord (i.1+1) (i.2+1) z)})=
      ∑ N∈Finset.range (K+1),(N+1:ℝ)*emptyProb P (N+2) := by
  rw [sum_seamIntervals]
  apply Finset.sum_congr rfl
  intro N _
  simp_rw [seamWord_empty_measure]
  calc
    _ = ∑ _i∈Finset.HasAntidiagonal.antidiagonal N,emptyProb P (N+2) := by
      apply Finset.sum_congr rfl
      intro i hi
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hi
      congr 1
      omega
    _ = _ := by simp

/-- Counting the actual distinct stopped seam intervals gives quantitative
quadratic-scale partial-sum lower bounds for the exact empty-word probabilities. -/
theorem emptyProb_partial_lower (P : Parameters) : ∃ (δ : ℝ) (A : ℕ),0<δ ∧ 0<A ∧ ∀ H : ℕ,
    δ*H ≤ ∑ N∈Finset.range (2*A*H^2+1),(N+1:ℝ)*emptyProb P (N+2) := by
  obtain ⟨δ,A,hδ,hA,h⟩ := short_seam_uniform P
  refine ⟨δ,A,hδ,hA,?_⟩
  intro H
  let μ := (streamLaw P ℕ).prod (streamLaw P ℕ)
  let S := Finset.Icc 1 H
  let T := seamIntervals (2*A*H^2)
  let F (h : ℕ) (z : (ℕ → Letter) × (ℕ → Letter)) : ℝ := if shortSeamSuccess A h z then 1 else 0
  let G (i : ℕ×ℕ) (z : (ℕ → Letter) × (ℕ → Letter)) : ℝ := if EmptyReducing (seamWord (i.1+1) (i.2+1) z) then 1 else 0
  have hF (h : ℕ) : Integrable (F h) μ := (integrable_const (1:ℝ)).indicator (shortSeamSuccess_measurable A h)
  have hG (i : ℕ×ℕ) : Integrable (G i) μ := (integrable_const (1:ℝ)).indicator
    ((Set.to_countable {w | EmptyReducing w}).measurableSet.preimage (seamWord_measurable (i.1+1) (i.2+1)))
  have heF (h : ℕ) : (∫ z,F h z ∂μ)=μ.real {z | shortSeamSuccess A h z} := integral_indicator_one (shortSeamSuccess_measurable A h)
  have heG (i : ℕ×ℕ) : (∫ z,G i z ∂μ)=μ.real {z | EmptyReducing (seamWord (i.1+1) (i.2+1) z)} :=
    integral_indicator_one ((Set.to_countable {w | EmptyReducing w}).measurableSet.preimage (seamWord_measurable (i.1+1) (i.2+1)))
  have hfin : ∀ᵐ z ∂μ,∀ h : ℕ,0<h → firstUp h z.1≠⊤ := by
    apply ae_all_iff.mpr
    intro h
    by_cases hh : 0<h
    · filter_upwards [(measurePreserving_fst (μ := streamLaw P ℕ) (ν := streamLaw P ℕ)).quasiMeasurePreserving.ae (firstUp_finite P h hh)] with z hz _
      exact hz
    · exact Filter.Eventually.of_forall (fun z hz => (hh hz).elim)
  have hm : (∫ z,∑ h∈S,F h z ∂μ)≤∫ z,∑ i∈T,G i z ∂μ := by
    apply integral_mono_ae (integrable_finsetSum _ (fun h _ => hF h)) (integrable_finsetSum _ (fun i _ => hG i))
    filter_upwards [hfin] with z hz
    exact seam_count_le A H z hz
  rw [integral_finsetSum _ (fun h _ => hF h),integral_finsetSum _ (fun i _ => hG i)] at hm
  simp_rw [heF,heG] at hm
  rw [interval_expected_count] at hm
  apply le_trans _ hm
  calc
    δ*(H:ℝ) = ∑ _h∈S,δ := by simp [S]; ring
    _ ≤ _ := Finset.sum_le_sum (fun j hj => h j (by have := (Finset.mem_Icc.mp hj).1; omega))

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Analysis

lemma log_lower_near_one {x : ℝ} (hx : (1:ℝ)/2≤x) (hx1 : x≤1) : -2*(1-x)≤Real.log x := by
  have hx0 : 0<x := by linarith
  apply le_trans _ (Real.one_sub_inv_le_log_of_pos hx0)
  have hi : x*x⁻¹=1 := mul_inv_cancel₀ hx0.ne'
  have hp := mul_nonneg (show 0≤1-x by linarith) (show 0≤2*x-1 by linarith)
  apply (mul_le_mul_iff_right₀ hx0).mp
  nlinarith

/-- A square-root lower bound on quadratic partial sums implies the exact
Abel square-root divergence, without an unproved Tauberian principle. -/
theorem quadratic_partial_abel_lower (b : ℕ → ℝ) (hb : ∀ n,0≤b n)
    (δ : ℝ) (hδ : 0<δ) (A : ℕ)
    (hpartial : ∀ H : ℕ,δ*H≤∑ n∈Finset.range (2*A*H^2+1),b n) :
    ∃ c : ℝ,0<c ∧ ∀ x : ℝ,(3:ℝ)/4≤x → x<1 →
      Summable (fun n => b n*x^n) → c/Real.sqrt (1-x)≤∑' n,b n*x^n := by
  let c := δ*Real.exp (-4*A)/2
  refine ⟨c,by dsimp [c]; positivity,?_⟩
  intro x hx hx1 hsum
  have hx0 : 0<x := by linarith
  have hu : 0<1-x := by linarith
  have hs : 0<Real.sqrt (1-x) := Real.sqrt_pos.mpr hu
  have hs2 : Real.sqrt (1-x)^2=1-x := Real.sq_sqrt hu.le
  have hsbound : Real.sqrt (1-x)≤1/2 := by nlinarith [Real.sqrt_nonneg (1-x)]
  let r := 1/Real.sqrt (1-x)
  let H := ⌊r⌋₊
  have hrpos : 0≤r := by dsimp [r]; positivity
  have hr2 : 2≤r := by dsimp [r]; apply (le_div_iff₀ hs).mpr; linarith
  have hHle : (H:ℝ)≤r := Nat.floor_le hrpos
  have hrlt : r<(H:ℝ)+1 := Nat.lt_floor_add_one r
  have hHhalf : r/2≤(H:ℝ) := by linarith
  have hHr : (H:ℝ)*Real.sqrt (1-x)≤1 := by
    have he := (le_div_iff₀ hs).mp hHle
    exact he
  have hHsq : (H:ℝ)^2*(1-x)≤1 := by
    have he := pow_le_pow_left₀ (show 0≤(H:ℝ)*Real.sqrt (1-x) by positivity) hHr 2
    simpa only [mul_pow,hs2,one_pow] using he
  let M := 2*A*H^2
  have hM : (M:ℝ)*(1-x)≤2*(A:ℝ) := by
    have he := mul_le_mul_of_nonneg_left hHsq (show 0≤2*(A:ℝ) by positivity)
    dsimp [M]
    push_cast
    nlinarith
  have hlog := log_lower_near_one (x := x) (by linarith) hx1.le
  have hpow : Real.exp (-4*A)≤x^M := by
    rw [← Real.exp_log hx0,← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hlog (show 0≤(M:ℝ) by positivity)
    nlinarith
  have hpart : δ*(H:ℝ)*x^M≤∑ n∈Finset.range (M+1),b n*x^n := by
    calc
      _ ≤ (∑ n∈Finset.range (M+1),b n)*x^M := mul_le_mul_of_nonneg_right (hpartial H) (pow_nonneg hx0.le _)
      _ = ∑ n∈Finset.range (M+1),b n*x^M := Finset.sum_mul _ _ _
      _ ≤ _ := Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hx0.le hx1.le (by have := Finset.mem_range.mp hn; omega)) (hb n))
  have htsum := hsum.sum_le_tsum (Finset.range (M+1)) (fun n _ => mul_nonneg (hb n) (pow_nonneg hx0.le _))
  apply le_trans _ (hpart.trans htsum)
  have he1 := mul_le_mul_of_nonneg_left hpow (show 0≤δ*(H:ℝ) by positivity)
  have he2 := mul_le_mul_of_nonneg_left hHhalf (show 0≤δ*Real.exp (-4*A) by positivity)
  dsimp [c,r] at *
  calc
    _ = (δ*Real.exp (-4*A))*((1/Real.sqrt (1-x))/2) := by ring
    _ ≤ (δ*Real.exp (-4*A))*(H:ℝ) := he2
    _ = δ*(H:ℝ)*Real.exp (-4*A) := by ring
    _ ≤ _ := he1

end FKCRT.Analysis
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma increment_sum_parity (w : List Letter) :
    (w.map Letter.increment).sum%2=(w.length:ℤ)%2 := by
  induction w with
  | nil => simp
  | cons a w ih =>
    cases a <;> simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,Letter.increment] <;> omega
lemma emptyReducing_even {w : List Letter} (h : EmptyReducing w) : Even w.length := by
  have hp := increment_sum_parity w
  rw [(emptyReducing_dyck w h).1] at hp
  exact ⟨w.length/2,by omega⟩
lemma emptyProb_odd (P : Parameters) (N : ℕ) : emptyProb P (2*N+1)=0 := by
  have he : {x | EmptyReducing (rawWord x (2*N+1))}=∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    obtain ⟨j,hj⟩ := emptyReducing_even hx
    simp only [rawWord,List.length_ofFn] at hj
    omega
  simp only [emptyProb,he,measureReal_empty]
lemma emptyProb_le_one (P : Parameters) (N : ℕ) : emptyProb P N≤1 := measureReal_le_one

lemma empty_interval_pair_sum (P : Parameters) (M : ℕ) :
    (∑ N∈Finset.range (2*M+1),(N+1:ℝ)*emptyProb P (N+2))=
      ∑ n∈Finset.range (M+1),(2*n+1:ℝ)*emptyProb P (2*(n+1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2*(M+1)+1=(2*M+1)+1+1 by omega,Finset.sum_range_succ (n := 2*M+1+1),Finset.sum_range_succ (n := 2*M+1),ih,Finset.sum_range_succ (n := M+1)]
    rw [show 2*M+1+2=2*(M+1)+1 by omega,emptyProb_odd]
    simp only [mul_zero,add_zero]
    congr 1
    push_cast
    congr 1; ring

lemma empty_even_partial_lower (P : Parameters) : ∃ (δ : ℝ) (A : ℕ),0<δ ∧ 0<A ∧ ∀ H : ℕ,
    δ*H≤∑ n∈Finset.range (2*A*H^2+1),(n:ℝ)*emptyProb P (2*n) := by
  obtain ⟨δ,A,hδ,hA,h⟩ := emptyProb_partial_lower P
  refine ⟨δ/2,A+1,by positivity,by omega,?_⟩
  intro H
  by_cases hH : H=0
  · simp [hH]
  have hH1 : 1≤H := by omega
  have hsquare : 1≤H^2 := by nlinarith
  have hle : A*H^2+2≤2*(A+1)*H^2+1 := by nlinarith
  have hp := h H
  rw [show 2*A*H^2=2*(A*H^2) by ring,empty_interval_pair_sum] at hp
  have hi : (∑ n∈Finset.range (A*H^2+1),(2*n+1:ℝ)*emptyProb P (2*(n+1)))≤
      2*(∑ n∈Finset.range (A*H^2+2),(n:ℝ)*emptyProb P (2*n)) := by
    rw [show A*H^2+2=(A*H^2+1)+1 by omega,Finset.sum_range_succ' (n := A*H^2+1)]
    simp only [Nat.cast_zero,zero_mul,add_zero,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    have := emptyProb_nonneg P (2*(n+1))
    push_cast
    nlinarith
  have hj := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hle)
    (fun n _ _ => mul_nonneg (Nat.cast_nonneg n) (emptyProb_nonneg P (2*n)))
  nlinarith [hp.trans hi]

lemma summable_empty_abel (P : Parameters) {x : ℝ} (hx : 0≤x) (hx' : x<1) :
    Summable (fun n : ℕ => (n:ℝ)*emptyProb P (2*n)*x^n) := by
  have hs : Summable (fun n : ℕ => (n:ℝ)*x^n) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1
      (by simpa only [Real.norm_eq_abs,abs_of_nonneg hx] using hx')
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (emptyProb_nonneg P (2*n))) (pow_nonneg hx n)) (fun n => ?_) hs
  have h := mul_le_mul_of_nonneg_left (emptyProb_le_one P (2*n)) (Nat.cast_nonneg n : (0:ℝ)≤n)
  exact mul_le_mul_of_nonneg_right (by simpa only [mul_one] using h) (pow_nonneg hx _)

/-- The exact genuine iid inventory empty-word coefficients satisfy the source
Abel square-root lower bound; no map-counting identity is assumed here. -/
theorem empty_abel_lower (P : Parameters) : ∃ c : ℝ,0<c ∧ ∀ x : ℝ,(3:ℝ)/4≤x → x<1 →
    c/Real.sqrt (1-x)≤∑' n : ℕ,(n:ℝ)*emptyProb P (2*n)*x^n := by
  obtain ⟨δ,A,hδ,_,hpartial⟩ := empty_even_partial_lower P
  obtain ⟨c,hc,h⟩ := Analysis.quadratic_partial_abel_lower (fun n => (n:ℝ)*emptyProb P (2*n))
    (fun n => mul_nonneg (Nat.cast_nonneg n) (emptyProb_nonneg P (2*n))) δ hδ A hpartial
  exact ⟨c,hc,fun x hx hx' => h x hx hx' (summable_empty_abel P (by linarith) hx')⟩

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.BlockCritical

def geomPrefix (k : ℕ) (x : ℝ) : ℝ := ∑ i ∈ Finset.range k,x^i

def triPrefix (k : ℕ) (x : ℝ) : ℝ := ∑ i ∈ Finset.range k,geomPrefix i x

lemma geomPrefix_nonneg (k : ℕ) {x : ℝ} (hx : 0≤x) : 0≤geomPrefix k x := by
  exact Finset.sum_nonneg (fun _ _ => pow_nonneg hx _)

lemma geomPrefix_mul (k : ℕ) (x : ℝ) : (1-x)*geomPrefix k x=1-x^k := by
  induction k with
  | zero => simp [geomPrefix]
  | succ k ih =>
    simp only [geomPrefix,Finset.sum_range_succ] at ih ⊢
    rw [mul_add,ih,pow_succ]
    ring

lemma geomPrefix_le_nat (k : ℕ) {x : ℝ} (hx : 0≤x) (hx' : x≤1) :
    geomPrefix k x≤k := by
  calc
    geomPrefix k x ≤ ∑ _i ∈ Finset.range k,(1:ℝ) :=
      Finset.sum_le_sum fun _ _ => pow_le_one₀ hx hx'
    _ = k := by simp

lemma geomPrefix_le_inv (k : ℕ) {x : ℝ} (hx : 0≤x) (hx' : x<1) :
    geomPrefix k x≤1/(1-x) := by
  apply (le_div_iff₀ (sub_pos.mpr hx')).2
  rw [mul_comm,geomPrefix_mul]
  linarith [pow_nonneg hx k]

@[simp] lemma geomPrefix_one (k : ℕ) : geomPrefix k 1=k := by simp [geomPrefix]

lemma continuous_geomPrefix (k : ℕ) : Continuous (geomPrefix k) := by
  unfold geomPrefix
  fun_prop

lemma triPrefix_nonneg (k : ℕ) {x : ℝ} (hx : 0≤x) : 0≤triPrefix k x :=
  Finset.sum_nonneg (fun _ _ => geomPrefix_nonneg _ hx)

lemma triPrefix_mul (k : ℕ) (x : ℝ) :
    (1-x)^2*triPrefix k x=x^k-1+(k:ℝ)*(1-x) := by
  induction k with
  | zero => simp [triPrefix]
  | succ k ih =>
    change (1-x)^2*(∑ i ∈ Finset.range (k+1),geomPrefix i x)=_
    rw [Finset.sum_range_succ,mul_add]
    change (1-x)^2*triPrefix k x+(1-x)^2*geomPrefix k x=_
    rw [ih,show (1-x)^2*geomPrefix k x=(1-x)*((1-x)*geomPrefix k x) by ring,
      geomPrefix_mul,pow_succ,Nat.cast_add,Nat.cast_one]
    ring

lemma triPrefix_le_div (k : ℕ) {x : ℝ} (hx : 0≤x) (hx' : x<1) :
    triPrefix k x≤(k:ℝ)/(1-x) := by
  calc
    triPrefix k x≤∑ _i ∈ Finset.range k,1/(1-x) :=
      Finset.sum_le_sum fun _ _ => geomPrefix_le_inv _ hx hx'
    _ = (k:ℝ)/(1-x) := by simp [div_eq_mul_inv]

lemma square_eq_triPrefix (k : ℕ) : (k:ℝ)^2=(k:ℝ)+2*triPrefix k 1 := by
  induction k with
  | zero => simp [triPrefix]
  | succ k ih =>
    change ((k+1:ℕ):ℝ)^2=((k+1:ℕ):ℝ)+2*(∑ i ∈ Finset.range (k+1),geomPrefix i 1)
    rw [Finset.sum_range_succ,geomPrefix_one,Nat.cast_add,Nat.cast_one]
    change ((k:ℝ)+1)^2=(k:ℝ)+1+2*(triPrefix k 1+(k:ℝ))
    nlinarith

lemma continuous_triPrefix (k : ℕ) : Continuous (triPrefix k) := by
  exact continuous_finsetSum _ (fun i _ => continuous_geomPrefix i)

structure Weights where
  mass : ℕ → ℝ
  nonneg : ∀ k,0 ≤ mass k
  total : HasSum mass 1

def Weights.pgf (p : Weights) (x : ℝ) : ℝ := ∑' k,p.mass k*x^k

lemma Weights.summable_pgf (p : Weights) {x : ℝ} (hx : 0≤x) (hx' : x≤1) :
    Summable (fun k => p.mass k*x^k) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (p.nonneg k) (pow_nonneg hx k))
    (fun k => ?_) p.total.summable
  exact mul_le_of_le_one_right (p.nonneg k) (pow_le_one₀ hx hx')

lemma Weights.pgf_nonneg (p : Weights) {x : ℝ} (hx : 0≤x) : 0≤p.pgf x :=
  tsum_nonneg (fun k => mul_nonneg (p.nonneg k) (pow_nonneg hx k))

lemma Weights.pgf_le_one (p : Weights) {x : ℝ} (hx : 0≤x) (hx' : x≤1) : p.pgf x≤1 := by
  rw [← p.total.tsum_eq]
  exact (p.summable_pgf hx hx').tsum_le_tsum
    (fun k => mul_le_of_le_one_right (p.nonneg k) (pow_le_one₀ hx hx')) p.total.summable

lemma Weights.summable_geom (p : Weights) {x : ℝ} (hx : 0≤x) (hx' : x<1) :
    Summable (fun k => p.mass k*geomPrefix k x) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (p.nonneg k) (geomPrefix_nonneg k hx))
    (fun k => mul_le_mul_of_nonneg_left (geomPrefix_le_inv k hx hx') (p.nonneg k))
    (p.total.summable.mul_right _)

lemma Weights.geom_identity (p : Weights) {x : ℝ} (hx : 0≤x) (hx' : x<1) :
    (1-x)*(∑' k,p.mass k*geomPrefix k x)=1-p.pgf x := by
  have hh := p.total.sub (p.summable_pgf hx hx'.le).hasSum
  have hi : ∀ k,p.mass k-p.mass k*x^k=(1-x)*(p.mass k*geomPrefix k x) := by
    intro k
    rw [show (1-x)*(p.mass k*geomPrefix k x)=p.mass k*((1-x)*geomPrefix k x) by ring,geomPrefix_mul]
    ring
  simp_rw [hi] at hh
  exact ((p.summable_geom hx hx').hasSum.mul_left (1-x)).unique hh

lemma Weights.tendsto_pgf (p : Weights) {x : ℕ → ℝ} (hx : ∀ n,0≤x n ∧ x n≤1)
    (ht : Tendsto x atTop (𝓝 1)) : Tendsto (fun n => p.pgf (x n)) atTop (𝓝 1) := by
  have hd := tendsto_tsum_of_dominated_convergence p.total.summable
    (fun k => (tendsto_const_nhds.mul (ht.pow k)))
    (Eventually.of_forall (fun n k => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (p.nonneg k) (pow_nonneg (hx n).1 k))]
      exact mul_le_of_le_one_right (p.nonneg k) (pow_le_one₀ (hx n).1 (hx n).2)))
  simpa only [one_pow,mul_one,p.total.tsum_eq,Weights.pgf] using hd

/-- A quadratic inverse gap is enough for the exact critical first moment and
finite second moment. No analyticity past the endpoint or third moment occurs.
The hypotheses are the normalized source inverse bound, not moment assumptions. -/
theorem Weights.moments_of_quadratic (p : Weights) {x : ℕ → ℝ}
    (hx : ∀ n,0≤x n ∧ x n<1) (ht : Tendsto x atTop (𝓝 1))
    {C : ℝ} (_hC : 0≤C)
    (hgap : ∀ n,0≤(p.pgf (x n))^2-x n ∧
      (p.pgf (x n))^2-x n≤C*(1-x n)^2) :
    HasSum (fun k : ℕ => (k:ℝ)*p.mass k) (1/2) ∧
      Summable (fun k : ℕ => (k:ℝ)^2*p.mass k) := by
  have hb (n) : (∑' k,p.mass k*geomPrefix k (x n))≤1 := by
    have hi := p.geom_identity (hx n).1 (hx n).2
    have hp := p.pgf_le_one (hx n).1 (hx n).2.le
    have hpos := p.pgf_nonneg (hx n).1
    have hg := (hgap n).1
    have hl : x n≤p.pgf (x n) := by nlinarith
    nlinarith [(sub_pos.mpr (hx n).2)]
  have hf (s : Finset ℕ) : (∑ k ∈ s,p.mass k*(k:ℝ))≤1 := by
    have hlim : Tendsto (fun n => ∑ k ∈ s,p.mass k*geomPrefix k (x n)) atTop
        (𝓝 (∑ k ∈ s,p.mass k*(k:ℝ))) := by
      apply tendsto_finsetSum
      intro k _
      simpa only [geomPrefix_one,Function.comp_def] using tendsto_const_nhds.mul ((continuous_geomPrefix k).tendsto 1 |>.comp ht)
    apply le_of_tendsto hlim
    exact Eventually.of_forall (fun n =>
      (Summable.sum_le_tsum s (fun k _ => mul_nonneg (p.nonneg k) (geomPrefix_nonneg k (hx n).1))
        (p.summable_geom (hx n).1 (hx n).2)).trans (hb n))
  have hm : Summable (fun k => p.mass k*(k:ℝ)) :=
    summable_of_sum_le (fun k => mul_nonneg (p.nonneg k) (Nat.cast_nonneg k)) hf
  let μ := ∑' k,p.mass k*(k:ℝ)
  have hD : Tendsto (fun n => ∑' k,p.mass k*geomPrefix k (x n)) atTop (𝓝 μ) := by
    apply tendsto_tsum_of_dominated_convergence hm
    · intro k
      simpa only [geomPrefix_one,Function.comp_def] using tendsto_const_nhds.mul ((continuous_geomPrefix k).tendsto 1 |>.comp ht)
    · exact Eventually.of_forall (fun n k => by
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (p.nonneg k) (geomPrefix_nonneg k (hx n).1))]
        exact mul_le_mul_of_nonneg_left (geomPrefix_le_nat k (hx n).1 (hx n).2.le) (p.nonneg k))
  have hp := p.tendsto_pgf (fun n => ⟨(hx n).1,(hx n).2.le⟩) ht
  have hprod : Tendsto (fun n => (1+p.pgf (x n))*(∑' k,p.mass k*geomPrefix k (x n))) atTop (𝓝 ((1+1)*μ)) := (tendsto_const_nhds.add hp).mul hD
  have he (n) : (1-x n)*(1-(1+p.pgf (x n))*(∑' k,p.mass k*geomPrefix k (x n)))=
      (p.pgf (x n))^2-x n := by
    rw [show (1-x n)*(1-(1+p.pgf (x n))*(∑' k,p.mass k*geomPrefix k (x n)))=
      1-x n-(1+p.pgf (x n))*((1-x n)*(∑' k,p.mass k*geomPrefix k (x n))) by ring,
      p.geom_identity (hx n).1 (hx n).2]
    ring
  have heBounds (n) : 0≤1-(1+p.pgf (x n))*(∑' k,p.mass k*geomPrefix k (x n)) ∧
      1-(1+p.pgf (x n))*(∑' k,p.mass k*geomPrefix k (x n))≤C*(1-x n) := by
    have hid := he n
    have h := hgap n
    have hxpos : 0<1-x n := sub_pos.mpr (hx n).2
    constructor <;> nlinarith
  have hμ : μ=1/2 := by
    have hl : 0≤1-(1+1)*μ := ge_of_tendsto (tendsto_const_nhds.sub hprod)
      (Eventually.of_forall (fun n => (heBounds n).1))
    have hz : Tendsto (fun n => C*(1-x n)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul (tendsto_const_nhds.sub ht) : Tendsto (fun n => C*(1-x n)) atTop (𝓝 (C*(1-1))))
    have hu : 1-(1+1)*μ≤0 := le_of_tendsto_of_tendsto (tendsto_const_nhds.sub hprod)
      hz
      (Eventually.of_forall (fun n => (heBounds n).2))
    linarith
  have hts (n) : Summable (fun k => p.mass k*triPrefix k (x n)) := by
    apply Summable.of_nonneg_of_le
      (fun k => mul_nonneg (p.nonneg k) (triPrefix_nonneg k (hx n).1))
      (fun k => ?_) (hm.mul_right (1/(1-x n)))
    simpa only [div_eq_mul_inv,one_mul,mul_assoc] using mul_le_mul_of_nonneg_left (triPrefix_le_div k (hx n).1 (hx n).2) (p.nonneg k)
  have htri (n) : (1-x n)^2*(∑' k,p.mass k*triPrefix k (x n))=
      p.pgf (x n)-1+(1-x n)/2 := by
    have hh := ((p.summable_pgf (hx n).1 (hx n).2.le).hasSum.sub p.total).add (hm.hasSum.mul_left (1-x n))
    have hid (k) : p.mass k*(x n)^k-p.mass k+(1-x n)*(p.mass k*(k:ℝ))=
        (1-x n)^2*(p.mass k*triPrefix k (x n)) := by
      rw [show (1-x n)^2*(p.mass k*triPrefix k (x n))=
        p.mass k*((1-x n)^2*triPrefix k (x n)) by ring,triPrefix_mul]
      ring
    simp_rw [hid] at hh
    have hu := ((hts n).hasSum.mul_left ((1-x n)^2)).unique hh
    change (1-x n)^2*(∑' k,p.mass k*triPrefix k (x n))=p.pgf (x n)-1+(1-x n)*μ at hu
    rw [hμ] at hu
    simpa only [mul_one_div] using hu
  have hbtri (n) : (∑' k,p.mass k*triPrefix k (x n))≤2*C := by
    have hp0 := p.pgf_nonneg (hx n).1
    have hxn := (hx n).1
    have hxp : 0<1-x n := sub_pos.mpr (hx n).2
    have hs0 : 0≤∑' k,p.mass k*triPrefix k (x n) := tsum_nonneg (fun k => mul_nonneg (p.nonneg k) (triPrefix_nonneg k hxn))
    have hrem : 0≤p.pgf (x n)-1+(1-x n)/2 := by rw [← htri n]; positivity
    have htpos : 0<(1-x n)^2 := sq_pos_of_pos hxp
    have hmul : (p.pgf (x n)-1+(1-x n)/2)*(p.pgf (x n)+(1+x n)/2)=
      (p.pgf (x n))^2-x n-(1-x n)^2/4 := by ring
    have hhalf : 1/2≤p.pgf (x n)+(1+x n)/2 := by linarith
    have hbound := (hgap n).2
    have hrf : (p.pgf (x n)-1+(1-x n)/2)/2≤C*(1-x n)^2 := by nlinarith
    rw [← htri n] at hrf
    nlinarith
  have htriSum : Summable (fun k => p.mass k*triPrefix k 1) := by
    apply summable_of_sum_le (fun k => mul_nonneg (p.nonneg k) (triPrefix_nonneg k (by norm_num)))
    intro s
    apply le_of_tendsto (tendsto_finsetSum s (fun k _ =>
      tendsto_const_nhds.mul ((continuous_triPrefix k).tendsto 1 |>.comp ht)))
    exact Eventually.of_forall (fun n =>
      (Summable.sum_le_tsum s (fun k _ => mul_nonneg (p.nonneg k) (triPrefix_nonneg k (hx n).1))
        (hts n)).trans (hbtri n))
  constructor
  · have hm' : HasSum (fun k => p.mass k*(k:ℝ)) μ := hm.hasSum
    rw [hμ] at hm'
    simpa only [mul_comm] using hm'
  · apply (hm.add (htriSum.mul_left 2)).congr
    intro k
    rw [square_eq_triPrefix]
    ring

end FKCRT.BlockCritical
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.BlockCritical

lemma Weights.mass_le_one (p : Weights) (k : ℕ) : p.mass k≤1 := by
  rw [← p.total.tsum_eq]
  exact p.total.summable.le_tsum k (fun i _ => p.nonneg i)

def Weights.abelMean (p : Weights) (x : ℝ) : ℝ := ∑' k : ℕ,(k:ℝ)*p.mass k*x^k

lemma Weights.summable_abelMean (p : Weights) {x : ℝ} (hx : 0≤x) (hx' : x<1) :
    Summable (fun k : ℕ => (k:ℝ)*p.mass k*x^k) := by
  have hs : Summable (fun k : ℕ => (k:ℝ)*x^k) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1
      (by simpa only [Real.norm_eq_abs,abs_of_nonneg hx] using hx')
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (p.nonneg k)) (pow_nonneg hx k)) (fun k => ?_) hs
  nlinarith [mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hx k),p.mass_le_one k]

lemma geomPrefix_lower (k : ℕ) {x : ℝ} (hx : 0≤x) (hx' : x≤1) :
    (k:ℝ)*x^k≤geomPrefix k x := by
  calc
    (k:ℝ)*x^k = ∑ _i ∈ Finset.range k,x^k := by simp
    _ ≤ geomPrefix k x := Finset.sum_le_sum (fun i hi =>
      pow_le_pow_of_le_one hx hx' (Finset.mem_range.mp hi).le)

lemma Weights.abelMean_gap (p : Weights) {x : ℝ} (hx : 0≤x) (hx' : x<1) :
    (1-x)*p.abelMean x≤1-p.pgf x := by
  rw [← p.geom_identity hx hx']
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hx'.le)
  apply (p.summable_abelMean hx hx').tsum_le_tsum _ (p.summable_geom hx hx')
  intro k
  nlinarith [mul_le_mul_of_nonneg_left (geomPrefix_lower k hx hx'.le) (p.nonneg k)]

/-- Endpoint passage for nonnegative coefficients. This supplies the endpoint
normalization of Phi from the actual interior substitution equation; it does
not assume the desired probability normalization. -/
lemma hasSum_of_pgf_limit {b : ℕ → ℝ} (hb : ∀ k,0≤b k)
    {x t : ℕ → ℝ} (hx : ∀ n,0≤x n ∧ x n≤1)
    (hxt : Tendsto x atTop (𝓝 1)) (ht : Tendsto t atTop (𝓝 1))
    (heq : ∀ n,HasSum (fun k => b k*(x n)^k) (t n)) : HasSum b 1 := by
  have hf (s : Finset ℕ) : (∑ k ∈ s,b k)≤1 := by
    have hl : Tendsto (fun n => ∑ k ∈ s,b k*(x n)^k) atTop (𝓝 (∑ k ∈ s,b k)) := by
      simpa only [one_pow,mul_one] using tendsto_finsetSum s
        (fun k _ => tendsto_const_nhds.mul (hxt.pow k))
    apply le_of_tendsto_of_tendsto hl ht
    exact Eventually.of_forall (fun n => by
      rw [← (heq n).tsum_eq]
      exact Summable.sum_le_tsum s (fun k _ => mul_nonneg (hb k) (pow_nonneg (hx n).1 k)) (heq n).summable)
  have hs := summable_of_sum_le hb hf
  have hp : Tendsto (fun n => ∑' k,b k*(x n)^k) atTop (𝓝 (∑' k,b k)) := by
    have hh := tendsto_tsum_of_dominated_convergence hs
      (fun k => tendsto_const_nhds.mul (hxt.pow k))
      (Eventually.of_forall (fun n k => by
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hb k) (pow_nonneg (hx n).1 k))]
        exact mul_le_of_le_one_right (hb k) (pow_le_one₀ (hx n).1 (hx n).2)))
    simpa only [one_pow,mul_one] using hh
  have he : (fun n => ∑' k,b k*(x n)^k)=t := funext (fun n => (heq n).tsum_eq)
  rw [he] at hp
  exact tendsto_nhds_unique hp ht ▸ hs.hasSum

/-- Source block:critical in normalized variables. Only the original
nonnegative generating-function substitution and Abel lower bound are used.
The mean/variance conclusions are proved, not included as assumptions. -/
theorem normalized_inverse_critical (p : Weights) {b : ℕ → ℝ}
    (hb : ∀ k,0≤b k) {x : ℕ → ℝ} (hx : ∀ n,0≤x n ∧ x n<1)
    (ht : Tendsto x atTop (𝓝 1))
    (heq : ∀ n,HasSum (fun k => b k*(x n*(p.pgf (x n))^2)^k) (p.pgf (x n)))
    {c : ℝ} (hc : 0<c)
    (hlower : ∀ n,c≤Real.sqrt (1-x n)*p.abelMean (x n)) :
    HasSum b 1 ∧ HasSum (fun k : ℕ => (k:ℝ)*b k) (1/2) ∧
      Summable (fun k : ℕ => (k:ℝ)^2*b k) := by
  let y := fun n => x n*(p.pgf (x n))^2
  have hpn (n) := p.pgf_nonneg (hx n).1
  have hpu (n) := p.pgf_le_one (hx n).1 (hx n).2.le
  have hyp (n) : 0≤y n ∧ y n<1 := by
    dsimp [y]
    have hp2 : (p.pgf (x n))^2≤1 := by nlinarith [hpn n,hpu n]
    constructor
    · exact mul_nonneg (hx n).1 (sq_nonneg _)
    · nlinarith [(hx n).1,(hx n).2]
  have hpt := p.tendsto_pgf (fun n => ⟨(hx n).1,(hx n).2.le⟩) ht
  have hyt : Tendsto y atTop (𝓝 1) := by
    simpa only [one_pow,mul_one] using ht.mul (hpt.pow 2)
  have hbtotal : HasSum b 1 := hasSum_of_pgf_limit hb
    (fun n => ⟨(hyp n).1,(hyp n).2.le⟩) hyt hpt heq
  let q : Weights := ⟨b,hb,hbtotal⟩
  have hq (n) : q.pgf (y n)=p.pgf (x n) := (heq n).tsum_eq
  have hgap (n) : c*Real.sqrt (1-x n)≤1-p.pgf (x n) := by
    have hgap := p.abelMean_gap (hx n).1 (hx n).2
    have hmul := mul_le_mul_of_nonneg_left (hlower n) (Real.sqrt_nonneg (1-x n))
    have hs := Real.sq_sqrt (sub_nonneg.mpr (hx n).2.le)
    rw [← mul_assoc,← sq,hs] at hmul
    linarith
  have hyl (n) : y n≤p.pgf (x n) := by
    dsimp [y]
    calc
      x n*(p.pgf (x n))^2≤(p.pgf (x n))^2 :=
        mul_le_of_le_one_left (sq_nonneg _) (hx n).2.le
      _ ≤ p.pgf (x n) := by nlinarith [hpn n,hpu n]
  have hquad (n) : 0≤(q.pgf (y n))^2-y n ∧
      (q.pgf (y n))^2-y n≤(1/c^2)*(1-y n)^2 := by
    rw [hq n]
    have hid : (p.pgf (x n))^2-y n=(1-x n)*(p.pgf (x n))^2 := by dsimp [y]; ring
    rw [hid]
    constructor
    · exact mul_nonneg (sub_nonneg.mpr (hx n).2.le) (sq_nonneg _)
    · have hg : c^2*(1-x n)≤(1-y n)^2 := by
        have h := hgap n
        have hs := Real.sq_sqrt (sub_nonneg.mpr (hx n).2.le)
        have hds : c*Real.sqrt (1-x n)≤1-y n := h.trans (by linarith [hyl n])
        have hnon := mul_nonneg hc.le (Real.sqrt_nonneg (1-x n))
        nlinarith [sq_nonneg (1-y n-c*Real.sqrt (1-x n))]
      have hp2 : (p.pgf (x n))^2≤1 := by nlinarith [hpn n,hpu n]
      have hle : (1-x n)*(p.pgf (x n))^2≤1-x n :=
        mul_le_of_le_one_right (sub_nonneg.mpr (hx n).2.le) hp2
      apply hle.trans
      rw [one_div,← div_eq_inv_mul]
      exact (le_div_iff₀ (sq_pos_of_pos hc)).2 (by nlinarith)
  exact ⟨hbtotal,q.moments_of_quadratic hyp hyt (by positivity) hquad⟩

end FKCRT.BlockCritical
end

end OAI
