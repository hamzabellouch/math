import OAI.Probability.FKMaps.LadderRecords
import OAI.Probability.FKMaps.Model

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

local instance : MeasurableSpace C(unitInterval, ℝ) := borel _
local instance : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩

def reversedPath (S : ℕ → ℤ) (b k : ℕ) : ℤ := S b-S (b-k)


lemma reverse_record_iff (S : ℕ → ℤ) {a b j : ℕ} (haj : a ≤ j) (hjb : j < b) :
    j ∈ reverseRecords S a b ↔ b-j ∈ weakRecords (reversedPath S b) (b-a) := by
  rw [mem_reverseRecords,mem_weakRecords]
  constructor
  · rintro ⟨_,_,hrec⟩
    refine ⟨by omega,by omega,?_⟩
    intro k hk
    have hr := hrec (b-k) (by omega) (by omega)
    dsimp [reversedPath]
    have he : b-(b-j)=j := by omega
    rw [he]
    omega
  · rintro ⟨_,_,hrec⟩
    refine ⟨haj,hjb,?_⟩
    intro r hjr hrb
    have hr := hrec (b-r) (by omega)
    dsimp [reversedPath] at hr
    have he : b-(b-r)=r := by omega
    have he' : b-(b-j)=j := by omega
    rw [he,he'] at hr
    omega


lemma reverse_record_filter_card (S : ℕ → ℤ) (a b : ℕ) (P : ℕ → Prop)
    [DecidablePred P] :
    ((reverseRecords S a b).filter P).card=
      ((weakRecords (reversedPath S b) (b-a)).filter fun k => P (b-k)).card := by
  classical
  apply Finset.card_bij (fun j _ => b-j)
  · intro j hj
    obtain ⟨hrec,hP⟩ := Finset.mem_filter.mp hj
    obtain ⟨haj,hjb,_⟩ := (mem_reverseRecords S a b j).mp hrec
    refine Finset.mem_filter.mpr ⟨(reverse_record_iff S haj hjb).mp hrec,?_⟩
    convert hP using 1
    omega
  · intro j hj k hk he
    have hjb := ((mem_reverseRecords S a b j).mp (Finset.mem_filter.mp hj).1).2.1
    have hkb := ((mem_reverseRecords S a b k).mp (Finset.mem_filter.mp hk).1).2.1
    omega
  · intro k hk
    obtain ⟨hrec,hP⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1,hkba,_⟩ := (mem_weakRecords _ _ _).mp hrec
    refine ⟨b-k,?_,by omega⟩
    refine Finset.mem_filter.mpr ⟨?_,hP⟩
    apply (reverse_record_iff S (by omega : a ≤ b-k) (by omega : b-k < b)).mpr
    convert hrec using 1
    omega


lemma recordHeight_dual (S : ℕ → ℤ) (a b : ℕ) :
    recordHeight S a b=(weakRecords (reversedPath S b) (b-a)).card := by
  simpa [recordHeight] using reverse_record_filter_card S a b (fun _ => True)


lemma reverseRecords_surviving_at_minimum {α : Type*} [LinearOrder α] (S : ℕ → α)
    {a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
    (hmin : ∀ r, a ≤ r → r ≤ b → S c ≤ S r)
    (hfirst : ∀ r, a ≤ r → r < c → S c < S r) :
    reverseRecords S 0 c=(reverseRecords S 0 a).filter fun j => S j ≤ S c := by
  classical
  ext j
  simp only [Finset.mem_filter,mem_reverseRecords]
  constructor
  · rintro ⟨hj0,hjc,hrec⟩
    have hja : j<a := by
      by_contra hn
      exact not_le_of_gt (hfirst j (by omega) hjc) (hrec c hjc.le le_rfl)
    exact ⟨⟨hj0,hja,fun r hjr hra => hrec r hjr (hra.trans hac)⟩,hrec c hjc.le le_rfl⟩
  · rintro ⟨⟨hj0,hja,hrec⟩,hjc⟩
    refine ⟨hj0,lt_of_lt_of_le hja hac,?_⟩
    intro r hjr hrc
    by_cases hra : r ≤ a
    · exact hrec r hjr hra
    · exact hjc.trans (hmin r (by omega) (hrc.trans hcb))


lemma recordHeight_fall_dual (S : ℕ → ℤ) {a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
    (hmin : ∀ r, a ≤ r → r ≤ b → S c ≤ S r)
    (hfirst : ∀ r, a ≤ r → r < c → S c < S r) :
    recordHeight S 0 a-recordHeight S 0 c=
      ((weakRecords (reversedPath S a) a).filter fun k => reversedPath S a k<S a-S c).card := by
  classical
  have he := reverseRecords_surviving_at_minimum S hac hcb hmin hfirst
  have hd := Finset.card_filter_add_card_filter_not (s := reverseRecords S 0 a)
    (p := fun j => S j ≤ S c)
  have hc : ((reverseRecords S 0 a).filter fun j => S c<S j).card=
      recordHeight S 0 a-recordHeight S 0 c := by
    unfold recordHeight
    rw [he]
    simp only [not_le] at hd
    omega
  rw [← hc,reverse_record_filter_card]
  simp only [Nat.sub_zero]
  congr 2
  funext k
  apply propext
  dsimp [reversedPath]
  omega


lemma recordHeight_at_first_minimum_split {α : Type*} [LinearOrder α] (S : ℕ → α)
    {a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
    (hmin : ∀ r, a ≤ r → r ≤ b → S c ≤ S r)
    (hfirst : ∀ r, a ≤ r → r < c → S c < S r) :
    recordHeight S 0 c ≤ recordHeight S 0 a ∧
      recordHeight S 0 b=recordHeight S 0 c+recordHeight S a b := by
  classical
  have he := reverseRecords_at_first_minimum S hac hcb hmin hfirst
  constructor
  · unfold recordHeight
    rw [reverseRecords_surviving_at_minimum S hac hcb hmin hfirst]
    exact Finset.card_filter_le _ _
  · unfold recordHeight
    rw [he]
    nth_rw 1 [reverseRecords_split S (hac.trans hcb)]
    apply Finset.card_union_of_disjoint
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    have hja := (Finset.mem_filter.mp hj).2
    have haj := ((mem_reverseRecords ..).mp hj').1
    omega


lemma height_oscillation_of_reverse_ladders (S : ℕ → ℤ) (a b m : ℕ) (hab : a ≤ b)
    (d : ℤ) (τa τb : ℕ → ℕ)
    (ha : LadderEnumeration (reversedPath S a) τa)
    (hb : LadderEnumeration (reversedPath S b) τb)
    (hla : d ≤ reversedPath S a (τa m)) (hlb : d ≤ reversedPath S b (τb m))
    (hosc : ∀ u v, a ≤ u → u ≤ b → a ≤ v → v ≤ b → S u-S v<d) :
    recordHeight S 0 b ≤ recordHeight S 0 a+m ∧
      recordHeight S 0 a ≤ recordHeight S 0 b+m := by
  obtain ⟨c,hac,hcb,hmin,hfirst⟩ := exists_first_path_minimum S hab
  obtain ⟨hca,hsplit⟩ := recordHeight_at_first_minimum_split S hac hcb hmin hfirst
  have hfall : recordHeight S 0 a-recordHeight S 0 c ≤ m := by
    rw [recordHeight_fall_dual S hac hcb hmin hfirst]
    exact ha.first_records_below a m (S a-S c) ((hosc a c le_rfl hab hac hcb).le.trans hla)
  have hrise : recordHeight S a b ≤ m := by
    rw [recordHeight_dual,hb.card_records]
    by_contra hn
    have hl : τb m ≤ b-a :=
      (le_renewalCount_iff hb.strictMono hb.zero m (b-a)).mp (by omega)
    have hh := hosc b (b-τb m) hab le_rfl (by omega) (by omega)
    dsimp [reversedPath] at hlb
    omega
  omega


lemma weakRecords_congr_prefix {S T : ℕ → ℤ} {n : ℕ}
    (he : ∀ k, k ≤ n → S k=T k) : weakRecords S n=weakRecords T n := by
  ext k
  simp only [mem_weakRecords]
  constructor <;> rintro ⟨hk,hkn,hr⟩ <;> refine ⟨hk,hkn,?_⟩
  · intro j hj
    rw [← he j (by omega),← he k hkn]
    exact hr j hj
  · intro j hj
    rw [he j (by omega),he k hkn]
    exact hr j hj


lemma height_oscillation_of_reverse_extensions (S : ℕ → ℤ) (a b m : ℕ) (hab : a ≤ b)
    (d : ℤ) (Ra Rb : ℕ → ℤ) (τa τb : ℕ → ℕ)
    (hea : ∀ k, k ≤ a → Ra k=reversedPath S a k)
    (heb : ∀ k, k ≤ b → Rb k=reversedPath S b k)
    (ha : LadderEnumeration Ra τa) (hb : LadderEnumeration Rb τb)
    (hla : d ≤ Ra (τa m)) (hlb : d ≤ Rb (τb m))
    (hosc : ∀ u v, a ≤ u → u ≤ b → a ≤ v → v ≤ b → S u-S v<d) :
    recordHeight S 0 b ≤ recordHeight S 0 a+m ∧
      recordHeight S 0 a ≤ recordHeight S 0 b+m := by
  classical
  obtain ⟨c,hac,hcb,hmin,hfirst⟩ := exists_first_path_minimum S hab
  obtain ⟨hca,hsplit⟩ := recordHeight_at_first_minimum_split S hac hcb hmin hfirst
  have hfall : recordHeight S 0 a-recordHeight S 0 c ≤ m := by
    rw [recordHeight_fall_dual S hac hcb hmin hfirst,
      ← weakRecords_congr_prefix hea]
    have he : ((weakRecords Ra a).filter fun k => reversedPath S a k<S a-S c)=
        ((weakRecords Ra a).filter fun k => Ra k<S a-S c) := by
      apply Finset.filter_congr
      intro k hk
      rw [hea k ((mem_weakRecords ..).mp hk).2.1]
    rw [he]
    exact ha.first_records_below a m (S a-S c) ((hosc a c le_rfl hab hac hcb).le.trans hla)
  have hrise : recordHeight S a b ≤ m := by
    rw [recordHeight_dual,← weakRecords_congr_prefix (fun k hk => heb k (by omega)),hb.card_records]
    by_contra hn
    have hl : τb m ≤ b-a :=
      (le_renewalCount_iff hb.strictMono hb.zero m (b-a)).mp (by omega)
    rw [heb (τb m) (by omega)] at hlb
    have hh := hosc b (b-τb m) hab le_rfl (by omega) (by omega)
    dsimp [reversedPath] at hlb
    omega
  omega


lemma height_oscillation_of_reverse_extensions_real (S : ℕ → ℤ) (a b m : ℕ) (hab : a ≤ b)
    (d : ℝ) (Ra Rb : ℕ → ℤ) (τa τb : ℕ → ℕ)
    (hea : ∀ k, k ≤ a → Ra k=reversedPath S a k)
    (heb : ∀ k, k ≤ b → Rb k=reversedPath S b k)
    (ha : LadderEnumeration Ra τa) (hb : LadderEnumeration Rb τb)
    (hla : d ≤ (Ra (τa m):ℝ)) (hlb : d ≤ (Rb (τb m):ℝ))
    (hosc : ∀ u v, a ≤ u → u ≤ b → a ≤ v → v ≤ b → (S u:ℝ)-(S v:ℝ)<d) :
    recordHeight S 0 b ≤ recordHeight S 0 a+m ∧
      recordHeight S 0 a ≤ recordHeight S 0 b+m := by
  classical
  obtain ⟨c,hac,hcb,hmin,hfirst⟩ := exists_first_path_minimum S hab
  obtain ⟨hca,hsplit⟩ := recordHeight_at_first_minimum_split S hac hcb hmin hfirst
  have hfall : recordHeight S 0 a-recordHeight S 0 c ≤ m := by
    rw [recordHeight_fall_dual S hac hcb hmin hfirst,
      ← weakRecords_congr_prefix hea]
    have he : ((weakRecords Ra a).filter fun k => reversedPath S a k<S a-S c)=
        ((weakRecords Ra a).filter fun k => Ra k<S a-S c) := by
      apply Finset.filter_congr
      intro k hk
      rw [hea k ((mem_weakRecords ..).mp hk).2.1]
    rw [he]
    apply ha.first_records_below a m (S a-S c)
    have hh := (hosc a c le_rfl hab hac hcb).le.trans hla
    exact_mod_cast hh
  have hrise : recordHeight S a b ≤ m := by
    rw [recordHeight_dual,← weakRecords_congr_prefix (fun k hk => heb k (by omega)),hb.card_records]
    by_contra hn
    have hl : τb m ≤ b-a :=
      (le_renewalCount_iff hb.strictMono hb.zero m (b-a)).mp (by omega)
    rw [heb (τb m) (by omega)] at hlb
    have hh := hosc b (b-τb m) hab le_rfl (by omega) (by omega)
    simp only [reversedPath,Int.cast_sub] at hlb
    linarith
  omega


def heightModulusFailure (N m : ℕ) (d : ℝ) : Set (ℕ → ℕ) :=
  {x | ∃ a b, a ≤ b ∧ b ≤ N ∧
    (∀ u v, a ≤ u → u ≤ b → a ≤ v → v ≤ b →
      (integerSum x u:ℝ)-(integerSum x v:ℝ)<d) ∧
    ¬(recordHeight (integerSum x) 0 b ≤ recordHeight (integerSum x) 0 a+m ∧
      recordHeight (integerSum x) 0 a ≤ recordHeight (integerSum x) 0 b+m)}


lemma CriticalEvenOffspring.ae_reverse_ladders (p : CriticalEvenOffspring) :
    ∀ᵐ x ∂p.streamLaw, ∀ b, HasAllLadders (reverseFirst b x) := by
  rw [ae_all_iff]
  intro b
  exact (reverseFirst_preserving p b).quasiMeasurePreserving.ae p.ae_all_ladders


lemma height_modulus_failure_subset {x : ℕ → ℕ} {N m : ℕ} {d : ℝ}
    (hx : ∀ b, HasAllLadders (reverseFirst b x)) (hbad : x ∈ heightModulusFailure N m d) :
    ∃ b ≤ N, renewalLevel m (reverseFirst b x) ≤ d := by
  by_contra hn
  push Not at hn
  obtain ⟨a,b,hab,hb,hosc,hfail⟩ := hbad
  apply hfail
  apply height_oscillation_of_reverse_extensions_real (integerSum x) a b m hab d
    (integerSum (reverseFirst a x)) (integerSum (reverseFirst b x))
    (ladderTime (reverseFirst a x)) (ladderTime (reverseFirst b x))
    (fun k hk => integerSum_reverseFirst x a k hk)
    (fun k hk => integerSum_reverseFirst x b k hk)
    (ladderTime_enumeration (hx a)) (ladderTime_enumeration (hx b))
  · rw [ladderTime_level_real (hx a)]
    exact (hn a (hab.trans hb)).le
  · rw [ladderTime_level_real (hx b)]
    exact (hn b hb).le
  · exact hosc


theorem CriticalEvenOffspring.height_modulus_probability (p : CriticalEvenOffspring) :
    ∃ c ρ : ℝ, 0<c ∧ 0<ρ ∧ ρ<1 ∧ ∀ N m : ℕ,
      p.streamLaw (heightModulusFailure N m (c*m)) ≤
        (N+1:ℕ)*ENNReal.ofReal (ρ^m) := by
  obtain ⟨c,ρ,hc,hr0,hr1,hbound⟩ := p.renewal_lower_tail
  refine ⟨c,ρ,hc,hr0,hr1,fun N m => ?_⟩
  let B := fun b => {x : ℕ → ℕ | renewalLevel m (reverseFirst b x) ≤ c*m}
  have hsub : heightModulusFailure N m (c*m) ≤ᵐ[p.streamLaw]
      ⋃ b ∈ Finset.range (N+1), B b := by
    filter_upwards [p.ae_reverse_ladders] with x hx
    intro hfail
    obtain ⟨b,hb,hbad⟩ := height_modulus_failure_subset hx hfail
    exact Set.mem_iUnion.mpr ⟨b,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),hbad⟩⟩
  apply (measure_mono_ae hsub).trans
  apply (measure_biUnion_finset_le (Finset.range (N+1)) B).trans
  calc
    ∑ b ∈ Finset.range (N+1),p.streamLaw (B b) ≤
        ∑ _b ∈ Finset.range (N+1),ENNReal.ofReal (ρ^m) := by
      apply Finset.sum_le_sum
      intro b _
      have he : B b=reverseFirst b ⁻¹' {x | renewalLevel m x ≤ c*m} := rfl
      rw [he,(reverseFirst_preserving p b).measure_preimage
        (measurableSet_le (measurable_renewalLevel m) measurable_const).nullMeasurableSet]
      exact hbound m
    _ = _ := by simp [nsmul_eq_mul]


lemma conditional_event_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {E : Set Ω} (hE : MeasurableSet E) (B : Set Ω) {a : ℝ≥0∞} (hB : μ B ≤ a) :
    cond μ E B ≤ (μ E)⁻¹*a := by
  rw [cond_apply hE]
  exact mul_le_mul le_rfl ((measure_mono Set.inter_subset_right).trans hB) bot_le bot_le


lemma CriticalEvenOffspring.conditional_height_modulus_probability (p : CriticalEvenOffspring) :
    ∃ c ρ : ℝ, 0<c ∧ 0<ρ ∧ ρ<1 ∧ ∀ N m : ℕ,
      ∀ E : Set (ℕ → ℕ), MeasurableSet E →
      cond p.streamLaw E (heightModulusFailure N m (c*m)) ≤
        (p.streamLaw E)⁻¹*((N+1:ℕ)*ENNReal.ofReal (ρ^m)) := by
  obtain ⟨c,ρ,hc,hr0,hr1,hb⟩ := p.height_modulus_probability
  exact ⟨c,ρ,hc,hr0,hr1,fun N m E hE => conditional_event_bound p.streamLaw hE _ (hb N m)⟩


def standardExcursion {Ω : Type} (B : Fin 3 → ℝ≥0 → Ω → ℝ) (ω : Ω)
    (t : unitInterval) : ℝ :=
  Real.sqrt (∑ i : Fin 3, (B i ⟨(t : ℝ), t.property.1⟩ ω -
    (t : ℝ) * B i 1 ω) ^ 2)


def diagonalExcursion {Ω : Type} (B : Fin 3 → ℝ≥0 → Ω → ℝ) (ω : Ω) :
    C(unitInterval, ℝ × ℝ) := by
  classical
  exact if h : Continuous (standardExcursion B ω) then
    (⟨standardExcursion B ω, h⟩ : C(unitInterval, ℝ)).prodMk ⟨standardExcursion B ω, h⟩
  else 0


def jointBrownianExpectation {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (B : Fin 3 → ℝ≥0 → Ω → ℝ) (F : C(unitInterval, ℝ × ℝ) → ℝ) : ℝ :=
  ∫ ω, F (diagonalExcursion B ω) ∂P


def JointCodingStatement (p : CriticalEvenOffspring) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @Measure Ω mΩ),
    @IsProbabilityMeasure Ω mΩ P →
    ∀ B : Fin 3 → ℝ≥0 → Ω → ℝ,
      (∀ i, @IsBrownianReal Ω mΩ (B i) P) →
      @iIndepFun Ω (Fin 3) mΩ (fun _ => ℝ≥0 → ℝ) (fun _ => inferInstance)
        (fun i ω t => B i t ω) P →
      ∀ F : BoundedContinuousFunction C(unitInterval, ℝ × ℝ) ℝ,
        Tendsto (fun n : ℕ => codeExpectation p (2*n+1) F) atTop
          (𝓝 (@jointBrownianExpectation Ω mΩ P B F))


def circularReversePath (S : ℕ → ℤ) (N v k : ℕ) : ℤ :=
  if k ≤ v then S v-S (v-k) else S v-1-S (N+v-k)


lemma circularReversePath_prefix (S : ℕ → ℤ) (N v k : ℕ) (hk : k ≤ v) :
    circularReversePath S N v k=reversedPath S v k := by
  simp only [circularReversePath,ite_eq_left hk,reversedPath]


lemma circular_records_of_good {S : ℕ → ℤ} {N v : ℕ} (hv : v<N)
    (hzero : S 0=0) (hpos : ∀ k, k<N → 0 ≤ S k) :
    weakRecords (circularReversePath S N v) N=weakRecords (reversedPath S v) v := by
  ext k
  simp only [mem_weakRecords]
  constructor
  · rintro ⟨hk1,hkN,hrec⟩
    have hkv : k ≤ v := by
      by_contra hn
      have hh := hrec v (by omega)
      simp only [circularReversePath,ite_eq_left le_rfl,Nat.sub_self,hzero,sub_zero,
        ite_eq_right (show ¬k ≤ v from hn)] at hh
      have hh' := hpos (N+v-k) (by omega)
      omega
    refine ⟨hk1,hkv,?_⟩
    intro j hj
    simpa only [circularReversePath_prefix _ _ _ _ (hj.trans hkv),
      circularReversePath_prefix _ _ _ _ hkv] using hrec j hj
  · rintro ⟨hk1,hkv,hrec⟩
    refine ⟨hk1,hkv.trans hv.le,?_⟩
    intro j hj
    simpa only [circularReversePath_prefix _ _ _ _ (hj.trans hkv),
      circularReversePath_prefix _ _ _ _ hkv] using hrec j hj


lemma circular_record_height_of_good {S : ℕ → ℤ} {N v : ℕ} (hv : v<N)
    (hzero : S 0=0) (hpos : ∀ k, k<N → 0 ≤ S k) :
    (weakRecords (circularReversePath S N v) N).card=recordHeight S 0 v := by
  rw [circular_records_of_good hv hzero hpos,recordHeight_dual,Nat.sub_zero]


lemma circular_maximum_of_good {S : ℕ → ℤ} {N v : ℕ} (hv : v<N)
    (hzero : S 0=0) (hpos : ∀ k, k<N → 0 ≤ S k) :
    circularReversePath S N v v=S v ∧
      ∀ k, k ≤ N → circularReversePath S N v k ≤ S v := by
  constructor
  · simp [circularReversePath,hzero]
  · intro k hk
    by_cases hkv : k ≤ v
    · simp only [circularReversePath,ite_eq_left hkv]
      have := hpos (v-k) (by omega)
      omega
    · simp only [circularReversePath,ite_eq_right hkv]
      have := hpos (N+v-k) (by omega)
      omega


lemma height_eq_recordHeight {N : ℕ} (d : Fin N → Fin N) {j : ℕ} (hj : j ≤ N) :
    height d j=recordHeight (walk d) 0 j := by
  classical
  unfold height recordHeight
  apply Finset.card_bij (fun k _ => k.val)
  · intro k hk
    obtain ⟨_,hkj,hrec⟩ := Finset.mem_filter.mp hk
    apply (mem_reverseRecords ..).mpr
    refine ⟨Nat.zero_le _,hkj,?_⟩
    intro r hkr hrj
    exact hrec ⟨r,by omega⟩ hkr hrj
  · intro k _ l _ he
    exact Fin.ext he
  · intro k hk
    obtain ⟨_,hkj,hrec⟩ := (mem_reverseRecords ..).mp hk
    refine ⟨⟨k,by omega⟩,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkj,fun r hr hjr => hrec r.val hr hjr⟩


lemma walk_rotate_left {N : ℕ} [NeZero N] (m : Fin N) (d : Fin N → Fin N)
    {j : ℕ} (hj : j ≤ N-m.val) :
    walk (rotateDegrees m d) j=walk d (m.val+j)-walk d m.val := by
  rw [← degreeList_prefixSum,degreeList_rotate,
    prefixSum_rotate_left _ (by simp) (by simpa using hj),
    degreeList_prefixSum,degreeList_prefixSum]


lemma walk_rotate_right {N : ℕ} [NeZero N] (m : Fin N) (d : Fin N → Fin N)
    {j : ℕ} (hj : N-m.val ≤ j) (hjN : j ≤ N) :
    walk (rotateDegrees m d) j=walk d N-walk d m.val+walk d (j-(N-m.val)) := by
  rw [← degreeList_prefixSum,degreeList_rotate,
    prefixSum_rotate_right _ (by simp) (by simpa using hj) (by simpa using hjN),
    degreeList_sum,degreeList_prefixSum,degreeList_length,degreeList_prefixSum]


lemma circular_reverse_rotate {N : ℕ} [NeZero N] (d : Bridge N) (v : Fin N)
    {k : ℕ} (hk : k ≤ N) :
    reversedPath (walk (rotateBridge v d).val) N k=
      circularReversePath (walk d.val) N v.val k := by
  change walk (rotateDegrees v d.val) N-walk (rotateDegrees v d.val) (N-k)=_
  rw [walk_rotate_terminal]
  by_cases hkv : k ≤ v.val
  · rw [walk_rotate_right v d.val (by omega) (by omega)]
    have he : N-k-(N-v.val)=v.val-k := by omega
    simp only [circularReversePath,ite_eq_left hkv,he]
    omega
  · rw [walk_rotate_left v d.val (by omega)]
    have he : v.val+(N-k)=N+v.val-k := by omega
    simp only [circularReversePath,ite_eq_right hkv,he]
    rw [d.property]
    omega


lemma rotated_code_reverse_records {N : ℕ} [NeZero N] (d : Code N) (v : Fin N) :
    (weakRecords (reversedPath (walk (rotateDegrees v d.val)) N) N).card=height d.val v.val := by
  have he : ∀ k, k ≤ N → reversedPath (walk (rotateDegrees v d.val)) N k=
      circularReversePath (walk d.val) N v.val k :=
    fun k hk => circular_reverse_rotate (⟨d.val,d.property.1⟩ : Bridge N) v hk
  rw [weakRecords_congr_prefix he,
    circular_record_height_of_good v.isLt (walk_zero d.val) d.property.2,
    height_eq_recordHeight d.val v.isLt.le]


def prefixMaximum (S : ℕ → ℤ) (N : ℕ) : ℤ :=
  (Finset.range (N+1)).sup' Finset.nonempty_range_add_one S


lemma prefixMaximum_congr {S T : ℕ → ℤ} {N : ℕ} (h : ∀ k, k ≤ N → S k=T k) :
    prefixMaximum S N=prefixMaximum T N := by
  unfold prefixMaximum
  apply Finset.sup'_congr _ rfl
  intro k hk
  exact h k (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk)


lemma prefixMaximum_eq {S : ℕ → ℤ} {N v : ℕ} (hv : v ≤ N)
    (h : ∀ k, k ≤ N → S k ≤ S v) : prefixMaximum S N=S v := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun k hk => h k (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk))
  · exact Finset.le_sup' S (Finset.mem_range.mpr (by omega))


lemma rotated_code_reverse_maximum {N : ℕ} [NeZero N] (d : Code N) (v : Fin N) :
    prefixMaximum (reversedPath (walk (rotateDegrees v d.val)) N) N=walk d.val v.val := by
  have hp : ∀ k, k ≤ N → reversedPath (walk (rotateDegrees v d.val)) N k=
      circularReversePath (walk d.val) N v.val k :=
    fun k hk => circular_reverse_rotate (⟨d.val,d.property.1⟩ : Bridge N) v hk
  rw [prefixMaximum_congr hp]
  obtain ⟨he,hmax⟩ := circular_maximum_of_good v.isLt (walk_zero d.val) d.property.2
  rw [← he]
  exact prefixMaximum_eq v.isLt.le (by simpa only [he] using hmax)


lemma rotation_sum_invariant {N : ℕ} [NeZero N] (G : Bridge N → ℝ) (d : Bridge N) (m : Fin N) :
    (∑ v : Fin N,G (rotateBridge v (rotateBridge m d)))=
      ∑ v : Fin N,G (rotateBridge v d) := by
  simp_rw [rotateBridge_add]
  exact Equiv.sum_comp (Equiv.addRight m) (fun v => G (rotateBridge v d))


lemma canonical_rotation_sum {N : ℕ} [NeZero N] (G : Bridge N → ℝ) (d : Bridge N) :
    (∑ v : Fin N,G (rotateBridge v ⟨(canonicalCode d).val,(canonicalCode d).property.1⟩))=
      ∑ v : Fin N,G (rotateBridge v d) := by
  exact rotation_sum_invariant G d (goodRotation d)


theorem uniform_vertex_cyclic_identity (p : CriticalEvenOffspring) (n : ℕ)
    (G : Bridge (2*n+1) → ℝ) :
    (∑ d : Code (2*n+1), (codeWeight p d/codePartition p (2*n+1)) *
      ((∑ v : Fin (2*n+1),G (rotateBridge v ⟨d.val,d.property.1⟩))/(2*n+1)))=
    ∑ d : Bridge (2*n+1),(bridgeWeight p d/bridgePartition p (2*n+1))*G d := by
  let N := 2*n+1
  let : NeZero N := ⟨by dsimp [N]; omega⟩
  rw [← canonicalCode_expectation p n]
  simp_rw [canonical_rotation_sum,Finset.sum_div,Finset.mul_sum]
  rw [Finset.sum_comm]
  have hrow (v : Fin N) :
      (∑ d : Bridge N,(bridgeWeight p d/bridgePartition p N)*(G (rotateBridge v d)/(N:ℝ)))=
        (∑ d : Bridge N,(bridgeWeight p d/bridgePartition p N)*G d)/(N:ℝ) := by
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    congr 1
    calc
      _ = ∑ d : Bridge N,(bridgeWeight p (rotateBridge v d)/bridgePartition p N)*G (rotateBridge v d) := by
        simp only [bridgeWeight_rotate]
      _ = _ := Equiv.sum_comp (rotateBridge v) (fun d : Bridge N => (bridgeWeight p d/bridgePartition p N)*G d)
  have hNR : (2*(n:ℝ)+1)=(N:ℝ) := by dsimp [N]; push_cast; rfl
  rw [hNR]
  change (∑ v : Fin N, ∑ d : Bridge N,
    (bridgeWeight p d/bridgePartition p N)*(G (rotateBridge v d)/(N:ℝ)))=_
  simp_rw [hrow]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_div_cancel₀ _ (by dsimp [N]; positivity : (N:ℝ)≠0)


theorem uniform_vertex_height_error (p : CriticalEvenOffspring) (n : ℕ) (ν a : ℝ) :
    (∑ d : Code (2*n+1), (codeWeight p d/codePartition p (2*n+1)) *
      ((∑ v : Fin (2*n+1), if a < |(walk d.val v.val:ℝ)-ν*height d.val v.val| then (1:ℝ) else 0)/(2*n+1)))=
    ∑ d : Bridge (2*n+1),(bridgeWeight p d/bridgePartition p (2*n+1))*
      (if a < |(prefixMaximum (reversedPath (walk d.val) (2*n+1)) (2*n+1):ℝ)-
        ν*(weakRecords (reversedPath (walk d.val) (2*n+1)) (2*n+1)).card| then (1:ℝ) else 0) := by
  classical
  let G : Bridge (2*n+1) → ℝ := fun d =>
    if a < |(prefixMaximum (reversedPath (walk d.val) (2*n+1)) (2*n+1):ℝ)-
      ν*(weakRecords (reversedPath (walk d.val) (2*n+1)) (2*n+1)).card| then 1 else 0
  have he : ∀ d : Code (2*n+1), ∀ v : Fin (2*n+1),
      G (rotateBridge v ⟨d.val,d.property.1⟩)=
        if a < |(walk d.val v.val:ℝ)-ν*height d.val v.val| then 1 else 0 := by
    intro d v
    change (if a < |(prefixMaximum (reversedPath (walk (rotateDegrees v d.val)) (2*n+1)) (2*n+1):ℝ)-
      ν*(weakRecords (reversedPath (walk (rotateDegrees v d.val)) (2*n+1)) (2*n+1)).card| then 1 else 0)=_
    rw [rotated_code_reverse_records d v,rotated_code_reverse_maximum d v]
  simpa only [he] using uniform_vertex_cyclic_identity p n G


def CriticalEvenOffspring.bridgeFourier (p : CriticalEvenOffspring) (n : ℕ) (t : ℝ) : ℂ :=
  p.fourierCutoff n t * Complex.exp ((t / (p.sigma * Real.sqrt (n+1)) : ℝ) * Complex.I)


lemma integral_standard_gaussian_complex :
    (∫ t : ℝ, Complex.exp (-(t : ℂ)^2/2)) = (Real.sqrt (2 * Real.pi) : ℂ) := by
  have heq (t : ℝ) : Complex.exp (-(t : ℂ)^2/2) =
      (Real.exp (-(1/2 : ℝ)*t^2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simp_rw [heq]
  rw [integral_complex_ofReal, integral_gaussian]
  congr 2
  ring


lemma CriticalEvenOffspring.bridgeFourier_limit (p : CriticalEvenOffspring) :
    Tendsto (fun n : ℕ => ∫ t : ℝ, p.bridgeFourier n t) atTop
      (𝓝 (Real.sqrt (2 * Real.pi) : ℂ)) := by
  obtain ⟨c, hc, hg⟩ := p.charFun_global_gaussian
  have hden : Tendsto (fun n : ℕ => p.sigma * Real.sqrt (n+1)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)).const_mul_atTop
        p.sigma_pos
  have hp (t : ℝ) : Tendsto (fun n => p.bridgeFourier n t) atTop
      (𝓝 (Complex.exp (-(t : ℂ)^2/2))) := by
    have hr : Tendsto (fun n : ℕ => t / (p.sigma * Real.sqrt (n+1))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    have he := ((Complex.continuous_ofReal.tendsto 0).comp hr).mul_const Complex.I
    have hex := Complex.continuous_exp.tendsto 0 |>.comp (by simpa using he)
    simpa [bridgeFourier] using (p.cutoff_pointwise t).mul hex
  have hm (n : ℕ) : AEStronglyMeasurable (p.bridgeFourier n) volume := by
    exact ((p.cutoff_measurable n).mul (by fun_prop)).aestronglyMeasurable
  have hn (n : ℕ) : ∀ᵐ t ∂volume, ‖p.bridgeFourier n t‖ ≤ Real.exp (-c*t^2) := by
    apply ae_of_all
    intro t
    simpa only [bridgeFourier, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using
      p.cutoff_gaussian_bound hg n t
  have hi := tendsto_integral_of_dominated_convergence (μ := volume)
    (fun t : ℝ => Real.exp (-c*t^2)) hm (integrable_exp_neg_mul_sq hc) hn
      (ae_of_all _ hp)
  simpa only [integral_standard_gaussian_complex] using hi


lemma CriticalEvenOffspring.bridgeFourier_integral (p : CriticalEvenOffspring) (n : ℕ) :
    (∫ t : ℝ, p.bridgeFourier n t) =
      (p.sigma * Real.sqrt (n+1)) •
        ∫ t : ℝ in -(Real.pi/2)..Real.pi/2,
          Complex.exp ((t : ℂ) * Complex.I) *
            (charFun (p.law.toMeasure.map p.standardStep) (p.sigma * t))^(n+1) := by
  let A := (p.sigma * Real.pi / 2) * Real.sqrt (n+1)
  let scale := p.sigma * Real.sqrt (n+1)
  let f : ℝ → ℂ := fun t =>
    (charFun (p.law.toMeasure.map p.standardStep) (t / Real.sqrt (n+1)))^(n+1) *
      Complex.exp ((t / scale : ℝ) * Complex.I)
  have hsqrt : 0 < Real.sqrt (n+1 : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hscale : 0 < scale := mul_pos p.sigma_pos hsqrt
  have hA : 0 ≤ A := mul_nonneg
    (div_nonneg (mul_nonneg p.sigma_pos.le Real.pi_pos.le) (by norm_num)) hsqrt.le
  have heq : p.bridgeFourier n = (Icc (-A) A).indicator f := by
    ext t
    simp only [bridgeFourier, fourierCutoff, Set.indicator_apply, mem_Icc, ← abs_le]
    split_ifs <;> simp [f, scale]
  rw [heq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (neg_le_self hA)]
  have hlo : -(Real.pi/2) * scale = -A := by dsimp [scale, A]; ring
  have hhi : (Real.pi/2) * scale = A := by dsimp [scale, A]; ring
  have hsub := intervalIntegral.smul_integral_comp_mul_right
    (a := -(Real.pi/2)) (b := Real.pi/2) f scale
  rw [hlo, hhi] at hsub
  rw [← hsub]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [f]
  rw [mul_div_cancel_right₀ _ hscale.ne']
  have ht : t * scale / Real.sqrt (n+1) = p.sigma * t := by
    dsimp [scale]
    field_simp
  rw [ht, mul_comm]


lemma CriticalEvenOffspring.bridgeFourier_partition (p : CriticalEvenOffspring) (n : ℕ) :
    (∫ t : ℝ, p.bridgeFourier (2*n) t) =
      (p.sigma * Real.sqrt (2*n+1) * Real.pi * bridgePartition p (2*n+1) : ℝ) := by
  have hpar : Even (((2*n+1 : ℕ) : ℤ) + (-1)) := by
    refine ⟨n, ?_⟩
    push_cast
    ring
  have hi := spanTwo_inversion (p.iidLaw (2*n+1)) totalStep
    (totalStep_measurable _) (-1) (p.iid_totalStep_parity _ hpar)
  simp only [Int.cast_neg, Int.cast_one, neg_neg, one_mul, p.iid_charFun] at hi
  rw [p.bridgeFourier_integral, hi, ← p.bridgePartition_eq_iid]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  push_cast
  ring


lemma CriticalEvenOffspring.bridgePartition_limit (p : CriticalEvenOffspring) :
    Tendsto (fun n : ℕ => Real.sqrt (2*n+1) * bridgePartition p (2*n+1)) atTop
      (𝓝 (Real.sqrt (2*Real.pi) / (p.sigma * Real.pi))) := by
  have hsub : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (p.bridgeFourier_limit.comp hsub)
  change Tendsto (fun n : ℕ => (∫ t : ℝ, p.bridgeFourier (2*n) t).re)
    atTop (𝓝 (Real.sqrt (2*Real.pi))) at h
  simp only [p.bridgeFourier_partition, Complex.ofReal_re] at h
  have hdiv := h.div_const (p.sigma * Real.pi)
  convert hdiv using 1
  ext n
  have hs := p.sigma_pos.ne'
  have hpi := Real.pi_pos.ne'
  field_simp


theorem CriticalEvenOffspring.codePartition_asymptotic (p : CriticalEvenOffspring) :
    Tendsto (fun n : ℕ => (2*n+1 : ℝ) * Real.sqrt (2*n+1) *
      codePartition p (2*n+1)) atTop (𝓝 (2 / (p.sigma * Real.sqrt (2*Real.pi)))) := by
  have hc : Real.sqrt (2*Real.pi) / (p.sigma * Real.pi) =
      2 / (p.sigma * Real.sqrt (2*Real.pi)) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
    have hsp : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
    field_simp [p.sigma_pos.ne', Real.pi_pos.ne', hsp.ne']
    nlinarith
  rw [← hc]
  convert p.bridgePartition_limit using 1
  ext n
  rw [codePartition_cyclic p (by omega)]
  push_cast
  ring


def CriticalEvenOffspring.squareTail (p : CriticalEvenOffspring) (R : ℝ) : ℝ :=
  ∑' k : ℕ, if R < (k : ℝ) then (k : ℝ)^2 * p.mass k else 0


lemma CriticalEvenOffspring.squareTail_tendsto (p : CriticalEvenOffspring) :
    Tendsto p.squareTail atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence p.second
    (f := fun R : ℝ => fun k : ℕ => if R < (k : ℝ) then (k : ℝ)^2 * p.mass k else 0)
    (g := fun _ => (0 : ℝ)) (𝓕 := atTop) ?_ ?_
  · change Tendsto (fun R : ℝ => ∑' k : ℕ,
      if R < (k : ℝ) then (k : ℝ)^2 * p.mass k else 0) atTop (𝓝 0)
    simpa only [tsum_apply, tsum_zero] using h
  · intro k
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (k : ℝ)] with R hR
    simp [not_lt.mpr hR]
  · apply Eventually.of_forall
    intro R k
    split_ifs
    · rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (p.nonneg k))]
    · simp [mul_nonneg (sq_nonneg _) (p.nonneg k)]


lemma CriticalEvenOffspring.squareTail_bound (p : CriticalEvenOffspring)
    (R : ℝ) (hR : 0 ≤ R) :
    R^2 * p.law.toMeasure.real {k | R < (k : ℝ)} ≤ p.squareTail R := by
  rw [p.law_real_set, ← tsum_mul_left]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have hs : Summable (fun k : ℕ => if R < (k : ℝ) then p.mass k else 0) :=
    p.total.summable.of_nonneg_of_le
      (fun k => by split_ifs <;> simp [p.nonneg])
      (fun k => by split_ifs <;> simp [p.nonneg])
  have hs₂ : Summable (fun k : ℕ => if R < (k : ℝ) then (k : ℝ)^2 * p.mass k else 0) :=
    p.second.of_nonneg_of_le
      (fun k => by split_ifs <;> simp [mul_nonneg (sq_nonneg _) (p.nonneg k)])
      (fun k => by split_ifs <;> simp [mul_nonneg (sq_nonneg _) (p.nonneg k)])
  apply Summable.tsum_le_tsum _ (hs.mul_left _) hs₂
  intro k
  split_ifs with hk
  · exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ hR (Nat.cast_nonneg k)).mpr hk.le) (p.nonneg k)
  · simp


theorem CriticalEvenOffspring.sqrt_tail_small (p : CriticalEvenOffspring)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (n+1 : ℝ) *
      p.law.toMeasure.real {k | ε * Real.sqrt (n+1) < (k : ℝ)}) atTop (𝓝 0) := by
  have hR : Tendsto (fun n : ℕ => ε * Real.sqrt (n+1)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)).const_mul_atTop hε
  have hlim := (p.squareTail_tendsto.comp hR).div_const (ε^2)
  simp only [zero_div] at hlim
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hlim
  rw [le_div_iff₀ (sq_pos_of_pos hε)]
  have h := p.squareTail_bound (ε * Real.sqrt (n+1)) (by positivity)
  rw [mul_pow, Real.sq_sqrt (by positivity)] at h
  dsimp only [Function.comp_apply] at *
  nlinarith


noncomputable def codeEventMass (p : CriticalEvenOffspring) (N : ℕ)
    (E : (Fin N → Fin N) → Prop) : ℝ := by
  classical
  exact ∑ d : Code N, if E d.val then codeWeight p d else 0


noncomputable def bridgeEventMass (p : CriticalEvenOffspring) (N : ℕ)
    (E : (Fin N → Fin N) → Prop) : ℝ := by
  classical
  exact ∑ d : Bridge N, if E d.val then bridgeWeight p d else 0


theorem codeEventMass_cyclic (p : CriticalEvenOffspring) {N : ℕ} [NeZero N]
    (E : (Fin N → Fin N) → Prop)
    (hE : ∀ (m : Fin N) d, E (rotateDegrees m d) ↔ E d) :
    bridgeEventMass p N E = (N : ℝ) * codeEventMass p N E := by
  classical
  have h := weighted_unique_rotation (rotateBridge (N := N))
    (fun d => if E d.val then bridgeWeight p d else 0)
    (fun d => IsTreeCode d.val)
    (fun m d => by
      change (if E (rotateDegrees m d.val) then bridgeWeight p (rotateBridge m d) else 0) = _
      rw [hE, bridgeWeight_rotate])
    (fun d => d.unique_good_rotation)
  rw [Fintype.card_fin] at h
  change (∑ d : Bridge N, if E d.val then bridgeWeight p d else 0) = _
  rw [h]
  congr 1
  rw [← Finset.sum_filter]
  unfold codeEventMass
  rw [Finset.sum_subtype (p := fun d : Bridge N => IsTreeCode d.val) _ (by simp)]
  let e : Code N ≃ {d : Bridge N // IsTreeCode d.val} := {
    toFun := fun d => ⟨⟨d.val, d.property.1⟩, d.property⟩
    invFun := fun d => ⟨d.val.val, d.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact (Equiv.sum_comp e (fun d => if E d.val.val then bridgeWeight p d.val else 0)).symm


lemma CriticalEvenOffspring.bridgeEventMass_eq_iid (p : CriticalEvenOffspring)
    (N : ℕ) (E : (Fin N → ℕ) → Prop) :
    bridgeEventMass p N (fun d => E (fun i => (d i).val)) =
      (p.iidLaw N).real {d | totalStep d = -1 ∧ E d} := by
  classical
  let s : Bridge N → Set (Fin N → ℕ) := fun b =>
    if E (bridgeEmbedding N b) then {bridgeEmbedding N b} else ∅
  have hset : {d : Fin N → ℕ | totalStep d = -1 ∧ E d} = ⋃ b, s b := by
    ext d
    constructor
    · rintro ⟨h₁, h₂⟩
      have hr : d ∈ Set.range (bridgeEmbedding N) := by
        rw [← totalStep_bridge_range]
        exact h₁
      obtain ⟨b, rfl⟩ := hr
      exact mem_iUnion.mpr ⟨b, by simp [s, h₂]⟩
    · intro hd
      obtain ⟨b, hb⟩ := mem_iUnion.mp hd
      dsimp [s] at hb
      split_ifs at hb with hE
      · have heq : d = bridgeEmbedding N b := hb
        exact ⟨heq ▸ totalStep_bridge b, heq ▸ hE⟩
      · exact hb.elim
  have hd : Pairwise (fun b c => Disjoint (s b) (s c)) := by
    intro b c hbc
    dsimp [s]
    split_ifs
    · exact Set.disjoint_singleton.mpr ((bridgeEmbedding N).injective.ne hbc)
    all_goals simp
  have hm (b : Bridge N) : MeasurableSet (s b) := by dsimp [s]; split_ifs <;> measurability
  rw [hset, measureReal_iUnion_fintype hd hm]
  unfold bridgeEventMass
  apply Finset.sum_congr rfl
  intro b _
  change (if E (bridgeEmbedding N b) then bridgeWeight p b else 0) = _
  dsimp [s]
  split_ifs
  · exact (p.iid_bridge_singleton b).symm
  · simp


def codeEventProbability (p : CriticalEvenOffspring) (N : ℕ)
    (E : (Fin N → Fin N) → Prop) : ℝ :=
  codeEventMass p N E / codePartition p N


lemma codeEventProbability_eq_bridge (p : CriticalEvenOffspring) {N : ℕ} (hN : 0 < N)
    (E : (Fin N → Fin N) → Prop)
    (hE : letI : NeZero N := ⟨hN.ne'⟩
      ∀ (m : Fin N) d, E (rotateDegrees m d) ↔ E d) :
    codeEventProbability p N E = bridgeEventMass p N E / bridgePartition p N := by
  let : NeZero N := ⟨hN.ne'⟩
  rw [codeEventMass_cyclic p E hE, codePartition_cyclic p hN, mul_div_mul_left]
  · rfl
  · exact_mod_cast hN.ne'


lemma maxDegree_rotation {N : ℕ} [NeZero N] (R : ℝ) (m : Fin N)
    (d : Fin N → Fin N) :
    (∃ i, R < ((rotateDegrees m d i).val : ℝ)) ↔ ∃ i, R < ((d i).val : ℝ) := by
  change (∃ i, R < ((d (i+m)).val : ℝ)) ↔ _
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i+m, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i-m, by simpa using hi⟩


lemma code_max_probability_eq_iid (p : CriticalEvenOffspring) {N : ℕ} (hN : 0 < N)
    (R : ℝ) :
    codeEventProbability p N (fun d => ∃ i, R < ((d i).val : ℝ)) =
      (p.iidLaw N).real {d | (∃ i, R < (d i : ℝ)) ∧ totalStep d = -1} /
        (p.iidLaw N).real {d | totalStep d = -1} := by
  let : NeZero N := ⟨hN.ne'⟩
  rw [codeEventProbability_eq_bridge p hN _ (by
    intro m d
    exact maxDegree_rotation R m d), p.bridgePartition_eq_iid,
    p.bridgeEventMass_eq_iid N (fun d => ∃ i, R < (d i : ℝ))]
  congr 2
  ext d
  exact and_comm


theorem CriticalEvenOffspring.conditioned_max_degree (p : CriticalEvenOffspring)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => codeEventProbability p (2*n+1)
      (fun d => ∃ i, ε * Real.sqrt (2*n+1) < ((d i).val : ℝ))) atTop (𝓝 0) := by
  obtain ⟨C, hCpos, hC⟩ := p.iid_site_uniform_bound
  have hsub : Tendsto (fun n : ℕ => 2*n+2) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have htail := (p.sqrt_tail_small ε hε).comp hsub
  have hnum : Tendsto (fun n : ℕ => Real.sqrt (2*n+3) *
      (p.iidLaw (2*n+3)).real
        {d | (∃ i, ε * Real.sqrt (2*n+3) < (d i : ℝ)) ∧ totalStep d = -1})
      atTop (𝓝 0) := by
    have hupper := htail.const_mul (2*C)
    simp only [mul_zero] at hupper
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      add_assoc, show (2:ℝ)+1=3 by norm_num] at hupper
    apply squeeze_zero (fun n => by positivity) (fun n => ?_) hupper
    have hb := p.iid_max_tail_bound hC (2*n+1) (ε * Real.sqrt (2*n+3)) (-1)
    have hs : Real.sqrt (2*n+3) ≤ 2 * Real.sqrt (2*n+2) := by
      have h₁ := Real.sq_sqrt (show 0 ≤ (2*n+3 : ℝ) by positivity)
      have h₂ := Real.sq_sqrt (show 0 ≤ (2*n+2 : ℝ) by positivity)
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      nlinarith [Real.sqrt_nonneg (2*n+3), Real.sqrt_nonneg (2*n+2)]
    have hh := mul_le_mul_of_nonneg_right hs
      (show 0 ≤ (p.iidLaw (2*n+3)).real
        {d | (∃ i, ε * Real.sqrt (2*n+3) < (d i : ℝ)) ∧ totalStep d = -1} from
          measureReal_nonneg)
    norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_assoc] at hb
    nlinarith
  have hden := p.bridgePartition_limit.comp (tendsto_add_atTop_nat 1)
  have hden' : Tendsto (fun n : ℕ => Real.sqrt (2*n+3) *
      (p.iidLaw (2*n+3)).real {d | totalStep d = -1}) atTop
      (𝓝 (Real.sqrt (2*Real.pi) / (p.sigma * Real.pi))) := by
    convert hden using 1
    ext n
    dsimp only [Function.comp_apply]
    rw [p.bridgePartition_eq_iid]
    congr 2; push_cast; ring
  have hB : Real.sqrt (2*Real.pi) / (p.sigma * Real.pi) ≠ 0 := by
    exact ne_of_gt (div_pos (Real.sqrt_pos.mpr (by positivity))
      (mul_pos p.sigma_pos Real.pi_pos))
  have hratio := hnum.div hden' hB
  simp only [zero_div] at hratio
  apply (tendsto_add_atTop_iff_nat 1).mp
  convert hratio using 1
  ext n
  dsimp only [Pi.div_apply]
  rw [code_max_probability_eq_iid p (by omega), mul_div_mul_left]
  · congr 2; push_cast; ring_nf; rfl
  · exact (Real.sqrt_pos.mpr (by positivity)).ne'


lemma CriticalEvenOffspring.iid_fixed_site_limit (p : CriticalEvenOffspring)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (j : ℤ)
    (hpar : ∀ n, Even (((m n+1:ℕ):ℤ)+j)) :
    Tendsto (fun n : ℕ => Real.sqrt (m n+1) *
      (p.iidLaw (m n+1)).real {d | totalStep d = j}) atTop
      (𝓝 (Real.sqrt (2*Real.pi)/(p.sigma*Real.pi))) := by
  obtain ⟨E, _, hE, hbound⟩ := p.uniform_local_limit
  have herr : Tendsto (fun n : ℕ =>
      |Real.sqrt (m n+1) * (p.iidLaw (m n+1)).real {d | totalStep d = j} -
        (Real.sqrt (2*Real.pi)/(p.sigma*Real.pi)) *
        Real.exp (-((j:ℝ)/(p.sigma*Real.sqrt (m n+1)))^2/2)|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) (fun n => hbound (m n) j (hpar n)) (hE.comp hm)
  have hden : Tendsto (fun n : ℕ => p.sigma * Real.sqrt (m n+1)) atTop atTop :=
    ((Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)).comp hm).const_mul_atTop
      p.sigma_pos
  have hz : Tendsto (fun n : ℕ => (j:ℝ)/(p.sigma*Real.sqrt (m n+1))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hg := (Real.continuous_exp.continuousAt.tendsto.comp
    ((hz.pow 2).neg.div_const 2)).const_mul
    (Real.sqrt (2*Real.pi)/(p.sigma*Real.pi))
  simp only [zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero,
    mul_one] at hg
  have hd : Tendsto (fun n : ℕ =>
      Real.sqrt (m n+1) * (p.iidLaw (m n+1)).real {d | totalStep d = j} -
        (Real.sqrt (2*Real.pi)/(p.sigma*Real.pi)) *
        Real.exp (-((j:ℝ)/(p.sigma*Real.sqrt (m n+1)))^2/2)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using herr)
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using hd.add hg


lemma sqrt_affine_ratio_limit (a b : ℝ) (hb : 0 < b) :
    Tendsto (fun n : ℕ => Real.sqrt (2*n+a) / Real.sqrt (2*n+b)) atTop (𝓝 1) := by
  have hden : Tendsto (fun n : ℕ => (2*n+b : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop b
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ)<2))
  have hz : Tendsto (fun n : ℕ => (a-b)/(2*n+b)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hh := ((tendsto_const_nhds (x := (1:ℝ))).add hz).sqrt
  have heq (n : ℕ) : (1:ℝ)+(a-b)/(2*n+b) = (2*n+a)/(2*n+b) := by
    have hb' : 2*(n:ℝ)+b ≠ 0 := ne_of_gt (by positivity)
    field_simp [hb']
    ring
  simp only [heq, add_zero, Real.sqrt_one] at hh
  have hsq (n : ℕ) : Real.sqrt ((2*n+a)/(2*n+b)) =
      Real.sqrt (2*n+a) / Real.sqrt (2*n+b) :=
    Real.sqrt_div' _ (by positivity)
  simpa only [hsq] using hh


lemma CriticalEvenOffspring.bridge_coordinate_limit (p : CriticalEvenOffspring) (k : ℕ) :
    Tendsto (fun n : ℕ =>
      (p.iidLaw (2*n+3)).real {d | d 0 = k ∧ totalStep d = -1} /
        (p.iidLaw (2*n+3)).real {d | totalStep d = -1}) atTop (𝓝 (p.mass k)) := by
  by_cases hk : Even k
  · have hd := p.iid_fixed_site_limit (fun n => 2*n+2)
      (tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id) (-1) (by
        intro n
        refine ⟨n+1, ?_⟩
        push_cast
        ring)
    have hn := p.iid_fixed_site_limit (fun n => 2*n+1)
      (tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id) (-(k:ℤ)) (by
        intro n
        have hk' : Even (k:ℤ) := by exact_mod_cast hk
        obtain ⟨r, hr⟩ := hk'
        refine ⟨(n:ℤ)+1-r, ?_⟩
        push_cast
        rw [hr]
        ring)
    have hc : Real.sqrt (2*Real.pi)/(p.sigma*Real.pi) ≠ 0 := by
      exact (div_pos (Real.sqrt_pos.mpr (by positivity))
        (mul_pos p.sigma_pos Real.pi_pos)).ne'
    have hr := (hn.div hd hc).mul (sqrt_affine_ratio_limit 3 2 (by norm_num))
    have hr' := hr.const_mul (p.mass k)
    simp only [div_self hc, mul_one] at hr'
    convert hr' using 1
    ext n
    rw [p.iid_coordinate_site (2*n+2)]
    have hs : -1 - ((k:ℤ)-1) = -(k:ℤ) := by omega
    rw [hs]
    dsimp only [Pi.div_apply]
    norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_assoc]
    have hs₂ : Real.sqrt (2*n+2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have hs₃ : Real.sqrt (2*n+3) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp [hs₂, hs₃]
  · have hk0 := p.even_support k (Nat.not_even_iff_odd.mp hk)
    rw [hk0]
    convert tendsto_const_nhds (x := (0:ℝ)) using 1
    ext n
    rw [p.iid_coordinate_site (2*n+2), hk0]
    simp


lemma CriticalEvenOffspring.iid_pair_site (p : CriticalEvenOffspring)
    (N : ℕ) (i : Fin (N+2)) (i' : Fin (N+1)) (k l : ℕ) (j : ℤ) :
    (p.iidLaw (N+2)).real
      {d | d i = k ∧ d (i.succAbove i') = l ∧ totalStep d = j} =
      p.mass k * p.mass l *
        (p.iidLaw N).real {d | totalStep d = j - ((k : ℤ)-1) - ((l : ℤ)-1)} := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+2) => ℕ) i
  have hp : MeasurePreserving e (p.iidLaw (N+2))
      (p.law.toMeasure.prod (p.iidLaw (N+1))) :=
    measurePreserving_piFinSuccAbove (fun _ => p.law.toMeasure) i
  have hset : {d : Fin (N+2) → ℕ | d i = k ∧ d (i.succAbove i') = l ∧ totalStep d = j} =
      e ⁻¹' (({k} : Set ℕ) ×ˢ
        {d : Fin (N+1) → ℕ | d i' = l ∧ totalStep d = j - ((k : ℤ) - 1)}) := by
    ext d
    change (d i = k ∧ d (i.succAbove i') = l ∧ totalStep d = j) ↔
      (d i = k ∧ d (i.succAbove i') = l ∧
        totalStep (fun a => d (i.succAbove a)) = j - ((k : ℤ) - 1))
    rw [totalStep_succAbove d i]
    constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;> refine ⟨h₁, h₂, ?_⟩ <;>
      rw [h₁] at * <;> omega
  rw [measureReal_def, hset, hp.measure_preimage (by measurability),
    Measure.prod_prod, ENNReal.toReal_mul, p.law_singleton,
    ENNReal.toReal_ofReal (p.nonneg _)]
  change p.mass k * (p.iidLaw (N+1)).real _ = _
  rw [p.iid_coordinate_site]
  ring


lemma CriticalEvenOffspring.bridge_coordinate_limit_any (p : CriticalEvenOffspring)
    (k : ℕ) (i : ∀ n, Fin (2*n+3)) :
    Tendsto (fun n : ℕ =>
      (p.iidLaw (2*n+3)).real {d | d (i n) = k ∧ totalStep d = -1} /
        (p.iidLaw (2*n+3)).real {d | totalStep d = -1}) atTop (𝓝 (p.mass k)) := by
  convert p.bridge_coordinate_limit k using 1
  ext n
  rw [p.iid_coordinate_site (2*n+2), p.iid_coordinate_site (2*n+2)]


lemma CriticalEvenOffspring.bridge_pair_limit (p : CriticalEvenOffspring)
    (k l : ℕ) (i : ∀ n, Fin (2*n+5)) (i' : ∀ n, Fin (2*n+4)) :
    Tendsto (fun n : ℕ =>
      (p.iidLaw (2*n+5)).real
        {d | d (i n) = k ∧ d ((i n).succAbove (i' n)) = l ∧ totalStep d = -1} /
        (p.iidLaw (2*n+5)).real {d | totalStep d = -1}) atTop (𝓝 (p.mass k * p.mass l)) := by
  by_cases hk : Even k
  · by_cases hl : Even l
    · have hd := p.iid_fixed_site_limit (fun n => 2*n+4)
        (tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id) (-1) (by
          intro n
          refine ⟨(n:ℤ)+2, ?_⟩
          push_cast
          ring)
      have hn := p.iid_fixed_site_limit (fun n => 2*n+2)
        (tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id)
        (1-(k:ℤ)-(l:ℤ)) (by
          intro n
          have hk' : Even (k:ℤ) := by exact_mod_cast hk
          have hl' : Even (l:ℤ) := by exact_mod_cast hl
          obtain ⟨r, hr⟩ := hk'
          obtain ⟨s, hs⟩ := hl'
          refine ⟨(n:ℤ)+2-r-s, ?_⟩
          push_cast
          rw [hr, hs]
          ring)
      have hc : Real.sqrt (2*Real.pi)/(p.sigma*Real.pi) ≠ 0 := by
        exact (div_pos (Real.sqrt_pos.mpr (by positivity))
          (mul_pos p.sigma_pos Real.pi_pos)).ne'
      have hr := (hn.div hd hc).mul (sqrt_affine_ratio_limit 5 3 (by norm_num))
      have hr' := hr.const_mul (p.mass k * p.mass l)
      simp only [div_self hc, mul_one] at hr'
      convert hr' using 1
      ext n
      rw [p.iid_pair_site (2*n+3)]
      have hs : -1 - ((k:ℤ)-1) - ((l:ℤ)-1) = 1-(k:ℤ)-(l:ℤ) := by omega
      rw [hs]
      dsimp only [Pi.div_apply]
      norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_assoc]
      have hs₃ : Real.sqrt (2*n+3) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
      have hs₅ : Real.sqrt (2*n+5) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
      field_simp [hs₃, hs₅]
    · have hl0 := p.even_support l (Nat.not_even_iff_odd.mp hl)
      rw [hl0, mul_zero]
      convert tendsto_const_nhds (x := (0:ℝ)) using 1
      ext n
      rw [p.iid_pair_site (2*n+3), hl0]
      simp
  · have hk0 := p.even_support k (Nat.not_even_iff_odd.mp hk)
    rw [hk0, zero_mul]
    convert tendsto_const_nhds (x := (0:ℝ)) using 1
    ext n
    rw [p.iid_pair_site (2*n+3), hk0]
    simp

end FKCRT.TreeCoding
end

end OAI
