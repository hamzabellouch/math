import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.TestPointMoments

namespace OAI

section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Finset
open scoped Classical
namespace SharpLogRamsey.PoissonSchedules
variable {ι : Type*} [Fintype ι]

noncomputable def scheduleLaw (r : ι → ℝ≥0) : Measure (ι → ℕ) :=
  Measure.pi fun i => poissonMeasure (r i)

instance schedule_probability (r : ι → ℝ≥0) : IsProbabilityMeasure (scheduleLaw r) := by
  unfold scheduleLaw
  infer_instance

theorem coordinate_independence (r : ι → ℝ≥0) :
    iIndepFun (fun i (x : ι → ℕ) => x i) (scheduleLaw r) := by
  exact iIndepFun_pi (X:=fun _ => id) (fun _ => aemeasurable_id)

def hitLedger (A : Finset ι) : Set (ι → ℕ) := {x | ∀ i ∈ A, x i ≠ 0}

def emptyLedger (A : Finset ι) : Set (ι → ℕ) := {x | ∀ i ∈ A, x i = 0}

theorem measurable_hitLedger (A : Finset ι) : MeasurableSet (hitLedger A) := by
  exact (Set.to_countable (hitLedger A)).measurableSet

theorem measurable_emptyLedger (A : Finset ι) : MeasurableSet (emptyLedger A) := by
  exact (Set.to_countable (emptyLedger A)).measurableSet

theorem poisson_zero_real (r : ℝ≥0) : (poissonMeasure r).real {0} = Real.exp (-r) := by
  simpa using poissonMeasure_real_singleton r 0

theorem poisson_nonzero_real (r : ℝ≥0) :
    (poissonMeasure r).real ({0}ᶜ) = 1-Real.exp (-r) := by
  rw [measureReal_compl (measurableSet_singleton 0),poisson_zero_real]
  simp

theorem hitLedger_probability (r : ι → ℝ≥0) (A : Finset ι) :
    (scheduleLaw r).real (hitLedger A) = ∏ i ∈ A, (1-Real.exp (-(r i : ℝ))) := by
  have he : hitLedger A = (A : Set ι).pi (fun _ => ({0}ᶜ : Set ℕ)) := by
    ext x; simp [hitLedger,Set.mem_pi]
  rw [he,measureReal_def,scheduleLaw,Measure.pi_pi_finset,ENNReal.toReal_prod]
  apply prod_congr rfl
  intro i hi
  exact poisson_nonzero_real (r i)

theorem emptyLedger_probability (r : ι → ℝ≥0) (A : Finset ι) :
    (scheduleLaw r).real (emptyLedger A) = Real.exp (-(∑ i ∈ A, (r i : ℝ))) := by
  have he : emptyLedger A = (A : Set ι).pi (fun _ => ({0} : Set ℕ)) := by
    ext x; simp [emptyLedger,Set.mem_pi]
  rw [he,measureReal_def,scheduleLaw,Measure.pi_pi_finset,ENNReal.toReal_prod]
  calc
    _ = ∏ i ∈ A, Real.exp (-(r i : ℝ)) := prod_congr rfl (fun i hi => poisson_zero_real (r i))
    _ = _ := by rw [← Real.exp_sum,sum_neg_distrib]

theorem hitLedger_le_mean_product (r : ι → ℝ≥0) (A : Finset ι) :
    (scheduleLaw r).real (hitLedger A) ≤ ∏ i ∈ A, (r i : ℝ) := by
  rw [hitLedger_probability]
  apply prod_le_prod₀
  · intro i hi
    have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (r i).coe_nonneg)
    linarith
  · intro i hi
    have h := Real.add_one_le_exp (-(r i : ℝ))
    linarith

theorem static_certificate_bound {κ : Type*} [Fintype κ]
    (r : ι → ℝ≥0) (ledger : κ → Finset ι)
    (E : Set (ι → ℕ)) (hcert : ∀ x ∈ E, ∃ c, x ∈ hitLedger (ledger c)) :
    (scheduleLaw r).real E ≤ ∑ c, ∏ i ∈ ledger c, (r i : ℝ) := by
  calc
    _ ≤ (scheduleLaw r).real (⋃ c, hitLedger (ledger c)) := by
      apply measureReal_mono (h₂:=measure_ne_top _ _)
      intro x hx
      obtain ⟨c,hc⟩ := hcert x hx
      exact Set.mem_iUnion.mpr ⟨c,hc⟩
    _ ≤ ∑ c, (scheduleLaw r).real (hitLedger (ledger c)) := measureReal_iUnion_fintype_le _
    _ ≤ _ := sum_le_sum fun c hc => hitLedger_le_mean_product r (ledger c)

end SharpLogRamsey.PoissonSchedules
namespace SharpLogRamsey.EmptyExceptional
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical NNReal
open SharpLogRamsey.PoissonSchedules SharpLogRamsey.BoundedProbability
noncomputable section
variable {ι H : Type*}

def emptySum (E : Finset H) (D : H → Finset ι) (w : H → ℝ) (ω : ι → ℕ) : ℝ :=
  ∑ h∈E,if ω∈emptyLedger (D h) then w h else 0

def emptySet (E : Finset H) (D : H → Finset ι) (ω : ι → ℕ) : Finset H :=
  E.filter (fun h =>  ω∈emptyLedger (D h))

lemma emptySum_eq (E : Finset H) (D : H → Finset ι) (w : H → ℝ) (ω : ι → ℕ) :
    emptySum E D w ω = ∑ h∈emptySet E D ω,w h := by
  rw [emptySum,emptySet,sum_filter]

lemma emptySum_one (E : Finset H) (D : H → Finset ι) (ω : ι → ℕ) :
    emptySum E D (fun _ =>  1) ω = ((emptySet E D ω).card:ℝ) := by
  rw [emptySum_eq]; simp

lemma emptySum_nonneg (E : Finset H) (D : H → Finset ι) (w : H → ℝ)
    (hw : ∀ h∈E,0 ≤ w h) (ω : ι → ℕ) : 0 ≤ emptySum E D w ω := by
  apply sum_nonneg
  intro h hh
  split_ifs
  · exact hw h hh
  · rfl

lemma emptySum_le_sum (E : Finset H) (D : H → Finset ι) (w : H → ℝ)
    (hw : ∀ h∈E,0 ≤ w h) (ω : ι → ℕ) : emptySum E D w ω  ≤  ∑ h∈E,w h := by
  apply sum_le_sum
  intro h hh
  split_ifs
  · rfl
  · exact hw h hh

variable [Fintype ι]

lemma integrable_emptySum (r : ι → ℝ≥0) (E : Finset H) (D : H → Finset ι) (w : H → ℝ) :
    Integrable (emptySum E D w) (scheduleLaw r) := by
  apply integrable_finsetSum
  intro h _
  exact (integrable_const (w h)).indicator (measurable_emptyLedger (D h))

lemma integral_emptySum (r : ι → ℝ≥0) (E : Finset H) (D : H → Finset ι) (w : H → ℝ) :
    (∫ ω,emptySum E D w ω ∂scheduleLaw r) =
      ∑ h∈E,w h*Real.exp (-(∑ i∈D h,(r i:ℝ))) := by
  simp only [emptySum]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro h _
    change (∫ ω,(emptyLedger (D h)).indicator (fun _ =>  w h) ω ∂scheduleLaw r) = _
    rw [integral_indicator_const _ (measurable_emptyLedger _),smul_eq_mul,emptyLedger_probability]
    ring
  · intro h _
    exact (integrable_const (w h)).indicator (measurable_emptyLedger (D h))

theorem many_empty (r : ι → ℝ≥0) (E : Finset H) (hE : E.Nonempty)
    (D : H → Finset ι) (b : ℝ) (hb : ∀ h∈E,∑ i∈D h,(r i:ℝ) ≤ b) :
    Real.exp (-b)/2  ≤  (scheduleLaw r).real {ω |
      (E.card:ℝ)*Real.exp (-b)/2 ≤ emptySum E D (fun _ =>  1) ω} := by
  apply mass_above_half _ _ (integrable_emptySum r E D _) _ _
  · exact_mod_cast card_pos.mpr hE
  · exact (Real.exp_pos _).le
  · intro ω
    simpa using emptySum_le_sum E D (fun _ =>  1) (by intros; norm_num) ω
  · rw [integral_emptySum]
    calc
      _ = ∑ _h∈E,Real.exp (-b) := by simp
      _  ≤  _ := sum_le_sum (fun h hh =>  by simp only [one_mul]; exact Real.exp_le_exp.mpr (neg_le_neg (hb h hh)))
  · exact (Set.to_countable _).measurableSet

theorem heavy_empty_expectation (r : ι → ℝ≥0) (E : Finset H)
    (D : H → Finset ι) (l : H → ℝ) (P δ W : ℝ) (hP : 0 ≤ P)
    (hl : ∀ h∈E,0 ≤ l h) (hmass : ∀ h∈E,∑ i∈D h,(r i:ℝ)=P*l h)
    (hW : ∑ h∈E,l h ≤ W) :
    (∫ ω,emptySum (E.filter (fun h =>  δ ≤ l h)) D l ω ∂scheduleLaw r)  ≤
      W*Real.exp (-P*δ) := by
  rw [integral_emptySum]
  calc
    _  ≤  ∑ h∈E.filter (fun h =>  δ ≤ l h),l h*Real.exp (-P*δ) := by
      apply sum_le_sum
      intro h hh
      have hh' := mem_filter.mp hh
      apply mul_le_mul_of_nonneg_left _ (hl h hh'.1)
      apply Real.exp_le_exp.mpr
      rw [hmass h hh'.1]
      nlinarith [mul_le_mul_of_nonneg_left hh'.2 hP]
    _  ≤  ∑ h∈E,l h*Real.exp (-P*δ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun h hh _ =>
        mul_nonneg (hl h hh) (Real.exp_pos _).le)
    _  ≤  _ := by rw [←sum_mul]; exact mul_le_mul_of_nonneg_right hW (Real.exp_pos _).le

omit [Fintype ι] in

lemma empty_weight_split (E : Finset H) (D : H → Finset ι) (l : H → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) (ω : ι → ℕ) :
    emptySum E D l ω  ≤  δ*emptySum E D (fun _ =>  1) ω+
      emptySum (E.filter (fun h =>  δ ≤ l h)) D l ω := by
  simp only [emptySum,sum_filter]
  rw [mul_sum,←sum_add_distrib]
  apply sum_le_sum
  intro h _
  by_cases he : ω∈emptyLedger (D h)  <;>  by_cases hh : δ ≤ l h  <;>  simp [he,hh]
  · exact hδ
  · exact (lt_of_not_ge hh).le

end
end SharpLogRamsey.EmptyExceptional
namespace SharpLogRamsey.EmptyExceptional
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical NNReal
open SharpLogRamsey.PoissonSchedules SharpLogRamsey.BoundedProbability
noncomputable section
variable {ι H : Type*} [Fintype ι]

omit [Fintype ι] in
lemma emptySum_mono (D : H → Finset ι) (w : H → ℝ) {E F : Finset H}
    (hEF : E⊆F) (hw : ∀ h∈F,0 ≤ w h) (ω : ι → ℕ) :
    emptySum E D w ω ≤ emptySum F D w ω := by
  apply sum_le_sum_of_subset_of_nonneg hEF
  intro h hh _
  split_ifs
  · exact hw h hh
  · rfl

theorem empty_good_event (r : ι → ℝ≥0) (E E₀ : Finset H) (hE₀ : E₀.Nonempty)
    (hsub : E₀⊆E) (D : H → Finset ι) (l : H → ℝ) (P b δ u zmin W : ℝ)
    (hP : 0 ≤ P) (hδ : 0 ≤ δ) (hu : 0 < u) (hz : 0 < zmin)
    (hl : ∀ h∈E,0 ≤ l h) (hmass : ∀ h∈E,∑ i∈D h,(r i:ℝ)=P*l h)
    (hb : ∀ h∈E₀,∑ i∈D h,(r i:ℝ) ≤ b)
    (hW : ∑ h∈E,l h ≤ W) (hzmin : zmin ≤ (E₀.card:ℝ)*Real.exp (-b)/2) :
    Real.exp (-b)/2 - W*Real.exp (-P*δ)/(u*zmin) ≤
      (scheduleLaw r).real {ω | zmin ≤ emptySum E D (fun _ => 1) ω ∧
        emptySum E D l ω ≤ (δ+u)*emptySum E D (fun _ => 1) ω} := by
  let Y := emptySum (E.filter (fun h => δ ≤ l h)) D l
  let G := {ω | (E₀.card:ℝ)*Real.exp (-b)/2 ≤ emptySum E₀ D (fun _ => 1) ω}
  let B := {ω | u*zmin ≤ Y ω}
  have hmany : Real.exp (-b)/2 ≤ (scheduleLaw r).real G := many_empty r E₀ hE₀ D b hb
  have hev := heavy_empty_expectation r E D l P δ W hP hl hmass hW
  have hmark := real_markov (scheduleLaw r) Y (integrable_emptySum r _ D l)
    (emptySum_nonneg _ D l (fun h hh => hl h (mem_filter.mp hh).1))
    (u*zmin) (mul_pos hu hz).le (Set.to_countable _).measurableSet
  have hbad : (scheduleLaw r).real B ≤ W*Real.exp (-P*δ)/(u*zmin) := by
    apply (le_div_iff₀ (mul_pos hu hz)).mpr
    simpa only [mul_comm] using hmark.trans hev
  have hcover : G\B ⊆ {ω | zmin ≤ emptySum E D (fun _ => 1) ω ∧
        emptySum E D l ω ≤ (δ+u)*emptySum E D (fun _ => 1) ω} := by
    intro ω hh
    have hn : Y ω < u*zmin := lt_of_not_ge hh.2
    have hc := emptySum_mono D (fun _ => (1:ℝ)) hsub (fun _ _ => by norm_num) ω
    have hsmall : zmin ≤ emptySum E D (fun _ => 1) ω := hzmin.trans (hh.1.trans hc)
    refine ⟨hsmall,?_⟩
    have hs := empty_weight_split E D l δ hδ ω
    have hh' := mul_le_mul_of_nonneg_left hsmall hu.le
    change emptySum E D l ω ≤ δ*emptySum E D (fun _ => 1) ω+Y ω at hs
    nlinarith
  have hdiff := good_minus_bad (scheduleLaw r) G B
  have hmono := measureReal_mono (h₂:=measure_ne_top (scheduleLaw r) _) hcover
  linarith

end
end SharpLogRamsey.EmptyExceptional
namespace SharpLogRamsey.LearningRow
open Finset
open scoped Classical BigOperators
noncomputable section
variable {A : Type*} [Fintype A]

def test (sample : Finset A) (score : A → ℝ) (z q : ℝ) : Finset A :=
  univ.filter (fun x => x∈sample ∨ score x<z/(2*q))

lemma capture_score (A T Z α z q : ℝ) (hq : 0<q) (hz : 0<z)
    (hZ : 0≤Z) (hZ1 : Z≤z/(10*q)) (_ha : 0≤α) (ha1 : α≤1)
    (he : |(A-T)-α*Z| ≤ z/(100*q)) (ht : |T|≤z/(10*q)) :
    A<z/(2*q) := by
  obtain ⟨_,he⟩ := abs_le.mp he
  obtain ⟨_,ht⟩ := abs_le.mp ht
  have ham : α*Z≤Z := by nlinarith
  have hh : 0<z/q := div_pos hz hq
  have hi : z/(100*q)= (z/q)/100 := by ring
  have hi1 : z/(10*q)= (z/q)/10 := by ring
  have hi2 : z/(2*q)= (z/q)/2 := by ring
  rw [hi] at he
  rw [hi1] at hZ1 ht
  rw [hi2]
  linarith

lemma exclude_score (A T Z α z q : ℝ) (hq : 0<q) (hz : 0<z)
    (hZ : (4/5)*z/q≤Z) (ha : 9/10≤α)
    (he : |(A-T)-α*Z| ≤ z/(100*q)) (ht : |T|≤z/(10*q)) :
    z/(2*q)<A := by
  obtain ⟨he,_⟩ := abs_le.mp he
  obtain ⟨ht,_⟩ := abs_le.mp ht
  have hh : 0<z/q := div_pos hz hq
  rw [mul_div_assoc] at hZ
  have hZ0 : 0≤Z := by nlinarith
  have ham : (9/10)*Z≤α*Z := mul_le_mul_of_nonneg_right ha hZ0
  have hi : z/(100*q)= (z/q)/100 := by ring
  have hi1 : z/(10*q)= (z/q)/10 := by ring
  have hi2 : z/(2*q)= (z/q)/2 := by ring
  rw [hi] at he
  rw [hi1] at ht
  rw [hi2]
  nlinarith

theorem capture_count (S sample D F E : Finset A) (score : A → ℝ) (z q : ℝ)
    (h : ∀ x∈S,x∉D → x∉F → x∉E → x∉sample → score x<z/(2*q)) :
    S.card ≤ (S∩test sample score z q).card+D.card+F.card+E.card := by
  have hs : S ⊆ ((S∩test sample score z q)∪D)∪F∪E := by
    intro x hx
    by_cases hd : x∈D
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ hd))
    by_cases hf : x∈F
    · exact mem_union_left _ (mem_union_right _ hf)
    by_cases he : x∈E
    · exact mem_union_right _ he
    apply mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨hx,?_⟩)))
    simp only [test,mem_filter,mem_univ,true_and]
    by_cases hp : x∈sample
    · exact Or.inl hp
    · exact Or.inr (h x hx hd hf he hp)
  calc
    _ ≤ (((S∩test sample score z q)∪D)∪F∪E).card := card_le_card hs
    _ ≤ _ := by
      have h1 := card_union_le (S∩test sample score z q) D
      have h2 := card_union_le ((S∩test sample score z q)∪D) F
      have h3 := card_union_le (((S∩test sample score z q)∪D)∪F) E
      omega

theorem ambient_count (sample D F E : Finset A) (score : A → ℝ) (z q : ℝ)
    (h : ∀ x,x∉D → x∉F → x∉E → x∉sample → z/(2*q)≤ score x) :
    (test sample score z q).card ≤ sample.card+D.card+F.card+E.card := by
  have hs : test sample score z q ⊆ sample∪D∪F∪E := by
    intro x hx
    by_cases hd : x∈D
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ hd))
    by_cases hf : x∈F
    · exact mem_union_left _ (mem_union_right _ hf)
    by_cases he : x∈E
    · exact mem_union_right _ he
    apply mem_union_left _ (mem_union_left _ (mem_union_left _ ?_))
    by_contra hp
    have ht := (mem_filter.mp hx).2.resolve_left hp
    exact (not_lt.mpr (h x hd hf he hp)) ht
  calc
    _ ≤ (sample∪D∪F∪E).card := card_le_card hs
    _ ≤ _ := by
      have h1 := card_union_le sample D
      have h2 := card_union_le (sample∪D) F
      have h3 := card_union_le (sample∪D∪F) E
      omega

end
end SharpLogRamsey.LearningRow

namespace SharpLogRamsey.LearningRow
open MeasureTheory Finset
open SharpLogRamsey.BoundedProbability
open scoped Classical BigOperators
noncomputable section
variable {Ω A : Type*} [MeasurableSpace Ω] [Fintype A]

def failures (S : Finset A) (E : A → Set Ω) (ω : Ω) : Finset A := S.filter (fun x => ω∈E x)

omit [MeasurableSpace Ω] [Fintype A] in
lemma eventCount_eq_card (S : Finset A) (E : A → Set Ω) (ω : Ω) :
    eventCount S E ω=(failures S E ω).card := by
  simp only [eventCount,failures,←sum_filter]
  simp

theorem row_success_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S Ds Da : Finset A) (sample : Ω → Finset A) (score typ zx : Ω → A → ℝ)
    (z : Ω → ℝ) (α : A → ℝ) (q tS tA eS eA M εS εA εM ρ : ℝ)
    (E : Set Ω) (FS FA : A → Set Ω)
    (hFS : ∀ x∈S,MeasurableSet (FS x)) (hFA : ∀ x,MeasurableSet (FA x))
    (hq : 0<q) (htS : 0<tS) (htA : 0<tA)
    (hE : ρ≤μ.real E)
    (hfS : ∀ x∈S,μ.real (FS x)≤εS) (hfA : ∀ x,μ.real (FA x)≤εA)
    (hM : μ.real {ω | M<(sample ω).card}≤εM)
    (hz : ∀ ω∈E,0<z ω) (hzx : ∀ ω∈E,∀ x,0≤zx ω x)
    (ha : ∀ x,9/10≤α x ∧ α x≤1)
    (herrors : ∀ ω∈E,∀ x,x∉Ds → x∉sample ω →
      |(score ω x-typ ω x)-α x*zx ω x|≤z ω/(100*q))
    (hs : ∀ ω∈E,∀ x∈S,x∉Ds → x∉sample ω → ω∉FS x → |typ ω x|≤z ω/(10*q))
    (hda : Ds⊆Da)
    (ht : ∀ ω∈E,∀ x,x∉Da → x∉sample ω → ω∉FA x → |typ ω x|≤z ω/(10*q))
    (hes : ∀ ω∈E,((S.filter (fun x => z ω/(10*q)<zx ω x)).card:ℝ)≤eS)
    (hea : ∀ ω∈E,((univ.filter (fun x => zx ω x<(4/5)*z ω/q)).card:ℝ)≤eA) :
    ρ-(S.card:ℝ)*εS/tS-(Fintype.card A:ℝ)*εA/tA-εM ≤
      μ.real {ω | (sample ω).card≤M ∧
        (S.card:ℝ)-(Ds.card:ℝ)-tS-eS≤(S∩test (sample ω) (score ω) (z ω) q).card ∧
        ((test (sample ω) (score ω) (z ω) q).card:ℝ)≤M+(Da.card:ℝ)+tA+eA} := by
  let BS : Set Ω := {ω | tS≤eventCount S FS ω}
  let BA : Set Ω := {ω | tA≤eventCount univ FA ω}
  let BM : Set Ω := {ω | M<(sample ω).card}
  have hbs : μ.real BS≤(S.card:ℝ)*εS/tS := eventCount_tail μ S FS hFS εS tS htS hfS
  have hba : μ.real BA≤(Fintype.card A:ℝ)*εA/tA := by
    simpa using eventCount_tail μ univ FA (fun x _ => hFA x) εA tA htA (fun x _ => hfA x)
  have hb : μ.real (BS∪BA∪BM)≤(S.card:ℝ)*εS/tS+(Fintype.card A:ℝ)*εA/tA+εM := by
    have h1 := measureReal_union_le (μ:=μ) BS BA
    have h2 := measureReal_union_le (μ:=μ) (BS∪BA) BM
    linarith
  have hc : E\(BS∪BA∪BM) ⊆ {ω | (sample ω).card≤M ∧
        (S.card:ℝ)-(Ds.card:ℝ)-tS-eS≤(S∩test (sample ω) (score ω) (z ω) q).card ∧
        ((test (sample ω) (score ω) (z ω) q).card:ℝ)≤M+(Da.card:ℝ)+tA+eA} := by
    intro ω hω
    have hnS : ω∉BS := fun h => hω.2 (Or.inl (Or.inl h))
    have hnA : ω∉BA := fun h => hω.2 (Or.inl (Or.inr h))
    have hnM : ω∉BM := fun h => hω.2 (Or.inr h)
    have hsmallS : ((failures S FS ω).card:ℝ)<tS := by
      rw [←eventCount_eq_card]
      exact lt_of_not_ge hnS
    have hsmallA : ((failures univ FA ω).card:ℝ)<tA := by
      rw [←eventCount_eq_card]
      exact lt_of_not_ge hnA
    have hm : ((sample ω).card:ℝ)≤M := le_of_not_gt hnM
    refine ⟨hm,?_,?_⟩
    · have hh := capture_count S (sample ω) Ds (failures S FS ω)
        (S.filter (fun x => z ω/(10*q)<zx ω x)) (score ω) (z ω) q (by
          intro x hx hds hfs hes hsample
          have htyp := hs ω hω.1 x hx hds hsample (fun hf => hfs (mem_filter.mpr ⟨hx,hf⟩))
          have hzx' : zx ω x≤z ω/(10*q) := by
            by_contra hh
            exact hes (mem_filter.mpr ⟨hx,lt_of_not_ge hh⟩)
          exact capture_score _ _ _ _ _ _ hq (hz ω hω.1) (hzx ω hω.1 x) hzx'
            (by linarith [(ha x).1]) (ha x).2 (herrors ω hω.1 x hds hsample) htyp)
      have hh' : (S.card:ℝ)≤(S∩test (sample ω) (score ω) (z ω) q).card+
          (Ds.card:ℝ)+(failures S FS ω).card+(S.filter (fun x => z ω/(10*q)<zx ω x)).card := by
        exact_mod_cast hh
      linarith [hes ω hω.1]
    · have hh := ambient_count (sample ω) Da (failures univ FA ω)
        (univ.filter (fun x => zx ω x<(4/5)*z ω/q)) (score ω) (z ω) q (by
          intro x hda' hfa hea hsample
          have hds : x∉Ds := fun hx => hda' (hda hx)
          have htyp := ht ω hω.1 x hda' hsample (fun hf => hfa (mem_filter.mpr ⟨mem_univ _,hf⟩))
          have hzx' : (4/5)*z ω/q≤zx ω x := by
            by_contra hh
            exact hea (mem_filter.mpr ⟨mem_univ _,lt_of_not_ge hh⟩)
          exact (exclude_score _ _ _ _ _ _ hq (hz ω hω.1) hzx' (ha x).1
            (herrors ω hω.1 x hds hsample) htyp).le)
      have hh' : ((test (sample ω) (score ω) (z ω) q).card:ℝ)≤(sample ω).card+
          (Da.card:ℝ)+(failures univ FA ω).card+
          (univ.filter (fun x => zx ω x<(4/5)*z ω/q)).card := by exact_mod_cast hh
      linarith [hea ω hω.1]
  have hg := good_minus_bad μ E (BS∪BA∪BM)
  have hh := measureReal_mono (h₂:=measure_ne_top μ _) hc
  linarith

end
end SharpLogRamsey.LearningRow
namespace SharpLogRamsey.PoissonTail
open MeasureTheory ProbabilityTheory Finset
open SharpLogRamsey.BoundedProbability SharpLogRamsey.PoissonGrouping
open scoped BigOperators NNReal Classical
noncomputable section

lemma weighted_power_hasSum (r : ℝ≥0) (a : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-(r:ℝ))*(r:ℝ)^n/(n.factorial:ℝ)*a^n)
      (Real.exp ((r:ℝ)*(a-1))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ((r:ℝ)*a)).mul_left (Real.exp (-(r:ℝ)))
  convert! h using 1
  · funext n
    rw [mul_pow]
    ring
  · rw [←Real.exp_eq_exp_ℝ,←Real.exp_add]
    congr 1
    ring

lemma integrable_power (r : ℝ≥0) (a : ℝ) :
    Integrable (fun n : ℕ => a^n) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa only [Real.norm_eq_abs,abs_pow] using (weighted_power_hasSum r |a|).summable

lemma integral_power (r : ℝ≥0) (a : ℝ) :
    (∫ n : ℕ,a^n ∂poissonMeasure r)=Real.exp ((r:ℝ)*(a-1)) := by
  rw [integral_poissonMeasure' (integrable_power r a)]
  simpa only [smul_eq_mul] using (weighted_power_hasSum r a).tsum_eq

theorem double_mean_tail (r : ℝ≥0) :
    (poissonMeasure r).real {n : ℕ | 2*(r:ℝ)≤n} ≤ Real.exp (-(r:ℝ)/3) := by
  have hlog : 2/3 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hE : {n : ℕ | 2*(r:ℝ)≤n} ⊆
      {n : ℕ | Real.exp (2*(r:ℝ)*Real.log 2) ≤ (2:ℝ)^n} := by
    intro n hn
    change Real.exp (2*(r:ℝ)*Real.log 2) ≤ (2:ℝ)^n
    have he : (2:ℝ)^n=Real.exp ((n:ℝ)*Real.log 2) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
    rw [he]
    change 2*(r:ℝ)≤(n:ℝ) at hn
    apply Real.exp_le_exp.mpr
    nlinarith
  have hm := real_markov (poissonMeasure r) (fun n : ℕ => (2:ℝ)^n)
    (integrable_power r 2) (fun _ => by positivity)
    (Real.exp (2*(r:ℝ)*Real.log 2)) (Real.exp_pos _).le
    (Set.to_countable _).measurableSet
  rw [integral_power] at hm
  have ht : (poissonMeasure r).real {n : ℕ | Real.exp (2*(r:ℝ)*Real.log 2)≤(2:ℝ)^n} ≤
      Real.exp ((r:ℝ)-2*(r:ℝ)*Real.log 2) := by
    rw [Real.exp_sub]
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    simpa only [sub_self, sub_zero,show (2:ℝ)-1=1 by norm_num,mul_one,mul_comm] using hm
  apply (measureReal_mono (h₂:=measure_ne_top _ _) hE).trans (ht.trans ?_)
  apply Real.exp_le_exp.mpr
  nlinarith [r.coe_nonneg]

theorem total_tail {ι : Type*} [Fintype ι] (rate : ι → ℝ≥0) :
    (law rate).real {ω | 2*(∑ i,(rate i:ℝ)) ≤ (∑ i,ω i : ℕ)} ≤
      Real.exp (-(∑ i,(rate i:ℝ))/3) := by
  have h := sum_hasLaw rate univ
  have hm := h.measurePreserving (measurable_of_countable _)
  have he : (law rate).real {ω | 2*(∑ i,(rate i:ℝ)) ≤ (∑ i,ω i : ℕ)} =
      (poissonMeasure (∑ i,rate i)).real {n : ℕ | 2*(∑ i,(rate i:ℝ))≤n} := by
    unfold Measure.real
    rw [←hm.measure_preimage (Set.to_countable _).measurableSet.nullMeasurableSet]
    rfl
  rw [he]
  simpa using double_mean_tail (∑ i,rate i)

end
end SharpLogRamsey.PoissonTail

namespace SharpLogRamsey.ExceptionalScore
open Finset
open scoped Classical BigOperators
noncomputable section
variable {A H R : Type*} [Fintype R]

def empty (S : Finset A) (ω : R → A → ℕ) (r : R) : Prop := ∀ x∈S,ω r x=0

def term (O X : Finset A) (b : ℝ) (ω : R → A → ℕ) : ℝ :=
  ∏ r,if empty O ω r then (if empty X ω r then 1-b else -b) else 0

def fullyEmpty (S : Finset A) (ω : R → A → ℕ) : Prop := ∀ r,empty S ω r

omit [Fintype R] in
lemma empty_mono {S T : Finset A} (h : S ⊆ T) (ω : R → A → ℕ) (r : R)
    (he : empty T ω r) : empty S ω r := fun x hx => he x (h hx)

omit [Fintype R] in
lemma factor_abs_le (O X : Finset A) (b : ℝ) (ω : R → A → ℕ) (r : R)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    |if empty O ω r then (if empty X ω r then 1-b else -b) else 0| ≤ 1 := by
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma term_empty (O X : Finset A) (b : ℝ) (ω : R → A → ℕ)
    (ho : fullyEmpty O ω) (hx : fullyEmpty X ω) :
    term O X b ω = (1-b)^(Fintype.card R) := by
  simp only [term,ite_eq_left (ho _),ite_eq_left (hx _),prod_const,card_univ]

lemma term_hit (O X : Finset A) (b : ℝ) (ω : R → A → ℕ)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hh : ¬fullyEmpty (O∪X) ω) :
    |term O X b ω| ≤ b := by
  classical
  have hw : ∃ r,¬empty (O∪X) ω r := by simpa only [fullyEmpty,not_forall] using hh
  obtain ⟨r,hr⟩ := hw
  have hr' : ¬empty O ω r ∨ ¬empty X ω r := by
    by_contra h
    push Not at h
    apply hr
    intro x hx
    rcases mem_union.mp hx with hx|hx
    · exact h.1 x hx
    · exact h.2 x hx
  have hf : |if empty O ω r then (if empty X ω r then 1-b else -b) else 0| ≤ b := by
    rcases hr' with ho|hx
    · simp only [ite_eq_right ho,abs_zero]; exact hb
    · split_ifs <;> simp_all only [abs_neg,abs_of_nonneg hb,le_refl,abs_zero]
  rw [term,abs_prod]
  calc
    _ = |if empty O ω r then (if empty X ω r then 1-b else -b) else 0| *
        ∏ j∈univ.erase r,|if empty O ω j then (if empty X ω j then 1-b else -b) else 0| :=
      (mul_prod_erase _ _ (mem_univ r)).symm
    _ ≤ b*1 := mul_le_mul hf (prod_le_one₀ (fun _ _ => abs_nonneg _)
      (fun j _ => factor_abs_le O X b ω j hb hb1)) (prod_nonneg (fun _ _ => abs_nonneg _)) hb
    _ = b := mul_one _

omit [Fintype R] in

lemma fullyEmpty_decomposition (S O X : Finset A) (x : A) (ω : R → A → ℕ)
    (ho : O ⊆ S) (hx : X=S\(O∪{x})) (hc : ∀ r,ω r x=0) :
    fullyEmpty S ω ↔ fullyEmpty (O∪X) ω := by
  subst X
  constructor
  · intro h r
    apply empty_mono (union_subset ho (sdiff_subset)) ω r (h r)
  · intro h r y hy
    by_cases hyo : y∈O
    · exact h r y (mem_union_left _ hyo)
    · by_cases hyx : y=x
      · simpa only [hyx] using hc r
      · exact h r y (mem_union_right _ (mem_sdiff.mpr ⟨hy,by simp [hyo,hyx]⟩))

theorem exceptional_error (E : Finset H) (S O X : H → Finset A)
    (b : ℝ) (ω : R → A → ℕ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hdec : ∀ H∈E,fullyEmpty (S H) ω ↔ fullyEmpty (O H∪X H) ω) :
    |(∑ H∈E,term (O H) (X H) b ω) -
      (1-b)^(Fintype.card R)*(E.filter (fun H => fullyEmpty (S H) ω)).card| ≤
      b*(E.card:ℝ) := by
  have heq : (1-b)^(Fintype.card R)*(E.filter (fun H => fullyEmpty (S H) ω)).card =
      ∑ H∈E,if fullyEmpty (S H) ω then (1-b)^(Fintype.card R) else 0 := by
    rw [←sum_filter]; simp [mul_comm]
  rw [heq,←sum_sub_distrib]
  calc
    _ ≤ ∑ H∈E,|term (O H) (X H) b ω-
      (if fullyEmpty (S H) ω then (1-b)^(Fintype.card R) else 0)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _H∈E,b := by
      apply sum_le_sum
      intro H hH
      by_cases he : fullyEmpty (S H) ω
      · have hu := (hdec H hH).mp he
        have ho : fullyEmpty (O H) ω := fun r => empty_mono (subset_union_left) ω r (hu r)
        have hx : fullyEmpty (X H) ω := fun r => empty_mono (subset_union_right) ω r (hu r)
        rw [ite_eq_left he,term_empty _ _ _ _ ho hx,sub_self,abs_zero]
        exact hb
      · rw [ite_eq_right he,sub_zero]
        exact term_hit _ _ _ _ hb hb1 (fun h => he ((hdec H hH).mpr h))
    _ = _ := by simp [mul_comm]

end
end SharpLogRamsey.ExceptionalScore

namespace SharpLogRamsey.PreparedMass
open Finset
open scoped Classical BigOperators
noncomputable section
variable {A H : Type*}

def count (S : Finset A) (R : A → Prop) : ℕ := (S.filter R).card

def outside (S O : Finset A) (x : A) : Finset A := S\(O∪{x})

lemma count_split (S O : Finset A) (x : A) (R : A → Prop) (ho : O ⊆ S) :
    count S R = count O R+count (outside S O x) R+
      (if x∈S ∧ x∉O ∧ R x then 1 else 0) := by
  classical
  have he : S.filter R = (O.filter R) ∪ (outside S O x).filter R ∪
      (({x} : Finset A).filter (fun y => y∈S ∧ y∉O ∧ R y)) := by
    ext y
    simp only [mem_filter,mem_union,mem_singleton, outside,mem_sdiff]
    constructor
    · rintro ⟨hy,hr⟩
      by_cases hyo : y∈O
      · exact Or.inl (Or.inl ⟨hyo,hr⟩)
      · by_cases hyx : y=x
        · exact Or.inr ⟨hyx,hy,hyo,hr⟩
        · exact Or.inl (Or.inr ⟨⟨hy,not_or.mpr ⟨hyo,hyx⟩⟩,hr⟩)
    · rintro ((⟨hy,hr⟩|⟨⟨hy,_⟩,hr⟩)|⟨_,hy,_,hr⟩)
      · exact ⟨ho hy,hr⟩
      · exact ⟨hy,hr⟩
      · exact ⟨hy,hr⟩
  have hd : Disjoint (O.filter R) ((outside S O x).filter R) := by
    apply disjoint_left.mpr
    intro y hy hz
    have hh := (mem_sdiff.mp (mem_filter.mp hz).1).2
    exact hh (mem_union_left _ (mem_filter.mp hy).1)
  have hd2 : Disjoint (O.filter R ∪ (outside S O x).filter R)
      (({x} : Finset A).filter (fun y => y∈S ∧ y∉O ∧ R y)) := by
    apply disjoint_left.mpr
    intro y hy hz
    obtain ⟨hyx,_,hyo,_⟩ := mem_filter.mp hz
    have hyx' : y=x := mem_singleton.mp hyx
    rcases mem_union.mp hy with hy|hy
    · exact hyo (mem_filter.mp hy).1
    · exact (mem_sdiff.mp (mem_filter.mp hy).1).2 (by simp only [mem_union,mem_singleton]; exact Or.inr hyx')
  unfold count
  rw [he,card_union_of_disjoint hd2,card_union_of_disjoint hd]
  simp only [filter_singleton]
  split_ifs <;> simp

lemma normalized_split (S O : Finset A) (x : A) (R : A → Prop) (ho : O ⊆ S)
    (q N : ℝ) :
    (q/N)*(count S R:ℝ)=(q/N)*(count O R:ℝ)+(q/N)*(count (outside S O x) R:ℝ)+
      (if x∈S ∧ x∉O ∧ R x then q/N else 0) := by
  rw [count_split S O x R ho]
  push_cast
  split_ifs <;> ring

theorem typical_range (full cell removed f : ℝ)
    (hf : 0 ≤ f) (hf4 : f ≤ 1/25)
    (hl : |full-1| ≤ 1/10) (hc : |cell-f| ≤ 1/50)
    (hr : 0 ≤ removed) (hr1 : removed ≤ 1/100) :
    3/4 ≤ full-cell-removed ∧ full-cell-removed < 2 ∧
      |(full-cell-removed)-(1-f)| ≤ 13/100 := by
  rw [abs_le] at hl hc ⊢
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem typical_square_sum (T : Finset H) (full cell removed : H → ℝ) (f E e : ℝ)
    (hfull : (∑ H∈T,(full H-1)^2) ≤ E)
    (hcell : (∑ H∈T,(cell H-f)^2) ≤ E)
    (hr : ∀ H∈T,0 ≤ removed H) (hre : ∀ H∈T,removed H ≤ e) :
    (∑ H∈T,((full H-cell H-removed H)-(1-f))^2) ≤
      6*E+3*(T.card:ℝ)*e^2 := by
  have hp : ∀ H∈T,removed H^2 ≤ e^2 := by
    intro H hH
    nlinarith [sq_nonneg (e-removed H),hr H hH,hre H hH]
  calc
    _ ≤ ∑ H∈T,(3*(full H-1)^2+3*(cell H-f)^2+3*e^2) := by
      apply sum_le_sum
      intro H hH
      have h1 := sq_nonneg ((full H-1)+(cell H-f))
      have h2 := sq_nonneg ((full H-1)+removed H)
      have h3 := sq_nonneg ((cell H-f)-removed H)
      nlinarith [hp H hH]
    _ = 3*(∑ H∈T,(full H-1)^2)+3*(∑ H∈T,(cell H-f)^2)+3*(T.card:ℝ)*e^2 := by
      rw [sum_add_distrib,sum_add_distrib,←mul_sum,←mul_sum]
      simp; ring
    _ ≤ _ := by linarith

end
end SharpLogRamsey.PreparedMass

end

end OAI
