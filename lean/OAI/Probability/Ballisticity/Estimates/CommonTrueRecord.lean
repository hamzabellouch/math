import Mathlib
import OAI.Probability.Ballisticity.Walk.FixedQuenchedKernel

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma noDropFinite_real_integral_translation {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (x : Lattice d) (n : ℕ) :
    (∫ ω, (noDropFinite ℓ x n ω).toReal ∂environmentLaw ν) =
      ∫ ω, (noDropFinite ℓ 0 n ω).toReal ∂environmentLaw ν := by
  conv_lhs => enter [2, ω]; rw [noDropFinite_translation ℓ ω x n]
  have h := integral_map (μ := environmentLaw ν)
    (show AEMeasurable (fun ω : Environment d => fun a => ω (x + a)) (environmentLaw ν) from
      (by fun_prop : Measurable (fun ω : Environment d => fun a => ω (x + a))).aemeasurable)
    ((noDropFinite_measurable ℓ 0 n).ennreal_toReal.aestronglyMeasurable)
  rw [environment_translation] at h
  exact h.symm

lemma noDropFinite_toReal_le_one {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (n : ℕ) (ω : Environment d) : (noDropFinite ℓ x n ω).toReal ≤ 1 := by
  exact (ENNReal.toReal_mono (by simp) (show noDropFinite ℓ x n ω ≤ 1 from prob_le_one)).trans
    (by simp)

lemma noDrop_real_integrable {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) :
    Integrable (fun ω => (noDropQuenched ℓ x ω).toReal) (environmentLaw ν) :=
  integrable_of_nonneg_bound _ (measurable_noDropQuenched ℓ x).ennreal_toReal
    (fun ω => ⟨ENNReal.toReal_nonneg, noDropQuenched_toReal_le_one ℓ x ω⟩)

lemma noDropFinite_real_integrable {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) (n : ℕ) :
    Integrable (fun ω => (noDropFinite ℓ x n ω).toReal) (environmentLaw ν) :=
  integrable_of_nonneg_bound _ (noDropFinite_measurable ℓ x n).ennreal_toReal
    (fun ω => ⟨ENNReal.toReal_nonneg, noDropFinite_toReal_le_one ℓ x n ω⟩)

lemma noDropFinite_real_integral_tendsto {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (x : Lattice d) :
    Tendsto (fun n => ∫ ω, (noDropFinite ℓ x n ω).toReal ∂environmentLaw ν) atTop
      (𝓝 (∫ ω, (noDropQuenched ℓ x ω).toReal ∂environmentLaw ν)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro n
    exact (noDropFinite_measurable ℓ x n).ennreal_toReal.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact noDropFinite_toReal_le_one ℓ x n ω
  · exact Filter.Eventually.of_forall fun ω =>
      (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (noDropFinite_tendsto ℓ x ω)

lemma sharedNoDropMass_toReal {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) :
    (sharedNoDropMass ν ℓ x y).toReal =
      ∫ ω, (noDropQuenched ℓ x ω).toReal * (noDropQuenched ℓ y ω).toReal
        ∂environmentLaw ν := by
  have h := integral_toReal (μ := environmentLaw ν)
    (((measurable_noDropQuenched ℓ x).mul (measurable_noDropQuenched ℓ y)).aemeasurable)
    (Filter.Eventually.of_forall fun ω => ENNReal.mul_lt_top (measure_ne_top _ _).lt_top
      (measure_ne_top _ _).lt_top)
  simpa only [Pi.mul_apply, ENNReal.toReal_mul, sharedNoDropMass] using h.symm

lemma sharedNoDropMass_mixing {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ x y : Lattice d, Disjoint (LatticeBall x n) (LatticeBall y n) →
      |(sharedNoDropMass ν ℓ x y).toReal -
        (annealedLaw ν (NoDrop ℓ 0)).toReal ^ 2| < ε := by
  let μ := environmentLaw ν
  let b := ∫ ω, (noDropQuenched ℓ 0 ω).toReal ∂μ
  let a := fun n => ∫ ω, (noDropFinite ℓ 0 n ω).toReal ∂μ
  have hb : 0 ≤ b ∧ b ≤ 1 := ⟨integral_nonneg fun _ => ENNReal.toReal_nonneg,
    (integral_mono (noDrop_real_integrable ν ℓ 0) (integrable_const (1 : ℝ))
      (fun ω => noDropQuenched_toReal_le_one ℓ 0 ω)).trans (by simp)⟩
  have ha n : 0 ≤ a n ∧ a n ≤ 1 := ⟨integral_nonneg fun _ => ENNReal.toReal_nonneg,
    (integral_mono (noDropFinite_real_integrable ν ℓ 0 n) (integrable_const (1 : ℝ))
      (fun ω => noDropFinite_toReal_le_one ℓ 0 n ω)).trans (by simp)⟩
  have hba n : b ≤ a n := integral_mono (noDrop_real_integrable ν ℓ 0)
    (noDropFinite_real_integrable ν ℓ 0 n) (fun ω =>
      ENNReal.toReal_mono (measure_ne_top _ _) (noDropQuenched_le_finite ℓ 0 ω n))
  have hlim : Tendsto (fun n => 2 * (a n - b)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [a, b, μ, sub_self, mul_zero] using
      ((noDropFinite_real_integral_tendsto ν ℓ 0).sub_const b).const_mul 2
  obtain ⟨n,hn⟩ := (hlim.eventually_lt_const hε).exists
  refine ⟨n, fun x y hxy => ?_⟩
  let f := fun z ω => (noDropFinite ℓ z n ω).toReal
  let g := fun z ω => (noDropQuenched ℓ z ω).toReal
  have hfi z : Integrable (f z) μ := noDropFinite_real_integrable ν ℓ z n
  have hgi z : Integrable (g z) μ := noDrop_real_integrable ν ℓ z
  have hfg z ω : g z ω ≤ f z ω :=
    ENNReal.toReal_mono (measure_ne_top _ _) (noDropQuenched_le_finite ℓ z ω n)
  have hf z ω : 0 ≤ f z ω ∧ f z ω ≤ 1 :=
    ⟨ENNReal.toReal_nonneg, noDropFinite_toReal_le_one ℓ z n ω⟩
  have hg z ω : 0 ≤ g z ω ∧ g z ω ≤ 1 :=
    ⟨ENNReal.toReal_nonneg, noDropQuenched_toReal_le_one ℓ z ω⟩
  have hfp : Integrable (fun ω => f x ω * f y ω) μ :=
    integrable_of_nonneg_bound _
      (((noDropFinite_measurable ℓ x n).ennreal_toReal).mul
        ((noDropFinite_measurable ℓ y n).ennreal_toReal))
      (fun ω => ⟨mul_nonneg (hf x ω).1 (hf y ω).1,
        by simpa only [one_mul] using mul_le_mul (hf x ω).2 (hf y ω).2 (hf y ω).1 zero_le_one⟩)
  have hgp : Integrable (fun ω => g x ω * g y ω) μ :=
    integrable_of_nonneg_bound _
      (((measurable_noDropQuenched ℓ x).ennreal_toReal).mul
        ((measurable_noDropQuenched ℓ y).ennreal_toReal))
      (fun ω => ⟨mul_nonneg (hg x ω).1 (hg y ω).1,
        by simpa only [one_mul] using mul_le_mul (hg x ω).2 (hg y ω).2 (hg y ω).1 zero_le_one⟩)
  have he : (∫ ω, f x ω * f y ω ∂μ) = a n ^ 2 := by
    rw [fresh_rows_factor ν hxy (noDropFinite_measurable_ball ℓ x n).ennreal_toReal
      (noDropFinite_measurable_ball ℓ y n).ennreal_toReal]
    rw [noDropFinite_real_integral_translation ν ℓ x,
      noDropFinite_real_integral_translation ν ℓ y]
    simp only [a,μ,pow_two]
  have hu := integral_mono hgp hfp (fun ω =>
    mul_le_mul (hfg x ω) (hfg y ω) (hg y ω).1 (hf x ω).1)
  have hl := integral_mono hfp (hgp.add (((hfi x).sub (hgi x)).add ((hfi y).sub (hgi y))))
    (fun ω => by
      change f x ω * f y ω ≤ g x ω * g y ω + (f x ω - g x ω + (f y ω - g y ω))
      nlinarith [(mul_nonneg (sub_nonneg.mpr (hfg x ω)) (sub_nonneg.mpr (hf y ω).2)),
        (mul_nonneg (sub_nonneg.mpr (hfg y ω)) (sub_nonneg.mpr (hg x ω).2))])
  have hix := integral_sub (hfi x) (hgi x)
  have hiy := integral_sub (hfi y) (hgi y)
  have hia := integral_add ((hfi x).sub (hgi x)) ((hfi y).sub (hgi y))
  have hio := integral_add hgp (((hfi x).sub (hgi x)).add ((hfi y).sub (hgi y)))
  simp only [Pi.add_apply, Pi.sub_apply] at hl hix hiy hia hio
  rw [hio, hia, hix, hiy, he] at hl
  simp only [f, g, μ, noDropFinite_real_integral_translation ν ℓ,
    noDrop_real_integral_translation ν ℓ] at hl
  change a n ^ 2 ≤ (∫ ω, g x ω * g y ω ∂μ) + (a n - b + (a n - b)) at hl
  rw [he] at hu
  have hbmass : b = (annealedLaw ν (NoDrop ℓ 0)).toReal := by
    rw [annealed_apply ν (measurableSet_noDrop ℓ 0)]
    exact integral_toReal (measurable_noDropQuenched ℓ 0).aemeasurable
      (Filter.Eventually.of_forall fun ω => (measure_ne_top _ _).lt_top)
  rw [sharedNoDropMass_toReal, ← hbmass, abs_lt]
  change -ε < (∫ ω, g x ω * g y ω ∂μ) - b ^ 2 ∧
    (∫ ω, g x ω * g y ω ∂μ) - b ^ 2 < ε
  have hpow : b ^ 2 ≤ a n ^ 2 := pow_le_pow_left₀ hb.1 (hba n) 2
  have hdiff : a n ^ 2 - b ^ 2 ≤ 2 * (a n - b) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (hba n))
      (show 0 ≤ 2 - (a n + b) by linarith [(ha n).2,hb.2])]
  constructor <;> linarith

def CommonTrueRecord {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) (n m : ℕ) : Prop :=
  TrueRecord ℓ P.1 n ∧ TrueRecord ℓ P.2 m ∧
    dot (realPosition (P.1 n)) ℓ = dot (realPosition (P.2 m)) ℓ

def FirstCommonTrueRecord {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) (n m : ℕ) : Prop :=
  0 < n ∧ 0 < m ∧ CommonTrueRecord ℓ P n m ∧
    ∀ j k, 0 < j → j < n → 0 < k → k < m → ¬ CommonTrueRecord ℓ P j k

lemma measurableSet_commonTrueRecord {d : ℕ} (ℓ : Vector d) (n m : ℕ) :
    MeasurableSet {P : Path d × Path d | CommonTrueRecord ℓ P n m} := by
  exact ((measurableSet_trueRecord ℓ n).preimage measurable_fst).inter
    (((measurableSet_trueRecord ℓ m).preimage measurable_snd).inter
      (measurableSet_eq_fun
        ((measurable_of_countable (fun z : Lattice d => dot (realPosition z) ℓ)).comp
          ((measurable_pi_apply n).comp measurable_fst))
        ((measurable_of_countable (fun z : Lattice d => dot (realPosition z) ℓ)).comp
          ((measurable_pi_apply m).comp measurable_snd))))

lemma measurableSet_firstCommonTrueRecord {d : ℕ} (ℓ : Vector d) (n m : ℕ) :
    MeasurableSet {P : Path d × Path d | FirstCommonTrueRecord ℓ P n m} := by
  simp only [FirstCommonTrueRecord, Set.ofPred_and, Set.ofPred_forall]
  refine (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((measurableSet_commonTrueRecord ℓ n m).inter ?_))
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun k =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
        (measurableSet_commonTrueRecord ℓ j k).compl

lemma not_trueRecord_before_true_iff {d : ℕ} (ℓ : Vector d) (X : Path d)
    {j n : ℕ} (hjn : j < n) (hj : StrictRecord ℓ X j) (hn : TrueRecord ℓ X n) :
    ¬ TrueRecord ℓ X j ↔ ∃ k, j < k ∧ k < n ∧
      dot (realPosition (X k)) ℓ < dot (realPosition (X j)) ℓ := by
  constructor
  · intro hnot
    have hD : ¬ X ∈ FutureNoDrop ℓ j := fun h => hnot ⟨hj,h⟩
    change ¬ ∀ k, dot (realPosition (X j)) ℓ ≤ dot (realPosition (X (j+k))) ℓ at hD
    push Not at hD
    obtain ⟨a,ha⟩ := hD
    have hpos : 0 < a := by
      by_contra h
      have hz : a = 0 := by omega
      simp [hz] at ha
    refine ⟨j+a, by omega, ?_, ha⟩
    by_contra hkn
    have hnj : dot (realPosition (X j)) ℓ < dot (realPosition (X n)) ℓ := hn.1 j hjn
    have hd := hn.2 (j+a-n)
    change dot (realPosition (X n)) ℓ ≤ dot (realPosition (X (n+(j+a-n)))) ℓ at hd
    rw [show n+(j+a-n) = j+a by omega] at hd
    linarith
  · rintro ⟨k,hjk,_,hdrop⟩ htrue
    have hd := htrue.2 (k-j)
    change dot (realPosition (X j)) ℓ ≤ dot (realPosition (X (j+(k-j)))) ℓ at hd
    rw [show j+(k-j) = k by omega] at hd
    exact (not_lt_of_ge hd) hdrop

def AdmissibleCommonWords {d : ℕ} (ℓ : Vector d) (x y : Lattice d)
    (w v : List (Direction d)) : Prop :=
  0 < w.length ∧ 0 < v.length ∧
  dot (realPosition (wordPath x w w.length)) ℓ =
    dot (realPosition (wordPath y v v.length)) ℓ ∧
  StrictRecord ℓ (wordPath x w) w.length ∧
  StrictRecord ℓ (wordPath y v) v.length ∧
  (∀ j ≤ w.length, dot (realPosition x) ℓ ≤ dot (realPosition (wordPath x w j)) ℓ) ∧
  (∀ k ≤ v.length, dot (realPosition y) ℓ ≤ dot (realPosition (wordPath y v k)) ℓ) ∧
  ∀ j k, 0 < j → j < w.length → 0 < k → k < v.length →
    StrictRecord ℓ (wordPath x w) j → StrictRecord ℓ (wordPath y v) k →
    dot (realPosition (wordPath x w j)) ℓ = dot (realPosition (wordPath y v k)) ℓ →
    (∃ a, j < a ∧ a < w.length ∧ dot (realPosition (wordPath x w a)) ℓ <
      dot (realPosition (wordPath x w j)) ℓ) ∨
    (∃ b, k < b ∧ b < v.length ∧ dot (realPosition (wordPath y v b)) ℓ <
      dot (realPosition (wordPath y v k)) ℓ)

lemma noDrop_iff_prefix_and_future {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (X : Path d) (n : ℕ) (hD : X ∈ FutureNoDrop ℓ n) :
    X ∈ NoDrop ℓ x ↔
      ∀ j ≤ n, dot (realPosition x) ℓ ≤ dot (realPosition (X j)) ℓ := by
  constructor
  · exact fun h j _ => h j
  · intro h j
    by_cases hj : j ≤ n
    · exact h j hj
    · have hd := hD (j-n)
      change dot (realPosition (X n)) ℓ ≤ dot (realPosition (X (n+(j-n)))) ℓ at hd
      rw [show n+(j-n) = j by omega] at hd
      exact (h n le_rfl).trans hd

lemma commonTrueRecord_congr_prefix {d : ℕ} (ℓ : Vector d)
    {P Q : Path d × Path d} {j k n m : ℕ}
    (hP : ∀ i ≤ n, P.1 i = Q.1 i) (hQ : ∀ i ≤ m, P.2 i = Q.2 i)
    (hj : j ≤ n) (hk : k ≤ m) :
    (StrictRecord ℓ P.1 j ∧ StrictRecord ℓ P.2 k ∧
        dot (realPosition (P.1 j)) ℓ = dot (realPosition (P.2 k)) ℓ) ↔
      (StrictRecord ℓ Q.1 j ∧ StrictRecord ℓ Q.2 k ∧
        dot (realPosition (Q.1 j)) ℓ = dot (realPosition (Q.2 k)) ℓ) := by
  rw [strictRecord_congr_prefix ℓ hj hP, strictRecord_congr_prefix ℓ hk hQ,
    hP j hj, hQ k hk]

lemma firstCommonWords_characterization {d : ℕ} (ℓ : Vector d) (x y : Lattice d)
    (w v : List (Direction d)) (P : Path d × Path d)
    (hw : P.1 ∈ wordCylinder x w) (hv : P.2 ∈ wordCylinder y v) :
    (P.1 ∈ NoDrop ℓ x ∧ P.2 ∈ NoDrop ℓ y ∧
      FirstCommonTrueRecord ℓ P w.length v.length) ↔
    (AdmissibleCommonWords ℓ x y w v ∧
      P.1 ∈ FutureNoDrop ℓ w.length ∧ P.2 ∈ FutureNoDrop ℓ v.length) := by
  have hr1 j (hj : j ≤ w.length) : StrictRecord ℓ P.1 j ↔
      StrictRecord ℓ (wordPath x w) j := strictRecord_congr_prefix ℓ hj hw
  have hr2 k (hk : k ≤ v.length) : StrictRecord ℓ P.2 k ↔
      StrictRecord ℓ (wordPath y v) k := strictRecord_congr_prefix ℓ hk hv
  constructor
  · rintro ⟨hD1,hD2,hwpos,hvpos,⟨ht1,ht2,he⟩,hfirst⟩
    refine ⟨⟨hwpos,hvpos,?_,(hr1 _ le_rfl).mp ht1.1,(hr2 _ le_rfl).mp ht2.1,
      ?_,?_,?_⟩,ht1.2,ht2.2⟩
    · simpa only [hw _ le_rfl,hv _ le_rfl] using he
    · intro j hj
      simpa only [hw j hj] using hD1 j
    · intro k hk
      simpa only [hv k hk] using hD2 k
    · intro j k hj hjn hk hkm hrj hrk heq
      have hj' := (hr1 j hjn.le).mpr hrj
      have hk' := (hr2 k hkm.le).mpr hrk
      have he' : dot (realPosition (P.1 j)) ℓ = dot (realPosition (P.2 k)) ℓ := by
        simpa only [hw j hjn.le,hv k hkm.le] using heq
      have hnot := hfirst j k hj hjn hk hkm
      have hdis : ¬ TrueRecord ℓ P.1 j ∨ ¬ TrueRecord ℓ P.2 k := by
        by_cases h1 : TrueRecord ℓ P.1 j
        · exact Or.inr fun h2 => hnot ⟨h1,h2,he'⟩
        · exact Or.inl h1
      rcases hdis with h1 | h2
      · obtain ⟨a,hja,han,ha⟩ := (not_trueRecord_before_true_iff ℓ P.1 hjn hj' ht1).mp h1
        exact Or.inl ⟨a,hja,han,by simpa only [hw a han.le,hw j hjn.le] using ha⟩
      · obtain ⟨b,hkb,hbm,hb⟩ := (not_trueRecord_before_true_iff ℓ P.2 hkm hk' ht2).mp h2
        exact Or.inr ⟨b,hkb,hbm,by simpa only [hv b hbm.le,hv k hkm.le] using hb⟩
  · rintro ⟨⟨hwpos,hvpos,he,hrw,hrv,hD1,hD2,hfail⟩,hF1,hF2⟩
    have ht1 : TrueRecord ℓ P.1 w.length := ⟨(hr1 _ le_rfl).mpr hrw,hF1⟩
    have ht2 : TrueRecord ℓ P.2 v.length := ⟨(hr2 _ le_rfl).mpr hrv,hF2⟩
    refine ⟨(noDrop_iff_prefix_and_future ℓ x P.1 _ hF1).mpr ?_,
      (noDrop_iff_prefix_and_future ℓ y P.2 _ hF2).mpr ?_,
      hwpos,hvpos,⟨ht1,ht2,?_⟩,?_⟩
    · intro j hj
      simpa only [hw j hj] using hD1 j hj
    · intro k hk
      simpa only [hv k hk] using hD2 k hk
    · simpa only [hw _ le_rfl,hv _ le_rfl] using he
    · intro j k hj hjn hk hkm htrue
      have hdis := hfail j k hj hjn hk hkm ((hr1 _ hjn.le).mp htrue.1.1)
        ((hr2 _ hkm.le).mp htrue.2.1.1)
        (by simpa only [hw j hjn.le,hv k hkm.le] using htrue.2.2)
      rcases hdis with ⟨a,hja,han,ha⟩ | ⟨b,hkb,hbm,hb⟩
      · exact (not_trueRecord_before_true_iff ℓ P.1 hjn htrue.1.1 ht1).mpr
          ⟨a,hja,han,by simpa only [hw a han.le,hw j hjn.le] using ha⟩ htrue.1
      · exact (not_trueRecord_before_true_iff ℓ P.2 hkm htrue.2.1.1 ht2).mpr
          ⟨b,hkb,hbm,by simpa only [hv b hbm.le,hv k hkm.le] using hb⟩ htrue.2.1

def commonPairSuffix {d : ℕ} (n m : ℕ) (P : Path d × Path d) : Path d × Path d :=
  ((fun j => P.1 (n+j)), (fun j => P.2 (m+j)))

lemma measurable_commonPairSuffix {d : ℕ} (n m : ℕ) :
    Measurable (commonPairSuffix (d := d) n m) := by
  unfold commonPairSuffix
  fun_prop

def commonWordEvent {d : ℕ} (ℓ : Vector d) (x y : Lattice d)
    (w v : List (Direction d)) : Set (Path d × Path d) :=
  (wordCylinder x w ×ˢ wordCylinder y v) ∩
    {P | FirstCommonTrueRecord ℓ P w.length v.length}

lemma measurableSet_commonWordEvent {d : ℕ} (ℓ : Vector d) (x y : Lattice d)
    (w v : List (Direction d)) : MeasurableSet (commonWordEvent ℓ x y w v) :=
  ((measurableSet_wordCylinder x w).prod (measurableSet_wordCylinder y v)).inter
    (measurableSet_firstCommonTrueRecord ℓ w.length v.length)

lemma common_word_suffix_event {d : ℕ} (ℓ : Vector d) (x y : Lattice d)
    (w v : List (Direction d)) (had : AdmissibleCommonWords ℓ x y w v)
    (A B : Set (Path d)) :
    ((commonPairSuffix w.length v.length ⁻¹' (A ×ˢ B)) ∩
        commonWordEvent ℓ x y w v) ∩ (NoDrop ℓ x ×ˢ NoDrop ℓ y) =
      (((fun X : Path d => fun j => X (w.length+j)) ⁻¹'
          (A ∩ NoDrop ℓ (wordPath x w w.length)) ∩ wordCylinder x w) ×ˢ
       ((fun X : Path d => fun j => X (v.length+j)) ⁻¹'
          (B ∩ NoDrop ℓ (wordPath y v v.length)) ∩ wordCylinder y v)) := by
  ext P
  constructor
  · rintro ⟨⟨hAB,⟨⟨hw,hv⟩,hfirst⟩⟩,hD1,hD2⟩
    have hFs := (firstCommonWords_characterization ℓ x y w v P hw hv).mp ⟨hD1,hD2,hfirst⟩
    refine ⟨⟨⟨hAB.1,?_⟩,hw⟩,⟨⟨hAB.2,?_⟩,hv⟩⟩
    · intro j
      rw [← hw _ le_rfl]
      exact hFs.2.1 j
    · intro j
      rw [← hv _ le_rfl]
      exact hFs.2.2 j
  · rintro ⟨⟨⟨hA,hD1⟩,hw⟩,⟨⟨hB,hD2⟩,hv⟩⟩
    have hFs : P.1 ∈ FutureNoDrop ℓ w.length ∧ P.2 ∈ FutureNoDrop ℓ v.length := by
      constructor
      · intro j
        rw [hw _ le_rfl]
        exact hD1 j
      · intro j
        rw [hv _ le_rfl]
        exact hD2 j
    have hcore := (firstCommonWords_characterization ℓ x y w v P hw hv).mpr
      ⟨had,hFs⟩
    exact ⟨⟨⟨hA,hB⟩,⟨⟨hw,hv⟩,hcore.2.2⟩⟩,hcore.1,hcore.2.1⟩

lemma shared_conditioned_common_word_rectangle {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (x y : Lattice d)
    (w v : List (Direction d)) (had : AdmissibleCommonWords ℓ x y w v)
    (A B : Set (Path d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hpt : sharedNoDropMass ν ℓ (wordPath x w w.length) (wordPath y v v.length) ≠ 0) :
    sharedConditionedPairLaw ν ℓ x y
      ((commonPairSuffix w.length v.length ⁻¹' (A ×ˢ B)) ∩ commonWordEvent ℓ x y w v) =
      (sharedNoDropMass ν ℓ x y)⁻¹ *
        sharedPairLaw ν x y (wordCylinder x w ×ˢ wordCylinder y v) *
        sharedNoDropMass ν ℓ (wordPath x w w.length) (wordPath y v v.length) *
        sharedConditionedPairLaw ν ℓ (wordPath x w w.length) (wordPath y v v.length) (A ×ˢ B) := by
  let a := wordPath x w w.length
  let b := wordPath y v v.length
  let T := {z : Lattice d | dot (realPosition a) ℓ ≤ dot (realPosition z) ℓ}
  have hb : b ∈ T := le_of_eq had.2.2.1
  have hdis : Disjoint ((wordDepartures x w : Set (Lattice d)) ∪ wordDepartures y v) T := by
    apply Set.disjoint_left.mpr
    intro z hz hzt
    rcases hz with hz | hz
    · obtain ⟨j,hj,rfl⟩ := (wordDepartures_mem_iff x z w).mp hz
      exact (not_le_of_gt (had.2.2.2.1 j hj)) hzt
    · obtain ⟨j,hj,rfl⟩ := (wordDepartures_mem_iff y z v).mp hz
      have hs := had.2.2.2.2.1 j hj
      rw [← had.2.2.1] at hs
      exact (not_le_of_gt hs) hzt
  have hBT : B ∩ NoDrop ℓ b ⊆ Stay T := by
    intro X hX j
    change dot (realPosition a) ℓ ≤ dot (realPosition (X j)) ℓ
    rw [had.2.2.1]
    exact hX.2 j
  have hm := ((hA.prod hB).preimage (measurable_commonPairSuffix w.length v.length)).inter
    (measurableSet_commonWordEvent ℓ x y w v)
  rw [sharedConditionedPairLaw, Measure.smul_apply, Measure.restrict_apply hm,
    common_word_suffix_event ℓ x y w v had A B,
    shared_pair_word_suffix ν x y w v T (by change dot (realPosition a) ℓ ≤ dot (realPosition a) ℓ; exact le_rfl) hb hdis
      (A ∩ NoDrop ℓ a) (B ∩ NoDrop ℓ b)
      (hA.inter (measurableSet_noDrop ℓ a)) (hB.inter (measurableSet_noDrop ℓ b))
      (fun _ h => h.2) hBT]
  rw [sharedConditionedPairLaw, Measure.smul_apply, Measure.restrict_apply (hA.prod hB)]
  have he : (A ×ˢ B) ∩ (NoDrop ℓ a ×ˢ NoDrop ℓ b) =
      ((A ∩ NoDrop ℓ a) ×ˢ (B ∩ NoDrop ℓ b)) := by ext P; simp only [Set.mem_inter_iff,Set.mem_prod]; tauto
  rw [he]
  simp only [smul_eq_mul]
  have hfin := (sharedNoDropMass_le_one ν ℓ a b).trans_lt (by simp : (1 : ℝ≥0∞) < ⊤)
  simp only [mul_assoc]
  rw [← mul_assoc (sharedNoDropMass ν ℓ a b), ENNReal.mul_inv_cancel hpt hfin.ne, one_mul]

lemma ae_of_frestrict_probability_lower {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α]
    (μ : Measure (ℕ → α)) [IsFiniteMeasure μ] (E : Set (ℕ → α))
    (hE : MeasurableSet E) (p : ℝ≥0∞) (hp : 0 < p) (hpt : p ≠ ∞)
    (h : ∀ (n : ℕ) (f : (i : Finset.Iic n) → α),
      p * μ (Preorder.frestrictLe n ⁻¹' {f}) ≤
        μ (E ∩ (Preorder.frestrictLe n ⁻¹' {f}))) : ∀ᵐ X ∂μ, X ∈ E := by
  classical
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → α)) := Filtration.piLE
  have hsup : (⨆ n, ℱ n) = (inferInstance : MeasurableSpace (ℕ → α)) := by
    apply le_antisymm (iSup_le ℱ.le)
    change (⨆ n : ℕ, MeasurableSpace.comap (fun X : ℕ → α => X n) inferInstance) ≤ _
    apply iSup_le
    intro n
    apply le_trans _ (le_iSup _ n)
    change MeasurableSpace.comap (fun X : ℕ → α => X n) inferInstance ≤ Filtration.piLE n
    rw [Filtration.piLE_eq_comap_frestrictLe]
    have hm : @Measurable (ℕ → α) α
        (MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance) _ (fun X => X n) :=
      (show Measurable (fun f : (i : Finset.Iic n) → α => f ⟨n, Finset.mem_Iic.mpr le_rfl⟩) from
        measurable_pi_apply _).comp (Measurable.of_comap_le le_rfl)
    exact hm.comap_le
  have hlow (n : ℕ) (S : Set (ℕ → α)) (hS : MeasurableSet[ℱ n] S) :
      p * μ S ≤ μ (E ∩ S) := by
    change MeasurableSet[Filtration.piLE n] S at hS
    rw [Filtration.piLE_eq_comap_frestrictLe] at hS
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hS
    have hsum (A : Set (ℕ → α)) :
        (μ.restrict A) (Preorder.frestrictLe n ⁻¹' B) =
          ∑' f : B, (μ.restrict A) (Preorder.frestrictLe n ⁻¹' {f.1}) :=
      (tsum_measure_preimage_singleton (μ := μ.restrict A) B.to_countable
        (fun f _ => (Preorder.measurable_frestrictLe n) (measurableSet_singleton f))).symm
    have hpre : MeasurableSet (Preorder.frestrictLe n ⁻¹' B) :=
      (Preorder.measurable_frestrictLe (X := fun _ : ℕ => α) n) hB
    have hp0 := hsum Set.univ
    simp only [Measure.restrict_univ] at hp0
    rw [hp0, ← ENNReal.tsum_mul_left]
    have hpE := hsum E
    rw [Measure.restrict_apply hpre, Set.inter_comm] at hpE
    rw [hpE]
    apply ENNReal.tsum_le_tsum
    intro f
    rw [Measure.restrict_apply ((Preorder.measurable_frestrictLe n)
      (measurableSet_singleton f.1)), Set.inter_comm]
    exact h n f.1
  let g : (ℕ → α) → ℝ := E.indicator (fun _ => 1)
  have hg : Integrable g μ := (integrable_const (1 : ℝ)).indicator hE
  have hlo (n : ℕ) : ∀ᵐ X ∂μ, p.toReal ≤ μ[g | ℱ n] X := by
    apply ae_of_ae_trim (ℱ.le n)
    apply ae_le_of_forall_setIntegral_le (integrable_const p.toReal)
      (integrable_condExp.trim (ℱ.le n) stronglyMeasurable_condExp)
    intro S hS _
    rw [← setIntegral_trim (ℱ.le n) stronglyMeasurable_const hS,
      ← setIntegral_trim (ℱ.le n) stronglyMeasurable_condExp hS,
      setIntegral_condExp (ℱ.le n) hg hS]
    have hreal := ENNReal.toReal_mono (measure_ne_top μ _) (hlow n S hS)
    rw [ENNReal.toReal_mul] at hreal
    simpa only [g, setIntegral_indicator hE, setIntegral_const, smul_eq_mul,
      mul_one, one_mul, Measure.real, Set.inter_comm E S, mul_comm] using hreal
  have hgmeas : StronglyMeasurable[⨆ n, ℱ n] g := by
    rw [hsup]
    exact stronglyMeasurable_const.indicator hE
  have hlim := hg.tendsto_ae_condExp (ℱ := ℱ) hgmeas
  filter_upwards [ae_all_iff.mpr hlo, hlim] with X hX hlimX
  have hge : p.toReal ≤ g X := ge_of_tendsto hlimX (Eventually.of_forall hX)
  by_contra hnot
  rw [show g X = 0 from Set.indicator_of_notMem hnot _] at hge
  exact (not_le_of_gt (ENNReal.toReal_pos hp.ne' hpt)) hge

end DirectionalTransience
end
end

end OAI
