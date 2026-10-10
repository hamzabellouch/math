import Mathlib
import OAI.Probability.IsingPerceptron.NextRowJoin

namespace OAI

/-! Contact Faces. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma enrichedContactObjective_faces {N n : ℕ} (hN : 0 < N)
    (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ) (hz0 : ζ 0=0) (hz1 : ζ (Fin.last (n+1))=1)
    (q : OverlapPath) (v : Fin (n+1) → ℝ) (hq : finiteStepFunction ζ v =ᵐ[pathMeasure] q.val)
    (hv : ∀ i, v i ≤ 1) {f : ℝ → ℝ} (F : BoundedC2Data f) (S H V : ℝ) (α : ℝ≥0)
    (hS : isingEntropy q ≤ (S:EReal))
    (hH : 1 < (chainWeight ζ (Fin.last n)*(1-v (Fin.last n))/2)*H-
      (∫ z : ℝ, |z| ∂gaussianReal 0 1)*Real.sqrt H-
      (∑ i : Fin n, Real.log 2/chainExponent ζ i)-(α:ℝ)*F.K-(α:ℝ)*|V|+S)
    (p : ContactParameter n N) (hp : p∈contactRegion n N (α*(N:ℝ≥0)) H)
    {ε : ℝ} (_hε : 0 < ε) (hc : 8*(perturbationScale N)^2 < ε)
    (hj : enrichedContactObjective gaussianCoordinates n (chainExponent ζ) (spinLaw N)
      (gaussianRowActivation f) (fun i => chainWeight ζ i*v i) S V p < -ε) :
    0 < p.1 ∧ (∑ i, p.2.1 i) < H := by
  have hh := contactRegion_nonneg hp
  have hu : ∀ j, |p.2.2 j| ≤ 2 := fun j => abs_le.mpr ⟨by linarith [(hh.2.2.2.2 j).1],(hh.2.2.2.2 j).2⟩
  constructor
  · by_contra hr
    have hr' : p.1=0 := le_antisymm (le_of_not_gt hr) bot_le
    have Hb := enrichedContactObjective_initial_lower hN ζ hz hz0 hz1 q v hq hS p.2.1 hh.2.2.1
      p.2.2 hu V gaussianCoordinates (measurable_gaussianRowActivation F.mf)
      ((abs_nonneg (f 0)).trans (F.bf 0)) (fun _ _ => F.bf _)
    have he : p=(0,p.2.1,p.2.2) := by ext <;> simp [hr']
    rw [← he] at Hb
    linarith
  · by_contra hcap
    have he : ∑ i, p.2.1 i=H := le_antisymm hh.2.2.2.1 (le_of_not_gt hcap)
    have hr : (p.1:ℝ) ≤ (α:ℝ)*N := by exact_mod_cast hh.2.1
    have Hb := enrichedContactObjective_cap_lower hN ζ hz hz0 hz1 v hv p.2.1 hh.2.2.1 p.2.2 hu
      α.coe_nonneg p.1 hr S V gaussianCoordinates (measurable_gaussianRowActivation F.mf)
      ((abs_nonneg (f 0)).trans (F.bf 0)) (fun _ _ => F.bf _)
    rw [he] at Hb
    change _ ≤ enrichedContactObjective gaussianCoordinates n (chainExponent ζ) (spinLaw N)
      (gaussianRowActivation f) (fun i => chainWeight ζ i*v i) S V p at Hb
    linarith

lemma contact_small_cost {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 8*(perturbationScale N)^2 < ε := by
  have ht : Tendsto (fun N => 8*(perturbationScale N)^2) atTop (𝓝 (0:ℝ)) := by
    simpa using (tendsto_const_nhds.mul (perturbationScale_tendsto.pow 2) :
      Tendsto (fun N => (8:ℝ)*(perturbationScale N)^2) atTop (𝓝 (8*(0:ℝ)^2)))
  exact ht.eventually (gt_mem_nhds hε)

 

theorem enriched_contact_eventually_lower {n : ℕ}
    (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ) (hz0 : ζ 0=0) (hz1 : ζ (Fin.last (n+1))=1)
    (q : OverlapPath) (v : Fin (n+1) → ℝ) (hq : finiteStepFunction ζ v =ᵐ[pathMeasure] q.val)
    (hv : ∀ i, v i ≤ 1) {f : ℝ → ℝ} (F : BoundedC2Data f) (S H : ℝ) (α : ℝ≥0)
    (hS : isingEntropy q ≤ (S:EReal)) {δ : ℝ} (hδ : 0 < δ) (hH0 : 0 ≤ H)
    (hH : 1 < (chainWeight ζ (Fin.last n)*(1-v (Fin.last n))/2)*H-
      (∫ z : ℝ, |z| ∂gaussianReal 0 1)*Real.sqrt H-
      (∑ i : Fin n, Real.log 2/chainExponent ζ i)-(α:ℝ)*F.K-(α:ℝ)*|patternFunctional f q+δ|+S)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p∈contactRegion n N (α*(N:ℝ≥0)) H,
      -ε ≤ enrichedContactObjective gaussianCoordinates n (chainExponent ζ) (spinLaw N)
        (gaussianRowActivation f) (fun i => chainWeight ζ i*v i) S (patternFunctional f q+δ) p := by
  classical
  by_contra hfail
  obtain ⟨M,hM⟩ := eventually_atTop.mp (contact_small_cost hε)
  rw [eventually_atTop] at hfail
  push Not at hfail
  have hex (k : ℕ) : ∃ N : ℕ, max M (k+1) ≤ N ∧ ∃ p∈contactRegion n N (α*(N:ℝ≥0)) H,
      enrichedContactObjective gaussianCoordinates n (chainExponent ζ) (spinLaw N)
        (gaussianRowActivation f) (fun i => chainWeight ζ i*v i) S (patternFunctional f q+δ) p < -ε := by
    exact hfail (max M (k+1))
  choose N hNk x hx hbad using hex
  have hN k : 0 < N k := lt_of_lt_of_le (by omega : 0 < k+1) ((le_max_right _ _).trans (hNk k))
  have hlim : Tendsto N atTop atTop := tendsto_atTop_mono
    (fun k => (show k ≤ k+1 by omega).trans ((le_max_right _ _).trans (hNk k))) tendsto_id
  have hmins k := enrichedContactObjective_exists_minimum (hN k) n (chainExponent ζ)
    (chainExponent_admissible hz hz0 hz1) (spinLaw (N k)) gaussianCoordinates
    (measurable_gaussianRowActivation F.mf) ((abs_nonneg (f 0)).trans (F.bf 0)) (fun _ _ => F.bf _)
    (α*(N k:ℝ≥0)) hH0 (fun i => chainWeight ζ i*v i) S (patternFunctional f q+δ)
  choose p hp hmin using hmins
  have hfaces k := enrichedContactObjective_faces (hN k) ζ hz hz0 hz1 q v hq hv F S H
    (patternFunctional f q+δ) α hS hH (p k) (hp k) hε
    (hM (N k) ((le_max_left _ _).trans (hNk k))) ((hmin k (hx k)).trans_lt (hbad k))
  exact no_interior_contact_sequence N hN hlim n ζ hz hz0 hz1 q v hq F S H α hδ p hp
    (fun k => (hfaces k).2) (fun k => (hfaces k).1) hmin

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma finiteFieldPath_zero {n : ℕ} : finiteFieldPath (n := n) (fun _ => 0)=fun _ => 0 := by
  ext i
  simp [finiteFieldPath]

 

theorem enriched_step_upper_tolerance {n : ℕ}
    (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ) (hz0 : ζ 0=0) (hz1 : ζ (Fin.last (n+1))=1)
    (q : OverlapPath) (v : Fin (n+1) → ℝ) (hq : finiteStepFunction ζ v =ᵐ[pathMeasure] q.val)
    (hv : ∀ i, v i ≤ 1) (hvlast : v (Fin.last n) < 1)
    {f : ℝ → ℝ} (F : BoundedC2Data f) (S : ℝ) (α : ℝ≥0)
    (hS : isingEntropy q ≤ (S:EReal)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      enrichedMeanPressure gaussianCoordinates (α*(N:ℝ≥0)) n (chainExponent ζ) (fun _ => 0) 0
        (spinLaw N) (gaussianRowActivation f) ≤ S+(α:ℝ)*patternFunctional f q+ε := by
  let δ := ε/(4*((α:ℝ)+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδb : (α:ℝ)*δ ≤ ε/4 := by
    have ha : (α:ℝ) ≤ (α:ℝ)+1 := by linarith
    have he : ((α:ℝ)+1)*δ=ε/4 := by dsimp [δ]; field_simp
    have hh := mul_le_mul_of_nonneg_right ha hδ.le
    linarith
  obtain ⟨H,hH0,hH⟩ := contact_cap_exists ζ hz v hvlast (α:ℝ) F.K (patternFunctional f q+δ) S
  have he := enriched_contact_eventually_lower ζ hz hz0 hz1 q v hq hv F S H α hS hδ hH0.le hH
    (ε := ε/4) (by positivity)
  filter_upwards [he, contact_small_cost (ε := ε/4) (by positivity),eventually_gt_atTop 0] with N he hc hN
  let p : ContactParameter n N := (α*(N:ℝ≥0),fun _ => 0,fun _ => (3:ℝ)/2)
  have hp : p∈contactRegion n N (α*(N:ℝ≥0)) H := contactRegion_mem le_rfl (fun _ => le_rfl)
    (by simpa [p] using hH0.le) (fun _ => by norm_num)
  have hj := he p hp
  simp only [p,enrichedContactObjective,finiteFieldPath_zero,mul_zero,Finset.sum_const_zero,
    zero_div,sub_zero,sub_self,zero_pow (by norm_num : (2:ℕ)≠0),add_zero] at hj
  have hr : ((α*(N:ℝ≥0):ℝ≥0):ℝ)/(N:ℝ)=(α:ℝ) := by
    simp only [NNReal.coe_mul, NNReal.coe_natCast]
    exact mul_div_cancel_right₀ _ (by exact_mod_cast hN.ne')
  rw [hr] at hj
  have hu := enrichedMeanPressure_zero_perturbation_cost hN n (chainExponent ζ)
    (chainExponent_admissible hz hz0 hz1) monotone_const (le_refl (0:ℝ))
    (fun _ => (3:ℝ)/2) (fun _ => by norm_num) (spinLaw N) gaussianCoordinates
    (measurable_gaussianRowActivation F.mf) ((abs_nonneg (f 0)).trans (F.bf 0)) (fun _ _ => F.bf _)
    (α*(N:ℝ≥0))
  linarith [(abs_le.mp hu).1]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma pathAmplitude_zero (i : ℕ) : pathAmplitude (fun _ => 0) i=0 := by
  cases i <;> simp [pathAmplitude,pathIncrement]

lemma enrichedCoefficients_zero {N : ℕ} (n : ℕ) (s : Spin N × LabeledLeaf n) :
    enrichedCoefficients n (fun _ => 0) 0 s=0 := by
  classical
  unfold enrichedCoefficients
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,Pi.zero_apply,mul_zero,zero_smul,
    tagCoefficients,Finsupp.mapDomain_zero,Finset.sum_const_zero,add_zero]
  suffices externalFieldCoefficients n (fun _ => 0) s=0 by rw [this,Finsupp.mapDomain_zero]
  simp [externalFieldCoefficients,treeFieldCoefficients,featureCoefficients,pathAmplitude_zero]

lemma enrichedCylinderPressure_zero {N : ℕ} {A : Type*} (n : ℕ)
    (ν : Measure (Spin N)) (φ : A → Spin N → ℝ) (p : EnrichedCylinderData n A) :
    enrichedCylinderPressure n (fun _ => 0) 0 ν φ p =
      finiteLogIntegral ν (patternBase φ (fun i : Fin p.1.1.1 => p.1.1.2 i))/N := by
  simp only [enrichedCylinderPressure,enrichedCoefficients_zero,cylinderField,Finsupp.sum_zero_index,
    add_zero,mul_zero,zero_div,sub_zero,labeledSpinReference,finiteLogIntegral]
  rw [integral_fun_fst (fun x => Real.exp (patternBase φ (fun i : Fin p.1.1.1 => p.1.1.2 i) x)), probReal_univ, one_smul]

 
def finiteRowPressure {N : ℕ} {A : Type*} (ν : Measure (Spin N))
    (φ : A → Spin N → ℝ) (m : ℕ) (y : ℕ → A) : ℝ :=
  finiteLogIntegral ν (patternBase φ (fun i : Fin m => y i))/N

lemma enrichedFixed_mean_zero {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (n : ℕ) (b : ℕ → ℝ)
    (ν : Measure (Spin N)) (φ : A → Spin N → ℝ) (m : ℕ) :
    (∫ z, enrichedCylinderPressure n (fun _ => 0) 0 ν φ (enrichedCountJoin (m,z)) ∂enrichedFixedLaw P n b) =
      ∫ y, finiteRowPressure ν φ m y ∂Measure.infinitePi (fun _ : ℕ => P) := by
  simp_rw [enrichedCylinderPressure_zero]
  change (∫ z, finiteRowPressure ν φ m z.1.1 ∂
    ((Measure.infinitePi (fun _ : ℕ => P)).prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)=_
  rw [integral_fun_fst (fun z : (ℕ → A) × LabeledTree n => finiteRowPressure ν φ m z.1), probReal_univ, one_smul,
    integral_fun_fst (finiteRowPressure ν φ m), probReal_univ, one_smul]

lemma enrichedMeanPressure_zero {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    enrichedMeanPressure P r n b (fun _ => 0) 0 ν φ =
      poissonMean (fun m => ∫ y, finiteRowPressure ν φ m y ∂Measure.infinitePi (fun _ : ℕ => P)) r := by
  rw [enrichedMeanPressure_eq_poissonMean hN n b hb (monotone_const) le_rfl 0
    (fun _ => by simp) ν P hm hK hφ r]
  simp_rw [enrichedFixed_mean_zero]

lemma spinLaw_singleton {N : ℕ} (x : Spin N) : (spinLaw N).real {x}=((2:ℝ)^N)⁻¹ := by
  rw [measureReal_def,spinLaw,Measure.pi_singleton]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply,Fintype.card_fin,Finset.prod_const,Finset.card_univ,
    ENNReal.toReal_pow,ENNReal.toReal_inv]
  simp [inv_pow]

lemma spinLaw_integral {N : ℕ} (F : Spin N → ℝ) :
    (∫ x, F x ∂spinLaw N)=(∑ x, F x)/(2:ℝ)^N := by
  rw [integral_fintype (Integrable.of_finite)]
  simp only [spinLaw_singleton,smul_eq_mul,Finset.mul_sum,div_eq_mul_inv,mul_comm]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma abs_nat_sequence_sub {a : ℕ → ℝ} {L : ℝ} (hstep : ∀ n, |a (n+1)-a n| ≤ L) (m n : ℕ) :
    |a m-a n| ≤ L*|(m:ℝ)-n| := by
  have hle : ∀ m n : ℕ, m ≤ n → |a n-a m| ≤ L*((n:ℝ)-m) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      calc
        |a (n+1)-a m| ≤ |a (n+1)-a n|+|a n-a m| := abs_sub_le _ _ _
        _ ≤ L+L*((n:ℝ)-m) := add_le_add (hstep n) ih
        _ = L*(((n+1:ℕ):ℝ)-m) := by push_cast; ring
  rcases le_total m n with hmn | hnm
  · rw [abs_sub_comm (a m) (a n),abs_sub_comm (m:ℝ) (n:ℝ),abs_of_nonneg (sub_nonneg.mpr (show (m:ℝ) ≤ n by exact_mod_cast hmn))]
    exact hle m n hmn
  · rw [abs_of_nonneg (sub_nonneg.mpr (show (n:ℝ) ≤ m by exact_mod_cast hnm))]
    exact hle n m hnm

lemma poisson_sequence_integrable {a : ℕ → ℝ} {L : ℝ} (_hL : 0 ≤ L)
    (hstep : ∀ n, |a (n+1)-a n| ≤ L) (r : ℝ≥0) : Integrable a (poissonMeasure r) := by
  have hg := (integrable_const (|a 0|)).add
    (((poisson_cast_memLp r).integrable (by norm_num)).const_mul L)
  apply hg.mono' (Measurable.of_discrete.aestronglyMeasurable)
  apply Eventually.of_forall
  intro n
  have hh := abs_nat_sequence_sub hstep n 0
  simp only [Nat.cast_zero,sub_zero,abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n)] at hh
  change |a n| ≤ |a 0|+L*n
  exact (abs_le.mpr (by
    constructor <;> linarith [(abs_le.mp hh).1,(abs_le.mp hh).2,neg_abs_le (a 0),le_abs_self (a 0)]) : |a n| ≤ |a 0|+L*n)

lemma poisson_coupling_bound {a : ℕ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hstep : ∀ n, |a (n+1)-a n| ≤ L) (r : ℝ≥0) :
    |poissonMean a r-a ⌊(r:ℝ)⌋₊| ≤ L*(Real.sqrt r+1) := by
  have hi := poisson_sequence_integrable hL hstep r
  have hm := (poisson_cast_memLp r).integrable (by norm_num)
  have hc : Integrable (fun m : ℕ => |(m:ℝ)-(r:ℝ)|) (poissonMeasure r) :=
    (hm.sub (integrable_const (r:ℝ))).abs
  have hvar := l1_center_le_sqrt_variance (poisson_cast_memLp r)
  rw [poisson_cast_variance,poisson_cast_mean] at hvar
  have hfloor : |(r:ℝ)-(⌊(r:ℝ)⌋₊:ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Nat.floor_le r.coe_nonneg))]
    linarith [Nat.lt_floor_add_one (r:ℝ)]
  have hb (m : ℕ) : |a m-a ⌊(r:ℝ)⌋₊| ≤ L*(|(m:ℝ)-(r:ℝ)|+1) := by
    refine (abs_nat_sequence_sub hstep m ⌊(r:ℝ)⌋₊).trans ?_
    apply mul_le_mul_of_nonneg_left _ hL
    exact (abs_sub_le (m:ℝ) r (⌊(r:ℝ)⌋₊:ℝ)).trans (by linarith)
  rw [poissonMean_eq_integral]
  have he : (∫ m, a m-a ⌊(r:ℝ)⌋₊ ∂poissonMeasure r)=(∫ m, a m ∂poissonMeasure r)-a ⌊(r:ℝ)⌋₊ := by
    rw [integral_sub hi (integrable_const _),integral_const,probReal_univ,one_smul]
  rw [← he,← Real.norm_eq_abs]
  calc
    _ ≤ ∫ m, |a m-a ⌊(r:ℝ)⌋₊| ∂poissonMeasure r := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun m => a m-a ⌊(r:ℝ)⌋₊)
    _ ≤ ∫ m, L*(|(m:ℝ)-(r:ℝ)|+1) ∂poissonMeasure r := integral_mono
      (hi.sub (integrable_const _)).abs ((hc.add (integrable_const 1)).const_mul L) hb
    _ = L*((∫ m, |(m:ℝ)-(r:ℝ)| ∂poissonMeasure r)+1) := by
      rw [integral_const_mul,integral_add hc (integrable_const 1),integral_const,probReal_univ,one_smul]
    _ ≤ L*(Real.sqrt r+1) := mul_le_mul_of_nonneg_left (by linarith) hL

lemma finiteRowPressure_mean_step {N : ℕ} (hN : 0 < N)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (m : ℕ) :
    |(∫ y, finiteRowPressure ν φ (m+1) y ∂Measure.infinitePi (fun _ : ℕ => P))-
      (∫ y, finiteRowPressure ν φ m y ∂Measure.infinitePi (fun _ : ℕ => P))| ≤ K/N := by
  have hb : CascadeExponents 0 (fun _ => 0) := by
    constructor
    · intro i hi; omega
    · intro i hi; omega
  have H := enrichedFixed_mean_step_bound hN 0 (fun _ => 0) hb monotone_const
    (le_refl (0:ℝ)) 0 (fun _ => by simp) ν P hm hK hφ m
  rw [enrichedFixed_mean_zero P 0 (fun _ => 0) ν φ (m+1),
    enrichedFixed_mean_zero P 0 (fun _ => 0) ν φ m] at H
  exact H

lemma poisson_error_tendsto (α : ℝ≥0) (K : ℝ) :
    Tendsto (fun N : ℕ => (K/N)*(Real.sqrt ((α:ℝ)*N)+1)) atTop (𝓝 0) := by
  have ht := ((tendsto_nat_rpow_neg (c := 1/2) (by norm_num)).const_mul (K*Real.sqrt α)).add
    ((tendsto_nat_rpow_neg (c := 1) (by norm_num)).const_mul K)
  apply Tendsto.congr' _ (show Tendsto _ _ (𝓝 (0:ℝ)) from by simpa using ht)
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have he : (N:ℝ)^(-(1/2:ℝ))=Real.sqrt N/N := by
    calc
      _ = (N:ℝ)^((1/2:ℝ)-1) := by congr 1; norm_num
      _ = (N:ℝ)^(1/2:ℝ)/(N:ℝ)^(1:ℝ) := Real.rpow_sub hn _ _
      _ = _ := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
  simp only [one_div] at he
  rw [he,Real.rpow_neg_one,Real.sqrt_mul α.coe_nonneg]
  ring

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def expectedPressure (α : ℝ) (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∫ g, pressure α f N g ∂gaussianPatterns (patternCount α N) N

lemma gaussian_matrix_preserving (M N : ℕ) :
    MeasurePreserving (fun y : ℕ → ℕ → ℝ => fun p : Fin M × Fin N => y p.1 p.2)
      (Measure.infinitePi (fun _ : ℕ => gaussianCoordinates)) (gaussianPatterns M N) := by
  have h₁ := infinite_prefix_preserving gaussianCoordinates M
  have h₂ := measurePreserving_pi (fun _ : Fin M => gaussianCoordinates)
    (fun _ : Fin M => Measure.pi (fun _ : Fin N => gaussianReal 0 1))
    (fun _ => gaussian_prefix_measurePreserving N)
  have h₃ : MeasurePreserving (MeasurableEquiv.curry (Fin M) (Fin N) ℝ).symm
      (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin N => gaussianReal 0 1)))
      (gaussianPatterns M N) := by
    refine ⟨(MeasurableEquiv.curry _ _ _).symm.measurable,?_⟩
    simpa only [Measure.infinitePi_eq_pi,gaussianPatterns] using
      Measure.infinitePi_map_curry_symm (fun _ : Fin M => fun _ : Fin N => gaussianReal 0 1)
  exact h₃.comp (h₂.comp h₁)

lemma finiteRowPressure_gaussian {N : ℕ} (α : ℝ) (f : ℝ → ℝ) (y : ℕ → ℕ → ℝ) :
    finiteRowPressure (spinLaw N) (gaussianRowActivation f) (patternCount α N) y =
      pressure α f N (fun p => y p.1 p.2) := by
  unfold finiteRowPressure finiteLogIntegral pressure partitionFunction
  rw [spinLaw_integral]
  congr 3
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  unfold patternBase gaussianRowActivation projection
  simp_rw [cylinderField_spinRow]

lemma measurable_pressure (α : ℝ) {f : ℝ → ℝ} (hf : Measurable f) (N : ℕ) :
    Measurable (pressure α f N) := by
  unfold pressure partitionFunction
  apply Measurable.div_const
  apply Measurable.log
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro x _
  apply Measurable.exp
  apply Finset.measurable_sum
  intro a _
  apply hf.comp
  unfold projection
  fun_prop

lemma finiteRowPressure_mean_gaussian (α : ℝ) {f : ℝ → ℝ} (hf : Measurable f) (N : ℕ) :
    (∫ y, finiteRowPressure (spinLaw N) (gaussianRowActivation f) (patternCount α N) y
      ∂Measure.infinitePi (fun _ : ℕ => gaussianCoordinates)) = expectedPressure α f N := by
  simp_rw [finiteRowPressure_gaussian]
  exact (gaussian_matrix_preserving (patternCount α N) N).hasLaw.integral_comp
    (measurable_pressure α hf N).aestronglyMeasurable

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 

theorem gaussian_step_upper_tolerance {n : ℕ}
    (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ) (hz0 : ζ 0=0) (hz1 : ζ (Fin.last (n+1))=1)
    (q : OverlapPath) (v : Fin (n+1) → ℝ) (hq : finiteStepFunction ζ v =ᵐ[pathMeasure] q.val)
    (hv : ∀ i, v i ≤ 1) (hvlast : v (Fin.last n) < 1)
    {f : ℝ → ℝ} (F : BoundedC2Data f) (S : ℝ) (α : ℝ≥0)
    (hS : isingEntropy q ≤ (S:EReal)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, expectedPressure α f N ≤ S+(α:ℝ)*patternFunctional f q+ε := by
  have he := enriched_step_upper_tolerance ζ hz hz0 hz1 q v hq hv hvlast F S α hS
    (ε := ε/2) (by positivity)
  have hp := (poisson_error_tendsto α F.K).eventually (gt_mem_nhds (by positivity : (0:ℝ)<ε/2))
  have hK := (abs_nonneg (f 0)).trans (F.bf 0)
  filter_upwards [he,hp,eventually_gt_atTop 0] with N he hp hN
  rw [enrichedMeanPressure_zero hN n (chainExponent ζ) (chainExponent_admissible hz hz0 hz1)
    (spinLaw N) gaussianCoordinates (measurable_gaussianRowActivation F.mf) hK (fun _ _ => F.bf _)] at he
  have hc := poisson_coupling_bound
    (a := fun m => ∫ y, finiteRowPressure (spinLaw N) (gaussianRowActivation f) m y
      ∂Measure.infinitePi (fun _ : ℕ => gaussianCoordinates)) (by positivity : 0≤F.K/(N:ℝ))
    (finiteRowPressure_mean_step hN (spinLaw N) gaussianCoordinates
      (measurable_gaussianRowActivation F.mf) hK (fun _ _ => F.bf _)) (α*(N:ℝ≥0))
  have hfloor : ⌊((α*(N:ℝ≥0):ℝ≥0):ℝ)⌋₊=patternCount α N := rfl
  rw [hfloor,finiteRowPressure_mean_gaussian (α:ℝ) F.mf N] at hc
  simp only [NNReal.coe_mul,NNReal.coe_natCast] at hc he
  linarith [(abs_le.mp hc).1]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def uniformCut (n : ℕ) (i : Fin (n+2)) : ℝ := (i.val:ℝ)/(n+1:ℕ)

lemma uniformCut_strict (n : ℕ) : StrictMono (uniformCut n) := by
  intro i j hij
  apply (div_lt_div_iff_of_pos_right (by positivity : (0:ℝ)<(n+1:ℕ))).mpr
  exact_mod_cast hij

lemma uniformCut_zero (n : ℕ) : uniformCut n 0=0 := by simp [uniformCut]
lemma uniformCut_last (n : ℕ) : uniformCut n (Fin.last (n+1))=1 := by
  change ((n+1:ℕ):ℝ)/((n+1:ℕ):ℝ)=1
  exact div_self (by positivity)

def lowerGrid (p : ℝ → ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (1-1/(n+1:ℕ))*p ((⌊(n+1:ℕ)*u⌋₊:ℝ)/(n+1:ℕ))

lemma lowerGrid_factor_nonneg (n : ℕ) : 0≤(1-1/(n+1:ℕ):ℝ) := by
  have h : (1:ℝ)≤(n+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have := (div_le_one (by positivity : (0:ℝ)<(n+1:ℕ))).mpr h
  linarith

lemma lowerGrid_monotone {p : ℝ → ℝ} (hp : Monotone p) (n : ℕ) : Monotone (lowerGrid p n) := by
  intro u v huv
  apply mul_le_mul_of_nonneg_left _ (lowerGrid_factor_nonneg n)
  apply hp
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.floor_mono (mul_le_mul_of_nonneg_left huv (by positivity : (0:ℝ)≤(n+1:ℕ)))

lemma lowerGrid_mem {p : ℝ → ℝ} (hb : ∀ u, p u∈Icc (0:ℝ) 1) (n : ℕ) (u : ℝ) :
    lowerGrid p n u∈Icc (0:ℝ) 1 := by
  rcases hb ((⌊(n+1:ℕ)*u⌋₊:ℝ)/(n+1:ℕ)) with ⟨h0,h1⟩
  have hf := lowerGrid_factor_nonneg n
  dsimp only [lowerGrid]
  constructor
  · positivity
  · nlinarith [show (0:ℝ)≤1/(n+1:ℕ) by positivity]

lemma lowerGrid_le {p : ℝ → ℝ} (hp : Monotone p) (hb : ∀ u, p u∈Icc (0:ℝ) 1)
    (n : ℕ) {u : ℝ} (hu : 0≤u) : lowerGrid p n u ≤ p u := by
  have hf : (⌊(n+1:ℕ)*u⌋₊:ℝ)/(n+1:ℕ)≤u :=
    (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using Nat.floor_le (mul_nonneg (by positivity) hu))
  have hv := hp hf
  have hb' := (hb ((⌊(n+1:ℕ)*u⌋₊:ℝ)/(n+1:ℕ))).1
  dsimp only [lowerGrid]
  nlinarith [show (0:ℝ)≤1/(n+1:ℕ) by positivity]

lemma uniformCell_ae (n : ℕ) : ∀ᵐ u ∂pathMeasure,
    ∃ i : Fin (n+1), uniformCut n i.castSucc<u ∧ u<uniformCut n i.succ := by
  have hn : ∀ᵐ u ∂pathMeasure, ∀ i : Fin (n+2), u≠uniformCut n i := by
    apply (ae_all_iff).mpr
    intro i
    exact ae_restrict_of_ae (volume.ae_ne _)
  filter_upwards [ae_restrict_mem measurableSet_Ioo,hn] with u hu hn
  let j := ⌊(n+1:ℕ)*u⌋₊
  have hj : j<n+1 := by
    change ⌊(n+1:ℕ)*u⌋₊<n+1
    rw [Nat.floor_lt (mul_nonneg (by positivity) hu.1.le)]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hu.2 (by positivity : (0:ℝ)<(n+1:ℕ))
  let i : Fin (n+1) := ⟨j,hj⟩
  refine ⟨i,?_,?_⟩
  · have hle : uniformCut n i.castSucc≤u := by
      unfold uniformCut
      apply (div_le_iff₀ (by positivity)).mpr
      simpa only [i,j,Fin.val_castSucc,mul_comm] using Nat.floor_le (mul_nonneg (by positivity) hu.1.le)
    exact lt_of_le_of_ne hle (Ne.symm (hn i.castSucc))
  · unfold uniformCut
    apply (lt_div_iff₀ (by positivity)).mpr
    simpa only [i,j,Fin.val_succ,Nat.cast_add,Nat.cast_one,mul_comm] using Nat.lt_floor_add_one ((n+1:ℕ)*u)

lemma floor_on_uniformCell (n : ℕ) (i : Fin (n+1)) {u : ℝ}
    (hu : uniformCut n i.castSucc<u ∧ u<uniformCut n i.succ) : ⌊(n+1:ℕ)*u⌋₊=i.val := by
  have hleft : (i.val:ℝ)<(n+1:ℕ)*u := by
    have := (div_lt_iff₀ (by positivity : (0:ℝ)<(n+1:ℕ))).mp hu.1
    simpa [uniformCut,mul_comm] using this
  apply (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg i.val) hleft.le)).mpr
  constructor
  · exact hleft.le
  · have := (lt_div_iff₀ (by positivity)).mp hu.2
    simpa [uniformCut,mul_comm] using this

lemma lowerGrid_step_ae (p : ℝ → ℝ) (n : ℕ) :
    lowerGrid p n =ᵐ[pathMeasure] finiteStepFunction (uniformCut n)
      (fun i : Fin (n+1) => (1-1/(n+1:ℕ))*p ((i.val:ℝ)/(n+1:ℕ))) := by
  filter_upwards [uniformCell_ae n] with u hu
  obtain ⟨i,hi⟩ := hu
  rw [finiteStepFunction_on_cell (uniformCut_strict n) _ hi]
  simp only [lowerGrid,floor_on_uniformCell n i hi]

lemma lowerGrid_ae_tendsto {p : ℝ → ℝ} (hp : Monotone p) :
    ∀ᵐ u ∂pathMeasure, Tendsto (fun n => lowerGrid p n u) atTop (𝓝 (p u)) := by
  have hc : ∀ᵐ u ∂pathMeasure, ContinuousAt p u := monotone_ae_continuous_unit hp
  filter_upwards [hc,ae_restrict_mem measurableSet_Ioo] with u hc hu
  have hf := (tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hl := hc.tendsto.comp (uniformCell_left_tendsto ⟨hu.1.le,hu.2⟩)
  simpa only [lowerGrid,uniformCellIndex_eq_floor _ ⟨hu.1.le,hu.2⟩,
    Nat.cast_add,Nat.cast_one,sub_zero,one_mul,Function.comp_apply] using hf.mul hl

lemma lowerGrid_integral_tendsto {p : ℝ → ℝ} (hp : Monotone p)
    (hb : ∀ u, p u∈Icc (0:ℝ) 1) :
    Tendsto (fun n => ∫ u, lowerGrid p n u ∂pathMeasure) atTop (𝓝 (∫ u, p u ∂pathMeasure)) := by
  let : IsFiniteMeasure pathMeasure := inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) 1)))
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro n
    exact (lowerGrid_monotone hp n).measurable.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ (fun u => by rw [Real.norm_eq_abs,abs_of_nonneg (lowerGrid_mem hb n u).1]; exact (lowerGrid_mem hb n u).2)
  · exact lowerGrid_ae_tendsto hp

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma stepFunction_nonneg (h : FieldStep) (u : ℝ) : 0 ≤ stepFunction h u := by
  apply Finset.sum_nonneg
  intro i _
  split
  · exact h.nonneg i
  · exact le_rfl

lemma stepFunction_bound (h : FieldStep) (u : ℝ) :
    |stepFunction h u|≤∑ i, h.value i := by
  rw [abs_of_nonneg (stepFunction_nonneg h u)]
  apply Finset.sum_le_sum
  intro i _
  split
  · exact le_rfl
  · exact h.nonneg i

lemma measurable_stepFunction (h : FieldStep) : Measurable (stepFunction h) :=
  measurable_finiteStepFunction h.partition.cut h.value

lemma overlapPath_bound (q : OverlapPath) : ∀ᵐ u ∂pathMeasure, q.val u∈Icc (0:ℝ) 1 := by
  obtain ⟨p,hp,_,hb⟩ := overlapPath_representative q
  filter_upwards [hp] with u hu
  rw [← hu]
  exact hb u

lemma stepFunction_mul_path_integrable (h : FieldStep) (q : OverlapPath) :
    Integrable (fun u => stepFunction h u*q.val u) pathMeasure := by
  let : IsFiniteMeasure pathMeasure := inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) 1)))
  apply Integrable.of_bound ((measurable_stepFunction h).aestronglyMeasurable.mul q.val.aestronglyMeasurable)
    (∑ i, h.value i)
  filter_upwards [overlapPath_bound q] with u hu
  change ‖stepFunction h u*q.val u‖≤_
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hu.1]
  exact (mul_le_mul_of_nonneg_left hu.2 (abs_nonneg _)).trans (by simpa using stepFunction_bound h u)

 
theorem isingEntropy_mono (p q : OverlapPath) (hle : p.val≤ᵐ[pathMeasure] q.val) :
    isingEntropy p ≤ isingEntropy q := by
  apply iSup_mono
  intro h
  apply EReal.coe_le_coe_iff.mpr
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply integral_mono_ae (stepFunction_mul_path_integrable h p) (stepFunction_mul_path_integrable h q)
  filter_upwards [hle] with u hu
  exact mul_le_mul_of_nonneg_left hu (stepFunction_nonneg h u)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussianFamilyFold_KX {I : Set ℝ} (hI : IsOpen I) (F : GaussianFamily I)
    (L : List (AffineGaussianStep I)) : (gaussianFamilyFold hI F L).KX=F.KX := by
  induction L with
  | nil => rfl
  | cons s L ih => exact ih

lemma VariationCertificate.time_bound {I : Set ℝ} {F : GaussianFamily I} {n : ℕ} {e : ℝ}
    {w : Fin n → ℝ} (V : VariationCertificate F n 0 e w)
    {p : ℝ × ℝ} (hp : p.1 ∈ I) : |F.T p| ≤ F.KX^2/2 * ∑ i, |w i| := by
  have h := V.formula p hp
  simp only [zero_div,zero_mul,add_zero] at h
  rw [h,abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  calc
    _ ≤ (1/2:ℝ)*∑ i, |w i*V.c i p| := mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ (1/2:ℝ)*∑ i, |w i| *F.KX^2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (V.bound i p) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

lemma gaussianFold_lipschitz {I : Set ℝ} (hI : IsOpen I) (F : GaussianFamily I)
    (hT : ∀ p, F.T p=0) (L : List (AffineGaussianStep I))
    (hsum : (L.map AffineGaussianStep.v).sum=0) (hseg : Icc (0:ℝ) 1 ⊆ I) (x : ℝ) :
    |L.foldr (fun s U => gaussianTransform (s.a+s.v*1) s.d U) (fun y => F.U (1,y)) x-
      L.foldr (fun s U => gaussianTransform (s.a+s.v*0) s.d U) (fun y => F.U (0,y)) x| ≤
        F.KX^2/2*∑ i, |variationWeights L i| := by
  let G := gaussianFamilyFold hI F L
  have hb : boundarySlope L=0 := by rw [boundarySlope_eq_neg_sum,hsum,neg_zero]
  have V : VariationCertificate G L.length 0 (boundaryCoefficient L) (variationWeights L) := by
    rw [← hb]
    exact gaussianFoldCertificate hI F hT L
  have H := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (G.time_derivative x (hseg ht)).hasDerivWithinAt)
    (fun t (ht : t∈Ico (0:ℝ) 1) => show ‖G.T (t,x)‖ ≤ G.KX^2/2*∑ i, |variationWeights L i| from
      by rw [Real.norm_eq_abs]; exact V.time_bound (hseg ⟨ht.1,ht.2.le⟩))
  simpa only [Real.norm_eq_abs,G,gaussianFamilyFold_value,gaussianFamilyFold_KX] using H

end IsingPerceptron

end

end OAI
