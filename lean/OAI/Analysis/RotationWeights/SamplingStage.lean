import OAI.Analysis.RotationWeights.ReturnSamples

namespace OAI

noncomputable section

universe uτ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators

namespace CircleSampling
open Set Filter MeasureTheory ContinuousCircleWeight.Sampling
open scoped Topology

lemma exists_sampling_stage {τ : Type uτ} [Fintype τ]
    (O : τ → Set CircleX) (hO : ∀ t, IsOpen (O t)) (hne : ∀ t, (O t).Nonempty)
    {K : ℕ} (hK : 0 < K) {η : ℝ} (hη : 0 < η)
    (P : ℕ → Prop) (hP : ∀ᶠ m : ℕ in atTop, P m)
    {a b : ℝ} (hab : a < b) {p : ℕ} (hp : 0 < p) (M : ℕ → ℝ) :
    ∃ m : ℕ, P m ∧ 3 ≤ m ∧ ∃ S : τ → Finset ℤ,
      (∀ t, (S t).Nonempty) ∧
      (∀ t n, n∈S t → (m:ℝ)^((7:ℝ)/10*m)/2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ (m:ℝ)^((7:ℝ)/10*m)) ∧
      ∃ q : ℕ → ℕ, q 0=p ∧ (∀ i ≤ m, 0 < q i) ∧
        (∀ i < m, q i ∣ q (i+1) ∧ M m < (q (i+1):ℝ)/q i) ∧
        ∃ d e : ℝ, d < e ∧ Icc d e ⊆ Ioo a b ∧ ∀ θ∈Icc d e,
          (∀ i : Fin m, Int.fract ((q (i+1):ℝ)*θ) ∈ Ioo (1/((m:ℝ)*K)) (2/((m:ℝ)*K))) ∧
          (∀ k : ℤ, ((m:ℝ)*K)/4 ≤ |(k:ℝ)| → |(k:ℝ)| ≤ (m:ℝ)^((4:ℝ)/5*m) →
            (m:ℝ)/20 ≤ ((Finset.univ.filter fun i : Fin m =>
              Int.fract ((q (i+1):ℝ)*θ) ∉ phaseFailure ((m:ℝ)^(-(19:ℝ)/20)) k).card:ℝ)) ∧
          (∀ t n, n∈S t → n•(θ:CircleX)∈O t) ∧
          ∀ t (positive : Bool),
            (∫ x : CircleX, (idealAverage positive (scaleEll m) (scaleAlpha m)
              (fun n : S t => (n.val:ℝ)) (characterCurve (fun i : Fin m => (q (i+1):ℤ)) x)
              (fun i => Int.fract ((q (i+1):ℝ)*θ))-1)^2) < η := by
  classical
  obtain ⟨θ0,hθirr,hθa,hθb⟩ := exists_irrational_btwn hab
  have hs : ∀ᶠ m : ℕ in atTop, ∀ t, ∃ S : Finset ℤ,
      (m:ℝ)^((69:ℝ)/100*m) ≤ (S.card:ℝ) ∧
      (∀ n∈S, (m:ℝ)^((7:ℝ)/10*m)/2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ (m:ℝ)^((7:ℝ)/10*m) ∧ n•(θ0:CircleX)∈O t) ∧
      (∀ n∈S, ∀ n'∈S, n≠n' → ∀ v v' : ℤ, |v| ≤ m^300 → |v'| ≤ m^300 →
        (v≠0 ∨ v'≠0) → (m*K*m^1000:ℤ) < |v*n+v'*n'|) :=
    Filter.eventually_all.mpr (fun t => eventually_separated_returns hθirr (hO t) (hne t) K)
  obtain ⟨m,hmP,hm3,hmnum,hbudget,hps,hmS⟩ :=
    (hP.and ((eventually_ge_atTop (3:ℕ)).and ((eventually_IdealNumerics K).and
      ((eventually_trial_budget (Fintype.card (τ×Bool)) hη).and (eventually_phase_failure_small.and hs))))).exists
  have hm0 : 0 < m := by omega
  have hmR : 0 < (m:ℝ) := Nat.cast_pos.mpr hm0
  choose S hSc hSbounds hSsep using hmS
  have hSnon (t : τ) : (S t).Nonempty := by
    apply Finset.card_pos.mp
    have hh : (0:ℝ) < ((S t).card:ℝ) := (Real.rpow_pos_of_pos hmR _).trans_le (hSc t)
    exact_mod_cast hh
  let (t : τ) : Nonempty (S t) := (hSnon t).to_subtype
  have hcpos (t : τ) (n : S t) : (0:ℝ) < (n.val:ℝ) :=
    (div_pos (Real.rpow_pos_of_pos hmR _) (by norm_num)).trans_le (hSbounds t n n.property).1
  have hN2 : 2 < (m:ℝ)*K := by
    have hm3R : (3:ℝ) ≤ m := Nat.cast_le.mpr hm3
    have hKR : (1:ℝ) ≤ K := by exact_mod_cast (show (1:ℕ) ≤ K by omega)
    nlinarith
  have hN : 0 < (m:ℝ)*K := by linarith
  let R := (m:ℝ)^((4:ℝ)/5*m)
  have hR1 : 1 ≤ R := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by positivity)
  obtain ⟨g,hg,hgphase,hgcover,hgE⟩ := exists_ideal_trial (κ:=fun t : τ×Bool => S t.1)
    hK hmnum Prod.snd (fun t n => (n.val:ℝ))
    (fun t => by simpa using hSc t.1)
    (fun t n => (hSbounds t.1 n n.property).1)
    (by
      intro t n n' hnn v w hv hw hvw
      have hne' : n.val≠n'.val := fun he => hnn (Subtype.ext he)
      have hv' : |v| ≤ (m:ℤ)^300 := by simpa only [Nat.cast_pow] using hv
      have hw' : |w| ≤ (m:ℤ)^300 := by simpa only [Nat.cast_pow] using hw
      have hh := (hSsep t.1 n n.property n' n'.property hne' v w hv' hw' hvw).le
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_abs] using
        (Int.cast_le (R := ℝ)).mpr hh)
    hps (phaseRange ((m:ℝ)*K) R) (phaseRange_bound hR1)
    (fun _ hk => phaseRange_lower hk) hη hbudget
  have hg01 (i : Fin m) : g i∈Ioo 0 1 := by
    refine ⟨lt_trans (one_div_pos.mpr hN) (hg i).1,lt_trans (hg i).2 ?_⟩
    exact (div_lt_one hN).mpr hN2
  let γ : PhaseCube m := fun i => ⟨g i,(hg01 i).1.le,(hg01 i).2.le⟩
  have hγ : ∀ i, (γ i:ℝ)∈Ioo 0 1 := hg01
  have hcover : ∀ᶠ β : PhaseCube m in 𝓝 γ, ∀ k∈phaseRange ((m:ℝ)*K) R,
      (m:ℝ)/20 ≤ ((Finset.univ.filter fun i => (β i:ℝ)∉phaseFailure ((m:ℝ)^(-(19:ℝ)/20)) k).card:ℝ) := by
    have hneK (k : ℤ) (hk : k∈phaseRange ((m:ℝ)*K) R) : k≠0 := by
      intro he
      have hh := phaseRange_lower hk
      rw [he] at hh
      norm_num at hh
      linarith
    filter_upwards [phase_cover_eventually γ (phaseRange ((m:ℝ)*K) R) ((m:ℝ)^(-(19:ℝ)/20))
      (fun k hk i => hgphase k (hneK k hk) i)] with β hβ k hk
    exact (hgcover k hk).trans (Nat.cast_le.mpr (hβ k hk))
  have hinterval : ∀ᶠ β : PhaseCube m in 𝓝 γ, ∀ i, (β i:ℝ)∈Ioo (1/((m:ℝ)*K)) (2/((m:ℝ)*K)) :=
    cube_interval_eventually γ hg
  have horbit : ∀ᶠ θ : ℝ in 𝓝 θ0, ∀ t n, n∈S t → n•(θ:CircleX)∈O t := by
    apply Filter.eventually_all.mpr
    intro t
    apply (Filter.eventually_all_finite (S t).finite_toSet).mpr
    intro n hn
    exact (show ContinuousAt (fun θ : ℝ => n•(θ:CircleX)) θ0 by fun_prop).eventually
      ((hO t).mem_nhds (hSbounds t n hn).2.2)
  obtain ⟨a',b',hθint,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (Filter.inter_mem (Ioo_mem_nhds hθa hθb) horbit)
  obtain ⟨q,hq0,hqp,hqM,d,e,hde,hdeSub,hreal⟩ := realize_finite_sampling (κ:=fun t : τ×Bool => S t.1)
    Prod.snd (Real.rpow_pos_of_pos hmR _) (scaleAlpha_pos hm0) (fun t n => (n.val:ℝ)) γ hγ
    (fun t n i => hgphase n (by exact_mod_cast (hcpos t.1 n).ne') i) hgE
    (hinterval.and hcover) (lt_trans hθint.1 hθint.2) hp (M m)
  refine ⟨m,hmP,hm3,S,hSnon,(fun t n hn => ⟨(hSbounds t n hn).1,(hSbounds t n hn).2.1⟩),
    q,hq0,hqp,hqM,d,e,hde,?_,?_⟩
  · exact fun θ hθ => (hsub (hdeSub hθ)).1
  · intro θ hθ
    refine ⟨(hreal θ hθ).1.1,?_,(hsub (hdeSub hθ)).2,?_⟩
    · intro k hk hkR
      exact (hreal θ hθ).1.2 k (mem_phaseRange hk hkR)
    · intro t positive
      exact (hreal θ hθ).2 (t,positive)
end CircleSampling

open scoped BigOperators
namespace ContinuousCircleWeight

theorem exists_nonzero_low_product_coefficient (K : ℕ) (A B : Polynomial ℂ)
    (hA : A.coeff K ≠ 0) (hB : B.coeff K ≠ 0) :
    ∃ n ≤ 2 * K, (A * B).coeff n ≠ 0 := by
  have hA0 : A ≠ 0 := by contrapose! hA; simp [hA]
  have hB0 : B ≠ 0 := by contrapose! hB; simp [hB]
  refine ⟨(A * B).natTrailingDegree, ?_,
    Polynomial.coeff_natTrailingDegree_ne_zero.mpr (mul_ne_zero hA0 hB0)⟩
  rw [Polynomial.natTrailingDegree_mul hA0 hB0]
  have ha := Polynomial.natTrailingDegree_le_of_ne_zero hA
  have hb := Polynomial.natTrailingDegree_le_of_ne_zero hB
  omega

def shiftedPolynomial (K : ℕ) (a : Fin (2 * K + 1) → ℂ) : Polynomial ℂ :=
  ∑ i, Polynomial.monomial i.val (a i)

@[simp] theorem coeff_shiftedPolynomial (K : ℕ) (a : Fin (2 * K + 1) → ℂ)
    (i : Fin (2 * K + 1)) : (shiftedPolynomial K a).coeff i = a i := by
  classical
  simp only [shiftedPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  simp only [Fin.val_inj]
  simp

theorem continuous_coeff_shiftedPolynomial (K n : ℕ) :
    Continuous (fun a : Fin (2 * K + 1) → ℂ => (shiftedPolynomial K a).coeff n) := by
  classical
  simp only [shiftedPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  apply continuous_finsetSum
  intro i _
  split_ifs <;> fun_prop

abbrev CoefficientPair (K : ℕ) :=
  (Fin (2 * K + 1) → ℂ) × (Fin (2 * K + 1) → ℂ)

def lowProduct (K : ℕ) (a : CoefficientPair K) : Fin (2 * K + 1) → ℂ :=
  fun n => (shiftedPolynomial K a.1 * shiftedPolynomial K a.2).coeff n

theorem continuous_lowProduct (K : ℕ) : Continuous (lowProduct K) := by
  apply continuous_pi
  intro n
  simp only [lowProduct, Polynomial.coeff_mul]
  apply continuous_finsetSum
  intro x _
  exact ((continuous_coeff_shiftedPolynomial K x.1).comp continuous_fst).mul
    ((continuous_coeff_shiftedPolynomial K x.2).comp continuous_snd)

def centerIndex (K : ℕ) : Fin (2 * K + 1) := ⟨K, by omega⟩

theorem lowProduct_ne_zero (K : ℕ) (a : CoefficientPair K)
    (hA : a.1 (centerIndex K) ≠ 0) (hB : a.2 (centerIndex K) ≠ 0) :
    lowProduct K a ≠ 0 := by
  have hA' : (shiftedPolynomial K a.1).coeff K ≠ 0 := by
    change (shiftedPolynomial K a.1).coeff (centerIndex K) ≠ 0
    simpa only [coeff_shiftedPolynomial] using hA
  have hB' : (shiftedPolynomial K a.2).coeff K ≠ 0 := by
    change (shiftedPolynomial K a.2).coeff (centerIndex K) ≠ 0
    simpa only [coeff_shiftedPolynomial] using hB
  obtain ⟨n, hn, hcoeff⟩ := exists_nonzero_low_product_coefficient K _ _ hA' hB'
  intro hzero
  have := congr_fun hzero (⟨n, by omega⟩ : Fin (2 * K + 1))
  exact hcoeff this

theorem finite_coefficient_bound (K : ℕ) (δ D : ℝ) (hδ : 0 < δ) (hD : 0 ≤ D) :
    ∃ ε > 0, ∀ a : CoefficientPair K,
      (∀ i, ‖a.1 i‖ ≤ D) → (∀ i, ‖a.2 i‖ ≤ D) →
      δ ≤ ‖a.1 (centerIndex K)‖ → δ ≤ ‖a.2 (centerIndex K)‖ →
      ∃ n : Fin (2 * K + 1), ε ≤ ‖lowProduct K a n‖ := by
  let S : Set (CoefficientPair K) :=
    Metric.closedBall 0 D ∩
      {a | δ ≤ ‖a.1 (centerIndex K)‖} ∩ {a | δ ≤ ‖a.2 (centerIndex K)‖}
  have hSc : IsCompact S := by
    apply IsCompact.inter_right
    · apply IsCompact.inter_right (isCompact_closedBall _ _)
      exact isClosed_le continuous_const (by fun_prop)
    · exact isClosed_le continuous_const (by fun_prop)
  have hpositive : ∀ a ∈ S, 0 < ‖lowProduct K a‖ := by
    intro a ha
    apply norm_pos_iff.mpr
    apply lowProduct_ne_zero
    · intro hz
      have : δ ≤ ‖a.1 (centerIndex K)‖ := ha.1.2
      simp only [hz, norm_zero] at this
      linarith
    · intro hz
      have : δ ≤ ‖a.2 (centerIndex K)‖ := ha.2
      simp only [hz, norm_zero] at this
      linarith
  obtain ⟨ε, hε, hlower⟩ := hSc.exists_forall_le'
    (continuous_lowProduct K).norm.continuousOn hpositive
  refine ⟨ε, hε, ?_⟩
  intro a ha hb hca hcb
  have haS : a ∈ S := by
    refine ⟨⟨?_, hca⟩, hcb⟩
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
    exact ⟨(pi_norm_le_iff_of_nonneg hD).mpr ha, (pi_norm_le_iff_of_nonneg hD).mpr hb⟩
  obtain ⟨n, _, hn⟩ := Finset.exists_max_image Finset.univ (fun n => ‖lowProduct K a n‖)
    Finset.univ_nonempty
  refine ⟨n, (hlower a haS).trans ?_⟩
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  exact fun i => hn i (Finset.mem_univ i)

end ContinuousCircleWeight

namespace CircleSampling
open Filter Set
open scoped Topology

def nextWindow (m : ℕ) : ℕ := ⌈(m:ℝ)^((3:ℝ)/4*m)⌉₊
def kappa (j : ℕ) : ℝ := 1/(100*((j:ℝ)+1))

lemma kappa_pos (j : ℕ) : 0 < kappa j := by unfold kappa; positivity
lemma kappa_le (j : ℕ) : kappa j ≤ (1:ℝ)/100 := by
  unfold kappa
  apply one_div_le_one_div_of_le (by norm_num)
  nlinarith [Nat.cast_nonneg (α:=ℝ) j]

lemma exists_exponential_budget (j K : ℕ) {ε : ℝ} (hε : 0 < ε) (L0 : ℝ) :
    ∃ L : ℝ, 1 ≤ L ∧ L0 ≤ L ∧ (2*(K:ℝ)+1)*3*Real.exp (-L/10000) ≤ ε/((j:ℝ)+1) := by
  have ht : Tendsto (fun L : ℝ => (2*(K:ℝ)+1)*3*Real.exp (-L/10000)) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_div_const (show (0:ℝ)<10000 by norm_num))
    simpa only [Function.comp_def, id_eq, neg_div, mul_zero] using he.const_mul ((2*(K:ℝ)+1)*3)
  have hpos : 0 < ε/((j:ℝ)+1) := div_pos hε (by positivity)
  obtain ⟨L,h1,h2,hb⟩ := ((eventually_ge_atTop (1:ℝ)).and
    ((eventually_ge_atTop L0).and (ht.eventually_lt_const hpos))).exists
  exact ⟨L,h1,h2,hb.le⟩

lemma exists_bridge_budget (j : ℕ) (L : ℝ) :
    ∃ G : ℝ, 1 ≤ G ∧ L ≤ kappa (j+1)*Real.sqrt G := by
  have ht : Tendsto (fun G : ℝ => kappa (j+1)*Real.sqrt G) atTop atTop :=
    Real.tendsto_sqrt_atTop.const_mul_atTop (kappa_pos _)
  obtain ⟨G,hG,hL⟩ := ((eventually_ge_atTop (1:ℝ)).and (ht.eventually_ge_atTop L)).exists
  exact ⟨G,hG,hL⟩

lemma eventually_nextWindow_superlinear (C : ℝ) :
    ∀ᶠ m : ℕ in atTop, C*(m:ℝ) < nextWindow m := by
  filter_upwards [eventually_rpow_linear_gap ((3:ℝ)/4) 0 (C+1) 1 (by norm_num),
    eventually_ge_atTop (1:ℕ)] with m hg hm
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
  have hh : (C+1)*(m:ℝ) ≤ (m:ℝ)^((3:ℝ)/4*m) := by simpa using hg
  exact (by nlinarith : C*(m:ℝ)<(m:ℝ)^((3:ℝ)/4*m)).trans_le (Nat.le_ceil _)

lemma eventually_nextWindow_overlap (G : ℝ) :
    ∀ᶠ m : ℕ in atTop, G*(nextWindow m:ℝ) < (m:ℝ)^((4:ℝ)/5*m) := by
  filter_upwards [eventually_rpow_linear_gap ((4:ℝ)/5) ((3:ℝ)/4) (2*|G|+1) 0 (by norm_num),
    eventually_ge_atTop (1:ℕ)] with m hg hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hr : 1 ≤ (m:ℝ)^((3:ℝ)/4*m) := Real.one_le_rpow hm1 (by positivity)
  have hc : (nextWindow m:ℝ) < (m:ℝ)^((3:ℝ)/4*m)+1 := Nat.ceil_lt_add_one (by positivity)
  have hc0 : 0 ≤ (nextWindow m:ℝ) := Nat.cast_nonneg _
  have habs := le_abs_self G
  have hh : (2*|G|+1)*(m:ℝ)^((3:ℝ)/4*m) ≤ (m:ℝ)^((4:ℝ)/5*m) := by simpa using hg
  have hc' : (nextWindow m:ℝ) ≤ 2*(m:ℝ)^((3:ℝ)/4*m) := by linarith
  calc
    G*(nextWindow m:ℝ) ≤ |G| *(nextWindow m:ℝ) := mul_le_mul_of_nonneg_right habs hc0
    _ ≤ |G| *(2*(m:ℝ)^((3:ℝ)/4*m)) := mul_le_mul_of_nonneg_left hc' (abs_nonneg G)
    _ < (2*|G|+1)*(m:ℝ)^((3:ℝ)/4*m) := by nlinarith
    _ ≤ (m:ℝ)^((4:ℝ)/5*m) := hh

def StageNumerics (j K : ℕ) (G L Gnext : ℝ) (m : ℕ) : Prop :=
  200 ≤ m ∧ 2^(j+1) ≤ m ∧ K ≤ m ∧ 4*G ≤ (m:ℝ) ∧
  L ≤ kappa j*(m:ℝ)^((1:ℝ)/40) ∧
  Gnext*(nextWindow m:ℝ) < (m:ℝ)^((4:ℝ)/5*m) ∧
  2*K < nextWindow m ∧ m < nextWindow m ∧
  (m:ℝ)^(-(19:ℝ)/20) ≤ 1/4

lemma eventually_StageNumerics (j K : ℕ) (G L Gnext : ℝ) :
    ∀ᶠ m : ℕ in atTop, StageNumerics j K G L Gnext m := by
  have ht : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun m : ℕ => kappa j*(m:ℝ)^((1:ℝ)/40)) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/40)).comp ht).const_mul_atTop (kappa_pos j)
  have hb : Tendsto (fun m : ℕ => (m:ℝ)^(-(19:ℝ)/20)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<19/20)).comp ht
  filter_upwards [eventually_ge_atTop (max 200 (max (2^(j+1)) K)), ht.eventually_ge_atTop (4*G),
    hp.eventually_ge_atTop L, eventually_nextWindow_overlap Gnext, eventually_nextWindow_superlinear 2,
    hb.eventually_lt_const (by norm_num : (0:ℝ)<1/4)] with m hm hG hL hov hnext hb
  have hK : K ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have hm0 : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
  refine ⟨(le_max_left _ _).trans hm,(le_max_left _ _).trans ((le_max_right _ _).trans hm),hK,hG,hL,hov,?_,?_,hb.le⟩
  · have : 2*(K:ℝ) < nextWindow m := lt_of_le_of_lt (by exact_mod_cast Nat.mul_le_mul_left 2 hK) hnext
    exact_mod_cast this
  · have : (m:ℝ) < nextWindow m := by linarith
    exact_mod_cast this
end CircleSampling

end

end OAI
