import Mathlib
import OAI.Probability.SLE.RetainedDyadicGeometry

namespace OAI

/-! Hausdorff Limits for chordal SLE. -/

section

 
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge
noncomputable def retainedThreshold (κ D : ℝ) (k : ℕ) : ℝ :=
  D * ((2:ℝ)^(-(k:ℝ)))^dimension κ * (Real.log (k:ℝ))^(codimension κ/2)
 
def excessiveSquares {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (k₀ N : ℕ) (ω : Ω) : Set ℂ :=
  ⋃ k ∈ Set.Icc k₀ N, ⋃ ij : ℤ × ℤ,
    {z | z ∈ retainedDyadicSquare k ij ∧
      ENNReal.ofReal (retainedThreshold κ D k) < ν N ω (retainedDyadicSquare k ij)}
noncomputable def retainedMeasure {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (k₀ N : ℕ) (ω : Ω) : Measure ℂ :=
  (ν N ω).restrict (excessiveSquares κ D ν k₀ N ω)ᶜ
 

def SourceRetainedConstructionTarget : Prop :=
  ∀ (Ω : Type*) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ ν : ℕ → Kernel Ω ℂ, (∀ N, IsFiniteKernel (ν N)) →
  ∀ K : Set ℂ, IsCompact K → (∀ N ω, ν N ω Kᶜ = 0) →
  ∀ (A c m₀ m₂ : ℝ), 0 < A → 0 < c → 0 < m₀ → 0 < m₂ →
  ∀ kmin : ℕ,
  (∀ N, kmin ≤ N → ENNReal.ofReal m₀ ≤ ∫⁻ ω, ν N ω K ∂P) →
  (∀ N, kmin ≤ N → (∫⁻ ω, (ν N ω K)^2 ∂P) ≤ ENNReal.ofReal m₂) →
  (∀ N k, kmin ≤ k → k ≤ N → ∀ ij : ℤ × ℤ, ∀ u : ℝ, 1 ≤ u →
    P {ω | ((2:ℝ)^(-(k:ℝ)))^dimension κ * u <
      (ν N ω (retainedDyadicSquare k ij)).toReal} ≤
    ENNReal.ofReal (A*((2:ℝ)^(-(k:ℝ)))^codimension κ *
      Real.exp (-c*u^(2/codimension κ)))) →
  ∃ (D a p B : ℝ) (k₀ : ℕ), 1 ≤ D ∧ 0 < a ∧ 0 < p ∧ 0 < B ∧ kmin ≤ k₀ ∧
    (∀ N, k₀ ≤ N →
      Measurable (fun ω => retainedMeasure κ D ν k₀ N ω K) ∧
      (∀ ω, retainedMeasure κ D ν k₀ N ω K ≤ ENNReal.ofReal B) ∧
      (∀ ω k, k₀ ≤ k → k ≤ N → ∀ ij,
        retainedMeasure κ D ν k₀ N ω (retainedDyadicSquare k ij) ≤
          ENNReal.ofReal (retainedThreshold κ D k)) ∧
      ENNReal.ofReal p ≤ P {ω | ENNReal.ofReal a ≤ retainedMeasure κ D ν k₀ N ω K}) ∧
    ENNReal.ofReal p ≤
      P {ω | ∃ᶠ N in atTop, ENNReal.ofReal a ≤ retainedMeasure κ D ν k₀ N ω K}

lemma excessiveSquares_measurable {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (k₀ N : ℕ) (ω : Ω) :
    MeasurableSet (excessiveSquares κ D ν k₀ N ω) := by
  apply MeasurableSet.iUnion
  intro k
  apply MeasurableSet.iUnion
  intro hk
  apply MeasurableSet.iUnion
  intro ij
  have hQ : MeasurableSet (retainedDyadicSquare k ij) := by
    have hre : Measurable (fun z : ℂ => (2:ℝ)^k*z.re) := by fun_prop
    have him : Measurable (fun z : ℂ => (2:ℝ)^k*z.im) := by fun_prop
    exact (measurableSet_le measurable_const hre).inter
      ((measurableSet_lt hre measurable_const).inter
      ((measurableSet_le measurable_const him).inter (measurableSet_lt him measurable_const)))
  exact hQ.inter (MeasurableSet.const _)

lemma excessiveSquares_prod_measurable {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (k₀ N : ℕ) :
    MeasurableSet {p : Ω × ℂ | p.2 ∈ excessiveSquares κ D ν k₀ N p.1} := by
  have hQ (k : ℕ) (ij : ℤ × ℤ) : MeasurableSet (retainedDyadicSquare k ij) := by
    have hre : Measurable (fun z : ℂ => (2:ℝ)^k*z.re) := by fun_prop
    have him : Measurable (fun z : ℂ => (2:ℝ)^k*z.im) := by fun_prop
    exact (measurableSet_le measurable_const hre).inter
      ((measurableSet_lt hre measurable_const).inter
      ((measurableSet_le measurable_const him).inter (measurableSet_lt him measurable_const)))
  have hh : MeasurableSet (⋃ k ∈ Set.Icc k₀ N, ⋃ ij : ℤ × ℤ,
      {p : Ω × ℂ | p.2 ∈ retainedDyadicSquare k ij ∧
        ENNReal.ofReal (retainedThreshold κ D k) < ν N p.1 (retainedDyadicSquare k ij)}) := by
    apply MeasurableSet.iUnion
    intro k
    apply MeasurableSet.iUnion
    intro hk
    apply MeasurableSet.iUnion
    intro ij
    exact (measurable_snd (hQ k ij)).inter (measurableSet_lt measurable_const
      ((Kernel.measurable_coe _ (hQ k ij)).comp measurable_fst))
  simpa only [excessiveSquares, mem_iUnion, mem_ofPred_eq, Set.ofPred_exists] using hh

lemma retainedMeasure_measurable {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (k₀ N : ℕ) [IsFiniteKernel (ν N)] {K : Set ℂ}
    (hK : MeasurableSet K) :
    Measurable (fun ω => retainedMeasure κ D ν k₀ N ω K) := by
  have hm := Kernel.measurable_kernel_prodMk_left (κ := ν N)
    ((measurable_snd hK).inter (excessiveSquares_prod_measurable κ D ν k₀ N).compl)
  convert hm using 1
  ext ω
  rw [retainedMeasure, Measure.restrict_apply hK]
  rfl

lemma retainedMeasure_square_bound {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (k₀ N : ℕ) (ω : Ω) (k : ℕ)
    (hk₀ : k₀ ≤ k) (hkN : k ≤ N) (ij : ℤ × ℤ) :
    retainedMeasure κ D ν k₀ N ω (retainedDyadicSquare k ij) ≤
      ENNReal.ofReal (retainedThreshold κ D k) := by
  by_cases hbad : ENNReal.ofReal (retainedThreshold κ D k) <
      ν N ω (retainedDyadicSquare k ij)
  · have hsub : retainedDyadicSquare k ij ⊆ excessiveSquares κ D ν k₀ N ω := by
      intro z hz
      exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨⟨hk₀,hkN⟩, mem_iUnion.mpr ⟨ij,hz,hbad⟩⟩⟩
    have hz : (ν N ω).restrict (excessiveSquares κ D ν k₀ N ω)ᶜ
        (retainedDyadicSquare k ij) = 0 := by
      apply MeasureTheory.measure_mono_null hsub
      simp [Measure.restrict_apply' (excessiveSquares_measurable κ D ν k₀ N ω).compl]
    exact hz.le.trans bot_le
  · exact (Measure.restrict_apply_le _ _).trans (le_of_not_gt hbad)

 

def SourceRetainedBadSquareTarget : Prop :=
  ∀ (Ω : Type*) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ (X : Ω → ℝ), Measurable X → (∀ ω, 0 ≤ X ω) →
  ∀ (A c l D : ℝ), 0 < A → 0 < c → 0 < l → 1 ≤ D →
  ∀ k : ℕ, 1 ≤ Real.log (k:ℝ) →
  (∀ u : ℝ, 1 ≤ u → P {ω | l^dimension κ * u < X ω} ≤
    ENNReal.ofReal (A*l^codimension κ*Real.exp (-c*u^(2/codimension κ)))) →
  (∫⁻ ω in {ω | D*l^dimension κ*(Real.log (k:ℝ))^(codimension κ/2) < X ω},
    ENNReal.ofReal (X ω) ∂P) ≤
    ENNReal.ofReal ((2*A/c)*l^2*(k:ℝ)^(-(c/2)*D^(2/codimension κ)))

 

lemma truncated_stretched_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (a c s H q : ℝ) (ha : 0 ≤ a) (hc : 0 < c) (hs : 0 < s)
    (hH : 1 ≤ H) (hq : 1 ≤ q)
    (htail : ∀ u : ℝ, 1 ≤ u → P {ω | s*u < X ω} ≤
      ENNReal.ofReal (a * Real.exp (-c*u^q))) :
    (∫⁻ ω in {ω | s*H < X ω}, ENNReal.ofReal (X ω) ∂P) ≤
      ENNReal.ofReal ((2*a*s/c)*Real.exp (-(c/2)*H^q)) := by
  let b : ℝ := c/(2*s)
  have hb : 0 < b := div_pos hc (by positivity)
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-b*t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hb) 0
  have hint : (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-b*t))) =
      ENNReal.ofReal (1/b) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hexp
      (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
    rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hb)]
    simp
  rw [lintegral_eq_lintegral_meas_lt _
    (Filter.Eventually.of_forall hX0) hX.aemeasurable]
  calc
    _ ≤ ∫⁻ t in Ioi (0:ℝ),
        ENNReal.ofReal (a * Real.exp (-(c/2)*H^q)) *
        ENNReal.ofReal (Real.exp (-b*t)) := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro t ht
      let u : ℝ := max H (t/s)
      have huH : H ≤ u := le_max_left _ _
      have hut : t/s ≤ u := le_max_right _ _
      have hu : 1 ≤ u := hH.trans huH
      have hu0 : 0 ≤ u := le_trans zero_le_one hu
      have hq0 : 0 ≤ q := le_trans zero_le_one hq
      have hr1 : H^q ≤ u^q := Real.rpow_le_rpow (by linarith) huH hq0
      have hr2 : u ≤ u^q := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hu hq
      have htu : t ≤ s*u := (div_le_iff₀ hs).mp hut |>.trans_eq (mul_comm u s)
      have hset : {ω | t < X ω} ∩ {ω | s*H < X ω} = {ω | s*u < X ω} := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq]
        dsimp [u]
        rw [mul_max_of_nonneg H (t/s) hs.le, mul_div_cancel₀ _ hs.ne']
        exact and_comm.trans max_lt_iff.symm
      rw [Measure.restrict_apply (measurableSet_lt measurable_const hX), hset]
      refine (htail u hu).trans ?_
      rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ ha
      apply Real.exp_le_exp.mpr
      have hlinear : b*t ≤ (c/2)*u^q := by
        calc
          b*t = (c/2)*(t/s) := by dsimp [b]; ring
          _ ≤ (c/2)*u^q := mul_le_mul_of_nonneg_left (hut.trans hr2) (by positivity)
      nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hr1)]
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop), hint]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [b]
      field_simp

 

theorem sourceRetainedBadSquare : SourceRetainedBadSquareTarget := by
  intro Ω _ P _ κ hκ0 hκ8 X hX hX0 A c l D hA hc hl hD k hk htail
  have hp : 0 < codimension κ := by dsimp [codimension, dimension]; linarith
  have hp1 : codimension κ < 1 := by dsimp [codimension, dimension]; linarith
  have hq : 1 ≤ 2/codimension κ := (le_div_iff₀ hp).mpr (by linarith)
  have hk0 : (0:ℝ) < k := by
    by_contra hh
    have hkz : (k:ℝ) = 0 := le_antisymm (le_of_not_gt hh) (Nat.cast_nonneg k)
    norm_num [hkz] at hk
  have hlog : 0 ≤ Real.log (k:ℝ) := le_trans zero_le_one hk
  have hH : 1 ≤ D*(Real.log (k:ℝ))^(codimension κ/2) := by
    have hr : 1 ≤ (Real.log (k:ℝ))^(codimension κ/2) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hk (show 0 ≤ codimension κ/2 by positivity)
    nlinarith
  have hpow : (D*(Real.log (k:ℝ))^(codimension κ/2))^(2/codimension κ) =
      D^(2/codimension κ)*Real.log (k:ℝ) := by
    rw [Real.mul_rpow (by linarith : 0 ≤ D) (Real.rpow_nonneg hlog _),
      ← Real.rpow_mul hlog]
    have he : (codimension κ/2)*(2/codimension κ) = 1 := by field_simp
    rw [he, Real.rpow_one]
  have hcoef : (2*(A*l^codimension κ)*l^dimension κ/c) = (2*A/c)*l^2 := by
    calc
      _ = (2*A/c)*(l^codimension κ*l^dimension κ) := by ring
      _ = _ := by rw [← Real.rpow_add hl]; simp [codimension]
  have hset : {ω | D*l^dimension κ*(Real.log (k:ℝ))^(codimension κ/2) < X ω} =
      {ω | l^dimension κ*(D*(Real.log (k:ℝ))^(codimension κ/2)) < X ω} := by
    have heq : D*l^dimension κ*(Real.log (k:ℝ))^(codimension κ/2) =
        l^dimension κ*(D*(Real.log (k:ℝ))^(codimension κ/2)) := by ring
    rw [heq]
  rw [hset]
  refine (truncated_stretched_tail P X hX hX0 (A*l^codimension κ) c
    (l^dimension κ) (D*(Real.log (k:ℝ))^(codimension κ/2))
    (2/codimension κ) (by positivity) hc (by positivity) hH hq htail).trans_eq ?_
  rw [hcoef, hpow, Real.rpow_def_of_pos hk0]
  congr 2
  congr 1
  ring

lemma retained_total_bound {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (k₀ N M : ℕ) (ω : Ω) (hN : k₀ ≤ N)
    {K : Set ℂ} (hK : ∀ z ∈ K, ‖z‖ ≤ M) :
    retainedMeasure κ D ν k₀ N ω K ≤
      (retainedCandidates M k₀).card * ENNReal.ofReal (retainedThreshold κ D k₀) := by
  calc
    _ ≤ retainedMeasure κ D ν k₀ N ω
        (⋃ ij ∈ retainedCandidates M k₀, retainedDyadicSquare k₀ ij) :=
      measure_mono (retainedCandidates_cover M k₀ hK)
    _ ≤ ∑ ij ∈ retainedCandidates M k₀,
        retainedMeasure κ D ν k₀ N ω (retainedDyadicSquare k₀ ij) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ ij ∈ retainedCandidates M k₀,
        ENNReal.ofReal (retainedThreshold κ D k₀) :=
      Finset.sum_le_sum (fun ij _ => retainedMeasure_square_bound κ D ν k₀ N ω k₀ le_rfl hN ij)
    _ = _ := by simp

noncomputable def retainedBadSquareMass {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (N k : ℕ) (ij : ℤ × ℤ) (ω : Ω) : ℝ≥0∞ :=
  if ENNReal.ofReal (retainedThreshold κ D k) < ν N ω (retainedDyadicSquare k ij)
  then ν N ω (retainedDyadicSquare k ij) else 0

lemma retainedBadSquareMass_measurable {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (N k : ℕ) (ij : ℤ × ℤ) :
    Measurable (retainedBadSquareMass κ D ν N k ij) := by
  have hm := Kernel.measurable_coe (ν N) (retainedSquare_measurable k ij)
  exact Measurable.ite (measurableSet_lt measurable_const hm) hm measurable_const

lemma retained_removed_bound {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (k₀ N M : ℕ) (ω : Ω)
    {K : Set ℂ} (hK : ∀ z ∈ K, ‖z‖ ≤ M) :
    ν N ω (K ∩ excessiveSquares κ D ν k₀ N ω) ≤
      ∑ k ∈ Finset.Icc k₀ N, ∑ ij ∈ retainedCandidates M k,
        retainedBadSquareMass κ D ν N k ij ω := by
  classical
  let E : ℕ → ℤ × ℤ → Set ℂ := fun k ij => {z | z ∈ retainedDyadicSquare k ij ∧
    ENNReal.ofReal (retainedThreshold κ D k) < ν N ω (retainedDyadicSquare k ij)}
  have hsub : K ∩ excessiveSquares κ D ν k₀ N ω ⊆
      ⋃ k ∈ Finset.Icc k₀ N, ⋃ ij ∈ retainedCandidates M k, E k ij := by
    intro z hz
    rcases mem_iUnion.mp hz.2 with ⟨k,hk⟩
    rcases mem_iUnion.mp hk with ⟨hk, hijk⟩
    rcases mem_iUnion.mp hijk with ⟨ij,hij,hbad⟩
    have hA : ij ∈ retainedCandidates M k := by
      rw [← (retainedSquare_iff_address k ij z).mp hij]
      exact retainedAddress_mem_candidates M k (hK z hz.1)
    exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨Finset.mem_Icc.mpr hk,
      mem_iUnion.mpr ⟨ij,mem_iUnion.mpr ⟨hA,hij,hbad⟩⟩⟩⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  apply Finset.sum_le_sum
  intro k hk
  refine (measure_biUnion_finset_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro ij hij
  by_cases hbad : ENNReal.ofReal (retainedThreshold κ D k) < ν N ω (retainedDyadicSquare k ij)
  · simp only [E, hbad, and_true, retainedBadSquareMass]
    rfl
  · simp [E, hbad, retainedBadSquareMass]

lemma retained_removed_expectation_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (κ D : ℝ) (ν : ℕ → Kernel Ω ℂ) (k₀ N M : ℕ)
    {K : Set ℂ} (hK : ∀ z ∈ K, ‖z‖ ≤ M) :
    (∫⁻ ω, ν N ω (K ∩ excessiveSquares κ D ν k₀ N ω) ∂P) ≤
      ∑ k ∈ Finset.Icc k₀ N, ∑ ij ∈ retainedCandidates M k,
        ∫⁻ ω, retainedBadSquareMass κ D ν N k ij ω ∂P := by
  refine (lintegral_mono (fun ω => retained_removed_bound κ D ν k₀ N M ω hK)).trans_eq ?_
  rw [lintegral_finsetSum _ (fun k _ => Finset.measurable_sum _
    (fun ij _ => retainedBadSquareMass_measurable κ D ν N k ij))]
  apply Finset.sum_congr rfl
  intro k hk
  exact lintegral_finsetSum _ (fun ij _ => retainedBadSquareMass_measurable κ D ν N k ij)

lemma retainedBadSquareMass_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (κ D : ℝ) (hκ0 : 0 < κ) (hκ8 : κ < 8)
    (ν : ℕ → Kernel Ω ℂ) (N k : ℕ) [IsFiniteKernel (ν N)] (ij : ℤ × ℤ)
    (A c : ℝ) (hA : 0 < A) (hc : 0 < c) (hD : 1 ≤ D)
    (hk : 1 ≤ Real.log (k:ℝ))
    (htail : ∀ u : ℝ, 1 ≤ u →
      P {ω | ((2:ℝ)^(-(k:ℝ)))^dimension κ * u <
        (ν N ω (retainedDyadicSquare k ij)).toReal} ≤
      ENNReal.ofReal (A*((2:ℝ)^(-(k:ℝ)))^codimension κ *
        Real.exp (-c*u^(2/codimension κ)))) :
    (∫⁻ ω, retainedBadSquareMass κ D ν N k ij ω ∂P) ≤
      ENNReal.ofReal ((2*A/c)*((2:ℝ)^(-(k:ℝ)))^2*
        (k:ℝ)^(-(c/2)*D^(2/codimension κ))) := by
  have hm := (Kernel.measurable_coe (ν N) (retainedSquare_measurable k ij)).ennreal_toReal
  have hH : 0 ≤ retainedThreshold κ D k := by
    dsimp [retainedThreshold]
    have hlog : 0 ≤ Real.log (k:ℝ) := le_trans zero_le_one hk
    have hD0 : 0 ≤ D := le_trans zero_le_one hD
    positivity
  have hfn : retainedBadSquareMass κ D ν N k ij =
      {ω | retainedThreshold κ D k < (ν N ω (retainedDyadicSquare k ij)).toReal}.indicator
        (fun ω => ENNReal.ofReal ((ν N ω (retainedDyadicSquare k ij)).toReal)) := by
    ext ω
    simp only [retainedBadSquareMass, Set.indicator_apply, Set.mem_ofPred_eq,
      ENNReal.ofReal_lt_iff_lt_toReal hH (measure_ne_top _ _),
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hfn, lintegral_indicator (measurableSet_lt measurable_const hm)]
  exact sourceRetainedBadSquare Ω inferInstance P inferInstance κ hκ0 hκ8 _ hm
    (fun _ => ENNReal.toReal_nonneg) A c ((2:ℝ)^(-(k:ℝ))) D hA hc
    (by positivity) hD k hk htail

lemma retained_choose_D (κ c : ℝ) (hκ8 : κ < 8) (hc : 0 < c) :
    ∃ D : ℝ, 1 ≤ D ∧ 1 < (c/2)*D^(2/codimension κ) := by
  have hp : 0 < codimension κ := by dsimp [codimension, dimension]; linarith
  let r := max 1 (4/c)
  have hr : 1 ≤ r := le_max_left _ _
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  refine ⟨r^(codimension κ/2), Real.one_le_rpow hr (by positivity), ?_⟩
  rw [← Real.rpow_mul hr0, show codimension κ/2*(2/codimension κ) = 1 by
    field_simp, Real.rpow_one]
  have : 4/c ≤ r := le_max_right _ _
  have hcr : 4 ≤ r*c := (div_le_iff₀ hc).mp this
  nlinarith

lemma retained_finite_power_tail (x C m : ℝ) (hx : x < -1) (_hC : 0 ≤ C) (hm : 0 < m)
    (nmin : ℕ) : ∃ n₀ : ℕ, nmin ≤ n₀ ∧ (∀ k, n₀ ≤ k → 1 ≤ Real.log (k:ℝ)) ∧
    ∀ N, (∑ k ∈ Finset.Icc n₀ N, ENNReal.ofReal (C*(k:ℝ)^x)) ≤ ENNReal.ofReal m := by
  have hs : Summable (fun k : ℕ => C*(k:ℝ)^x) :=
    ((Real.summable_nat_rpow).mpr hx).mul_left C
  have ht := ENNReal.tendsto_sum_nat_add
    (fun k : ℕ => ENNReal.ofReal (C*(k:ℝ)^x)) hs.tsum_ofReal_ne_top
  have hm0 : (0:ℝ≥0∞) < ENNReal.ofReal m := ENNReal.ofReal_pos.mpr hm
  have hev := ht.eventually (gt_mem_nhds hm0)
  have hlog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop 1)
  obtain ⟨j, hj⟩ := eventually_atTop.1 hlog
  obtain ⟨n₀, ⟨hn₀, hj₀⟩, hn⟩ :=
    (((eventually_ge_atTop nmin).and (eventually_ge_atTop j)).and hev).exists
  refine ⟨n₀, hn₀, fun k hk => hj k (hj₀.trans hk), fun N => ?_⟩
  have he : Finset.Icc n₀ N = Finset.Ico n₀ (N+1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [he, Finset.sum_Ico_eq_sum_range]
  calc
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (C*((n₀+k:ℕ):ℝ)^x) := ENNReal.sum_le_tsum _
    _ = ∑' k : ℕ, ENNReal.ofReal (C*((k+n₀:ℕ):ℝ)^x) := by
      congr 1; funext k; rw [Nat.add_comm]
    _ ≤ ENNReal.ofReal m := hn.le

lemma retained_level_sum_bound (M k : ℕ) (A c x : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    (∑ _ij ∈ retainedCandidates M k,
      ENNReal.ofReal ((2*A/c)*((2:ℝ)^(-(k:ℝ)))^2*(k:ℝ)^x)) ≤
    ENNReal.ofReal (((2*A/c)*(2*(M:ℝ)+1)^2)*(k:ℝ)^x) := by
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity :
    0 ≤ ((retainedCandidates M k).card : ℝ))]
  apply ENNReal.ofReal_le_ofReal
  have hscale := retainedCandidates_scale_card M k
  have hC : 0 ≤ 2*A/c := by positivity
  have hx : 0 ≤ (k:ℝ)^x := Real.rpow_nonneg (by positivity) _
  calc
    _ = (2*A/c)*(((retainedCandidates M k).card : ℝ)*((2:ℝ)^(-(k:ℝ)))^2)*(k:ℝ)^x := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hC) hx

lemma retained_mass_add_removed {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (k₀ N : ℕ) (ω : Ω) {K : Set ℂ} (hK : MeasurableSet K) :
    retainedMeasure κ D ν k₀ N ω K + ν N ω (K ∩ excessiveSquares κ D ν k₀ N ω) =
      ν N ω K := by
  rw [retainedMeasure, Measure.restrict_apply hK]
  exact measure_sdiff_add_inter K (excessiveSquares_measurable κ D ν k₀ N ω)

lemma retained_first_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (κ D : ℝ) (ν : ℕ → Kernel Ω ℂ) (k₀ N : ℕ) [IsFiniteKernel (ν N)]
    {K : Set ℂ} (hK : MeasurableSet K) (m : ℝ) (hm : 0 < m)
    (hfirst : ENNReal.ofReal m ≤ ∫⁻ ω, ν N ω K ∂P)
    (hloss : (∫⁻ ω, ν N ω (K ∩ excessiveSquares κ D ν k₀ N ω) ∂P) ≤
      ENNReal.ofReal (m/2)) :
    ENNReal.ofReal (m/2) ≤ ∫⁻ ω, retainedMeasure κ D ν k₀ N ω K ∂P := by
  have hadd : (∫⁻ ω, ν N ω K ∂P) =
      (∫⁻ ω, retainedMeasure κ D ν k₀ N ω K ∂P) +
      (∫⁻ ω, ν N ω (K ∩ excessiveSquares κ D ν k₀ N ω) ∂P) := by
    rw [← lintegral_add_left (retainedMeasure_measurable κ D ν k₀ N hK)]
    exact lintegral_congr (fun ω => (retained_mass_add_removed κ D ν k₀ N ω hK).symm)
  rw [hadd] at hfirst
  have hle := hfirst.trans (add_le_add le_rfl hloss)
  have hsplit : ENNReal.ofReal m = ENNReal.ofReal (m/2)+ENNReal.ofReal (m/2) := by
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ m/2) (by positivity : 0 ≤ m/2)]
    congr 1; ring
  rw [hsplit] at hle
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hle

 

lemma retained_positive_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ≥0∞) (hY : Measurable Y)
    (B m : ℝ) (hB : 0 < B) (hm : 0 < m) (hbound : ∀ ω, Y ω ≤ ENNReal.ofReal B)
    (hfirst : ENNReal.ofReal m ≤ ∫⁻ ω, Y ω ∂P) :
    ENNReal.ofReal (m/(2*B)) ≤ P {ω | ENNReal.ofReal (m/2) ≤ Y ω} := by
  let E := {ω | ENNReal.ofReal (m/2) ≤ Y ω}
  have hE : MeasurableSet E := measurableSet_le measurable_const hY
  have hpoint (ω : Ω) : Y ω ≤ ENNReal.ofReal (m/2) + E.indicator (fun _ => ENNReal.ofReal B) ω := by
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω]
      exact (hbound ω).trans (le_add_left le_rfl)
    · rw [Set.indicator_of_notMem hω, add_zero]
      exact le_of_not_ge hω
  have hle := hfirst.trans (lintegral_mono hpoint)
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ,
    mul_one, lintegral_indicator hE, lintegral_const, Measure.restrict_apply_univ] at hle
  have ht : ENNReal.ofReal (m/2) + ENNReal.ofReal B * P E ≠ ∞ := by
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)⟩
  have hreal := ENNReal.toReal_mono ht hle
  rw [ENNReal.toReal_ofReal hm.le, ENNReal.toReal_add ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ m/2), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hB.le] at hreal
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr
  apply (div_le_iff₀ (by positivity : 0 < 2*B)).mpr
  nlinarith

lemma retained_limsup_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ℕ → Set Ω)
    (hE : ∀ N, MeasurableSet (E N)) (n₀ : ℕ) (p : ℝ≥0∞)
    (hp : ∀ N, n₀ ≤ N → p ≤ P (E N)) :
    p ≤ P {ω | ∃ᶠ N in atTop, ω ∈ E N} := by
  let U : ℕ → Set Ω := fun n => ⋃ N ≥ n, E N
  have hU : ∀ n, MeasurableSet (U n) := fun n =>
    MeasurableSet.iUnion (fun N => MeasurableSet.iUnion (fun _ => hE N))
  have hanti : Antitone U := by
    intro n m hnm ω hω
    rcases mem_iUnion.mp hω with ⟨N,hN⟩
    rcases mem_iUnion.mp hN with ⟨hmN,hω⟩
    exact mem_iUnion.mpr ⟨N, mem_iUnion.mpr ⟨hnm.trans hmN, hω⟩⟩
  have heq : {ω | ∃ᶠ N in atTop, ω ∈ E N} = ⋂ n, U n := by
    ext ω
    simp [U, frequently_atTop]
  rw [heq, hanti.measure_iInter (fun n => (hU n).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩]
  apply le_iInf
  intro n
  refine (hp (max n₀ n) (le_max_left _ _)).trans (measure_mono ?_)
  exact subset_iUnion₂_of_subset (max n₀ n) (le_max_right _ _) Subset.rfl

 

theorem sourceRetainedConstruction : SourceRetainedConstructionTarget := by
  intro Ω _ P hP κ hκ0 hκ8 ν hν K hK hsupport A c m₀ m₂ hA hc hm₀ hm₂
    kmin hfirst hsecond htail
  let := hP
  let (N : ℕ) := hν N
  obtain ⟨M, hM⟩ := compact_retained_candidate_radius hK
  obtain ⟨D,hD,hβ⟩ := retained_choose_D κ c hκ8 hc
  let x : ℝ := -(c/2)*D^(2/codimension κ)
  let C : ℝ := (2*A/c)*(2*(M:ℝ)+1)^2
  have hx : x < -1 := by dsimp [x]; nlinarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨k₀,hmin,hlog,htail_sum⟩ :=
    retained_finite_power_tail x C (m₀/2) hx hC (by positivity) kmin
  have hloss (N : ℕ) (hN : k₀ ≤ N) :
      (∫⁻ ω, ν N ω (K ∩ excessiveSquares κ D ν k₀ N ω) ∂P) ≤
        ENNReal.ofReal (m₀/2) := by
    refine (retained_removed_expectation_bound P κ D ν k₀ N M hM).trans
      ((Finset.sum_le_sum (fun k hk => ?_)).trans (htail_sum N))
    have hk₀ : k₀ ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
    calc
      _ ≤ ∑ ij ∈ retainedCandidates M k,
          ENNReal.ofReal ((2*A/c)*((2:ℝ)^(-(k:ℝ)))^2*(k:ℝ)^x) :=
        Finset.sum_le_sum (fun ij _ => retainedBadSquareMass_expectation P κ D hκ0 hκ8
          ν N k ij A c hA hc hD (hlog k hk₀) (htail N k (hmin.trans hk₀) hkN ij))
      _ ≤ ENNReal.ofReal (C*(k:ℝ)^x) := retained_level_sum_bound M k A c x hA.le hc
  have hthreshold : 0 ≤ retainedThreshold κ D k₀ := by
    have hD0 : 0 ≤ D := zero_le_one.trans hD
    have hlog0 : 0 ≤ Real.log (k₀:ℝ) := zero_le_one.trans (hlog k₀ le_rfl)
    dsimp [retainedThreshold]
    positivity
  let B : ℝ := (retainedCandidates M k₀).card * retainedThreshold κ D k₀ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound (N : ℕ) (hN : k₀ ≤ N) (ω : Ω) :
      retainedMeasure κ D ν k₀ N ω K ≤ ENNReal.ofReal B := by
    refine (retained_total_bound κ D ν k₀ N M ω hN hM).trans ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity :
      0 ≤ ((retainedCandidates M k₀).card : ℝ))]
    apply ENNReal.ofReal_le_ofReal
    dsimp [B]; linarith
  have hmoment (N : ℕ) (hN : k₀ ≤ N) :
      ENNReal.ofReal (m₀/2) ≤ ∫⁻ ω, retainedMeasure κ D ν k₀ N ω K ∂P :=
    retained_first_moment P κ D ν k₀ N hK.measurableSet m₀ hm₀
      (hfirst N (hmin.trans hN)) (hloss N hN)
  have hprob (N : ℕ) (hN : k₀ ≤ N) :
      ENNReal.ofReal ((m₀/2)/(2*B)) ≤
        P {ω | ENNReal.ofReal ((m₀/2)/2) ≤ retainedMeasure κ D ν k₀ N ω K} :=
    retained_positive_probability P _ (retainedMeasure_measurable κ D ν k₀ N hK.measurableSet)
      B (m₀/2) hB (by positivity) (hbound N hN) (hmoment N hN)
  refine ⟨D, (m₀/2)/2, (m₀/2)/(2*B), B, k₀, hD, by positivity, by positivity,
    hB, hmin, ?_, ?_⟩
  · intro N hN
    exact ⟨retainedMeasure_measurable κ D ν k₀ N hK.measurableSet, hbound N hN,
      fun ω k hk₀ hkN ij => retainedMeasure_square_bound κ D ν k₀ N ω k hk₀ hkN ij,
      hprob N hN⟩
  · exact retained_limsup_probability P _ (fun N => measurableSet_le measurable_const
      (retainedMeasure_measurable κ D ν k₀ N hK.measurableSet)) k₀ _ hprob

end SLEExactGauge
end

 
section

 

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

structure IsGauge (h : ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn h (Ici 0)
  monotoneOn : MonotoneOn h (Ici 0)
  zero : h 0 = 0
  positive : ∀ r, 0 < r → 0 < h r

noncomputable def hFormula (κ r : ℝ) : ℝ :=
  r ^ dimension κ * (Real.log (Real.log (1 / r))) ^ (codimension κ / ((2 : ℕ) : ℝ))

noncomputable def gFormula (κ r : ℝ) : ℝ :=
  r ^ dimension κ * Real.log (Real.log (1 / r))

 
def HasSmallRadiusFormula (h f : ℝ → ℝ) : Prop :=
  h =ᶠ[𝓝[>] 0] f

 
noncomputable def extendedGauge (h : ℝ → ℝ) (r : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (h r.toReal)

 
noncomputable def hausdorffGauge (h : ℝ → ℝ) : Measure ℂ :=
  Measure.mkMetric (extendedGauge h)

 
def SourceRetainedDyadicTarget : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ h : ℝ → ℝ, IsGauge h → HasSmallRadiusFormula h (hFormula κ) →
  ∀ K E : Set ℂ, IsCompact K → IsClosed E →
  ∀ μ : ℕ → FiniteMeasure ℂ, ∀ a : ℝ≥0, 0 < a →
  (∃ᶠ N in atTop, a ≤ (μ N).mass) →
  (∀ N, μ N Kᶜ = 0) →
  ∀ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) →
  (∀ N, (μ N : Measure ℂ) (Metric.cthickening (e N) E)ᶜ = 0) →
  ∀ D : ℝ, 0 < D → ∀ k₀ : ℕ,
  (∀ N k, k₀ ≤ k → k ≤ N → ∀ ij : ℤ × ℤ,
    μ N (retainedDyadicSquare k ij) ≤ ENNReal.ofReal (retainedThreshold κ D k)) →
  0 < hausdorffGauge h E

 

lemma normalized_supported_probability_compact {K : Set ℂ} (hK : IsCompact K) :
    IsCompact {ν : ProbabilityMeasure ℂ | ν Kᶜ = 0} := by
  have he : Topology.IsClosedEmbedding
      (ProbabilityMeasure.toFiniteMeasure (Ω := ℂ)) :=
    ⟨ProbabilityMeasure.toFiniteMeasure_isEmbedding ℂ, by
      rw [ProbabilityMeasure.range_toFiniteMeasure]
      exact isClosed_eq FiniteMeasure.continuous_mass continuous_const⟩
  have hc := he.isCompact_preimage
    (isCompact_setOfPred_finiteMeasure_le_of_isCompact (1 : ℝ≥0) hK)
  simpa only [Set.preimage_ofPred_eq, ProbabilityMeasure.mass_toFiniteMeasure,
    le_refl, true_and, ProbabilityMeasure.coeFn_toFiniteMeasure] using hc

lemma probability_limit_ball_bound
    {νs : ℕ → ProbabilityMeasure ℂ} {ν : ProbabilityMeasure ℂ}
    (hlim : Tendsto νs atTop (𝓝 ν)) (x : ℂ) (r : ℝ) (c : ℝ≥0∞)
    (hb : ∀ᶠ n in atTop, (νs n : Measure ℂ) (Metric.ball x r) ≤ c) :
    (ν : Measure ℂ) (Metric.ball x r) ≤ c := by
  exact (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim Metric.isOpen_ball).trans
    (liminf_le_of_frequently_le hb.frequently)

lemma probability_limit_shrinking_carriers
    {νs : ℕ → ProbabilityMeasure ℂ} {ν : ProbabilityMeasure ℂ}
    (hlim : Tendsto νs atTop (𝓝 ν)) {E : Set ℂ} (hE : IsClosed E)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hcarrier : ∀ n, (νs n : Measure ℂ) (Metric.cthickening (e n) E)ᶜ = 0) :
    (ν : Measure ℂ) Eᶜ = 0 := by
  have hnull (δ : ℝ) (hδ : 0 < δ) :
      (ν : Measure ℂ) (Metric.cthickening δ E)ᶜ = 0 := by
    apply le_antisymm _ bot_le
    apply (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim
      Metric.isClosed_cthickening.isOpen_compl).trans
    have hzero : ∀ᶠ n in atTop, (νs n : Measure ℂ) (Metric.cthickening δ E)ᶜ ≤ 0 := by
      filter_upwards [he.eventually_le_const hδ] with n hn
      exact (measure_mono (Set.compl_subset_compl.mpr (Metric.cthickening_mono hn E))).trans
        (hcarrier n).le
    exact liminf_le_of_frequently_le hzero.frequently
  let δ : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  apply measure_mono_null (t := ⋃ n, (Metric.cthickening (δ n) E)ᶜ)
  · intro x hx
    have hnot : x ∉ closure E := by simpa only [hE.closure_eq, Set.mem_compl_iff] using hx
    obtain ⟨n, hn⟩ := (hδlim.eventually
      (Metric.eventually_notMem_cthickening_of_infEDist_pos hnot)).exists
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  · exact measure_iUnion_null (fun n => hnull (δ n) (hδpos n))

 

lemma gauge_mass_distribution {h : ℝ → ℝ} (hh : IsGauge h)
    (ν : Measure ℂ) (C : ℝ≥0) (hC : 0 < C)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hball : ∀ x r, 0 < r → r < ρ →
      ν (Metric.ball x r) ≤ (C : ℝ≥0∞) * ENNReal.ofReal (h r)) :
    ν ≤ (C : ℝ≥0∞) • hausdorffGauge h := by
  let m : ℝ≥0∞ → ℝ≥0∞ := fun r => (C : ℝ≥0∞) * extendedGauge h r
  have hs : ν ≤ Measure.mkMetric m := by
    refine Measure.le_mkMetric m ν (ENNReal.ofReal (ρ / 2))
      (ENNReal.ofReal_pos.mpr (by positivity)) ?_
    intro s hs
    by_cases he : s.Nonempty
    · obtain ⟨x, hx⟩ := he
      have htop : Metric.ediam s ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
      let d : ℝ := (Metric.ediam s).toReal
      have hd : 0 ≤ d := ENNReal.toReal_nonneg
      have hdρ : d ≤ ρ / 2 := by
        exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hs).trans_eq
          (ENNReal.toReal_ofReal (by positivity))
      have hdρ' : d < ρ := by linarith
      have hcont : Tendsto h (𝓝[>] d) (𝓝 (h d)) :=
        (hh.continuousOn d hd).mono (fun y hy => hd.trans (le_of_lt hy))
      have ht : Tendsto (fun r => ENNReal.ofReal ((C : ℝ) * h r))
          (𝓝[>] d) (𝓝 (ENNReal.ofReal ((C : ℝ) * h d))) :=
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          (tendsto_const_nhds.mul hcont)
      have hle : ν s ≤ ENNReal.ofReal ((C : ℝ) * h d) := by
        apply ge_of_tendsto ht
        filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hdρ').filter_mono inf_le_left]
          with r hr hrρ
        have hsub : s ⊆ Metric.ball x r := by
          intro y hy
          have hdist : dist y x ≤ d := by
            simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using
              ENNReal.toReal_mono htop (Metric.edist_le_ediam_of_mem hy hx)
          exact hdist.trans_lt hr
        have := (measure_mono hsub).trans (hball x r (hd.trans_lt hr) hrρ)
        simpa only [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal] using this
      simpa only [m, extendedGauge, d, ENNReal.ofReal_mul C.coe_nonneg,
        ENNReal.ofReal_coe_nnreal] using hle
    · rw [Set.not_nonempty_iff_eq_empty.mp he, measure_empty]
      exact bot_le
  exact hs.trans (Measure.mkMetric_mono_smul ENNReal.coe_ne_top
    (ENNReal.coe_ne_zero.mpr hC.ne') (Filter.Eventually.of_forall fun _ => le_rfl))

 

theorem retained_compact_mass_lower_bound
    {h : ℝ → ℝ} (hh : IsGauge h) {K E : Set ℂ}
    (hK : IsCompact K) (hE : IsClosed E)
    (μ : ℕ → FiniteMeasure ℂ) (a C : ℝ≥0) (ha : 0 < a) (hC : 0 < C)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hmass : ∀ n, a ≤ (μ n).mass)
    (hKsupport : ∀ n, μ n Kᶜ = 0)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hcarrier : ∀ n, (μ n : Measure ℂ) (Metric.cthickening (e n) E)ᶜ = 0)
    (hball : ∀ x r, 0 < r → r < ρ →
      ∀ᶠ n in atTop, (μ n : Measure ℂ) (Metric.ball x r) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (h r)) :
    0 < hausdorffGauge h E := by
  have hmpos (n : ℕ) : 0 < (μ n).mass := ha.trans_le (hmass n)
  have hmne (n : ℕ) : μ n ≠ 0 := (μ n).mass_nonzero_iff.mp (hmpos n).ne'
  let νs : ℕ → ProbabilityMeasure ℂ := fun n => (μ n).normalize
  have hνK (n : ℕ) : νs n ∈ {ν : ProbabilityMeasure ℂ | ν Kᶜ = 0} := by
    change (μ n).normalize Kᶜ = 0
    rw [(μ n).normalize_eq_of_nonzero (hmne n), hKsupport n, mul_zero]
  obtain ⟨ν, _hνK, φ, hφ, hlim⟩ :=
    (normalized_supported_probability_compact hK).tendsto_subseq hνK
  have hνcarrier (n : ℕ) :
      ((νs ∘ φ) n : Measure ℂ) (Metric.cthickening ((e ∘ φ) n) E)ᶜ = 0 := by
    change ((μ (φ n)).normalize : Measure ℂ) (Metric.cthickening (e (φ n)) E)ᶜ = 0
    rw [(μ (φ n)).toMeasure_normalize_eq_of_nonzero (hmne (φ n)),
      Measure.coe_nnreal_smul_apply, hcarrier (φ n), mul_zero]
  have hνE : (ν : Measure ℂ) E = 1 :=
    (prob_compl_eq_zero_iff hE.measurableSet).mp
      (probability_limit_shrinking_carriers hlim hE (e ∘ φ)
        (he.comp hφ.tendsto_atTop) hνcarrier)
  have hνball (x : ℂ) (r : ℝ) (hr : 0 < r) (hrρ : r < ρ) :
      (ν : Measure ℂ) (Metric.ball x r) ≤ (↑(C / a) : ℝ≥0∞) * ENNReal.ofReal (h r) := by
    apply probability_limit_ball_bound hlim
    filter_upwards [hφ.tendsto_atTop.eventually (hball x r hr hrρ)] with n hn
    change ((μ (φ n)).normalize : Measure ℂ) (Metric.ball x r) ≤ _
    rw [(μ (φ n)).toMeasure_normalize_eq_of_nonzero (hmne (φ n)),
      Measure.coe_nnreal_smul_apply]
    have hfactor : (↑((μ (φ n)).mass⁻¹) : ℝ≥0∞) ≤ (↑(a⁻¹) : ℝ≥0∞) := by
      rw [ENNReal.coe_inv (hmpos (φ n)).ne', ENNReal.coe_inv ha.ne']
      exact ENNReal.inv_le_inv.mpr (ENNReal.coe_le_coe.mpr (hmass (φ n)))
    calc
      (↑((μ (φ n)).mass⁻¹) : ℝ≥0∞) * (μ (φ n) : Measure ℂ) (Metric.ball x r)
          ≤ (↑(a⁻¹) : ℝ≥0∞) * ((C : ℝ≥0∞) * ENNReal.ofReal (h r)) :=
        mul_le_mul' hfactor hn
      _ = (↑(C / a) : ℝ≥0∞) * ENNReal.ofReal (h r) := by
        rw [div_eq_mul_inv, ENNReal.coe_mul]
        ac_rfl
  have hdom := gauge_mass_distribution hh (ν : Measure ℂ) (C / a)
    (div_pos hC ha) ρ hρ hνball
  by_contra hn
  have hz : hausdorffGauge h E = 0 := le_antisymm (le_of_not_gt hn) bot_le
  have hbound := Measure.le_iff'.mp hdom E
  simp only [hνE, Measure.smul_apply, hz, smul_eq_mul, mul_zero, not_le_of_gt zero_lt_one]
    at hbound

 
theorem retained_compact_mass_lower_bound_of_frequently
    {h : ℝ → ℝ} (hh : IsGauge h) {K E : Set ℂ}
    (hK : IsCompact K) (hE : IsClosed E)
    (μ : ℕ → FiniteMeasure ℂ) (a C : ℝ≥0) (ha : 0 < a) (hC : 0 < C)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hmass : ∃ᶠ n in atTop, a ≤ (μ n).mass)
    (hKsupport : ∀ n, μ n Kᶜ = 0)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hcarrier : ∀ n, (μ n : Measure ℂ) (Metric.cthickening (e n) E)ᶜ = 0)
    (hball : ∀ x r, 0 < r → r < ρ →
      ∀ᶠ n in atTop, (μ n : Measure ℂ) (Metric.ball x r) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (h r)) :
    0 < hausdorffGauge h E := by

  obtain ⟨φ, hφ, hm⟩ := Filter.subseq_forall_of_frequently (p := fun n : ℕ => a ≤ (μ n).mass)
    (x := id) tendsto_id hmass
  apply retained_compact_mass_lower_bound hh hK hE (μ ∘ φ) a C ha hC ρ hρ hm
    (fun n => hKsupport (φ n)) (e ∘ φ) (he.comp hφ) (fun n => hcarrier (φ n))
  intro x r hr hrρ
  exact hφ.eventually (hball x r hr hrρ)

lemma source_gauge_bounded_scaling (κ : ℝ) (_hκ : 0 < κ) (hκ8 : κ < 8)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    (L : ℝ) (hL : 1 ≤ L) :
    ∃ a : ℝ, 0 < a ∧ ∀ r : ℝ, 0 ≤ r → r ≤ a →
      h (L * r) ≤ L ^ dimension κ * h r := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨δ, hδ, hδf⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hf
  change 0 < δ at hδ
  let a := min δ (Real.exp (-1)) / (2 * L)
  have ha : 0 < a := div_pos (lt_min hδ (Real.exp_pos _)) (by positivity)
  refine ⟨a, ha, fun r hr hra => ?_⟩
  rcases hr.eq_or_lt with rfl | hr
  · simp [hh.zero]
  have hR : L * r ≤ min δ (Real.exp (-1)) / 2 := by
    have := (le_div_iff₀ (show 0 < 2 * L by positivity)).mp hra
    nlinarith
  have hRδ : L * r < δ := by
    have := min_le_left δ (Real.exp (-1))
    linarith
  have hRe : L * r ≤ Real.exp (-1) := by
    have := min_le_right δ (Real.exp (-1))
    have := Real.exp_pos (-1)
    linarith
  have hrR : r ≤ L * r := by nlinarith
  have hRpos : 0 < L * r := mul_pos hLp hr
  have hlog : 1 ≤ Real.log (1 / (L * r)) := by
    have := Real.log_le_log hRpos hRe
    rw [Real.log_exp] at this
    rw [one_div, Real.log_inv]
    linarith
  have hlogle : Real.log (1 / (L * r)) ≤ Real.log (1 / r) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le hr hrR)
  have hll0 : 0 ≤ Real.log (Real.log (1 / (L * r))) :=
    Real.log_nonneg hlog
  have hllle := Real.log_le_log (by linarith : 0 < Real.log (1 / (L * r))) hlogle
  have hp : 0 ≤ codimension κ / 2 := by dsimp [codimension, dimension]; linarith
  rw [hδf ⟨hRpos, hRδ⟩, hδf ⟨hr, hrR.trans_lt hRδ⟩]
  dsimp [hFormula]
  rw [Real.mul_rpow hLp.le hr.le, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hll0 hllle hp)
      (Real.rpow_nonneg hr.le _)) (Real.rpow_nonneg hLp.le _)

noncomputable def retainedBallSquares (k : ℕ) (x : ℂ) : Finset (ℤ × ℤ) :=
  (Finset.Icc ((retainedDyadicAddress k x).1 - 1) ((retainedDyadicAddress k x).1 + 1)).product
    (Finset.Icc ((retainedDyadicAddress k x).2 - 1) ((retainedDyadicAddress k x).2 + 1))

lemma retainedBallSquares_card (k : ℕ) (x : ℂ) :
    (retainedBallSquares k x).card = 9 := by
  have hc (a : ℤ) : (Finset.Icc (a-1) (a+1)).card = 3 := by
    rw [Int.card_Icc]
    have he : a+1+1-(a-1) = 3 := by ring
    rw [he]
    rfl
  simp [retainedBallSquares, Finset.card_product, hc]

lemma retainedBallSquares_cover (k : ℕ) (x : ℂ) (r : ℝ)
    (hr : r ≤ (1/2:ℝ)^k) :
    Metric.ball x r ⊆ ⋃ ij ∈ (retainedBallSquares k x : Set (ℤ × ℤ)),
      retainedDyadicSquare k ij := by
  intro z hz
  have hdist : ‖z-x‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hs : (2:ℝ)^k * r ≤ 1 := by
    calc
      (2:ℝ)^k*r ≤ (2:ℝ)^k*(1/2:ℝ)^k := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = 1 := by rw [← mul_pow]; norm_num
  have bound (a b : ℝ) (hb : |b-a| < r) :
      ⌊(2:ℝ)^k*a⌋ - 1 ≤ ⌊(2:ℝ)^k*b⌋ ∧
      ⌊(2:ℝ)^k*b⌋ ≤ ⌊(2:ℝ)^k*a⌋ + 1 := by
    have hb1 := mul_lt_mul_of_pos_left (abs_lt.mp hb).1 (by positivity : 0 < (2:ℝ)^k)
    have hb2 := mul_lt_mul_of_pos_left (abs_lt.mp hb).2 (by positivity : 0 < (2:ℝ)^k)
    have hf1 := Int.floor_le ((2:ℝ)^k*a)
    have hf2 := Int.lt_floor_add_one ((2:ℝ)^k*a)
    constructor
    · apply Int.le_floor.mpr
      push_cast
      nlinarith
    · apply Int.floor_le_iff.mpr
      push_cast
      nlinarith
  have hre : |z.re-x.re| < r := by
    exact (Complex.abs_re_le_norm (z-x)).trans_lt hdist
  have him : |z.im-x.im| < r := by
    exact (Complex.abs_im_le_norm (z-x)).trans_lt hdist
  refine mem_iUnion.mpr ⟨retainedDyadicAddress k z, mem_iUnion.mpr ⟨?_, retainedSquare_address k z⟩⟩
  change (⌊(2:ℝ)^k*z.re⌋, ⌊(2:ℝ)^k*z.im⌋) ∈
    (Finset.Icc (⌊(2:ℝ)^k*x.re⌋ - 1) (⌊(2:ℝ)^k*x.re⌋ + 1)) ×ˢ
    (Finset.Icc (⌊(2:ℝ)^k*x.im⌋ - 1) (⌊(2:ℝ)^k*x.im⌋ + 1))
  simpa only [Finset.mem_product, Finset.mem_Icc] using And.intro (bound _ _ hre) (bound _ _ him)

lemma retained_dyadic_ball_bound (μ : Measure ℂ) (k : ℕ) (b : ℝ≥0∞)
    (hb : ∀ ij, μ (retainedDyadicSquare k ij) ≤ b) (x : ℂ) (r : ℝ)
    (hr : r ≤ (1/2:ℝ)^k) : μ (Metric.ball x r) ≤ 9*b := by
  calc
    μ (Metric.ball x r) ≤ μ (⋃ ij ∈ (retainedBallSquares k x : Set (ℤ×ℤ)),
        retainedDyadicSquare k ij) := measure_mono (retainedBallSquares_cover k x r hr)
    _ ≤ ∑ ij ∈ retainedBallSquares k x, μ (retainedDyadicSquare k ij) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ ij ∈ retainedBallSquares k x, b := Finset.sum_le_sum (fun _ _ => hb _)
    _ = 9*b := by simp [retainedBallSquares_card, nsmul_eq_mul]

lemma dyadic_side_rpow (k : ℕ) : (2:ℝ)^(-(k:ℝ)) = (1/2:ℝ)^k := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ← inv_pow]
  norm_num

lemma dyadic_side_loglog (k : ℕ) (hk : 0 < k) :
    Real.log (Real.log (1 / ((1/2:ℝ)^k))) =
      Real.log (k:ℝ) + Real.log (Real.log 2) := by
  have he : 1 / ((1/2:ℝ)^k) = (2:ℝ)^k := by
    rw [one_div, ← inv_pow]
    norm_num
  rw [he, Real.log_pow, Real.log_mul (by exact_mod_cast hk.ne')
    (Real.log_pos (by norm_num : (1:ℝ)<2)).ne']

lemma retained_threshold_gauge_eventually (κ : ℝ) (hκ8 : κ < 8)
    (h : ℝ → ℝ) (hf : HasSmallRadiusFormula h (hFormula κ))
    (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ k : ℕ in atTop, retainedThreshold κ D k ≤
      D * (2:ℝ)^(codimension κ/2) * h ((1/2:ℝ)^k) := by
  have ht : Tendsto (fun k : ℕ => (1/2:ℝ)^k) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num),
      Eventually.of_forall (fun k => by change 0 < (1/2:ℝ)^k; positivity)⟩
  have hform : ∀ᶠ k : ℕ in atTop, h ((1/2:ℝ)^k) = hFormula κ ((1/2:ℝ)^k) :=
    ht.eventually hf
  have hlog : Tendsto (fun k : ℕ => Real.log (k:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hform, hlog.eventually_ge_atTop (max 0 (-2*Real.log (Real.log 2))),
    eventually_ge_atTop 1] with k hkf hkl hk1
  have hla : 0 ≤ Real.log (k:ℝ) := (le_max_left _ _).trans hkl
  have hlb : -2*Real.log (Real.log 2) ≤ Real.log (k:ℝ) := (le_max_right _ _).trans hkl
  have hll := dyadic_side_loglog k (by omega)
  have hll0 : 0 ≤ Real.log (Real.log (1 / ((1/2:ℝ)^k))) := by rw [hll]; linarith
  have hle : Real.log (k:ℝ) ≤ 2 * Real.log (Real.log (1 / ((1/2:ℝ)^k))) := by
    rw [hll]; linarith
  have hp : 0 ≤ codimension κ / 2 := by dsimp [codimension, dimension]; linarith
  unfold retainedThreshold
  rw [dyadic_side_rpow]
  calc
    D * ((1/2:ℝ)^k)^dimension κ * (Real.log (k:ℝ))^(codimension κ/2)
      ≤ D * ((1/2:ℝ)^k)^dimension κ *
          (2 * Real.log (Real.log (1 / ((1/2:ℝ)^k))))^(codimension κ/2) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hla hle hp)
          (mul_nonneg hD (Real.rpow_nonneg (by positivity) _))
    _ = D * (2:ℝ)^(codimension κ/2) * h ((1/2:ℝ)^k) := by
      rw [Real.mul_rpow (by norm_num) hll0, hkf]
      dsimp [hFormula]
      ring

theorem sourceRetainedDyadic_proved : SourceRetainedDyadicTarget := by
  intro κ hκ hκ8 h hh hf K E hK hE μ a ha hmass hKsupport e he hcarrier D hD k₀ htest
  obtain ⟨b, hb, hscale⟩ := source_gauge_bounded_scaling κ hκ hκ8 h hh hf 2 (by norm_num)
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp
    (retained_threshold_gauge_eventually κ hκ8 h hf D hD.le)
  let J := max k₀ k₁
  let ρ : ℝ := min 1 (min b ((1/2:ℝ)^J/2))
  have hρ : 0 < ρ := lt_min (by norm_num) (lt_min hb (by positivity))
  let C : ℝ≥0 := ⟨9 * D * (2:ℝ)^(codimension κ/2) * (2:ℝ)^dimension κ, by positivity⟩
  have hC : 0 < C := by change 0 < 9 * D * (2:ℝ)^(codimension κ/2) * (2:ℝ)^dimension κ; positivity
  apply retained_compact_mass_lower_bound_of_frequently hh hK hE μ a C ha hC ρ hρ
    hmass hKsupport e he hcarrier
  intro x r hr hrρ
  have hr1 : r ≤ 1 := hrρ.le.trans (min_le_left _ _)
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near_of_lt_one hr hr1
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  have hside : (1/2:ℝ)^k < 2*r := by rw [pow_succ] at hklo; linarith
  have hrJ : 2*r < (1/2:ℝ)^J := by
    have hv : r < (1/2:ℝ)^J/2 := hrρ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hJk : J ≤ k := (pow_lt_pow_iff_right_of_lt_one₀
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)).mp (hside.trans hrJ) |>.le
  have hbound : retainedThreshold κ D k ≤
      D * (2:ℝ)^(codimension κ/2) * (2:ℝ)^dimension κ * h r := by
    have hmono : h ((1/2:ℝ)^k) ≤ h (2*r) :=
      hh.monotoneOn (show 0 ≤ (1/2:ℝ)^k by positivity)
        (show 0 ≤ 2*r by positivity) hside.le
    have hrb : r ≤ b := hrρ.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    calc
      retainedThreshold κ D k ≤ D * (2:ℝ)^(codimension κ/2) * h ((1/2:ℝ)^k) :=
        hk₁ k ((le_max_right _ _).trans hJk)
      _ ≤ D * (2:ℝ)^(codimension κ/2) * ((2:ℝ)^dimension κ * h r) :=
        mul_le_mul_of_nonneg_left (hmono.trans (hscale r hr.le hrb)) (by positivity)
      _ = _ := by ring
  filter_upwards [eventually_ge_atTop k] with N hN
  calc
    (μ N : Measure ℂ) (Metric.ball x r) ≤ 9 * ENNReal.ofReal (retainedThreshold κ D k) :=
      retained_dyadic_ball_bound (μ N) k _ (by
        simpa only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
          htest N k ((le_max_left _ _).trans hJk) hN) x r hkhi
    _ = ENNReal.ofReal (9 * retainedThreshold κ D k) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤9)]
      norm_num
    _ ≤ ENNReal.ofReal ((C:ℝ)*h r) := by
      apply ENNReal.ofReal_le_ofReal
      change 9 * retainedThreshold κ D k ≤
        (9 * D * (2:ℝ)^(codimension κ/2) * (2:ℝ)^dimension κ) * h r
      calc
        9 * retainedThreshold κ D k ≤ 9 * (D * (2:ℝ)^(codimension κ/2) * (2:ℝ)^dimension κ * h r) :=
          mul_le_mul_of_nonneg_left hbound (by norm_num)
        _ = _ := by ring
    _ = (C:ℝ≥0∞) * ENNReal.ofReal (h r) := by
      rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]

end SLEExactGauge
end
end

end OAI
