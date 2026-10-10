import Mathlib

namespace OAI

 

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology ContDiff

namespace CoulombAtoms

 
abbrev Position := EuclideanSpace ℝ (Fin 3)

 
abbrev Configuration (n : ℕ) := Fin n → Position

 
abbrev SpinConfiguration (n : ℕ) := Fin n → Fin 2

abbrev WaveFunction (n : ℕ) := SpinConfiguration n → Configuration n → ℂ

 
def coordinateVector {n : ℕ} (i : Fin n) (a : Fin 3) : Configuration n :=
  fun j => if j = i then EuclideanSpace.single a 1 else 0

 
def permutationSign {n : ℕ} (π : Equiv.Perm (Fin n)) : ℂ :=
  ((Equiv.Perm.sign π : ℤˣ) : ℤ)

 

structure FormState (n : ℕ) where
  wave : WaveFunction n
  deriv : SpinConfiguration n → Fin n → Fin 3 → Configuration n → ℂ
  wave_memLp : ∀ σ, MemLp (wave σ) 2 volume
  deriv_memLp : ∀ σ i a, MemLp (deriv σ i a) 2 volume
  weak_deriv : ∀ σ i a (φ : Configuration n → ℝ),
    ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, (φ x : ℂ) * deriv σ i a x) =
      -(∫ x, ((fderiv ℝ φ x (coordinateVector i a)) : ℂ) * wave σ x)
  antisymmetric : ∀ (π : Equiv.Perm (Fin n)) σ,
    ∀ᵐ x ∂volume,
      wave (σ ∘ π) (x ∘ π) = permutationSign π * wave σ x

 
def normSq {n : ℕ} (ψ : FormState n) : ℝ :=
  ∑ σ : SpinConfiguration n, ∫ x, ‖ψ.wave σ x‖ ^ 2

 
def kineticEnergy {n : ℕ} (ψ : FormState n) : ℝ :=
  (1 / 2 : ℝ) * ∑ σ : SpinConfiguration n, ∑ i : Fin n, ∑ a : Fin 3,
    ∫ x, ‖ψ.deriv σ i a x‖ ^ 2

 

def nuclearPotential {n : ℕ} (Z : ℝ) (x : Configuration n) : ℝ :=
  ∑ i : Fin n, Z / ‖x i‖

 
def pairPotential {n : ℕ} (x : Configuration n) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
    ‖x i - x j‖⁻¹

 
def atomicCoulombForm {n : ℕ} (Z : ℝ) (ψ : FormState n) : ℝ :=
  kineticEnergy ψ -
    (∑ σ : SpinConfiguration n, ∫ x, nuclearPotential Z x * ‖ψ.wave σ x‖ ^ 2) +
    (∑ σ : SpinConfiguration n, ∫ x, pairPotential x * ‖ψ.wave σ x‖ ^ 2)

 

def IsNormalizedGroundState {n : ℕ} (Z : ℝ) (ψ : FormState n) : Prop :=
  normSq ψ = 1 ∧
  ∀ φ : FormState n, normSq φ = 1 → atomicCoulombForm Z ψ ≤ atomicCoulombForm Z φ

 

def density : {n : ℕ} → FormState n → Position → ℝ
  | 0, _, _ => 0
  | n + 1, ψ, x =>
      (n + 1 : ℝ) * ∑ σ : SpinConfiguration (n + 1),
        ∫ y : Configuration n, ‖ψ.wave σ (Fin.cons x y)‖ ^ 2

 
def exteriorMass (ρ : Position → ℝ) (r : ℝ) : ℝ :=
  ∫ x in {x : Position | r < ‖x‖}, ρ x

 
def halfElectronRadius (ρ : Position → ℝ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ exteriorMass ρ r ≤ (1 / 2 : ℝ)}

def outerRadius {n : ℕ} (ψ : FormState n) : ℝ :=
  halfElectronRadius (density ψ)

 

lemma integrable_cons {n : ℕ} {f : Configuration (n + 1) → ℝ}
    (hf : Integrable f) :
    Integrable (fun p : Position × Configuration n => f (Fin.cons p.1 p.2)) := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => Position) 0).symm
  have h := (hp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hf
  simpa [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove] using h

lemma integral_cons {n : ℕ} {f : Configuration (n + 1) → ℝ}
    (hf : Integrable f) :
    (∫ x : Position, ∫ y : Configuration n, f (Fin.cons x y)) = ∫ z, f z := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => Position) 0).symm
  have he := hp.integral_comp' f
  have hprod := integral_prod _ (integrable_cons hf)
  rw [← hprod]
  simpa [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove, Measure.volume_eq_prod] using he

lemma density_one (ψ : FormState 1) (x : Position) :
    density ψ x = ∑ σ : SpinConfiguration 1, ‖ψ.wave σ (fun _ => x)‖ ^ 2 := by
  have hm : volume.real (Set.univ : Set (Configuration 0)) = 1 := by
    simp [measureReal_def, Configuration, volume_pi]
  simp only [density, Nat.cast_zero, zero_add, one_mul]
  apply Finset.sum_congr rfl
  intro σ _
  rw [integral_unique, hm, one_smul]
  congr 3
  funext i
  fin_cases i
  rfl

lemma density_nonneg {n : ℕ} (ψ : FormState n) (x : Position) : 0 ≤ density ψ x := by
  cases n with
  | zero => exact le_refl _
  | succ n =>
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun σ _ => integral_nonneg fun y => sq_nonneg _)

lemma density_integrable {n : ℕ} (ψ : FormState n) : Integrable (density ψ) := by
  cases n with
  | zero => exact integrable_zero Position ℝ volume
  | succ n =>
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro σ _
    exact (integrable_cons ((ψ.wave_memLp σ).integrable_norm_pow (by norm_num : 2 ≠ 0))).integral_prod_left

lemma integral_density {n : ℕ} (ψ : FormState n) : (∫ x, density ψ x) = (n : ℝ) * normSq ψ := by
  cases n with
  | zero => simp [density]
  | succ n =>
    simp only [density]
    rw [integral_const_mul, integral_finsetSum]
    · simp_rw [integral_cons ((ψ.wave_memLp _).integrable_norm_pow (by norm_num : 2 ≠ 0))]
      simp [normSq]
    · intro σ _
      exact (integrable_cons ((ψ.wave_memLp σ).integrable_norm_pow (by norm_num : 2 ≠ 0))).integral_prod_left

lemma integral_density_of_normalized {n : ℕ} (ψ : FormState n) (hψ : normSq ψ = 1) :
    (∫ x, density ψ x) = n := by
  rw [integral_density, hψ, mul_one]

 

lemma measurableSet_exterior (r : ℝ) : MeasurableSet {x : Position | r < ‖x‖} :=
  (isOpen_lt continuous_const continuous_norm).measurableSet

lemma exteriorMass_nonneg {ρ : Position → ℝ} (hρ : ∀ x, 0 ≤ ρ x) (r : ℝ) :
    0 ≤ exteriorMass ρ r :=
  integral_nonneg hρ

lemma exteriorMass_antitone {ρ : Position → ℝ} (hρ : Integrable ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) : Antitone (exteriorMass ρ) := by
  intro r s hrs
  apply setIntegral_mono_set hρ.integrableOn
  · exact Filter.Eventually.of_forall hρ₀
  · exact Filter.Eventually.of_forall (fun x hx => lt_of_le_of_lt hrs hx)

lemma halfElectronRadius_le {ρ : Position → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hTail : exteriorMass ρ R ≤ (1 / 2 : ℝ)) :
    halfElectronRadius ρ ≤ R :=
  csInf_le ⟨0, fun _ hr => hr.1⟩ ⟨hR, hTail⟩

 
lemma halfElectronRadius_bounds_of_tails {ρ : Position → ℝ}
    (hρ : Integrable ρ) (hρ₀ : ∀ x, 0 ≤ ρ x) {c R : ℝ}
    (hR : 0 ≤ R) (hc : (1 / 2 : ℝ) < exteriorMass ρ c)
    (hTail : exteriorMass ρ R ≤ (1 / 2 : ℝ)) :
    c ≤ halfElectronRadius ρ ∧ halfElectronRadius ρ ≤ R := by
  refine ⟨le_csInf ⟨R, hR, hTail⟩ ?_, halfElectronRadius_le hR hTail⟩
  intro r hr
  by_contra! hcr
  exact (not_le_of_gt hc) (((exteriorMass_antitone hρ hρ₀) hcr.le).trans hr.2)

 
lemma norm_ne_ae (r : ℝ) : ∀ᵐ x : Position, ‖x‖ ≠ r := by
  rw [ae_iff]
  simpa [Metric.sphere, dist_zero_right] using
    (Measure.addHaar_sphere (volume : Measure Position) 0 r)

 

lemma exteriorMass_eq_ge (ρ : Position → ℝ) (r : ℝ) :
    exteriorMass ρ r = ∫ x in {x : Position | r ≤ ‖x‖}, ρ x := by
  apply setIntegral_congr_set
  filter_upwards [norm_ne_ae r] with x hx
  exact propext ⟨le_of_lt, fun h => lt_of_le_of_ne h (Ne.symm hx)⟩

lemma exteriorMass_zero (ρ : Position → ℝ) : exteriorMass ρ 0 = ∫ x, ρ x := by
  rw [exteriorMass, ← integral_indicator (measurableSet_exterior 0)]
  apply integral_congr_ae
  filter_upwards [norm_ne_ae 0] with x hx
  apply Set.indicator_of_mem
  exact lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)

lemma norm_exterior_indicator_le (ρ : Position → ℝ) (r : ℝ) (x : Position) :
    ‖({x : Position | r < ‖x‖}.indicator ρ) x‖ ≤ ‖ρ x‖ := by
  by_cases hx : r < ‖x‖
  · simp [Set.indicator, hx]
  · simp [Set.indicator, hx]

lemma exteriorMass_tendsto_zero {ρ : Position → ℝ} (hρ : Integrable ρ) :
    Tendsto (exteriorMass ρ) atTop (𝓝 0) := by
  change Tendsto (fun r => ∫ x in {x : Position | r < ‖x‖}, ρ x) atTop (𝓝 0)
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure Position)) (l := (atTop : Filter ℝ))
    (F := fun r => {x : Position | r < ‖x‖}.indicator ρ) (f := fun _ => (0 : ℝ))
    (fun x => ‖ρ x‖)
    (Filter.Eventually.of_forall fun r =>
      hρ.aestronglyMeasurable.indicator (measurableSet_exterior r))
    (Filter.Eventually.of_forall fun r => Filter.Eventually.of_forall fun x =>
      norm_exterior_indicator_le ρ r x) hρ.norm ?_
  · simpa only [integral_indicator (measurableSet_exterior _), integral_zero, exteriorMass] using h
  · exact Filter.Eventually.of_forall fun x =>
      tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop ‖x‖] with r hr
        simp [Set.indicator, not_lt.mpr hr])

lemma exteriorMass_continuous {ρ : Position → ℝ} (hρ : Integrable ρ) :
    Continuous (exteriorMass ρ) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  change Tendsto (fun s => ∫ x in {x : Position | s < ‖x‖}, ρ x) (𝓝 r)
    (𝓝 (∫ x in {x : Position | r < ‖x‖}, ρ x))
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure Position)) (l := 𝓝 r)
    (F := fun s => {x : Position | s < ‖x‖}.indicator ρ)
    (f := {x : Position | r < ‖x‖}.indicator ρ)
    (fun x => ‖ρ x‖)
    (Filter.Eventually.of_forall fun s =>
      hρ.aestronglyMeasurable.indicator (measurableSet_exterior s))
    (Filter.Eventually.of_forall fun s => Filter.Eventually.of_forall fun x =>
      norm_exterior_indicator_le ρ s x) hρ.norm ?_
  · simpa only [integral_indicator (measurableSet_exterior _), exteriorMass] using h
  · filter_upwards [norm_ne_ae r] with x hx
    rcases lt_or_gt_of_ne hx with hxr | hrx
    · have hnot : ¬ r < ‖x‖ := not_lt.mpr hxr.le
      simp only [Set.indicator, Set.mem_ofPred_eq, ite_eq_right hnot]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_nhds hxr] with s hs
      simp [not_lt.mpr hs.le]
    · simp only [Set.indicator, Set.mem_ofPred_eq, ite_eq_left hrx]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_lt_nhds hrx] with s hs
      simp [hs]

lemma exists_exteriorMass_le_half {ρ : Position → ℝ} (hρ : Integrable ρ) :
    ∃ R : ℝ, 0 ≤ R ∧ exteriorMass ρ R ≤ (1 / 2 : ℝ) := by
  have h := (exteriorMass_tendsto_zero hρ).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨R, hR, ht⟩ := ((eventually_ge_atTop (0 : ℝ)).and h).exists
  exact ⟨R, hR, ht.le⟩

lemma exists_pos_exteriorMass_gt_half {ρ : Position → ℝ} (hρ : Integrable ρ)
    (hm : (1 / 2 : ℝ) < ∫ x, ρ x) :
    ∃ c : ℝ, 0 < c ∧ (1 / 2 : ℝ) < exteriorMass ρ c := by
  have h0 : (1 / 2 : ℝ) < exteriorMass ρ 0 := by rwa [exteriorMass_zero]
  have h := (exteriorMass_continuous hρ).continuousAt.eventually (eventually_gt_nhds h0)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨ε / 2, half_pos hε, hball ?_⟩
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
  linarith

 

lemma halfElectronRadius_pos {ρ : Position → ℝ} (hρ : Integrable ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) (hm : (1 / 2 : ℝ) < ∫ x, ρ x) :
    0 < halfElectronRadius ρ := by
  obtain ⟨R, hR, hTail⟩ := exists_exteriorMass_le_half hρ
  obtain ⟨c, hc, hcTail⟩ := exists_pos_exteriorMass_gt_half hρ hm
  exact hc.trans_le (halfElectronRadius_bounds_of_tails hρ hρ₀ hR hcTail hTail).1

 

lemma outerRadius_pos {n : ℕ} (hn : 1 ≤ n) (ψ : FormState n) (hψ : normSq ψ = 1) :
    0 < outerRadius ψ := by
  apply halfElectronRadius_pos (density_integrable ψ) (density_nonneg ψ)
  rw [integral_density_of_normalized ψ hψ]
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

 
lemma halfElectronRadius_mem {ρ : Position → ℝ} (hρ : Integrable ρ) :
    0 ≤ halfElectronRadius ρ ∧ exteriorMass ρ (halfElectronRadius ρ) ≤ (1 / 2 : ℝ) := by
  have hc : IsClosed {r : ℝ | 0 ≤ r ∧ exteriorMass ρ r ≤ (1 / 2 : ℝ)} :=
    isClosed_Ici.inter (isClosed_le (exteriorMass_continuous hρ) continuous_const)
  exact hc.csInf_mem (exists_exteriorMass_le_half hρ) ⟨0, fun _ hr => hr.1⟩

lemma halfElectronRadius_le_iff {ρ : Position → ℝ} (hρ : Integrable ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) {r : ℝ} (hr : 0 ≤ r) :
    halfElectronRadius ρ ≤ r ↔ exteriorMass ρ r ≤ (1 / 2 : ℝ) := by
  constructor
  · intro h
    exact ((exteriorMass_antitone hρ hρ₀) h).trans (halfElectronRadius_mem hρ).2
  · exact halfElectronRadius_le hr

lemma lt_halfElectronRadius_iff {ρ : Position → ℝ} (hρ : Integrable ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) {r : ℝ} (hr : 0 ≤ r) :
    r < halfElectronRadius ρ ↔ (1 / 2 : ℝ) < exteriorMass ρ r := by
  rw [← not_le, halfElectronRadius_le_iff hρ hρ₀ hr, not_le]

 

lemma exteriorMass_halfElectronRadius {ρ : Position → ℝ} (hρ : Integrable ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) (hm : (1 / 2 : ℝ) < ∫ x, ρ x) :
    exteriorMass ρ (halfElectronRadius ρ) = (1 / 2 : ℝ) := by
  apply le_antisymm (halfElectronRadius_mem hρ).2
  by_contra! hlt
  have hpos := halfElectronRadius_pos hρ hρ₀ hm
  have hneigh : ∀ᶠ r in 𝓝 (halfElectronRadius ρ),
      0 < r ∧ exteriorMass ρ r < (1 / 2 : ℝ) :=
    (eventually_gt_nhds hpos).and
      ((exteriorMass_continuous hρ).continuousAt.eventually (eventually_lt_nhds hlt))
  have hleft : ∀ᶠ r in 𝓝[Set.Iio (halfElectronRadius ρ)] (halfElectronRadius ρ),
      0 < r ∧ exteriorMass ρ r < (1 / 2 : ℝ) :=
    hneigh.filter_mono nhdsWithin_le_nhds
  have hltleft : ∀ᶠ r in 𝓝[Set.Iio (halfElectronRadius ρ)] (halfElectronRadius ρ),
      r < halfElectronRadius ρ := self_mem_nhdsWithin
  obtain ⟨r, ⟨hr, ht⟩, hrlt⟩ := (hleft.and hltleft).exists
  exact (not_le_of_gt hrlt) (halfElectronRadius_le hr.le ht.le)

lemma exteriorMass_outerRadius {n : ℕ} (hn : 1 ≤ n) (ψ : FormState n)
    (hψ : normSq ψ = 1) : exteriorMass (density ψ) (outerRadius ψ) = (1 / 2 : ℝ) := by
  apply exteriorMass_halfElectronRadius (density_integrable ψ) (density_nonneg ψ)
  rw [integral_density_of_normalized ψ hψ]
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

 

lemma halfElectronRadius_bounds_of_compact_family {ι : Type*}
    [TopologicalSpace ι] [CompactSpace ι] (ρ : ι → Position → ℝ)
    (hInt : ∀ i, Integrable (ρ i)) (hNonneg : ∀ i x, 0 ≤ ρ i x)
    (hMass : ∀ i, (1 / 2 : ℝ) < ∫ x, ρ i x)
    (hCont : ∀ r, Continuous (fun i => exteriorMass (ρ i) r)) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ i, c ≤ halfElectronRadius (ρ i) ∧ halfElectronRadius (ρ i) ≤ C := by
  classical
  by_cases hne : Nonempty ι
  · have hlocal : ∀ i, ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
        (1 / 2 : ℝ) < exteriorMass (ρ i) c ∧ exteriorMass (ρ i) C < (1 / 2 : ℝ) := by
      intro i
      obtain ⟨c, hc, ht⟩ := exists_pos_exteriorMass_gt_half (hInt i) (hMass i)
      have hlim := (exteriorMass_tendsto_zero (hInt i)).eventually_lt_const
        (by norm_num : (0 : ℝ) < 1 / 2)
      obtain ⟨C, hC, hTail⟩ := ((eventually_ge_atTop (0 : ℝ)).and hlim).exists
      exact ⟨c, C, hc, hC, ht, hTail⟩
    choose c C hc hC hlow hupp using hlocal
    let U : ι → Set ι := fun i => {j | (1 / 2 : ℝ) < exteriorMass (ρ j) (c i) ∧
      exteriorMass (ρ j) (C i) < (1 / 2 : ℝ)}
    have hU : ∀ i, IsOpen (U i) := fun i =>
      (isOpen_lt continuous_const (hCont (c i))).inter
        (isOpen_lt (hCont (C i)) continuous_const)
    obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover U hU (by
      intro i _
      exact Set.mem_iUnion.mpr ⟨i, hlow i, hupp i⟩)
    have hIne : I.Nonempty := by
      obtain ⟨i⟩ := hne
      obtain ⟨j, hj, _⟩ := Set.mem_iUnion₂.mp (hI (Set.mem_univ i))
      exact ⟨j, hj⟩
    refine ⟨I.inf' hIne c, max (I.inf' hIne c) (I.sup' hIne C), ?_, le_max_left _ _, ?_⟩
    · exact (Finset.lt_inf'_iff hIne).mpr (fun i _ => hc i)
    · intro i
      obtain ⟨j, hj, hlj, huj⟩ := Set.mem_iUnion₂.mp (hI (Set.mem_univ i))
      have hb := halfElectronRadius_bounds_of_tails (hInt i) (hNonneg i) (hC j) hlj huj.le
      exact ⟨(Finset.inf'_le c hj).trans hb.1,
        hb.2.trans ((Finset.le_sup' C hj).trans (le_max_right _ _))⟩
  · exact ⟨1, 1, by norm_num, le_rfl, fun i => (hne ⟨i⟩).elim⟩

end CoulombAtoms

end

end OAI
