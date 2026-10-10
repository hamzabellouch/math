import OAI.Analysis.IrrationalRotation.Model.CircleSamplingStage
import OAI.Analysis.IrrationalRotation.Analysis.FrequencyTower
import OAI.Analysis.IrrationalRotation.Sampling.SamplingHorizon
import OAI.Analysis.IrrationalRotation.Analysis.LaurentNoncancellation
import OAI.Analysis.IrrationalRotation.Analysis.OrbitPartition
import OAI.Analysis.IrrationalRotation.Rotation.CircleParameterBlocks
import OAI.Analysis.IrrationalRotation.Sampling.PhaseRanges

namespace OAI

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Invariant233.CircleParameterRecursion
open PrescribedPhaseRealization SamplingHorizon FiniteWindow

private structure State where
  K : ℕ
  G : ℕ
  d : ℕ
  q : ℕ → ℕ
  cost : ℝ
  previousL : ℝ
  previousN : ℝ
  K_pos : 0 < K
  G_pos : 0 < G
  q_zero : q 0 = 1
  q_pos : ∀ i ≤ d, 0 < q i
  q_mono : ∀ i < d, q i < q (i + 1)
  q_div : ∀ i < d, q i ∣ q (i + 1)

private structure Step (θ : ℝ) (height : ℕ → ℕ) (n : ℕ) (s : State) where
  m : ℕ
  Gnext : ℕ
  L : ℝ
  ε : ℝ
  epsilon_pos : 0 < ε
  L_one : 1 ≤ L
  L_previous : s.previousL ≤ L
  gain_one : 1 ≤ Gnext
  gain : L ≤ CircleParameterData.kappa (n + 2) * Real.sqrt (Gnext : ℝ)
  m_K : s.K ≤ m
  m_pow : 2 ^ (n + 1) ≤ m
  m_G : 4 * s.G ≤ m
  m_large : 200 ≤ m
  attenuation_m : L ≤ CircleParameterData.kappa (n + 1) *
    (m : ℝ) ^ (1 / 40 : ℝ)
  gap : (Gnext : ℝ) * (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) <
    (m : ℝ) ^ ((4 / 5 : ℝ) * m)
  continuity : (height (n + 2) : ℝ) /
    (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) ≤ (1 / 2 : ℝ) ^ (n + 1)
  double : 2 * s.K < ⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊
  attenuation : ((2 * s.K + 1 : ℕ) : ℝ) * 3 * Real.exp (-L / 10000) ≤
    ε / ((n + 1 : ℕ) : ℝ)
  polynomial : ∀ A B : ℤ → ℂ,
    (∀ i, |i| ≤ (s.K : ℤ) → ‖A i‖ ≤ Real.exp (((s.K : ℝ) + 1) * s.cost)) →
    (∀ i, |i| ≤ (s.K : ℤ) → ‖B i‖ ≤ Real.exp (((s.K : ℝ) + 1) * s.cost)) →
    1 / ((n + 1 : ℕ) : ℝ) ≤ ‖A 0‖ → 1 / ((n + 1 : ℕ) : ℝ) ≤ ‖B 0‖ →
    ∃ i : ℕ, i ≤ 2 * s.K ∧ ε ≤ ‖convolution s.K A B i‖
  sampling : CircleSamplingStage θ (n + 1) s.K s.d (s.q s.d) m
    (max s.previousN ((m : ℝ) * s.K))

private theorem step_exists {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (n : ℕ) (s : State) : Nonempty (Step θ height n s) := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨ε, hε, hpoly⟩ := uniform_convolution_lower_bound s.K
    (Real.exp (((s.K : ℝ) + 1) * s.cost)) (1 / ((n + 1 : ℕ) : ℝ)) (by positivity)
  obtain ⟨L, hL1, hLprev, hL⟩ := exists_attenuation
    (((2 * s.K + 1 : ℕ) : ℝ) * 3) s.previousL
    (ε / ((n + 1 : ℕ) : ℝ)) (div_pos hε hn)
  have hk : 0 < CircleParameterData.kappa (n + 2) := by
    unfold CircleParameterData.kappa
    positivity
  obtain ⟨G, hG, hgain⟩ := exists_next_gain (CircleParameterData.kappa (n + 2)) L hk
  have hnum := eventually_stage_size (n + 1) (by omega) s.K s.G G L
    (height (n + 2)) s.d
  have hsam := hs (n + 1) s.K s.d (s.q s.d) (by omega) s.K_pos (s.q_pos _ le_rfl)
  obtain ⟨m, hm, ht⟩ := (hnum.and hsam).exists
  obtain ⟨hmK, hmpow, hmG, hmlarge, _hcount, hmL, hgap, hheight, hdouble⟩ := hm
  obtain ⟨t⟩ := ht (max s.previousN ((m : ℝ) * s.K))
  exact ⟨{
    m := m, Gnext := G, L := L, ε := ε
    epsilon_pos := hε, L_one := hL1, L_previous := hLprev
    gain_one := hG, gain := hgain
    m_K := by exact_mod_cast hmK
    m_pow := by exact_mod_cast hmpow
    m_G := by exact_mod_cast hmG
    m_large := hmlarge
    attenuation_m := hmL, gap := hgap, continuity := hheight
    double := by exact_mod_cast hdouble
    attenuation := hL, polynomial := hpoly, sampling := t }⟩

private def chooseStep {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (n : ℕ) (s : State) : Step θ height n s :=
  Classical.choice (step_exists hs height n s)

private def nextState {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (n : ℕ) (s : State) : State := by
  let t := chooseStep hs height n s
  let q := spliceFrequency s.q t.sampling.q s.d
  have hb := t.sampling.q_zero
  exact {
    K := ⌈(t.m : ℝ) ^ ((3 / 4 : ℝ) * t.m)⌉₊
    G := t.Gnext
    d := s.d + t.m
    q := q
    cost := s.cost + max t.L ((s.K : ℝ) ^ 2) * t.m
    previousL := t.L
    previousN := (t.m : ℝ) * s.K
    K_pos := by have := t.double; omega
    G_pos := by have := t.gain_one; omega
    q_zero := (spliceFrequency_eq_old s.q t.sampling.q (Nat.zero_le _)).trans s.q_zero
    q_pos := fun i _ => spliceFrequency_pos s.q t.sampling.q s.d s.q_pos t.sampling.q_pos i
    q_mono := fun i _ => spliceFrequency_strictMono s.q t.sampling.q s.d hb
      s.q_mono t.sampling.q_strict (Nat.lt_succ_self i)
    q_div := fun i _ => spliceFrequency_divisible s.q t.sampling.q s.d hb
      s.q_div t.sampling.q_div i }

private def initial : State where
  K := 100
  G := 1
  d := 0
  q := fun _ => 1
  cost := 0
  previousL := 0
  previousN := 0
  K_pos := by norm_num
  G_pos := by norm_num
  q_zero := rfl
  q_pos := fun _ _ => by norm_num
  q_mono := fun _ h => by omega
  q_div := fun _ h => by omega

private def states {θ : ℝ} (hs : CircleStageSupply θ) (height : ℕ → ℕ) : ℕ → State :=
  Nat.rec initial (nextState hs height)

private def choices {θ : ℝ} (hs : CircleStageSupply θ) (height : ℕ → ℕ) (n : ℕ) :
    Step θ height n (states hs height n) := chooseStep hs height n (states hs height n)

private theorem states_d_succ {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (n : ℕ) :
    (states hs height (n + 1)).d = (states hs height n).d + (choices hs height n).m := rfl

private theorem states_d_ge {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (n : ℕ) : n ≤ (states hs height n).d := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rw [states_d_succ]
    have := (choices hs height n).m_large
    omega

private theorem states_d_mono {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) : Monotone (fun n => (states hs height n).d) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [states_d_succ]
  omega

private theorem states_keep {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (n i : ℕ) (hi : i ≤ (states hs height n).d) :
    (states hs height (n + 1)).q i = (states hs height n).q i :=
  spliceFrequency_eq_old _ _ hi

private theorem exists_global_frequency {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) :
    ∃ Q : ℕ → ℕ,
      (∀ n i, i ≤ (states hs height n).d → Q i = (states hs height n).q i) ∧
      (∀ i, 0 < Q i) ∧ StrictMono Q ∧ (∀ i, Q i ∣ Q (i + 1)) :=
  exists_frequency_of_prefix_tower (fun n => (states hs height n).d)
    (fun n => (states hs height n).q) (states_d_mono hs height)
    (states_d_ge hs height) (states_keep hs height)
    (fun n => (states hs height n).q_pos) (fun n => (states hs height n).q_mono)
    (fun n => (states hs height n).q_div)

private def globalFrequency {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) : ℕ → ℕ := Classical.choose (exists_global_frequency hs height)

private theorem global_agree {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (n i : ℕ) (hi : i ≤ (states hs height n).d) :
    globalFrequency hs height i = (states hs height n).q i :=
  (Classical.choose_spec (exists_global_frequency hs height)).1 n i hi

private theorem global_block {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (n i : ℕ) (hi : i ≤ (choices hs height n).m) :
    globalFrequency hs height ((states hs height n).d + i) =
      (choices hs height n).sampling.q i := by
  rw [global_agree hs height (n + 1) _ (by rw [states_d_succ]; omega)]
  exact spliceFrequency_add _ _ _ _ (choices hs height n).sampling.q_zero

private def constructed {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) : CircleParameterData where
  m j := (choices hs height (j - 1)).m
  K j := (states hs height (j - 1)).K
  G j := (states hs height (j - 1)).G
  q := globalFrequency hs height
  L j := (choices hs height (j - 1)).L
  C j := max (choices hs height (j - 1)).L (((states hs height (j - 1)).K : ℝ) ^ 2)
  ε j := (choices hs height (j - 1)).ε
  height := height
  partition := φ
  samples j r := if hr : r < (states hs height (j - 1)).q (states hs height (j - 1)).d
    then (choices hs height (j - 1)).sampling.samples ⟨r, hr⟩ else ∅

private theorem blockEnd_eq {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n : ℕ) :
    (constructed hs height φ).blockEnd n = (states hs height n).d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [CircleParameterData.blockEnd_succ, ih, states_d_succ]
    simp [constructed]

private theorem cost_eq {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n : ℕ) :
    (states hs height n).cost =
      ∑ j ∈ Finset.Icc 1 n, (constructed hs height φ).C j * (constructed hs height φ).m j := by
  induction n with
  | zero => simp [states, initial]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← ih]
    rfl

private theorem block_mem {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n i : ℕ) :
    i ∈ (constructed hs height φ).block (n + 1) ↔
      (states hs height n).d < i ∧ i ≤ (states hs height n).d + (choices hs height n).m := by
  rw [CircleParameterData.mem_block_iff]
  simp only [Nat.add_sub_cancel, blockEnd_eq, states_d_succ]

private theorem coefficientBound_eq {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n : ℕ) :
    (constructed hs height φ).coefficientBound (n + 1) =
      Real.exp ((((states hs height n).K : ℝ) + 1) * (states hs height n).cost) := by
  simp only [CircleParameterData.coefficientBound, Nat.add_sub_cancel]
  rw [← cost_eq hs height φ n]
  rfl

private theorem sample_index_bound {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n r : ℕ) :
    r < (constructed hs height φ).q ((constructed hs height φ).blockEnd n) ↔
      r < (states hs height n).q (states hs height n).d := by
  rw [blockEnd_eq]
  change r < globalFrequency hs height (states hs height n).d ↔ _
  rw [global_agree hs height n _ le_rfl]

private theorem samples_eq {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n r : ℕ)
    (hr : r < (states hs height n).q (states hs height n).d) :
    (constructed hs height φ).samples (n + 1) r =
      (choices hs height n).sampling.samples ⟨r, hr⟩ := by
  simp [constructed, hr]

private theorem alpha_block {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n : ℕ)
    (i : Fin (choices hs height n).m) :
    (constructed hs height φ).alpha θ ((states hs height n).d + (i.val + 1)) =
      Int.fract (((choices hs height n).sampling.q (i.val + 1) : ℝ) * θ) := by
  unfold CircleParameterData.alpha
  change Int.fract ((globalFrequency hs height _ : ℝ) * θ) = _
  rw [global_block hs height n _ (by have := i.isLt; omega)]

private theorem constructed_phases {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n i : ℕ)
    (hi : i ∈ (constructed hs height φ).block (n + 1)) :
    1 / (constructed hs height φ).N (n + 1) < (constructed hs height φ).alpha θ i ∧
      (constructed hs height φ).alpha θ i < 2 / (constructed hs height φ).N (n + 1) := by
  have hmem := (block_mem hs height φ n i).mp hi
  let r : Fin (choices hs height n).m := ⟨i - (states hs height n).d - 1, by omega⟩
  have heq : (states hs height n).d + (r.val + 1) = i := by dsimp [r]; omega
  have hphase := (choices hs height n).sampling.phases r
  rw [← alpha_block hs height φ n r, heq] at hphase
  exact hphase

private theorem convolution_eq_supported (K : ℕ) (A B : ℤ → ℂ)
    (hB : Function.support B ⊆ Set.Icc (-(K : ℤ)) (K : ℤ)) (n : ℕ) :
    CircleParameterData.convolutionCoefficient K A B (-(n : ℤ)) =
      convolution K A B n := by
  classical
  unfold CircleParameterData.convolutionCoefficient FiniteWindow.convolution
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : |(n : ℤ) + i| ≤ (K : ℤ)
  · simp [hi]
  · simp only [hi, ite_false]
    have hzero : B (-(n : ℤ) - i) = 0 := by
      by_contra hne
      have hmem := hB (Function.mem_support.mpr hne)
      have ha : |-(n : ℤ) - i| ≤ (K : ℤ) := abs_le.mpr hmem
      have heq : -(n : ℤ) - i = -((n : ℤ) + i) := by ring
      rw [heq, abs_neg] at ha
      exact hi ha
    simp [hzero]

private theorem constructed_ratios {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n i : ℕ)
    (hi : i ∈ (constructed hs height φ).block (n + 1)) :
    (constructed hs height φ).N (n + 1) ≤
      ((constructed hs height φ).q (i + 1) : ℝ) / (constructed hs height φ).q i := by
  have hmem := (block_mem hs height φ n i).mp hi
  by_cases hlt : i < (states hs height n).d + (choices hs height n).m
  · let r := i - (states hs height n).d
    have hr : r < (choices hs height n).m := by dsimp [r]; omega
    have heq : (states hs height n).d + r = i := by dsimp [r]; omega
    have hq0 := global_block hs height n r hr.le
    have hq1 := global_block hs height n (r + 1) (by omega)
    rw [heq] at hq0
    rw [← Nat.add_assoc, heq] at hq1
    change ((choices hs height n).m : ℝ) * (states hs height n).K ≤
      (globalFrequency hs height (i + 1) : ℝ) / globalFrequency hs height i
    rw [hq0, hq1]
    exact (le_max_right _ _).trans ((choices hs height n).sampling.q_ratio r hr)
  · have heq : i = (states hs height (n + 1)).d := by
      rw [states_d_succ]
      omega
    have hm : 0 < (choices hs height (n + 1)).m := by
      have := (choices hs height (n + 1)).m_large
      omega
    have hq0 := global_block hs height (n + 1) 0 (Nat.zero_le _)
    have hq1 := global_block hs height (n + 1) 1 hm
    simp only [Nat.add_zero, ← heq] at hq0 hq1
    change ((choices hs height n).m : ℝ) * (states hs height n).K ≤
      (globalFrequency hs height (i + 1) : ℝ) / globalFrequency hs height i
    rw [hq0, hq1]
    exact (le_max_left _ _).trans ((choices hs height (n + 1)).sampling.q_ratio 0 hm)

private theorem constructed_spread {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n : ℕ) (k : ℤ)
    (hlo : (constructed hs height φ).N (n + 1) / 4 ≤ |(k : ℝ)|)
    (hhi : |(k : ℝ)| ≤ ((constructed hs height φ).m (n + 1) : ℝ) ^
      ((4 / 5 : ℝ) * (constructed hs height φ).m (n + 1))) :
    ((constructed hs height φ).m (n + 1) : ℝ) / 20 ≤
      (((constructed hs height φ).block (n + 1)).filter (fun i =>
        1 - Int.fract ((k : ℝ) * (constructed hs height φ).alpha θ i) ∈
          Set.Icc ((constructed hs height φ).b (n + 1))
            (1 - (constructed hs height φ).b (n + 1)))).card := by
  classical
  have hspread := (choices hs height n).sampling.spread k hlo
    (by simpa [constructed] using hhi)
  simp only [Finset.card_univ, Fintype.card_fin, ProductPhases.strictPhaseGoodCount] at hspread
  let f : Fin (choices hs height n).m → ℕ := fun r => (states hs height n).d + (r.val + 1)
  have hcard :
      (Finset.univ.filter (fun r : Fin (choices hs height n).m =>
        1 - Int.fract ((k : ℝ) * Int.fract
          (((choices hs height n).sampling.q (r.val + 1) : ℝ) * θ)) ∈
            Set.Ioo (((choices hs height n).m : ℝ) ^ (-19 / 20 : ℝ))
              (1 - ((choices hs height n).m : ℝ) ^ (-19 / 20 : ℝ)))).card ≤
      (((constructed hs height φ).block (n + 1)).filter (fun i =>
        1 - Int.fract ((k : ℝ) * (constructed hs height φ).alpha θ i) ∈
          Set.Icc ((constructed hs height φ).b (n + 1))
            (1 - (constructed hs height φ).b (n + 1)))).card := by
    apply Finset.card_le_card_of_injOn f
    · intro r hr
      obtain ⟨_, hr⟩ := Finset.mem_filter.mp hr
      apply Finset.mem_filter.mpr
      constructor
      · apply (block_mem hs height φ n (f r)).mpr
        dsimp [f]
        have := r.isLt
        omega
      · change 1 - Int.fract ((k : ℝ) * (constructed hs height φ).alpha θ
            ((states hs height n).d + (r.val + 1))) ∈ _
        rw [alpha_block]
        have hneg : (-19 / 20 : ℝ) = -(19 / 20 : ℝ) := by norm_num
        rw [hneg] at hr
        exact ⟨hr.1.le, hr.2.le⟩
    · intro r _ s _ hrs
      apply Fin.ext
      dsimp [f] at hrs
      omega
  exact hspread.trans (by exact_mod_cast hcard)

private theorem prod_constructed_block {A : Type*} [CommMonoid A]
    {θ : ℝ} (hs : CircleStageSupply θ) (height : ℕ → ℕ)
    (φ : ℕ → ℕ → C(Circle, ℝ)) (n : ℕ) (f : ℕ → A) :
    (∏ i ∈ (constructed hs height φ).block (n + 1), f i) =
      ∏ r : Fin (choices hs height n).m, f ((states hs height n).d + (r.val + 1)) := by
  classical
  symm
  apply Finset.prod_bij (fun r _ => (states hs height n).d + (r.val + 1))
  · intro r _
    apply (block_mem hs height φ n _).mpr
    have := r.isLt
    omega
  · intro r _ s _ hrs
    apply Fin.ext
    omega
  · intro i hi
    have hmem := (block_mem hs height φ n i).mp hi
    refine ⟨⟨i - (states hs height n).d - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    simp only
    omega
  · intro r _
    rfl

private theorem samplingAverage_eq {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n r : ℕ)
    (hr : r < (states hs height n).q (states hs height n).d)
    (endpoint : Bool) (x : Circle) :
    (constructed hs height φ).samplingAverage θ (n + 1) r endpoint x =
      TrialSampling.average (choices hs height n).m
        ((choices hs height n).sampling.samples ⟨r, hr⟩) endpoint
        (fun i : Fin (choices hs height n).m =>
          Int.fract (((choices hs height n).sampling.q (i.val + 1) : ℝ) * θ))
        (fun i : Fin (choices hs height n).m =>
          ((choices hs height n).sampling.q (i.val + 1) : ℤ) • x) := by
  unfold CircleParameterData.samplingAverage TrialSampling.average
  rw [samples_eq hs height φ n r hr, one_div]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [prod_constructed_block]
  apply Finset.prod_congr rfl
  intro i _
  rw [alpha_block]
  congr 2
  unfold CircleParameterData.coordinate
  change CircleParameterData.rep (globalFrequency hs height
    ((states hs height n).d + (i.val + 1)) • x) = _
  rw [global_block hs height n _ (by have := i.isLt; omega)]
  simp

private theorem shift_eq {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n r : ℕ) :
    (constructed hs height φ).shift (n + 1) r =
      (r : ℝ) / (states hs height n).q (states hs height n).d := by
  unfold CircleParameterData.shift
  simp only [Nat.add_sub_cancel, blockEnd_eq]
  change (r : ℝ) / globalFrequency hs height (states hs height n).d = _
  rw [global_agree hs height n _ le_rfl]

private theorem ell_eq {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n : ℕ) :
    (constructed hs height φ).ell (n + 1) =
      1 / (((n + 2 : ℕ) : ℝ) ^ 2 * (1 + ((states hs height n).d : ℝ)) *
        (states hs height n).q (states hs height n).d) := by
  unfold CircleParameterData.ell
  simp only [Nat.add_sub_cancel, blockEnd_eq]
  change 1 / (((n + 2 : ℕ) : ℝ) ^ 2 * (1 + ((states hs height n).d : ℝ)) *
    globalFrequency hs height (states hs height n).d) = _
  rw [global_agree hs height n _ le_rfl]

private theorem constructed_laws {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ))
    (hφnonneg : ∀ j n x, 0 ≤ φ j n x)
    (hφsum : ∀ j x, ∑ n ∈ Finset.range (height j + 1), φ j n x = 1)
    (hφsupport : ∀ j, 1 ≤ j → ∀ n, ∀ x ∈ tsupport (φ j n),
      dist (x + (((n : ℝ) * θ : ℝ) : Circle)) 0 < 1 / (10 * (j : ℝ))) :
    CircleParameterLaws θ (constructed hs height φ) := by
  have hmpos (n : ℕ) : 0 < (choices hs height n).m := by
    have := (choices hs height n).m_large
    omega
  have hLmono : Monotone (fun n => (choices hs height n).L) := by
    apply monotone_nat_of_le_succ
    intro n
    exact (choices hs height (n + 1)).L_previous
  have globalSpec := Classical.choose_spec (exists_global_frequency hs height)
  refine {
    m_pos := ?_
    K_pos := ?_
    G_pos := ?_
    q_pos := globalSpec.2.1
    L_pos := ?_
    C_pos := ?_
    epsilon_pos := ?_
    partition_nonneg := fun j _ n _ x => hφnonneg j n x
    partition_sum := fun j _ x => hφsum j x
    partition_support := fun j hj n _ x hx => hφsupport j hj n x hx
    frequency_zero := ?_
    frequency_increasing := globalSpec.2.2.1
    frequency_divisible := globalSpec.2.2.2
    phase_bounds := ?_
    frequency_ratios := ?_
    spread_high := ?_
    spread_low := ?_
    initial_K := rfl
    initial_G := rfl
    L_ge_one := ?_
    L_monotone := ?_
    C_eq := fun _ _ => rfl
    m_ge_K := ?_
    m_ge_pow := ?_
    m_ge_G := ?_
    m_ge_200 := ?_
    next_K := ?_
    K_double := ?_
    next_G_gap := ?_
    attenuation_m := ?_
    attenuation_G := ?_
    continuity_height := ?_
    polynomial_lower := ?_
    polynomial_attenuation := ?_
    samples_nonempty := ?_
    samples_positive := ?_
    samples_range := ?_
    samples_phase := ?_
    sampling_L2 := ?_ }
  · intro j _
    exact hmpos (j - 1)
  · intro j _
    exact (states hs height (j - 1)).K_pos
  · intro j _
    exact (states hs height (j - 1)).G_pos
  · intro j _
    exact (by norm_num : (0 : ℝ) < 1).trans_le (choices hs height (j - 1)).L_one
  · intro j _
    exact ((by norm_num : (0 : ℝ) < 1).trans_le
      (choices hs height (j - 1)).L_one).trans_le (le_max_left _ _)
  · intro j _
    exact (choices hs height (j - 1)).epsilon_pos
  · exact (global_agree hs height 0 0 (Nat.zero_le _)).trans rfl
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact constructed_phases hs height φ n
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact constructed_ratios hs height φ n
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact constructed_spread hs height φ n
  · intro j hj k hlo hhi i hi
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have ha := constructed_phases hs height φ n i hi
    exact phase_small_window (by exact_mod_cast hmpos n)
      (by exact_mod_cast (states hs height n).K_pos)
      (by exact_mod_cast (states hs height n).G_pos) ha.1.le ha.2.le hlo hhi
  · intro j _
    exact (choices hs height (j - 1)).L_one
  · intro j k _ hjk
    exact hLmono (Nat.sub_le_sub_right hjk 1)
  · intro j _
    exact (choices hs height (j - 1)).m_K
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact (choices hs height n).m_pow
  · intro j _
    exact (choices hs height (j - 1)).m_G
  · intro j _
    exact (choices hs height (j - 1)).m_large
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rfl
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact (choices hs height n).double
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact (choices hs height n).gap
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact (choices hs height n).attenuation_m
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact (choices hs height n).gain
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact (choices hs height n).continuity
  · intro j hj A B _hAs hBs hA hB hA0 hB0
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [coefficientBound_eq] at hA hB
    obtain ⟨r, hr, hcoef⟩ := (choices hs height n).polynomial A B
      (fun i _ => hA i) (fun i _ => hB i) hA0 hB0
    refine ⟨r, Finset.mem_Icc.mpr ⟨Nat.zero_le _, hr⟩, ?_⟩
    rw [convolution_eq_supported _ A B hBs]
    exact hcoef
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact (choices hs height n).attenuation
  · intro j hj r hr
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hr' := (sample_index_bound hs height φ n r).mp hr
    rw [samples_eq hs height φ n r hr']
    exact (choices hs height n).sampling.samples_nonempty ⟨r, hr'⟩
  · intro j hj r hr l hl
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hr' := (sample_index_bound hs height φ n r).mp hr
    rw [samples_eq hs height φ n r hr'] at hl
    exact (choices hs height n).sampling.samples_positive ⟨r, hr'⟩ l hl
  · intro j hj r hr l hl
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hr' := (sample_index_bound hs height φ n r).mp hr
    rw [samples_eq hs height φ n r hr'] at hl
    exact (choices hs height n).sampling.samples_range ⟨r, hr'⟩ l hl
  · intro j hj r hr l hl
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hr' := (sample_index_bound hs height φ n r).mp hr
    rw [samples_eq hs height φ n r hr'] at hl
    rw [shift_eq, ell_eq]
    exact (choices hs height n).sampling.samples_phase ⟨r, hr'⟩ l hl
  · intro j hj r hr endpoint
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hr' := (sample_index_bound hs height φ n r).mp hr
    have heq : (fun x : Circle => (constructed hs height φ).samplingAverage θ
        (n + 1) r endpoint x - 1) =
      (fun x : Circle => TrialSampling.average (choices hs height n).m
        ((choices hs height n).sampling.samples ⟨r, hr'⟩) endpoint
        (fun i : Fin (choices hs height n).m =>
          Int.fract (((choices hs height n).sampling.q (i.val + 1) : ℝ) * θ))
        (fun i : Fin (choices hs height n).m =>
          ((choices hs height n).sampling.q (i.val + 1) : ℤ) • x) - 1) := by
      funext x
      rw [samplingAverage_eq hs height φ n r hr']
    rw [heq]
    exact (choices hs height n).sampling.sampling_L2 ⟨r, hr'⟩ endpoint

theorem exists_parameters_of_stage_supply {θ : ℝ} (hθ : Irrational θ)
    (hs : CircleStageSupply θ) : ∃ p : CircleParameterData, CircleParameterLaws θ p := by
  obtain ⟨height, φ, hnonneg, hsum, hsupport, _⟩ := exists_preparatory_partitions hθ
  exact ⟨constructed hs height φ, constructed_laws hs height φ hnonneg hsum hsupport⟩

end Invariant233.CircleParameterRecursion

end

end OAI
