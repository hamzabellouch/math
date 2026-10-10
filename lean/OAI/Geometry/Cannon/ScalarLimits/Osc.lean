import Mathlib
import OAI.Geometry.Cannon.Modulus.ClosedAnnulus

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open scoped NNReal ENNReal
open Set Filter Metric Topology
open Set Filter Topology

namespace CannonScales

lemma inverse_geometric_tendsto_zero {a : ℝ} (ha : 1 < a) :
    Tendsto (fun n : ℕ => (a^n)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt ha)

lemma inverse_geometric_antitone {a : ℝ} (ha : 1 < a) :
    Antitone (fun n : ℕ => (a^n)⁻¹) := by
  intro i j hij
  exact inv_le_inv₀ (by positivity) (by positivity) |>.mpr
    (pow_le_pow_right₀ ha.le hij)

theorem exists_spaced_geometric {a : ℝ} (ha : 1 < a) (l₀ : ℕ) :
    ∃ b : ℕ, 0 < b ∧ ∀ i j : ℕ, i < j →
      16*(a^(l₀+b*j))⁻¹ < (a^(l₀+b*i))⁻¹ := by
  obtain ⟨b,hb⟩ := ((tendsto_pow_atTop_atTop_of_one_lt ha).eventually
    (eventually_gt_atTop (16 : ℝ))).exists
  have hbpos : 0 < b := by
    by_contra hn
    have : b = 0 := Nat.eq_zero_of_not_pos hn
    norm_num [this] at hb
  refine ⟨b,hbpos,?_⟩
  intro i j hij
  have hexp : l₀+b*i+b ≤ l₀+b*j := by
    have hh := Nat.mul_le_mul_left b (Nat.succ_le_of_lt hij)
    simpa only [Nat.mul_succ, Nat.add_assoc] using Nat.add_le_add_left hh l₀
  have hp : (a^(l₀+b*i))*16 < a^(l₀+b*j) := by
    calc
      _ < (a^(l₀+b*i))*(a^b) := mul_lt_mul_of_pos_left hb (by positivity)
      _ = a^(l₀+b*i+b) := (pow_add ..).symm
      _ ≤ a^(l₀+b*j) := pow_le_pow_right₀ ha.le hexp
  have hap : 0 < a := zero_lt_one.trans ha
  rw [mul_inv_lt_iff₀ (pow_pos hap _)]
  rw [inv_mul_eq_div, lt_div_iff₀ (pow_pos hap _)]
  simpa only [mul_comm] using hp

end CannonScales

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace CannonScalarLimit

theorem finite_measure_subsequence {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (μ : ℕ → FiniteMeasure X) (C : ℝ≥0) (hmass : ∀ n, (μ n).mass ≤ C) :
    ∃ ν : FiniteMeasure X, ν.mass ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  obtain ⟨c, hc, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq
    (s := Icc (0 : ℝ≥0) C) (x := fun n => (μ n).mass)
    (fun n => ⟨by positivity, hmass n⟩)
  obtain ⟨p, ψ, hψ, hp⟩ := CompactSpace.tendsto_subseq
    (fun n => (μ (φ n)).normalize)
  refine ⟨c • p.toFiniteMeasure, ?_, φ ∘ ψ, hφ.comp hψ, ?_⟩
  · change (c • p.toFiniteMeasure) univ ≤ C
    rw [FiniteMeasure.smul_apply]
    change c * p.toFiniteMeasure.mass ≤ C
    rw [ProbabilityMeasure.mass_toFiniteMeasure, mul_one]
    exact hc.2
  · have hm := hlim.comp hψ.tendsto_atTop
    have hpn := ProbabilityMeasure.toFiniteMeasure_continuous.tendsto p |>.comp hp
    have h := hm.smul hpn
    simpa only [Function.comp_def, ← FiniteMeasure.self_eq_mass_smul_normalize] using h

theorem scalar_subsequence {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SigmaCompactSpace X]
    (f : ℕ → C(X, ℝ)) (heq : Equicontinuous (fun n x => f n x))
    (hb : ∀ n x, f n x ∈ Icc (0 : ℝ) 1) :
    ∃ u : C(X, ℝ), (∀ x, u x ∈ Icc (0 : ℝ) 1) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (f ∘ φ) atTop (𝓝 u) := by
  classical
  have : T2Space (UniformOnFun X ℝ {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      apply eq_univ_of_forall
      intro x
      exact mem_sUnion_of_mem (mem_singleton x) isCompact_singleton)
  have hcompact : IsCompact (closure (range f)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun g : C(X, ℝ) => (g : X → ℝ)) (𝔖 := {K | IsCompact K}) (fun _ h => h)
    · exact ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro K hK
      have hindex : ∀ g : range f, ∃ n, f n = g.val := fun g => g.property
      choose index hindex using hindex
      have heq' := heq.comp index
      have heq'' : Equicontinuous (fun g : range f => (g.val : X → ℝ)) := by
        convert heq' using 1
        funext g x
        exact congrArg (fun h : C(X, ℝ) => h x) (hindex g).symm
      exact heq''.equicontinuousOn K
    · intro K hK x hx
      refine ⟨Icc (0 : ℝ) 1, isCompact_Icc, ?_⟩
      rintro g ⟨n,rfl⟩
      exact hb n x
  obtain ⟨u, hu, φ, hφ, ht⟩ := hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  refine ⟨u, ?_, φ, hφ, ht⟩
  intro x
  have hclosed : IsClosed {g : C(X, ℝ) | g x ∈ Icc (0 : ℝ) 1} :=
    isClosed_Icc.preimage (continuous_eval_const x)
  exact closure_minimal (by rintro g ⟨n,rfl⟩; exact hb n x) hclosed hu

def osc {X : Type*} (K : Set X) (f : X → ℝ) : ℝ :=
  sSup (f '' K) - sInf (f '' K)

lemma continuous_osc {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    {K : Set X} (hK : IsCompact K) :
    Continuous (fun f : C(X, ℝ) => osc K f) :=
  (hK.continuous_sSup continuous_eval).sub (hK.continuous_sInf continuous_eval)

lemma tendsto_osc {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    {K : Set X} (hK : IsCompact K) {f : ℕ → C(X, ℝ)} {u : C(X, ℝ)}
    (hf : Tendsto f atTop (𝓝 u)) :
    Tendsto (fun n => osc K (f n)) atTop (𝓝 (osc K u)) :=
  (continuous_osc hK).tendsto u |>.comp hf

theorem closed_domination_limit {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {μ : ℕ → FiniteMeasure X} {ν : FiniteMeasure X}
    (hμ : Tendsto μ atTop (𝓝 ν)) {K : Set X} (hK : IsClosed K)
    {a : ℕ → ℝ} {b C : ℝ} (ha : Tendsto a atTop (𝓝 b)) (hC : 0 ≤ C)
    (hbound : ∀ᶠ n in atTop, a n ≤ C * (μ n K : ℝ)) :
    b ≤ C * (ν K : ℝ) := by
  rcases eq_or_lt_of_le hC with hC | hC
  · subst C
    simpa using le_of_tendsto ha (hbound.mono (by intro n hn; simpa using hn))
  have he : ∀ᶠ n in atTop,
      ENNReal.ofReal (a n / C) ≤ (μ n : Measure X) K := by
    filter_upwards [hbound] with n hn
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    apply ENNReal.ofReal_le_iff_le_toReal (by simp) |>.mpr
    change a n / C ≤ ((μ n K : ℝ≥0) : ℝ)
    exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hn)
  have ht := ENNReal.continuous_ofReal.tendsto (b / C) |>.comp (ha.div_const C)
  have hl := (Filter.limsup_le_limsup he).trans
    (FiniteMeasure.limsup_measure_closed_le_of_tendsto hμ hK)
  simp only [Function.comp_def] at ht
  rw [ht.limsup_eq] at hl
  have hreal := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hl
  have hh : b / C ≤ (ν K : ℝ) := by
    exact hreal
  exact (div_le_iff₀ hC).mp hh |>.trans_eq (mul_comm _ _)

theorem oscillation_measure_limit {X Y : Type*}
    [TopologicalSpace X] [LocallyCompactSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {K : Set X} (hK : IsCompact K) {B : Set Y} (hB : IsClosed B)
    {f : ℕ → C(X, ℝ)} {u : C(X, ℝ)} (hf : Tendsto f atTop (𝓝 u))
    {μ : ℕ → FiniteMeasure Y} {ν : FiniteMeasure Y} (hμ : Tendsto μ atTop (𝓝 ν))
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᶠ n in atTop, (osc K (f n)) ^ 2 ≤ C * (μ n B : ℝ)) :
    (osc K u) ^ 2 ≤ C * (ν B : ℝ) :=
  closed_domination_limit hμ hB ((tendsto_osc hK hf).pow 2) hC hb

end CannonScalarLimit

namespace CannonScalarLimit

open CannonAtomic CannonAnnularCompactness CannonScales Set Filter Metric Topology MeasureTheory

attribute [local instance] Classical.propDecidable

theorem atomic_record_equicontinuous {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (U : Set X)
    (Idx : ℕ → Type*) [∀ n, Fintype (Idx n)]
    (p : ∀ n, Idx n → X) (w : ∀ n, Idx n → ℝ)
    (f : ℕ → C(U, ℝ)) (N : ℕ → ℕ) (hN : StrictMono N)
    (M : ℕ → ℝ) (hM : ∀ n, 0 < M n)
    (a L A C : ℝ) (ha : 1 < a) (hL : 0 < L) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (henergy : ∀ n, (∑ i, (w n i)^2) ≤ C/M (N n))
    (hrecord : ∀ n l, l ≤ N n → M (N n-l) ≤ M (N n))
    (hann : ∀ x : U, ∃ l₀ m₀ : ℕ, ∀ l, l₀ ≤ l → ∀ n, l+m₀ ≤ N n →
      ∀ y : U, dist y x < (a^l)⁻¹/(2*L) →
      (f n x-f n y)^2 ≤ A*M (N n-l)*
        (∑ i ∈ Finset.univ.filter (fun i =>
          (a^l)⁻¹/4 ≤ dist (p n i) x.val ∧ dist (p n i) x.val ≤ 4*(a^l)⁻¹), (w n i)^2)) :
    Equicontinuous (fun n x => f n x) := by
  intro x
  let μ : ℕ → FiniteMeasure X := fun n => atomic (p n) (w n) (M (N n)) (hM (N n)).le
  have hmass (n : ℕ) : ((μ n).mass : ℝ) ≤ C := mass_bound (p n) (w n) (M (N n))
    (hM (N n)) C (henergy n)
  apply equicontinuousAt_of_disjoint_measures (fun n x => f n x) x μ A C hA hC hmass
    (fun n => (f n).continuous.continuousAt)
  intro m
  obtain ⟨l₀,m₀,hann⟩ := hann x
  obtain ⟨b,hb,hspace⟩ := exists_spaced_geometric ha l₀
  let ell : Fin (m+1) → ℕ := fun i => l₀+b*i.val
  let S : Fin (m+1) → Set X := fun i => closedAnnulus x.val ((a^(ell i))⁻¹)
  have hmeas (i : Fin (m+1)) : MeasurableSet (S i) :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet.inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const).measurableSet
  refine ⟨S,hmeas,?_,?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hij
    · exact annuli_disjoint x.val _ _ (hspace i j hij)
    · exact (annuli_disjoint x.val _ _ (hspace j i hij)).symm
  · intro i
    obtain ⟨j₀,hj₀⟩ := eventually_atTop.mp
      (hN.tendsto_atTop.eventually (eventually_ge_atTop (ell i+m₀)))
    have hadelta : 0 < (a^(ell i))⁻¹/(2*L) := by positivity
    refine ⟨(a^(ell i))⁻¹/(2*L),hadelta,j₀,?_⟩
    intro n hn y hy
    have hnlarge := hj₀ n hn
    have hrec := hrecord n (ell i) (by omega)
    have hraw := hann (ell i) (Nat.le_add_right _ _) n hnlarge y hy
    have hbound := record_annular_bound (p n) (w n) (M (N n)) (M (N n-ell i))
      A (f n x-f n y) 1 (hM (N n)) hA zero_lt_one (by simpa using hrec)
      (S i) (hmeas i) (by
        convert hraw using 1; congr 2
        apply Finset.filter_congr
        intro j _
        rfl)
    simpa only [div_one] using hbound

end CannonScalarLimit

namespace CannonScalarLimit

open CannonAtomic CannonAnnularCompactness Set Filter Metric Topology MeasureTheory
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

theorem atomic_record_limit {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (U : Set X) (hU : IsOpen U)
    (Idx : ℕ → Type*) [∀ n, Fintype (Idx n)]
    (p : ∀ n, Idx n → X) (w : ∀ n, Idx n → ℝ)
    (f : ℕ → C(U, ℝ)) (N : ℕ → ℕ) (hN : StrictMono N)
    (M : ℕ → ℝ) (hM : ∀ n, 0 < M n)
    (a L A C : ℝ) (ha : 1 < a) (hL : 0 < L) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (henergy : ∀ n, (∑ i, (w n i)^2) ≤ C/M (N n))
    (hrecord : ∀ n l, l ≤ N n → M (N n-l) ≤ M (N n))
    (hann : ∀ x : U, ∃ l₀ m₀ : ℕ, ∀ l, l₀ ≤ l → ∀ n, l+m₀ ≤ N n →
      ∀ y : U, dist y x < (a^l)⁻¹/(2*L) →
      (f n x-f n y)^2 ≤ A*M (N n-l)*
        (∑ i ∈ Finset.univ.filter (fun i =>
          (a^l)⁻¹/4 ≤ dist (p n i) x.val ∧ dist (p n i) x.val ≤ 4*(a^l)⁻¹), (w n i)^2))
    (hvalues : ∀ n x, f n x ∈ Icc (0 : ℝ) 1)
    (top bot : U) (htop : ∀ n, f n top = 0) (hbot : ∀ n, f n bot = 1) :
    let μ : ℕ → FiniteMeasure X := fun n => atomic (p n) (w n) (M (N n)) (hM (N n)).le
    ∃ u : C(U, ℝ), (∀ x, u x ∈ Icc (0 : ℝ) 1) ∧ u top = 0 ∧ u bot = 1 ∧
      ∃ ν : FiniteMeasure X, (ν.mass : ℝ) ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (f ∘ φ) atTop (𝓝 u) ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : Nonempty X := ⟨top.val⟩
  let μ : ℕ → FiniteMeasure X := fun n => atomic (p n) (w n) (M (N n)) (hM (N n)).le
  change ∃ u : C(U, ℝ), (∀ x, u x ∈ Icc (0 : ℝ) 1) ∧ u top = 0 ∧ u bot = 1 ∧
    ∃ ν : FiniteMeasure X, (ν.mass : ℝ) ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (f ∘ φ) atTop (𝓝 u) ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν)
  have heq := atomic_record_equicontinuous U Idx p w f N hN M hM
    a L A C ha hL hA hC henergy hrecord hann
  obtain ⟨u,hu,φ,hφ,ht⟩ := scalar_subsequence f heq hvalues
  have hutop : u top = 0 := by
    have hh := (continuous_eval_const top).tendsto u |>.comp ht
    simp only [Function.comp_def,htop] at hh
    exact tendsto_nhds_unique hh (tendsto_const_nhds (x := (0 : ℝ)))
  have hubot : u bot = 1 := by
    have hh := (continuous_eval_const bot).tendsto u |>.comp ht
    simp only [Function.comp_def,hbot] at hh
    exact tendsto_nhds_unique hh (tendsto_const_nhds (x := (1 : ℝ)))
  let Cplus : ℝ≥0 := Real.toNNReal C
  have hCplus : (Cplus : ℝ) = C := Real.coe_toNNReal C hC
  have hmass (n : ℕ) : (μ n).mass ≤ Cplus := by
    apply NNReal.coe_le_coe.mp
    rw [hCplus]
    exact mass_bound (p n) (w n) (M (N n)) (hM (N n)) C (henergy n)
  obtain ⟨ν,hν,ψ,hψ,hconv⟩ := finite_measure_subsequence (μ ∘ φ) Cplus (fun n => hmass (φ n))
  refine ⟨u,hu,hutop,hubot,ν,?_,φ ∘ ψ,hφ.comp hψ,ht.comp hψ.tendsto_atTop,hconv⟩
  exact (NNReal.coe_le_coe.mpr hν).trans_eq hCplus

end CannonScalarLimit

end
end
end
end
end
end
end
end
end

end OAI
