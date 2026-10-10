import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.WeightedAction

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.BorelCoefficients
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
variable {k : ℕ} {T : Functional X k}
variable (μ : Measure X) [IsFiniteMeasure μ]

lemma borelAction_const_coord (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {f : X → ℝ} (hf : Integrable f μ) (π : Fin k → X → ℝ)
    (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k) (c : ℝ)
    (hc : ∀ x, π i x = c) : borelAction μ hT f π = 0 := by
  simpa using borelAction_locality_mul μ hT hμ hf (BoundedLip.const 1) π hπ
    ⟨i, univ, c, isOpen_univ, subset_univ _, fun x _ => hc x⟩

noncomputable def levelClamp (c ε : ℝ) (u : X → ℝ) (x : X) : ℝ :=
  max (c - ε) (min (c + ε) (u x))

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma levelClamp_lipschitz {c ε : ℝ} {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : LipschitzWith K (levelClamp c ε u) :=
  (hu.const_min (c + ε)).const_max (c - ε)

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma levelClamp_eq {c ε : ℝ} {u : X → ℝ} {x : X} (h : |u x - c| < ε) :
    levelClamp c ε u x = u x := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp h
  dsimp [levelClamp]
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma levelClamp_tendsto (c : ℝ) (u : X → ℝ) (x : X) :
    Tendsto (fun n : ℕ => levelClamp c (1 / (n + 1)) u x) atTop (𝓝 c) := by
  have hd : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using (tendsto_const_nhds.sub hd :
      Tendsto (fun n : ℕ => c - 1 / (n + 1 : ℝ)) atTop (𝓝 (c - 0))))
    (by simpa using (tendsto_const_nhds.add hd :
      Tendsto (fun n : ℕ => c + 1 / (n + 1 : ℝ)) atTop (𝓝 (c + 0))))
  · intro n
    dsimp [levelClamp]
    simpa only [one_div] using (le_max_left (c - 1 / (n + 1 : ℝ)) (min (c + 1 / (n + 1 : ℝ)) (u x)))
  · intro n
    simp only [levelClamp, one_div]
    apply max_le _ (min_le_left _ _)
    have h : 0 ≤ 1 / (n + 1 : ℝ) := by positivity
    simpa only [one_div] using (show c - 1 / (n + 1 : ℝ) ≤ c + 1 / (n + 1 : ℝ) by linarith)

lemma borelAction_eq_levelClamp (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {f : X → ℝ} (hf : Integrable f μ) (π : Fin k → X → ℝ)
    (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k) (c : ℝ)
    (hc : ∀ x, f x ≠ 0 → π i x = c) {ε : ℝ} (hε : 0 < ε) :
    borelAction μ hT f π =
      borelAction μ hT f (Function.update π i (levelClamp c ε (π i))) := by
  classical
  obtain ⟨K, hK⟩ := hπ i
  let v := levelClamp c ε (π i)
  let w : X → ℝ := fun x => π i x - v x
  let ζ : X → ℝ := fun x => max 0 (ε - dist (π i x) c)
  have hv : LipschitzWith K v := levelClamp_lipschitz hK
  have hw : ∃ L : ℝ≥0, LipschitzWith L w := ⟨K + K, hK.sub hv⟩
  have hζ : BoundedLip ζ := by
    apply Foundations.boundedLip_of_lipschitz
    have hd : LipschitzWith K (fun x => dist (π i x) c) :=
      by simpa only [one_mul, Function.comp_def] using (LipschitzWith.dist_left c).comp hK
    simpa using ((LipschitzWith.const ε).sub hd).const_max 0
  let ρ := Function.update π i w
  have hρ : ∀ j, ∃ L : ℝ≥0, LipschitzWith L (ρ j) := by
    intro j
    by_cases hji : j = i
    · simpa [ρ, hji] using hw
    · simpa [ρ, Function.update_of_ne hji] using hπ j
  have hz : borelAction μ hT (fun x => f x * ζ x) ρ = 0 := by
    apply borelAction_locality_mul μ hT hμ hf hζ ρ hρ
    refine ⟨i, {x | dist (π i x) c < ε}, 0,
      isOpen_lt (hK.continuous.dist continuous_const) continuous_const, ?_, ?_⟩
    · intro x hx
      change max 0 (ε - dist (π i x) c) ≠ 0 at hx
      change dist (π i x) c < ε
      by_contra h
      exact hx (max_eq_left (by linarith [le_of_not_gt h]))
    · intro x hx
      simp only [ρ, Function.update_self]
      change π i x - levelClamp c ε (π i) x = 0
      rw [levelClamp_eq (by simpa [Real.dist_eq] using hx), sub_self]
  have heq : (fun x => f x * ζ x) = ε • f := by
    funext x
    by_cases hfx : f x = 0
    · simp [hfx]
    · simp [ζ, hc x hfx, max_eq_right hε.le, mul_comm]
  rw [heq, borelAction_smul μ hT hf ρ ε hρ] at hz
  have hzero : borelAction μ hT f ρ = 0 := (mul_eq_zero.mp hz).resolve_left hε.ne'
  have hlin := borelAction_linearCoord μ hT hμ hf π hπ i v ⟨K, hv⟩ 1 (-1)
  have hform : Function.update π i (fun x => 1 * π i x + -1 * v x) = ρ := by
    simp only [one_mul, neg_one_mul, ← sub_eq_add_neg]
    rfl
  rw [hform, hzero] at hlin
  linarith

theorem borelAction_locality_level (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {f : X → ℝ} (hf : Integrable f μ) (π : Fin k → X → ℝ)
    (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k) (c : ℝ)
    (hc : ∀ x, f x ≠ 0 → π i x = c) : borelAction μ hT f π = 0 := by
  classical
  let πs (n : ℕ) := Function.update π i (levelClamp c (1 / (n + 1)) (π i))
  let π₀ := Function.update π i (fun _ => c)
  have hLip : ∀ j, ∃ K : ℝ≥0, ∀ n, LipschitzWith K (πs n j) := by
    intro j
    by_cases hji : j = i
    · obtain ⟨K,hK⟩ := hπ i
      exact ⟨K, fun _ => by simpa [πs, hji] using levelClamp_lipschitz hK⟩
    · obtain ⟨K,hK⟩ := hπ j
      exact ⟨K, fun _ => by simpa [πs, Function.update_of_ne hji] using hK⟩
  have hpt : ∀ j x, Tendsto (fun n => πs n j x) atTop (𝓝 (π₀ j x)) := by
    intro j x
    by_cases hji : j = i
    · simpa [πs, π₀, hji] using levelClamp_tendsto c (π i) x
    · simp [πs, π₀, Function.update_of_ne hji]
  have hlim := borelAction_sequentialContinuity μ hT hμ hf π₀ πs hLip hpt
  have heq (n : ℕ) : borelAction μ hT f (πs n) = borelAction μ hT f π :=
    (borelAction_eq_levelClamp μ hT hμ hf π hπ i c hc (by positivity)).symm
  simp only [heq] at hlim
  have heq' := tendsto_nhds_unique hlim (tendsto_const_nhds)
  have hπ₀ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π₀ j) := by
    intro j
    by_cases hji : j = i
    · exact ⟨0, by simp [π₀, hji]⟩
    · simpa [π₀, Function.update_of_ne hji] using hπ j
  rw [← heq']
  exact borelAction_const_coord μ hT hμ hf π₀ hπ₀ i c (by simp [π₀])

theorem borelAction_congr_coord_on_support (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {f : X → ℝ} (hf : Integrable f μ) (π : Fin k → X → ℝ)
    (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k)
    (u : X → ℝ) (hu : ∃ K : ℝ≥0, LipschitzWith K u)
    (heq : ∀ x, f x ≠ 0 → π i x = u x) :
    borelAction μ hT f π = borelAction μ hT f (Function.update π i u) := by
  classical
  obtain ⟨K,hK⟩ := hπ i
  obtain ⟨L,hL⟩ := hu
  let ρ := Function.update π i (fun x => π i x - u x)
  have hρ : ∀ j, ∃ M : ℝ≥0, LipschitzWith M (ρ j) := by
    intro j
    by_cases hj : j = i
    · exact ⟨K + L, by simpa [ρ, hj] using hK.sub hL⟩
    · simpa [ρ, Function.update_of_ne hj] using hπ j
  have hz := borelAction_locality_level μ hT hμ hf ρ hρ i 0
    (fun x hx => by simp [ρ, heq x hx])
  have hl := borelAction_linearCoord μ hT hμ hf π hπ i u ⟨L,hL⟩ 1 (-1)
  have hform : Function.update π i (fun x => 1 * π i x + -1 * u x) = ρ := by
    simp only [one_mul, neg_one_mul, ← sub_eq_add_neg]
    rfl
  rw [hform, hz] at hl
  linarith

end CAT0Fillings.BorelCoefficients
end

section

open Set Filter Metric TopologicalSpace
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction
variable {Y : Type*} [MetricSpace Y] [SeparableSpace Y] [Nonempty Y]

noncomputable def metricCone (φ : Y → ℝ) (K : ℝ≥0) (q : Y) (x : Y) : ℝ :=
  φ q + (K : ℝ)*dist x q

omit [SeparableSpace Y] [Nonempty Y] in
lemma metricCone_lipschitz (φ : Y → ℝ) (K : ℝ≥0) (q : Y) :
    LipschitzWith K (metricCone φ K q) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [metricCone,Real.dist_eq,add_sub_add_left_eq_sub,←mul_sub,
    abs_mul,abs_of_nonneg K.coe_nonneg]
  exact mul_le_mul_of_nonneg_left (abs_dist_sub_le x y q) K.coe_nonneg

noncomputable def metricConeApprox (φ : Y → ℝ) (K : ℝ≥0) : ℕ → Y → ℝ
  | 0 => metricCone φ K (denseSeq Y 0)
  | n+1 => fun x => min (metricConeApprox φ K n x) (metricCone φ K (denseSeq Y (n+1)) x)

lemma metricConeApprox_lipschitz (φ : Y → ℝ) (K : ℝ≥0) (n : ℕ) :
    LipschitzWith K (metricConeApprox φ K n) := by
  induction n with
  | zero => exact metricCone_lipschitz φ K _
  | succ n ih => simpa only [metricConeApprox,max_self] using ih.min (metricCone_lipschitz φ K _)

lemma le_metricConeApprox {φ : Y → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (n : ℕ) (x : Y) :
    φ x ≤ metricConeApprox φ K n x := by
  induction n with
  | zero => exact hφ.le_add_mul _ _
  | succ n ih => exact le_min ih (hφ.le_add_mul _ _)

lemma metricConeApprox_antitone (φ : Y → ℝ) (K : ℝ≥0) (x : Y) :
    Antitone (fun n => metricConeApprox φ K n x) :=
  antitone_nat_of_succ_le fun _ => min_le_left _ _

lemma metricConeApprox_le_cone (φ : Y → ℝ) (K : ℝ≥0) {n m : ℕ} (hm : m ≤ n) (x : Y) :
    metricConeApprox φ K n x ≤ metricCone φ K (denseSeq Y m) x := by
  apply (metricConeApprox_antitone φ K x hm).trans
  cases m with
  | zero => exact le_rfl
  | succ m => exact min_le_right _ _

lemma metricConeApprox_tendsto {φ : Y → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (x : Y) :
    Tendsto (fun n => metricConeApprox φ K n x) atTop (𝓝 (φ x)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (le_metricConeApprox hφ n x)
  · intro b hb
    have hD : 0 < 2*(K : ℝ)+1 := by positivity
    obtain ⟨m,hm⟩ := (denseRange_denseSeq Y).exists_dist_lt x (div_pos (sub_pos.mpr hb) hD)
    filter_upwards [eventually_ge_atTop m] with n hn
    have hcone := metricConeApprox_le_cone φ K hn x
    have hq := hφ.le_add_mul (denseSeq Y m) x
    rw [dist_comm (denseSeq Y m) x] at hq
    have hdist : dist x (denseSeq Y m) < (b-φ x)/(2*(K : ℝ)+1) := by
      simpa only [dist_comm] using hm
    have hsmall := (lt_div_iff₀ hD).mp hdist
    dsimp only [metricCone] at hcone
    nlinarith [dist_nonneg (x := x) (y := denseSeq Y m)]

variable {X : Type*} [MetricSpace X]

structure LipLattice (P : (X → ℝ) → Prop) : Prop where
  const : ∀ c : ℝ, P (fun _ => c)
  linear : ∀ {u v : X → ℝ}, (∃ K, LipschitzWith K u) → (∃ K, LipschitzWith K v) →
    P u → P v → ∀ a c : ℝ, P (fun x => a*u x+c*v x)
  min : ∀ {u v : X → ℝ}, (∃ K, LipschitzWith K u) → (∃ K, LipschitzWith K v) →
    P u → P v → P (fun x => min (u x) (v x))
  max : ∀ {u v : X → ℝ}, (∃ K, LipschitzWith K u) → (∃ K, LipschitzWith K v) →
    P u → P v → P (fun x => max (u x) (v x))
  limit : ∀ {us : ℕ → X → ℝ} {u : X → ℝ} {K : ℝ≥0}, (∀ n, P (us n)) →
    (∀ n, LipschitzWith K (us n)) →
    (∀ x, Tendsto (fun n => us n x) atTop (𝓝 (u x))) → P u

lemma LipLattice.pi_dist {m : ℕ} {P : (X → ℝ) → Prop} (hP : LipLattice P)
    {u : X → (Fin m → ℝ)} {L : ℝ≥0} (hu : LipschitzWith L u)
    (hgen : ∀ i, P (fun x => u x i)) (q : Fin m → ℝ) :
    P (fun x => dist (u x) q) := by
  classical
  have hcoord (i : Fin m) : LipschitzWith L (fun x => u x i) :=
    (LipschitzWith.eval i).comp hu |>.weaken (by simp)
  have habs (i : Fin m) : P (fun x => |u x i-q i|) := by
    have hp := hP.linear ⟨L,hcoord i⟩ ⟨0,LipschitzWith.const _⟩ (hgen i) (hP.const (q i)) 1 (-1)
    have hn := hP.linear ⟨L,hcoord i⟩ ⟨0,LipschitzWith.const _⟩ (hgen i) (hP.const (q i)) (-1) 1
    have hp' : P (fun x => u x i-q i) := by simpa only [one_mul,neg_mul,one_mul,sub_eq_add_neg] using hp
    have hn' : P (fun x => -(u x i-q i)) := by convert hn using 1; funext x; ring
    have hsub : LipschitzWith L (fun x => u x i-q i) := by
      simpa only [add_zero] using (hcoord i).sub (LipschitzWith.const (q i))
    convert hP.max ⟨L,hsub⟩ ⟨L,hsub.neg⟩ hp' hn' using 1
    funext x
    exact abs_eq_max_neg
  have hs (s : Finset (Fin m)) :
      P (fun x => ((s.sup fun i => nndist (u x i) (q i) : ℝ≥0) : ℝ)) ∧
        LipschitzWith L (fun x => ((s.sup fun i => nndist (u x i) (q i) : ℝ≥0) : ℝ)) := by
    induction s using Finset.induction_on with
    | empty => simpa using And.intro (hP.const 0) ((LipschitzWith.const (0:ℝ)).weaken (by positivity))
    | @insert i s hi ih =>
      have hl : LipschitzWith L (fun x => (nndist (u x i) (q i) : ℝ)) :=
        by simpa only [one_mul,Function.comp_def,coe_nndist] using (LipschitzWith.dist_left (q i)).comp (hcoord i)
      have hp : P (fun x => (nndist (u x i) (q i) : ℝ)) := by
        simpa only [coe_nndist,Real.dist_eq] using habs i
      simpa only [Finset.sup_insert, NNReal.coe_max,max_self] using
        And.intro (hP.max ⟨L,hl⟩ ⟨L,ih.2⟩ hp ih.1) (hl.max ih.2)
  simpa only [dist_pi_def] using (hs Finset.univ).1

lemma LipLattice.comp_pi {m : ℕ} {P : (X → ℝ) → Prop} (hP : LipLattice P)
    {u : X → (Fin m → ℝ)} {L : ℝ≥0} (hu : LipschitzWith L u)
    (hgen : ∀ i, P (fun x => u x i)) {φ : (Fin m → ℝ) → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) : P (fun x => φ (u x)) := by
  have hc (q : Fin m → ℝ) : P (fun x => metricCone φ K q (u x)) := by
    have hp := hP.linear ⟨0,LipschitzWith.const (φ q)⟩ ⟨L,by simpa only [one_mul,Function.comp_def,coe_nndist] using (LipschitzWith.dist_left q).comp hu⟩
      (hP.const (φ q)) (hP.pi_dist hu hgen q) 1 K
    simpa only [one_mul,metricCone] using hp
  have hs : ∀ n, P (fun x => metricConeApprox φ K n (u x)) := by
    intro n
    induction n with
    | zero => exact hc _
    | succ n ih =>
      exact hP.min ⟨K*L,(metricConeApprox_lipschitz φ K n).comp hu⟩
        ⟨K*L,(metricCone_lipschitz φ K _).comp hu⟩ ih (hc _)
  exact hP.limit hs (fun n => (metricConeApprox_lipschitz φ K n).comp hu)
    (fun x => metricConeApprox_tendsto hφ (u x))

end CAT0Fillings.SliceReconstruction
end

end OAI
