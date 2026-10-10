import Mathlib
import OAI.Probability.Ballisticity.Estimates.BufferStageCount
import OAI.Probability.Ballisticity.Walk.CoordinateKernelComp

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical

lemma countable_prod_bind {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    [Countable A] [Countable B] [Countable C] [Countable D]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    [MeasurableSingletonClass C] [MeasurableSingletonClass D]
    (μ : Measure A) (ν : Measure B) [SFinite ν]
    (K : A → Measure C) (L : B → Measure D) [∀ b, SFinite (L b)] [SFinite (ν.bind L)] :
    (μ.prod ν).bind (fun p => (K p.1).prod (L p.2)) = (μ.bind K).prod (ν.bind L) := by
  apply Measure.ext_of_singleton
  rintro ⟨c,d⟩
  rw [Measure.bind_apply (measurableSet_singleton _) (measurable_of_countable _).aemeasurable]
  simp_rw [←Set.singleton_prod_singleton,Measure.prod_prod]
  rw [Measure.bind_apply (measurableSet_singleton _) (measurable_of_countable _).aemeasurable,
    Measure.bind_apply (measurableSet_singleton _) (measurable_of_countable _).aemeasurable]
  rw [lintegral_prod _ (measurable_of_countable _).aemeasurable]
  exact lintegral_lintegral_mul (measurable_of_countable (fun a => K a {c})).aemeasurable (measurable_of_countable (fun b => L b {d})).aemeasurable

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma rawPairEndpointLaw_comp_le {d : ℕ} (e : Direction d) (k m : ℕ)
    (ω : Environment d) (x : Lattice d × Lattice d) :
    rawPairMixture (realPosition (step e)) m (rawPairEndpointLaw (realPosition (step e)) k ω x) ω ≤
      rawPairEndpointLaw (realPosition (step e)) (k+m) ω x := by
  let ℓ := realPosition (step e)
  let K := fun (n : ℕ) (y : Lattice d) => hitKernel (Strip ℓ y n) (Upper ℓ y n) (ω,y)
  have hone (n : ℕ) (y : Lattice d) : K n y Set.univ ≤ 1 :=
    hitKernel_total_le_one (disjoint_strip_upper ℓ y n) (ω,y)
  let hfinite : ∀ (n : ℕ) (y : Lattice d), IsFiniteMeasure (K n y) := fun n y =>
    ⟨lt_of_le_of_lt (hone n y) ENNReal.one_lt_top⟩
  have hcomp (y : Lattice d) : (K k y).bind (K m) ≤ K (k+m) y := by
    intro U
    rw [Measure.bind_apply (Set.to_countable _).measurableSet (measurable_of_countable _).aemeasurable]
    simpa only [K,ℓ,Nat.cast_add] using coordinate_raw_kernel_comp_le e k m ω y U
  let : IsFiniteMeasure ((K k x.2).bind (K m)) :=
    ⟨lt_of_le_of_lt ((hcomp x.2 Set.univ).trans (hone (k+m) x.2)) ENNReal.one_lt_top⟩
  change ((K k x.1).prod (K k x.2)).bind (fun p => (K m p.1).prod (K m p.2)) ≤
    (K (k+m) x.1).prod (K (k+m) x.2)
  rw [countable_prod_bind]
  exact Measure.prod_mono (hcomp x.1) (hcomp x.2)

lemma rawPairMixture_comp_le {d : ℕ} (e : Direction d) (k m : ℕ)
    (ω : Environment d) (π : Measure (Lattice d × Lattice d)) :
    rawPairMixture (realPosition (step e)) m (rawPairMixture (realPosition (step e)) k π ω) ω ≤
      rawPairMixture (realPosition (step e)) (k+m) π ω := by
  intro U
  rw [rawPairMixture_apply,rawPairMixture_apply]
  change (∫⁻ y, rawPairEndpointLaw (realPosition (step e)) m ω y U
    ∂π.bind (rawPairEndpointLaw (realPosition (step e)) k ω)) ≤ _
  rw [Measure.lintegral_bind (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
  apply lintegral_mono
  intro x
  simpa only [rawPairMixture_apply] using (rawPairEndpointLaw_comp_le e k m ω x) U
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def bufferRetentionCost (R₀ g : ℝ) (κ : ℝ≥0) : ℝ≥0∞ :=
  ((κ:ℝ≥0∞)^2*ENNReal.ofReal g)*(κ:ℝ≥0∞)^(⌈max 0 R₀⌉₊+2)

lemma bufferRetentionCost_pos (R₀ : ℝ) {g : ℝ} (hg : 0 < g) {κ : ℝ≥0} (hκ : 0 < κ) :
    0 < bufferRetentionCost R₀ g κ := by
  unfold bufferRetentionCost
  positivity

lemma bufferChildNode_retained_uniform {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) {κ : ℝ≥0} (hκ1 : κ ≤ 1) (hg1 : g ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hα : 0 ≤ α)
    (N : AdaptedBufferNode e) (hr : 0 ≤ N.radius) (hN : BufferNodeValid e f z₀ κ N)
    (H : ℕ) (hH : 0 < H) (k : ℕ) (b : Bool) (ω : Environment d)
    (hκ : ∀ y u, κ ≤ (ω y).1 u)
    (ha : ω ∈ (bufferChildNode e f hef R₀ z₀ ε α g κ N H hH k b).active) :
    bufferRetentionCost R₀ g κ • ((bufferChildNode e f hef R₀ z₀ ε α g κ N H hH k b).law ω).val ≤
      rawPairMixture (realPosition (step e)) (k+1) (N.law ω).val ω := by
  have hm := bufferRestoreLength_le hr hε1 hα b (R₀ := R₀)
  have hk1 : (κ:ℝ≥0∞) ≤ 1 := by exact_mod_cast hκ1
  have hp := pow_le_pow_of_le_one (show (0:ℝ≥0∞) ≤ κ from zero_le) hk1 (Nat.add_le_add_right hm 2)
  have hc : bufferRetentionCost R₀ g κ ≤
      ((κ:ℝ≥0∞)^2*ENNReal.ofReal g)*(κ:ℝ≥0∞)^(bufferRestoreLength R₀ N.radius ε α b+2) := by
    unfold bufferRetentionCost
    gcongr
  have hsmul : bufferRetentionCost R₀ g κ • ((bufferChildNode e f hef R₀ z₀ ε α g κ N H hH k b).law ω).val ≤
      (((κ:ℝ≥0∞)^2*ENNReal.ofReal g)*(κ:ℝ≥0∞)^(bufferRestoreLength R₀ N.radius ε α b+2)) •
      ((bufferChildNode e f hef R₀ z₀ ε α g κ N H hH k b).law ω).val := by
    intro U
    simp only [Measure.smul_apply,smul_eq_mul]
    gcongr
  exact hsmul.trans ((bufferChildNode_retained_composed e f hef R₀ z₀ ε α g hκ1 hg1 hε
    N hr hN H hH k b ω hκ ha).trans (rawPairMixture_comp_le e k 1 ω (N.law ω).val))
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma bufferNodeAt_retained {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (z₀ ε α g : ℝ) {κ : ℝ≥0}
    (hκpos : 0 < κ) (hκ1 : κ ≤ 1) (hg : 0 < g) (hg1 : g ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hα : 0 ≤ α)
    (H : ℝ → ℕ) (hH : ∀ r, 0 < H r) (root : AdaptedBufferNode e)
    (hr : R₀ ≤ root.radius) (hroot : BufferNodeValid e f z₀ κ root)
    (l : List (ℕ × Bool)) (ω : Environment d) (hκ : ∀ y u, κ ≤ (ω y).1 u)
    (ha : ω ∈ (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l).active) :
    (bufferRetentionCost R₀ g κ)^l.length • ((bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l).law ω).val ≤
      rawPairMixture (realPosition (step e)) (bufferWordHeight l) (root.law ω).val ω := by
  induction l with
  | nil => simp only [List.length_nil,pow_zero,one_smul,bufferWordHeight,bufferNodeAt,rawPairMixture_zero,le_refl]
  | cons p l ih =>
    let N := bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l
    let q := bufferRetentionCost R₀ g κ
    have hpa : ω ∈ N.active := ha.1
    have hv := bufferNodeAt_valid e f hef hR₀ z₀ ε α g hκpos hκ1 hg hg1 hε H hH root hr hroot l
    have hnr := hR₀.trans (bufferNodeAt_radius e f hef R₀ z₀ ε α g κ H hH root hr l)
    have hc := bufferChildNode_retained_uniform e f hef R₀ z₀ ε α g hκ1 hg1 hε hε1 hα
      N hnr hv (H N.radius) (hH N.radius) p.1 p.2 ω hκ ha
    have hs : q^l.length • (q • ((bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root (p::l)).law ω).val) ≤
        q^l.length • rawPairMixture (realPosition (step e)) (p.1+1) (N.law ω).val ω := by
      intro U
      simp only [Measure.smul_apply,smul_eq_mul]
      have hh := hc U
      simp only [Measure.smul_apply,smul_eq_mul] at hh
      gcongr
      exact hh
    rw [←rawPairMixture_smul] at hs
    have hm := rawPairMixture_mono (realPosition (step e)) (p.1+1) ω (ih hpa)
    have hh := hs.trans (hm.trans (rawPairMixture_comp_le e (bufferWordHeight l) (p.1+1) ω (root.law ω).val))
    simpa only [q,smul_smul,List.length_cons,pow_succ,bufferWordHeight,Nat.add_comm] using hh
end DirectionalTransience

end

end

end OAI
