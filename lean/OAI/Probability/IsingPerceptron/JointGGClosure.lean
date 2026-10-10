import Mathlib
import OAI.Probability.IsingPerceptron.TiltedLabelLaw

namespace OAI

/-! Joint G G Closure. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

 
def jointMonomialResidual (μ : Measure JointArray) (n : ℕ) (i : Fin n)
    (D : JointBlock n → ℝ) (p d : ℕ) : ℝ :=
  (n : ℝ)*(∫ x, D (jointBlockView n x)*(x (i,n)).1.1^p*(x (i,n)).2.1^d ∂μ) -
    (∫ x, D (jointBlockView n x) ∂μ)*(∫ x, (x (0,1)).1.1^p*(x (0,1)).2.1^d ∂μ) -
    ∑ j ∈ Finset.univ.erase i,
      ∫ x, D (jointBlockView n x)*(x (i,j)).1.1^p*(x (i,j)).2.1^d ∂μ

lemma jointMonomialResidual_weak_limit {L : ℕ → ProbabilityMeasure JointArray}
    {μ : ProbabilityMeasure JointArray} (hL : Tendsto L atTop (𝓝 μ))
    (n : ℕ) (i : Fin n) (D : JointBlock n → ℝ) (hD : Continuous D) (p d : ℕ) :
    Tendsto (fun N => jointMonomialResidual (L N) n i D p d) atTop
      (𝓝 (jointMonomialResidual μ n i D p d)) := by
  have hI : ∀ F : JointArray → ℝ, Continuous F →
      Tendsto (fun N => ∫ x, F x ∂(L N : Measure JointArray)) atTop
        (𝓝 (∫ x, F x ∂(μ : Measure JointArray))) := by
    intro F hF
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL)
      (BoundedContinuousFunction.mkOfCompact ⟨F,hF⟩)
  have hcD : Continuous (fun x => D (jointBlockView n x)) := hD.comp (continuous_jointBlockView n)
  have ht (j : ℕ) := hI (fun x => D (jointBlockView n x)*(x (i,j)).1.1^p*(x (i,j)).2.1^d)
    (hcD.mul (by fun_prop) |>.mul (by fun_prop))
  exact (((ht n).const_mul (n : ℝ)).sub ((hI _ hcD).mul (hI _ (by fun_prop)))).sub
    (tendsto_finsetSum _ (fun j _ => ht j))

 

theorem jointGG_of_weak_monomial_residuals {L : ℕ → ProbabilityMeasure JointArray}
    {μ : ProbabilityMeasure JointArray} (hL : Tendsto L atTop (𝓝 μ))
    (hg : ∀ n, 2 ≤ n → ∀ i : Fin n, ∀ D : JointBlock n → ℝ, Continuous D → ∀ p d : ℕ,
      Tendsto (fun N => jointMonomialResidual (L N) n i D p d) atTop (𝓝 0)) :
    HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (μ : Measure JointArray) := by
  apply joint_monomialGG_measurable
  intro n hn i D hD p d
  have he := tendsto_nhds_unique (jointMonomialResidual_weak_limit hL n i D hD p d)
    (hg n hn i D hD p d)
  dsimp only [jointMonomialResidual] at he
  linarith

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma replica_injective_map {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] {r : ℕ} (ι : Fin r → ℕ) (hi : Function.Injective ι) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun σ => fun i : Fin r => σ (ι i)) =
      Measure.pi (fun _ : Fin r => ν) := by
  have h0 : iIndepFun (fun i : ℕ => fun σ : ℕ → X => σ i)
      (Measure.infinitePi (fun _ : ℕ => ν)) := iIndepFun_infinitePi (fun _ => measurable_id)
  have h := h0.precomp hi
  have he := h.map_fun_eq_pi_map (fun _ => (by fun_prop : Measurable _).aemeasurable)
  simpa only [Measure.infinitePi_map_eval] using he

lemma replicaLaw_integral_injective {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {r : ℕ} (D : (Fin r → X) → ℝ) {C : ℝ} (hD : ∀ σ, |D σ| ≤ C)
    (ι : Fin r → ℕ) (hi : Function.Injective ι) :
    (∫ σ, D (fun i : Fin r => σ (ι i)) ∂replicaLaw P ν hν) =
      ∫ ω, ∫ σ, D σ ∂Measure.pi (fun _ : Fin r => ν ω) ∂P := by
  rw [replicaLaw_integral_bounded P ν hν (F := fun σ => D (fun i : Fin r => σ (ι i)))
    ((measurable_of_countable D).comp (by fun_prop)) (fun _ => hD _)]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => ((HasLaw.mk
    ((Measurable.of_eval (fun coordinate : Fin r => measurable_pi_apply (ι coordinate))).aemeasurable)
    (replica_injective_map (ν ω) ι hi)).integral_comp (measurable_of_countable D).aestronglyMeasurable))

def enrichedGibbs {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (ν : Measure (Spin N)) (φ : A → Spin N → ℝ) (p : EnrichedCylinderData n A) :
    Measure (Spin N × LabeledLeaf n) :=
  gibbsProbability (labeledSpinReference n ν p.1.2) (enrichedHamiltonian n h u φ p)

instance enrichedGibbs_probability {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν] (φ : A → Spin N → ℝ)
    (p : EnrichedCylinderData n A) : IsProbabilityMeasure (enrichedGibbs n h u ν φ p) :=
  inferInstanceAs (IsProbabilityMeasure (gibbsProbability _ _))

lemma measurable_enrichedGibbs {N : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) :
    Measurable (enrichedGibbs n h u ν φ) :=
  measurable_gibbsProbability
    (ν := fun p : EnrichedCylinderData n A => labeledSpinReference n ν p.1.2)
    ((measurable_labeledSpinReference n ν).comp measurable_fst.snd)
    (measurable_enrichedHamiltonian n h u hm)

lemma spinOverlap_mem {N : ℕ} (x y : Spin N) : spinOverlap x y ∈ Icc (-1:ℝ) 1 := by
  by_cases hn : N = 0
  · subst N; simp [spinOverlap]
  · exact abs_le.mp (abs_spinOverlap_le (Nat.pos_of_ne_zero hn) x y)

lemma treeOverlap_mem (n : ℕ) (x y : LabeledLeaf n) : treeOverlap n x y ∈ Icc (0:ℝ) 1 := by
  constructor
  · unfold treeOverlap; positivity
  · unfold treeOverlap
    apply (div_le_one (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    exact_mod_cast (labeledCommonDepth_le n x y).trans (Nat.le_succ n)

def enrichedJointEntry {N : ℕ} (n : ℕ) (x y : Spin N × LabeledLeaf n) : JointEntry :=
  (⟨spinOverlap x.1 y.1,spinOverlap_mem x.1 y.1⟩,⟨treeOverlap n x.2 y.2,treeOverlap_mem n x.2 y.2⟩)

def enrichedReplicaLaw {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) : Measure (ℕ → Spin N × LabeledLeaf n) :=
  replicaLaw (enrichedCylinderLaw P r n b) (enrichedGibbs n h u ν φ) (measurable_enrichedGibbs n h u ν hm)

instance enrichedReplicaLaw_probability {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) : IsProbabilityMeasure (enrichedReplicaLaw P r n b h u ν hm) :=
  inferInstanceAs (IsProbabilityMeasure (replicaLaw _ _ _))

def enrichedArrayLaw {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) : ProbabilityMeasure JointArray :=
  overlapArrayLaw (enrichedCylinderLaw P r n b) (enrichedGibbs n h u ν φ)
    (measurable_enrichedGibbs n h u ν hm) (enrichedJointEntry n)

lemma enrichedReplicaLaw_integral {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0)
    {m : ℕ} (D : (Fin m → Spin N × LabeledLeaf n) → ℝ) {C : ℝ} (hD : ∀ σ, |D σ| ≤ C)
    (ι : Fin m → ℕ) (hi : Function.Injective ι) :
    (∫ σ, D (fun i => σ (ι i)) ∂enrichedReplicaLaw P r n b h u ν hm) =
      enrichedReplicaAverage P r n b h u ν φ D := by
  rw [enrichedReplicaLaw,replicaLaw_integral_injective _ _ _ D hD ι hi]
  unfold enrichedReplicaAverage
  apply integral_congr_ae
  filter_upwards [enrichedCylinder_exp_ae hN n b hh h0 u hu ν P hK hφ r] with z hz
  change Integrable (fun s => Real.exp (enrichedHamiltonian n h u φ z s))
    (labeledSpinReference n ν z.1.2) at hz
  rw [referenceReplicaMean_eq_tilted _ _ hz]
  simp only [enrichedGibbs,gibbsProbability_eq_tilted _ _ hz]

lemma enrichedArrayLaw_integral {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ)
    (F : JointArray → ℝ) (hF : Measurable F) :
    (∫ x, F x ∂(enrichedArrayLaw P r n b h u ν hm : Measure JointArray)) =
      ∫ σ, F (sampledOverlapArray (enrichedJointEntry n) σ) ∂enrichedReplicaLaw P r n b h u ν hm := by
  exact integral_map (measurable_sampledOverlapArray (enrichedJointEntry n)).aemeasurable hF.aestronglyMeasurable

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 
def enrichedCoordinateObjective {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (j : Fin N) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (v : ℝ) : ℝ :=
  -enrichedMeanPressure P r n b h (Function.update u j v) ν φ +
    perturbationWeight j*(v-3/2)^2

lemma enriched_contact_cgf {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (j : Fin N)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0)
    {s : ℝ} (hlo : 1 ≤ u j-s) (hhi : u j+s ≤ 2) (hs : 0 < s)
    (hmin : ∀ v ∈ Icc (1:ℝ) 2, enrichedCoordinateObjective P r n b h u j ν φ (u j) ≤
      enrichedCoordinateObjective P r n b h u j ν φ v) :
    let a := perturbationAmplitude N j
    let Q := (enrichedFrozenLaw P r n b j).prod gaussianCoordinates
    let L := fun t => ∫ z, cgf (fun x => cylinderField
      (monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2 x) z.2)
      (enrichedFrozenReference n h u j ν φ z.1) t ∂Q
    ∀ t ∈ Icc (a*u j-a*s) (a*u j+a*s),
      -L (a*u j)+(N*perturbationWeight j/a^2)*(a*u j-a*(3/2))^2 ≤
      -L t+(N*perturbationWeight j/a^2)*(t-a*(3/2))^2 := by
  let a := perturbationAmplitude N j
  have ha : 0 < a := perturbationAmplitude_pos hN j
  have hn : (0:ℝ) ≤ N := Nat.cast_nonneg N
  dsimp only
  intro t ht
  have ht' : t/a ∈ Icc (1:ℝ) 2 := by
    constructor
    · apply (le_div_iff₀ ha).2
      nlinarith [ht.1]
    · apply (div_le_iff₀ ha).2
      nlinarith [ht.2]
  have htabs : |t/a| ≤ 2 := abs_le.mpr ⟨by linarith [ht'.1],ht'.2⟩
  have htmean := (enrichedCGF_integral hN n b hb hh h0 u hu j htabs ν P hm hK hφ r).2
  have hvmean := (enrichedCGF_integral hN n b hb hh h0 u hu j (hu j) ν P hm hK hφ r).2
  change (∫ z, cgf (fun x => cylinderField
    (monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2 x) z.2)
    (enrichedFrozenReference n h u j ν φ z.1) (a*(t/a))
      ∂(enrichedFrozenLaw P r n b j).prod gaussianCoordinates) = _ at htmean
  rw [mul_div_cancel₀ _ ha.ne'] at htmean
  rw [show perturbationAmplitude N j = a from rfl]
  change (∫ z, cgf (fun x => cylinderField
    (monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2 x) z.2)
    (enrichedFrozenReference n h u j ν φ z.1) (a*u j)
      ∂(enrichedFrozenLaw P r n b j).prod gaussianCoordinates) = _ at hvmean
  rw [htmean,hvmean]
  have hc := mul_le_mul_of_nonneg_left (hmin (t/a) ht') hn
  unfold enrichedCoordinateObjective at hc
  have he1 : (N*perturbationWeight j/a^2)*(a*u j-a*(3/2))^2 =
      N*(perturbationWeight j*(u j-3/2)^2) := by field_simp [ha.ne']
  have he2 : (N*perturbationWeight j/a^2)*(t-a*(3/2))^2 =
      N*(perturbationWeight j*(t/a-3/2)^2) := by field_simp [ha.ne']
  rw [he1,he2]
  linarith

 

theorem enriched_gg_at_coordinate_minimum {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    {H : ℝ} (hH : h n ≤ H) (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (j : Fin N)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) {α : ℝ} (hr : (r:ℝ) ≤ α*N)
    {s θ : ℝ} (hs : 0 < s) (hθ : 0 < θ) (hlo : 1 ≤ u j-s) (hhi : u j+s ≤ 2)
    (hmin : ∀ v ∈ Icc (1:ℝ) 2, enrichedCoordinateObjective P r n b h u j ν φ (u j) ≤
      enrichedCoordinateObjective P r n b h u j ν φ v)
    {m : ℕ} (D : (Fin (m+1) → Spin N × LabeledLeaf n) → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hD : ∀ σ, |D σ| ≤ B) :
    let a := perturbationAmplitude N j
    let c := N*perturbationWeight j/a^2
    let C := 4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
    let δ := 2*N*Real.sqrt ((C+H+4+5*K^2*α)/N)
    let κ := fun x y : Spin N × LabeledLeaf n =>
      spinOverlap x.1 y.1 ^ (monomialIndex j).1 * treeOverlap n x.2 y.2 ^ (monomialIndex j).2
    |a*u j| * |(m+1 : ℕ)*enrichedReplicaAverage P r n b h u ν φ
        (fun τ : Fin (m+1+1) → Spin N × LabeledLeaf n => D (Fin.tail τ)*κ ((Fin.tail τ) 0) (τ 0)) -
      enrichedReplicaAverage P r n b h u ν φ D * enrichedReplicaAverage P r n b h u ν φ
        (fun τ : Fin 2 → Spin N × LabeledLeaf n => κ (τ 1) (τ 0)) -
      enrichedReplicaAverage P r n b h u ν φ
        (fun σ => D σ*(∑ l : Fin m, κ (σ 0) (σ l.succ)))| ≤
      2*B*((2*c+θ^2)/(2*θ)+c*(a*s)+4*δ/(a*s)) := by
  let a := perturbationAmplitude N j
  have ha : 0 < a := perturbationAmplitude_pos hN j
  let δ := 2*N*Real.sqrt ((4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2
    ∂(rawCascadeLaw n b : Measure (RawTree n)))+H+4+5*K^2*α)/N)
  have hν := measurable_enrichedFrozenReference n h u j ν hm
  have hcontact := enriched_contact_cgf hN n b hb hh h0 u hu j ν P hm hK hφ r hlo hhi hs hmin
  have hconc : ∀ t ∈ ({a*u j-a*s,a*u j,a*u j+a*s} : Set ℝ),
      (∫ z : EnrichedFrozenData n j A × (ℕ → ℝ),
        |cgf (fun x => cylinderField (monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2 x) z.2)
          (enrichedFrozenReference n h u j ν φ z.1) t -
        (∫ z' : EnrichedFrozenData n j A × (ℕ → ℝ),
          cgf (fun x => cylinderField (monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2 x) z'.2)
          (enrichedFrozenReference n h u j ν φ z'.1) t
          ∂(enrichedFrozenLaw P r n b j).prod gaussianCoordinates)|
        ∂(enrichedFrozenLaw P r n b j).prod gaussianCoordinates) ≤ δ := by
    intro t ht
    have hti : t/a ∈ Icc (1:ℝ) 2 := by
      rcases ht with ht | ht | ht
      · rw [ht]
        constructor <;> (first | apply (le_div_iff₀ ha).2 | apply (div_le_iff₀ ha).2) <;> nlinarith
      · rw [ht]
        rw [mul_div_cancel_left₀ _ ha.ne']
        constructor <;> linarith
      · rw [Set.mem_singleton_iff.mp ht]
        constructor <;> (first | apply (le_div_iff₀ ha).2 | apply (div_le_iff₀ ha).2) <;> nlinarith
    have hbnd := enrichedCGF_center_bound hN n b hb hh h0 hH u hu j
      (v := t/a) (abs_le.mpr ⟨by linarith [hti.1],hti.2⟩) ν P hm hK hφ r hr
    simpa only [enrichedCGF,show perturbationAmplitude N j = a from rfl,mul_div_cancel₀ _ ha.ne'] using hbnd
  have hg := monomial_gg_at_minimum (P := enrichedFrozenLaw P r n b j) hN hν
    (monomialIndex j).1 (monomialIndex j).2 (mul_pos ha hs) hθ hcontact hconc D hB hD
  have hrep {l : ℕ} (E : (Fin l → Spin N × LabeledLeaf n) → ℝ) :
      randomReplicaAverage (enrichedFrozenLaw P r n b j) (enrichedFrozenReference n h u j ν φ)
        (monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2) (a*u j) E =
        enrichedReplicaAverage P r n b h u ν φ E := by
    have he := enrichedReplicaAverage_eq_random hN n b hh h0 u hu j (hu j) ν P hm hK hφ r E
    simpa only [Function.update_eq_self] using he.symm
  dsimp only at hg ⊢
  rw [hrep,hrep,hrep,hrep] at hg
  exact hg

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussian_log_partition_mean_bounds {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) :
    0 ≤ (∫ ω, Real.log (∫ x, Real.exp (H (ω,x)) ∂ν) ∂μ) ∧
      (∫ ω, Real.log (∫ x, Real.exp (H (ω,x)) ∂ν) ∂μ) ≤ K/2 := by
  let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
  have hmZ : Measurable Z := hm.exp.stronglyMeasurable.integral_prod_right'.measurable
  have hiH := gaussian_field_integrable (ν := ν) hm hg hv
  have hexp := gaussian_field_exp_integrable (ν := ν) hm hg hv 1
  simp only [one_mul,one_pow] at hexp
  have hZ : Integrable Z μ := hexp.1.integral_prod_left
  have hpos : ∀ᵐ ω ∂μ, 0 < Z ω := by
    filter_upwards [hexp.1.prod_right_ae] with ω hω
    exact MeasureTheory.integral_exp_pos hω
  have hiLog : Integrable (fun ω => Real.log (Z ω)) μ :=
    ((memLp_two_iff_integrable_sq hmZ.log.aestronglyMeasurable).2
      (gaussian_log_partition_second hm hg hv).1).integrable (by norm_num)
  have hexplog : Integrable (fun ω => Real.exp (Real.log (Z ω))) μ := by
    apply hZ.congr
    filter_upwards [hpos] with ω hω
    exact (Real.exp_log hω).symm
  have hmean : (∫ ω, ∫ x, H (ω,x) ∂ν ∂μ) = 0 := by
    rw [integral_integral_swap (f := fun ω x => H (ω,x)) hiH]
    have hz : ∀ x, (∫ ω, H (ω,x) ∂μ) = 0 := by
      intro x
      have hmx : Measurable (fun ω => H (ω,x)) := hm.comp (measurable_id.prodMk measurable_const)
      have he := integral_map hmx.aemeasurable (measurable_id.aestronglyMeasurable :
        AEStronglyMeasurable (fun y : ℝ => y) (μ.map (fun ω => H (ω,x))))
      simp only [hg x,id_eq,integral_id_gaussianReal] at he
      exact he.symm
    simp_rw [hz]
    simp
  refine ⟨?_, ?_⟩
  · rw [← hmean]
    apply integral_mono_ae hiH.integral_prod_left hiLog
    filter_upwards [hiH.prod_right_ae,hexp.1.prod_right_ae,hpos] with ω hω heω hpω
    exact Real.exp_le_exp.mp (by
      rw [Real.exp_log hpω]
      exact exp_integral_le_partition hω heω)
  · apply Real.exp_le_exp.mp
    calc
      _ ≤ ∫ ω, Real.exp (Real.log (Z ω)) ∂μ := exp_integral_le_partition hiLog hexplog
      _ = ∫ ω, Z ω ∂μ := integral_congr_ae (hpos.mono (fun _ h => Real.exp_log h))
      _ ≤ _ := hexp.2

lemma cylinder_cgf_mean_bounds {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (A : X → ℕ →₀ ℝ) {K : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    0 ≤ (∫ g, cgf (fun x => cylinderField (A x) g) ν t ∂gaussianCoordinates) ∧
      (∫ g, cgf (fun x => cylinderField (A x) g) ν t ∂gaussianCoordinates) ≤ t^2*K/2 := by
  have hm : Measurable (fun z : (ℕ → ℝ) × X => t*cylinderField (A z.2) z.1) :=
    (measurable_cylinderFields A).const_mul t
  have hv (x : X) : ((⟨t^2,sq_nonneg t⟩ : NNReal)*(((A x).sum (fun _ c => c^2)).toNNReal) : ℝ) ≤ t^2*K := by
    change t^2*((((A x).sum (fun _ c => c^2)).toNNReal : NNReal) : ℝ) ≤ t^2*K
    rw [Real.coe_toNNReal _ (show 0 ≤ (A x).sum (fun _ c => c^2) from
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hA x) (sq_nonneg _)
  exact gaussian_log_partition_mean_bounds (ν := ν) hm (fun x => cylinder_scaled_law A x t) hv

lemma random_cylinder_cgf_mean_bounds {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) {K : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    let F := fun z : Ω × (ℕ → ℝ) => cgf (fun x => cylinderField (A x) z.2) (ν z.1) t
    0 ≤ (∫ z, F z ∂P.prod gaussianCoordinates) ∧
      (∫ z, F z ∂P.prod gaussianCoordinates) ≤ t^2*K/2 := by
  have hi := integrable_random_cylinder_cgf (P := P) hν A hA t
  dsimp only
  rw [integral_prod _ hi]
  refine ⟨integral_nonneg (fun ω => (cylinder_cgf_mean_bounds (ν ω) A hA t).1), ?_⟩
  calc
    _ ≤ ∫ _ : Ω, t^2*K/2 ∂P := integral_mono hi.integral_prod_left
      (integrable_const _) (fun ω => (cylinder_cgf_mean_bounds (ν ω) A hA t).2)
    _ = _ := by simp

 

lemma enriched_coordinate_pressure_cost {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (j : Fin N) {v : ℝ} (hv : |v| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    let d := enrichedMeanPressure P r n b h (Function.update u j v) ν φ -
      enrichedMeanPressure P r n b h (Function.update u j 0) ν φ
    0 ≤ d ∧ d ≤ (perturbationAmplitude N j*v)^2/(2*N) := by
  have he := (enrichedCGF_integral hN n b hb hh h0 u hu j hv ν P hm hK hφ r).2
  have hbnd := random_cylinder_cgf_mean_bounds (P := enrichedFrozenLaw P r n b j)
    (measurable_enrichedFrozenReference n h u j ν hm)
    (monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2)
    (monomialCoefficients_variance_le hN n (monomialIndex j).1 (monomialIndex j).2)
    (perturbationAmplitude N j*v)
  change 0 ≤ (∫ z, enrichedCGF n h u j ν φ v z ∂(enrichedFrozenLaw P r n b j).prod gaussianCoordinates) ∧
    (∫ z, enrichedCGF n h u j ν φ v z ∂(enrichedFrozenLaw P r n b j).prod gaussianCoordinates) ≤
      (perturbationAmplitude N j*v)^2*1/2 at hbnd
  rw [he] at hbnd
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  dsimp only
  constructor
  · exact nonneg_of_mul_nonneg_right hbnd.1 hn
  · apply (le_div_iff₀ (by positivity : 0 < 2*(N:ℝ))).2
    nlinarith [hbnd.2]

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma perturbationWeight_pos (j : ℕ) : 0 < perturbationWeight j := by
  unfold perturbationWeight
  positivity

lemma perturbationAmplitude_sq (N j : ℕ) :
    (perturbationAmplitude N j)^2 = N*(perturbationScale N)^2*(perturbationWeight j)^2 := by
  unfold perturbationAmplitude
  rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]

lemma enriched_coordinate_minimum_penalty {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (j : Fin N)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0)
    (hmin : ∀ v ∈ Icc (1:ℝ) 2, enrichedCoordinateObjective P r n b h u j ν φ (u j) ≤
      enrichedCoordinateObjective P r n b h u j ν φ v) :
    (u j-3/2)^2 ≤ 2*(perturbationScale N)^2*perturbationWeight j := by
  have hc := hmin (3/2) (by norm_num)
  unfold enrichedCoordinateObjective at hc
  have hv := enriched_coordinate_pressure_cost hN n b hb hh h0 u hu j (hu j) ν P hm hK hφ r
  have hz := (enriched_coordinate_pressure_cost hN n b hb hh h0 u hu j
    (v := 3/2) (by norm_num) ν P hm hK hφ r).1
  dsimp only at hv hz
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hw := perturbationWeight_pos j
  have ha := perturbationAmplitude_sq N j
  have hanu : (perturbationAmplitude N j*u j)^2/(2*N) ≤
      2*(perturbationScale N)^2*(perturbationWeight j)^2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*(N:ℝ))).2
    rw [mul_pow,ha]
    have hu2 : (u j)^2 ≤ 4 := by
      have ha := (abs_le.mp (hu j))
      nlinarith [sq_nonneg (u j+2),sq_nonneg (u j-2)]
    nlinarith [mul_le_mul_of_nonneg_left hu2
      (show 0 ≤ (N:ℝ)*(perturbationScale N)^2*(perturbationWeight j)^2 by positivity)]
  have hmul : perturbationWeight j*(u j-3/2)^2 ≤
      perturbationWeight j*(2*(perturbationScale N)^2*perturbationWeight j) := by
    nlinarith [hv.2]
  exact (mul_le_mul_iff_right₀ hw).mp hmul

lemma enriched_coordinate_minimum_interior {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (j : Fin N)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0)
    (hmin : ∀ v ∈ Icc (1:ℝ) 2, enrichedCoordinateObjective P r n b h u j ν φ (u j) ≤
      enrichedCoordinateObjective P r n b h u j ν φ v)
    (he : perturbationScale N ≤ 1/8) {s : ℝ} (hs : s ≤ 1/4) :
    1 ≤ u j-s ∧ u j+s ≤ 2 := by
  have hp := enriched_coordinate_minimum_penalty hN n b hb hh h0 u hu j ν P hm hK hφ r hmin
  have he0 := perturbationScale_nonneg N
  have hw := perturbationWeight_le_one j
  have hbnd : (u j-3/2)^2 ≤ 1/32 := by
    have hmul := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2*(perturbationScale N)^2 by positivity)
    nlinarith [sq_nonneg (perturbationScale N-1/8)]
  constructor <;> nlinarith [sq_nonneg (u j-3/2-1/4),sq_nonneg (u j-3/2+1/4)]

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def contactStep (N : ℕ) : ℝ := (N:ℝ)^(-1/4:ℝ)

def contactGGRate (N j : ℕ) (L B : ℝ) : ℝ :=
  let a := perturbationAmplitude N j
  let c := N*perturbationWeight j/a^2
  let θ := 1/perturbationScale N
  let δ := 2*N*Real.sqrt (L/N)
  2*B*((2*c+θ^2)/(2*θ)+c*(a*contactStep N)+4*δ/(a*contactStep N))/a

lemma contactGGRate_eq {N : ℕ} (hN : 0 < N) (j : ℕ) (L B : ℝ) :
    contactGGRate N j L B =
      (B*(2/perturbationWeight j+1)/perturbationWeight j)*(N:ℝ)^(-3/8:ℝ) +
      (2*B/perturbationWeight j)*(N:ℝ)^(-1/8:ℝ) +
      (16*B*Real.sqrt L/(perturbationWeight j)^2)*(N:ℝ)^(-1/8:ℝ) := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have he : 0 < perturbationScale N := Real.rpow_pos_of_pos hn _
  have hs : 0 < contactStep N := Real.rpow_pos_of_pos hn _
  have hw := perturbationWeight_pos j
  have hr : 0 < Real.sqrt N := Real.sqrt_pos.2 hn
  have he2 : (perturbationScale N)^2 = (N:ℝ)^(-1/8:ℝ) := by
    unfold perturbationScale
    rw [← Real.rpow_mul_natCast hn.le]
    congr 1
    norm_num
  have h1 : 1/(Real.sqrt N*(perturbationScale N)^2) = (N:ℝ)^(-3/8:ℝ) := by
    rw [Real.sqrt_eq_rpow,he2,← Real.rpow_add hn,one_div,← Real.rpow_neg hn.le]
    norm_num
  have h2 : contactStep N/(perturbationScale N)^2 = (N:ℝ)^(-1/8:ℝ) := by
    rw [he2]
    unfold contactStep
    rw [← Real.rpow_sub hn]
    norm_num
  have h3 : 1/(Real.sqrt N*(perturbationScale N)^2*contactStep N) = (N:ℝ)^(-1/8:ℝ) := by
    rw [Real.sqrt_eq_rpow,he2]
    unfold contactStep
    rw [← Real.rpow_add hn,← Real.rpow_add hn,one_div,← Real.rpow_neg hn.le]
    norm_num
  calc
    contactGGRate N j L B =
      (B*(2/perturbationWeight j+1)/perturbationWeight j)*(1/(Real.sqrt N*(perturbationScale N)^2)) +
      (2*B/perturbationWeight j)*(contactStep N/(perturbationScale N)^2) +
      (16*B*Real.sqrt L/(perturbationWeight j)^2)*(1/(Real.sqrt N*(perturbationScale N)^2*contactStep N)) := by
        unfold contactGGRate perturbationAmplitude
        rw [Real.sqrt_div' L hn.le]
        have hn' : (N:ℝ) = (Real.sqrt N)^2 := (Real.sq_sqrt hn.le).symm
        conv_lhs => rw [hn']
        simp only [Real.sqrt_sq hr.le]
        field_simp
        ring
    _ = _ := by rw [h1,h2,h3]

lemma tendsto_nat_rpow_neg {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => (N:ℝ)^(-c)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hc).comp tendsto_natCast_atTop_atTop

lemma perturbationScale_tendsto : Tendsto perturbationScale atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => (N:ℝ)^(-1/16:ℝ)) atTop (𝓝 0)
  simpa only [neg_div] using tendsto_nat_rpow_neg (c := 1/16) (by norm_num)

lemma contactStep_tendsto : Tendsto contactStep atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => (N:ℝ)^(-1/4:ℝ)) atTop (𝓝 0)
  simpa only [neg_div] using tendsto_nat_rpow_neg (c := 1/4) (by norm_num)

lemma contactGGRate_tendsto (j : ℕ) (L B : ℝ) :
    Tendsto (fun N => contactGGRate N j L B) atTop (𝓝 0) := by
  have h1 := (tendsto_nat_rpow_neg (c := 3/8) (by norm_num)).const_mul
    (B*(2/perturbationWeight j+1)/perturbationWeight j)
  have h2 := (tendsto_nat_rpow_neg (c := 1/8) (by norm_num)).const_mul (2*B/perturbationWeight j)
  have h3 := (tendsto_nat_rpow_neg (c := 1/8) (by norm_num)).const_mul
    (16*B*Real.sqrt L/(perturbationWeight j)^2)
  apply Tendsto.congr' _ (show Tendsto _ _ (𝓝 (0:ℝ)) from by simpa using (h1.add h2).add h3)
  filter_upwards [eventually_gt_atTop 0] with N hN
  simpa only [neg_div,one_div] using (contactGGRate_eq hN j L B).symm

end IsingPerceptron

end

end OAI
