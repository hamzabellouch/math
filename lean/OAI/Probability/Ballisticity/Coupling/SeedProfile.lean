import Mathlib
import OAI.Probability.Ballisticity.Coupling.SeedMedian

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def SeedProfile {d : ℕ} (e : Direction d) (a : ℤ) :=
  {μ : ProbabilityMeasure (Lattice d) // ∀ᵐ x ∂μ.toMeasure, signedHeight e x=a}

instance seedProfile_measurableSpace {d : ℕ} (e : Direction d) (a : ℤ) : MeasurableSpace (SeedProfile e a) :=
  inferInstanceAs (MeasurableSpace {μ : ProbabilityMeasure (Lattice d) // ∀ᵐ x ∂μ.toMeasure, signedHeight e x=a})

noncomputable def SeedProfile.measure {d : ℕ} {e : Direction d} {a : ℤ} (μ : SeedProfile e a) : Measure (Lattice d) := μ.val.toMeasure
instance SeedProfile.probability {d : ℕ} {e : Direction d} {a : ℤ} (μ : SeedProfile e a) : IsProbabilityMeasure μ.measure := μ.val.property

lemma SeedProfile.measurable_measure {d : ℕ} (e : Direction d) (a : ℤ) :
    Measurable (SeedProfile.measure (e:=e) (a:=a)) := measurable_subtype_coe.comp measurable_subtype_coe

noncomputable def seedHalfProfile {d : ℕ} (e f : Direction d) (a s : ℤ) (upper : Bool)
    (μ : SeedProfile e a) : SeedProfile e a :=
  ⟨seedHalf f s upper μ.val,seedHalf_inherits f s upper μ.val _ μ.property⟩

lemma measurable_seedHalfProfile {d : ℕ} (e f : Direction d) (a s : ℤ) (upper : Bool) :
    Measurable (seedHalfProfile e f a s upper) :=
  ((measurable_seedHalf f s upper).comp measurable_subtype_coe).subtype_mk

noncomputable def seedShift {d : ℕ} (e : Direction d) (H : ℕ) (μ : ProbabilityMeasure (Lattice d)) :
    ProbabilityMeasure (Lattice d) :=
  ⟨μ.toMeasure.map (fun x => x+H • step e),inferInstance⟩

lemma measurable_seedShift {d : ℕ} (e : Direction d) (H : ℕ) : Measurable (seedShift e H) :=
  ((Measure.measurable_map _ (measurable_of_countable _)).comp measurable_subtype_coe).subtype_mk

lemma seedShift_height {d : ℕ} (e : Direction d) (a : ℤ) (H : ℕ) (μ : SeedProfile e a) :
    ∀ᵐ x ∂(seedShift e H μ.val).toMeasure, signedHeight e x=a+H := by
  rw [show (seedShift e H μ.val).toMeasure=μ.measure.map (fun x => x+H • step e) from rfl,
    ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet]
  filter_upwards [μ.property] with x hx
  rw [signedHeight_add_nsmul_step,hx]

noncomputable def seedAdvance {d : ℕ} (e : Direction d) (a : ℤ) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : SeedProfile e a) (ω : Environment d) : SeedProfile e (a+H) :=
  ⟨⟨normalizeOr (seedEndpointRaw e H R μ.measure ω) (seedShift e H μ.val).toMeasure,
    normalizeOr_probability _ _⟩,
    normalizeOr_ae _ _ _ (seedEndpointRaw_supported e H R μ.measure ω a μ.property)
      (seedShift_height e a H μ)⟩

lemma seedAdvance_mass {d : ℕ} (e : Direction d) (a : ℤ) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : SeedProfile e a) (ω : Environment d) :
    seedEndpointRaw e H R μ.measure ω Set.univ • (seedAdvance e a H R μ ω).measure =
      seedEndpointRaw e H R μ.measure ω := normalizeOr_mass _ _

lemma seedAdvance_domination {d : ℕ} (e : Direction d) (a : ℤ) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : SeedProfile e a) (ω : Environment d)
    (c : ℝ≥0∞) (hc : c ≤ seedEndpointRaw e H R μ.measure ω Set.univ) :
    c • (seedAdvance e a H R μ ω).measure ≤ seedEndpointRaw e H R μ.measure ω := by
  rw [← seedAdvance_mass e a H R μ ω]
  intro U
  simp only [Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul_left hc _

lemma seedAdvance_ae {d : ℕ} (e : Direction d) (a : ℤ) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : SeedProfile e a) (ω : Environment d)
    (hm : seedEndpointRaw e H R μ.measure ω Set.univ ≠ 0)
    (P : Lattice d → Prop) (hP : ∀ᵐ x ∂seedEndpointRaw e H R μ.measure ω, P x) :
    ∀ᵐ x ∂(seedAdvance e a H R μ ω).measure, P x := by
  change ∀ᵐ x ∂normalizeOr _ _, P x
  rw [normalizeOr,ite_eq_right hm,normalizedMeasure]
  exact Measure.ae_smul_measure hP _

lemma SeedProfile.measurable_supported {d : ℕ} (e : Direction d) (a : ℤ) :
    Measurable (fun μ : SeedProfile e a =>
      (⟨μ.measure,μ.property⟩ : {ρ : Measure (Lattice d) // ∀ᵐ x ∂ρ, signedHeight e x=a})) :=
  (SeedProfile.measurable_measure e a).subtype_mk

lemma seedAdvance_joint_rows {d : ℕ} (e : Direction d) (a : ℤ) {H : ℕ} (hH : 0 < H)
    (R : Lattice d → Lattice d → Prop) (S : Set (Lattice d))
    (hS : ∀ x, signedHeight e x=a → Strip (realPosition (step e)) x H ⊆ S) :
    @Measurable (SeedProfile e a × Environment d) (SeedProfile e (a+H))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => seedAdvance e a H R p.1 p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  have hm := (seedEndpointRaw_joint_rows e hH R {x | signedHeight e x=a} S hS).comp
    (((SeedProfile.measurable_supported e a).comp measurable_fst).prodMk measurable_snd)
  have hρ : Measurable (fun p : SeedProfile e a × Environment d => (seedShift e H p.1.val).toMeasure) :=
    measurable_subtype_coe.comp ((measurable_seedShift e H).comp (measurable_subtype_coe.comp measurable_fst))
  exact ((measurable_normalizeOr _ _ hm hρ).subtype_mk).subtype_mk

lemma seedAdvance_retained {d : ℕ} (e : Direction d) (a : ℤ) (h H : ℕ)
    (R : Lattice d → Lattice d → Prop) (π : Measure (Lattice d))
    (μ : SeedProfile e a) (ω : Environment d) (δ c : ℝ≥0∞)
    (hμ : δ • μ.measure ≤ seedEndpointRaw e h (fun _ _ => True) π ω)
    (hc : c ≤ seedEndpointRaw e H R μ.measure ω Set.univ) :
    (δ*c) • (seedAdvance e a H R μ ω).measure ≤ seedEndpointRaw e (h+H) (fun _ _ => True) π ω := by
  have hd : δ • (c • (seedAdvance e a H R μ ω).measure) ≤ δ • seedEndpointRaw e H R μ.measure ω := by
    intro U
    simp only [Measure.smul_apply,smul_eq_mul]
    exact mul_le_mul_right (seedAdvance_domination e a H R μ ω c hc U) δ
  rw [smul_smul,← seedEndpointRaw_smul] at hd
  exact hd.trans ((seedEndpointRaw_mono e H R hμ ω).trans
    (seedEndpointRaw_comp_le e h H _ R π ω))

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def SeedCentral {d : ℕ} (f : Direction d) (H : ℕ) (θ z : ℝ) (x y : Lattice d) : Prop :=
  |signedCoordinate f (y-x)-(H:ℝ)*θ| ≤ z

def SeedJump {d : ℕ} (f : Direction d) (H : ℕ) (s : ℤ) (θ z : ℝ) (x y : Lattice d) : Prop :=
  z < (s:ℝ)*(signedCoordinate f (y-x)-(H:ℝ)*θ)

lemma seedCentral_total_ge {d : ℕ} (e f : Direction d) (H : ℕ) (θ z : ℝ)
    (μ : Measure (Lattice d)) [IsFiniteMeasure μ] (ω : Environment d) :
    (∫ x, centralPrefixMass (realPosition (step e)) f θ z H ω x ∂μ) ≤
      (seedEndpointRaw e H (SeedCentral f H θ z) μ ω Set.univ).toReal := by
  have he : (∫ x, centralPrefixMass (realPosition (step e)) f θ z H ω x ∂μ) =
      (∫⁻ x, quenchedKernel (ω,x) (TubePrefix (realPosition (step e)) f x θ z H) ∂μ).toReal :=
    integral_toReal (measurable_of_countable _).aemeasurable
      (ae_of_all _ fun x => measure_lt_top _ _)
  rw [he]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  rw [seedEndpointRaw_apply]
  exact lintegral_mono fun x => by
    simpa only [Set.univ_inter,SeedCentral] using tube_le_seedCentral e f H θ z ω x

lemma seedJump_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (H : ℕ) (b a s j : ℝ) (hj : 0 ≤ j)
    (hjump : ∀ x, j ≤ (environmentLaw ν).real {ω |
      j ≤ jumpPrefixMass (realPosition (step e)) f b a s H ω x})
    (μ : Measure (Lattice d)) [IsProbabilityMeasure μ] :
    j/2 ≤ (environmentLaw ν).real {ω | j^2/2 ≤
      (seedEndpointRaw e H (fun x y => a < s*(signedCoordinate f (y-x)-b)) μ ω Set.univ).toReal} := by
  let A := fun ω x => j ≤ jumpPrefixMass (realPosition (step e)) f b a s H ω x
  have hp := favorable_fraction_probability (environmentLaw ν) μ A
    (measurableSet_le measurable_const (jumpPrefixMass_measurable _ _ _ _ _ _)) hj hjump
  apply hp.trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro ω hω
  change j^2/2 ≤ _
  rw [seedEndpointRaw_jump_total]
  have hi := integral_lower_from_fraction μ (A ω) (Set.to_countable _).measurableSet
    (jumpPrefixMass (realPosition (step e)) f b a s H ω) (measurable_of_countable _)
    (fun x => (jumpPrefixMass_bounds _ _ _ _ _ _ _ _).1)
    (fun x => (jumpPrefixMass_bounds _ _ _ _ _ _ _ _).2) hj (fun x hx => hx) hω
  convert hi using 1
  ring

theorem seed_block_tests {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ a j : ℝ, 0 < a ∧ 0 < j ∧ j ≤ 1/2 ∧
      ∀ T η ε : ℝ, 0 < T → 0 < η → 0 < ε →
      ∃ c R : ℝ, 0 < c ∧ 0 < R ∧ ∀ r : ℝ, R ≤ r →
      let n := fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) r
      0 < ⌊n⌋₊ ∧ ∃ θ : ℝ, ∃ s : ℤ, (s=1 ∨ s= -1) ∧
      (∀ (H : ℕ) (μ : ProbabilityMeasure (Lattice d)), (H:ℝ) ≤ T*n →
        (environmentLaw ν).real {ω | (seedEndpointRaw e H (SeedCentral f H θ (η*r)) μ.toMeasure ω Set.univ).toReal < c} ≤ ε) ∧
      (∀ μ : ProbabilityMeasure (Lattice d), j ≤ (environmentLaw ν).real
        {ω | j ≤ (seedEndpointRaw e ⌊n⌋₊ (SeedJump f ⌊n⌋₊ s θ (a*r)) μ.toMeasure ω Set.univ).toReal}) := by
  obtain ⟨a,j,R,ha,hj,hR,hjump⟩ := uniform_raw_jump ν hue e f hef htrans
  let q := min (j/2) (min (j^2/2) (1/2))
  have hq : 0 < q := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  refine ⟨a,q,ha,hq,(min_le_right _ _).trans (min_le_right _ _),fun T η ε hT hη hε => ?_⟩
  obtain ⟨c,hc,hc1,R',hR',hclip⟩ := clipping_uniform ν hue e f hef htrans hT hη
    (show 0 < ε/2 by positivity)
  have hct : c ≠ ⊤ := ne_top_of_le_ne_top (by simp) hc1
  have hcr : 0 < c.toReal := ENNReal.toReal_pos (ne_of_gt hc) hct
  refine ⟨c.toReal/2,max R R',by positivity,hR.trans_le (le_max_left _ _),fun r hr => ?_⟩
  obtain ⟨hH,hjr⟩ := hjump r ((le_max_left R R').trans hr)
  obtain ⟨θ,hθ⟩ := hclip r ((le_max_right R R').trans hr)
  let n := fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
    (commonIncrementProcess (realPosition (step e)) f 0) r
  obtain ⟨s,hs,hsj⟩ := hjr ((⌊n⌋₊:ℝ)*θ)
  have hcentral (H : ℕ) (μ : ProbabilityMeasure (Lattice d)) (hHn : (H:ℝ) ≤ T*n) :
      (environmentLaw ν).real {ω | (seedEndpointRaw e H (SeedCentral f H θ (η*r)) μ.toMeasure ω Set.univ).toReal < c.toReal/2} ≤ ε := by
    have hbad (x : Lattice d) : (environmentLaw ν).real {ω |
        centralPrefixMass (realPosition (step e)) f θ (η*r) H ω x < 2*(c.toReal/2)} ≤ ε/2 := by
      have he : {ω | centralPrefixMass (realPosition (step e)) f θ (η*r) H ω x < 2*(c.toReal/2)} =
          {ω | quenchedKernel (ω,x) (TubePrefix (realPosition (step e)) f x θ (η*r) H) < c} := by
        ext ω
        simp only [centralPrefixMass,Measure.real,mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)]
        exact ENNReal.toReal_lt_toReal (measure_ne_top _ _) hct
      rw [he]
      exact (hθ x H hHn).le
    have hb := mixture_small_mass_probability (environmentLaw ν) μ.toMeasure
      (centralPrefixMass (realPosition (step e)) f θ (η*r) H)
      (centralPrefixMass_measurable _ _ _ _ _) (fun ω x => measureReal_nonneg)
      (fun ω x => measureReal_le_one) (show 0 < c.toReal/2 by positivity) hbad
    have hm : (environmentLaw ν).real {ω | (seedEndpointRaw e H (SeedCentral f H θ (η*r)) μ.toMeasure ω Set.univ).toReal < c.toReal/2} ≤
        (environmentLaw ν).real {ω | (∫ x, centralPrefixMass (realPosition (step e)) f θ (η*r) H ω x ∂μ.toMeasure) < c.toReal/2} :=
      measureReal_mono fun ω hω => (seedCentral_total_ge e f H θ (η*r) μ.toMeasure ω).trans_lt hω
    exact hm.trans (by linarith)
  have hjump' (t : ℤ) (ht : (t:ℝ)=s) (μ : ProbabilityMeasure (Lattice d)) :
      q ≤ (environmentLaw ν).real {ω | q ≤
        (seedEndpointRaw e ⌊n⌋₊ (SeedJump f ⌊n⌋₊ t θ (a*r)) μ.toMeasure ω Set.univ).toReal} := by
    have hh := seedJump_probability ν e f ⌊n⌋₊ ((⌊n⌋₊:ℝ)*θ) (a*r) s j hj.le hsj μ.toMeasure
    apply (min_le_left _ _).trans (hh.trans _)
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro ω hω
    change q ≤ (seedEndpointRaw e ⌊n⌋₊ (SeedJump f ⌊n⌋₊ t θ (a*r)) μ.toMeasure ω Set.univ).toReal
    have hqj : q ≤ j^2/2 := (min_le_right _ _).trans (min_le_left _ _)
    have he : SeedJump f ⌊n⌋₊ t θ (a*r) =
        (fun x y => a*r < s*(signedCoordinate f (y-x)-(⌊n⌋₊:ℝ)*θ)) := by
      funext x y
      simp only [SeedJump,ht]
    rw [he]
    exact hqj.trans hω
  refine ⟨hH,θ,?_⟩
  rcases hs with hs | hs
  · refine ⟨1,Or.inl rfl,hcentral,fun μ => hjump' 1 ?_ μ⟩
    simpa using hs.symm
  · refine ⟨-1,Or.inr rfl,hcentral,fun μ => hjump' (-1) ?_ μ⟩
    simpa using hs.symm

end DirectionalTransience

end

end OAI
