import OAI.Analysis.HotSpots.DouglasEnergy
import OAI.Analysis.HotSpots.KernelLimit

namespace OAI

section LipschitzBoundaryScalarSupport

noncomputable section

section SubcriticalEnergyScalarSupportLayer
open Set MeasureTheory
open scoped InnerProductSpace ENNReal
namespace StrictHotSpots.SubcriticalExtension

lemma energy_cancel {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b c q : G) (x z r : H)
    (ha : inner ℝ a q = inner ℝ a b) (hc : inner ℝ c q = inner ℝ z r) :
    inner ℝ (a+c) q - inner ℝ (x+z) r = inner ℝ a b - inner ℝ x r := by
  rw [inner_add_left,inner_add_left,ha,hc]
  ring

variable {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict Ω)
local instance : NormedSpace ℝ (H10 ho) := (H10.innerProductSpace ho).toNormedSpace
local instance : NormedSpace ℝ (H1 Ω) := (h1Graph Ω).normedSpace



lemma extension_energy (hT : ‖H10.greenOperator ho hb hC hν‖ < 1)
    (A B : H1 Ω) (hA : Harmonic ho A) (hB : Harmonic ho B) :
    inner ℝ (H1.grad (extension ho hb hC hν A)) (H1.grad (extension ho hb hC hν B)) -
      inner ℝ (observe hC hν (extension ho hb hC hν A))
        (observe hC hν (extension ho hb hC hν B)) =
    inner ℝ (H1.grad A) (H1.grad B) -
      inner ℝ (observe hC hν A)
        (BanachResolvent.resolvent (H10.greenOperator ho hb hC hν) (observe hC hν B)) := by
  let a := solve ho hb hC hν
    (BanachResolvent.resolvent (H10.greenOperator ho hb hC hν) (observe hC hν A))
  let b := solve ho hb hC hν
    (BanachResolvent.resolvent (H10.greenOperator ho hb hC hν) (observe hC hν B))
  have hgA : H1.grad (extension ho hb hC hν A) = H1.grad A + H10.grad ho a :=
    extension_grad ho hb hC hν A
  have hoA : observe hC hν (extension ho hb hC hν A) = observe hC hν A + H10.weightedValue ho hC hν a :=
    observe_add_coe ho hC hν A a
  have hga : inner ℝ (H1.grad A) (H1.grad (extension ho hb hC hν B)) =
      inner ℝ (H1.grad A) (H1.grad B) := by
    have hgB : H1.grad (extension ho hb hC hν B) = H1.grad B + H10.grad ho b :=
      extension_grad ho hb hC hν B
    calc
      _ = inner ℝ (H1.grad A) (H1.grad B + H10.grad ho b) :=
        congrArg (fun z : Lp Plane 2 (volume.restrict Ω) => inner ℝ (H1.grad A) z) hgB
      _ = inner ℝ (H1.grad A) (H1.grad B) + inner ℝ (H1.grad A) (H10.grad ho b) :=
        inner_add_right _ _ _
      _ = inner ℝ (H1.grad A) (H1.grad B) + 0 :=
        congrArg (fun r : ℝ => inner ℝ (H1.grad A) (H1.grad B) + r) (hA b)
      _ = _ := add_zero _
  have hgc : inner ℝ (H10.grad ho a) (H1.grad (extension ho hb hC hν B)) =
      inner ℝ (H10.weightedValue ho hC hν a) (observe hC hν (extension ho hb hC hν B)) :=
    (real_inner_comm _ _).trans ((extension_weak ho hb hC hν hT B hB a).trans (real_inner_comm _ _))
  have hq := extension_observe ho hb hC hν hT B
  calc
    _ = inner ℝ (H1.grad A + H10.grad ho a) (H1.grad (extension ho hb hC hν B)) -
        inner ℝ (observe hC hν A + H10.weightedValue ho hC hν a)
          (observe hC hν (extension ho hb hC hν B)) :=
      congrArg₂ (fun (g : Lp Plane 2 (volume.restrict Ω)) (v : Lp ℝ 2 ν) =>
        inner ℝ g (H1.grad (extension ho hb hC hν B)) -
          inner ℝ v (observe hC hν (extension ho hb hC hν B))) hgA hoA
    _ = inner ℝ (H1.grad A) (H1.grad B) -
        inner ℝ (observe hC hν A) (observe hC hν (extension ho hb hC hν B)) :=
      energy_cancel _ _ _ _ _ _ _ hga hgc
    _ = _ := congrArg (fun v : Lp ℝ 2 ν => inner ℝ (H1.grad A) (H1.grad B) -
      inner ℝ (observe hC hν A) v) hq
end StrictHotSpots.SubcriticalExtension
end SubcriticalEnergyScalarSupportLayer

section SubcriticalUniquenessScalarSupportLayer

open Set MeasureTheory
open scoped InnerProductSpace ENNReal
namespace StrictHotSpots.SubcriticalExtension
variable {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict Ω)
local instance : NormedSpace ℝ (H10 ho) := (H10.innerProductSpace ho).toNormedSpace
local instance : NormedSpace ℝ (H1 Ω) := (h1Graph Ω).normedSpace


def WeakPotential (F : H1 Ω) : Prop := ∀ v : H10 ho,
  inner ℝ (H1.grad F) (H10.grad ho v) =
    inner ℝ (observe hC hν F) (H10.weightedValue ho hC hν v)

lemma weakPotential_sub {F G : H1 Ω}
    (hF : WeakPotential ho hC hν F) (hG : WeakPotential ho hC hν G) :
    WeakPotential ho hC hν (F-G) := by
  intro v
  have hg := H1.grad.map_sub F G
  have hh := (observe hC hν).map_sub F G
  calc
    _ = inner ℝ (H1.grad F-H1.grad G) (H10.grad ho v) :=
      congrArg (fun z : Lp Plane 2 (volume.restrict Ω) => inner ℝ z (H10.grad ho v)) hg
    _ = inner ℝ (H1.grad F) (H10.grad ho v)-inner ℝ (H1.grad G) (H10.grad ho v) :=
      inner_sub_left _ _ _
    _ = inner ℝ (observe hC hν F) (H10.weightedValue ho hC hν v) -
        inner ℝ (observe hC hν G) (H10.weightedValue ho hC hν v) :=
      congrArg₂ (fun a b : ℝ => a-b) (hF v) (hG v)
    _ = inner ℝ (observe hC hν F-observe hC hν G) (H10.weightedValue ho hC hν v) :=
      (inner_sub_left _ _ _).symm
    _ = _ := congrArg (fun z : Lp ℝ 2 ν => inner ℝ z (H10.weightedValue ho hC hν v)) hh.symm

include hb in
lemma weakPotential_zero_class {d : ℝ} (hd : d < 1)
    (hsub : ∀ v : H10 ho, ‖H10.weightedValue ho hC hν v‖^2 ≤ d*‖H10.grad ho v‖^2)
    {F : H1 Ω} (hF : WeakPotential ho hC hν F) (h0 : ∃ v : H10 ho, F = v.val) : F = 0 := by
  obtain ⟨v,rfl⟩ := h0
  have he := hF v
  change inner ℝ (H10.grad ho v) (H10.grad ho v) =
    inner ℝ (H10.weightedValue ho hC hν v) (H10.weightedValue ho hC hν v) at he
  simp only [real_inner_self_eq_norm_sq] at he
  have hz : ‖H10.grad ho v‖^2 = 0 := by nlinarith [hsub v,sq_nonneg ‖H10.grad ho v‖]
  exact congrArg (fun v : H10 ho => v.val) (h10_eq_zero_of_grad_norm_sq ho hb v hz)

lemma extension_difference (A : H1 Ω) :
    ∃ v : H10 ho, extension ho hb hC hν A-A = v.val := by
  refine ⟨solve ho hb hC hν
    (BanachResolvent.resolvent (H10.greenOperator ho hb hC hν) (observe hC hν A)), ?_⟩
  change A+_-A = _
  abel

include hb in
lemma weakPotential_unique {d : ℝ} (hd : d < 1)
    (hsub : ∀ v : H10 ho, ‖H10.weightedValue ho hC hν v‖^2 ≤ d*‖H10.grad ho v‖^2)
    {A F G : H1 Ω} (hF : WeakPotential ho hC hν F) (hG : WeakPotential ho hC hν G)
    (hFA : ∃ v : H10 ho, F-A = v.val) (hGA : ∃ v : H10 ho, G-A = v.val) : F = G := by
  apply sub_eq_zero.mp
  apply weakPotential_zero_class ho hb hC hν hd hsub
    (weakPotential_sub ho hC hν hF hG)
  obtain ⟨v,hv⟩ := hFA
  obtain ⟨w,hw⟩ := hGA
  refine ⟨v-w,?_⟩
  change F-G=v.val-w.val
  calc
    _ = (F-A)-(G-A) := by abel
    _ = _ := congrArg₂ (fun x y : H1 Ω => x-y) hv hw

include hb in


theorem existsUnique_weakPotential {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ v : H10 ho, ‖H10.weightedValue ho hC hν v‖^2 ≤ d*‖H10.grad ho v‖^2)
    (F : H1 Ω) : ∃! W : H1 Ω, WeakPotential ho hC hν W ∧
      ∃ v : H10 ho, W-F = v.val := by
  let A := harmonicLift ho hb F
  let W := extension ho hb hC hν A
  have hT : ‖H10.greenOperator ho hb hC hν‖ < 1 :=
    (H10.greenOperator_norm_le ho hb hC hν hd0 hsub).trans_lt hd1
  have hW : WeakPotential ho hC hν W :=
    extension_weak ho hb hC hν hT A (harmonicLift_harmonic ho hb F)
  have hWF : ∃ v : H10 ho, W-F=v.val := by
    obtain ⟨v,hv⟩ := extension_difference ho hb hC hν A
    obtain ⟨w,hw⟩ := harmonicLift_difference ho hb F
    refine ⟨v+w,?_⟩
    change W-F=v.val+w.val
    calc
      _ = (W-A)+(A-F) := by abel
      _ = _ := congrArg₂ (fun x y : H1 Ω => x+y) hv hw
  refine ⟨W,⟨hW,hWF⟩,?_⟩
  intro G hG
  exact weakPotential_unique ho hb hC hν hd1 hsub hG.1 hW hG.2 hWF

end StrictHotSpots.SubcriticalExtension
end SubcriticalUniquenessScalarSupportLayer

section BoundaryMeasureScalarSupportLayer

section BoundaryMeasureLayer
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

local instance twoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

def circleBoundary : Circle ≃ₜ Boundary where
  toFun s := ⟨complexIso (s : ℂ), by simp⟩
  invFun s := ⟨complexIso.symm (s : Plane), by change dist (complexIso.symm (s : Plane)) 0 = 1; simpa using s.property⟩
  left_inv s := by ext; simp
  right_inv s := by ext; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def angleBoundary : AddCircle (2 * Real.pi) ≃ₜ Boundary :=
  AddCircle.homeomorphCircle'.trans circleBoundary


def boundaryMeasure : Measure Boundary := Measure.map angleBoundary volume

instance boundaryMeasure_finite : IsFiniteMeasure boundaryMeasure := by
  unfold boundaryMeasure
  infer_instance

instance boundaryMeasure_nullSingleton : NullSingletonClass boundaryMeasure := by
  constructor
  intro s
  rw [boundaryMeasure, Measure.map_apply angleBoundary.continuous.measurable (measurableSet_singleton s)]
  rw [show angleBoundary ⁻¹' {s} = {angleBoundary.symm s} by ext x; exact angleBoundary.toEquiv.eq_symm_apply.symm]
  simpa only [closedBall_zero, mul_zero, min_eq_right Real.two_pi_pos.le, ENNReal.ofReal_zero] using
    (AddCircle.volume_closedBall (2 * Real.pi) (x := angleBoundary.symm s) 0)

instance boundaryMeasure_openPos : boundaryMeasure.IsOpenPosMeasure :=
  angleBoundary.continuous.isOpenPosMeasure_map angleBoundary.surjective

lemma boundaryMeasure_univ : boundaryMeasure univ = ENNReal.ofReal (2 * Real.pi) := by
  rw [boundaryMeasure, Measure.map_apply angleBoundary.continuous.measurable MeasurableSet.univ]
  simp

lemma boundaryMeasure_real : boundaryMeasure.real univ = 2 * Real.pi := by
  rw [Measure.real, boundaryMeasure_univ, ENNReal.toReal_ofReal Real.two_pi_pos.le]

lemma integral_boundary_angles {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Boundary → E) :
    ∫ s, f s ∂boundaryMeasure = ∫ θ in 0..2*Real.pi,
      f (circleBoundary (Circle.exp θ)) := by
  change ∫ s, f s ∂Measure.map angleBoundary.toMeasurableEquiv volume = _
  rw [integral_map_equiv]
  change (∫ x : AddCircle (2 * Real.pi), f (angleBoundary x)) = _
  rw [← AddCircle.intervalIntegral_preimage (2 * Real.pi) 0 (fun s => f (angleBoundary s))]
  simp only [zero_add]
  rfl

lemma poisson_eq_standard (s : Boundary) (x : Plane) :
    poisson s x = (2*Real.pi)⁻¹ *
      _root_.poissonKernel 0 (complexIso.symm x) (complexIso.symm (s : Plane)) := by
  simp only [poisson, DiskFormula.poisson, _root_.poissonKernel_def, sub_zero,
    LinearIsometryEquiv.norm_map, s.property, one_pow]
  ring

lemma integral_poisson (x : disk) : ∫ s, poisson s x ∂boundaryMeasure = 1 := by
  have hx : complexIso.symm (x : Plane) ∈ ball (0:ℂ) 1 := by
    simpa [disk, mem_ball_zero_iff] using x.property
  have hc : InnerProductSpace.HarmonicOnNhd (fun _ : ℂ => (1:ℝ)) (closedBall 0 1) := by
    intro z _
    exact InnerProductSpace.harmonicAt_const (1:ℝ)
  have he := hc.circleAverage_poissonKernel_smul hx
  rw [integral_boundary_angles]
  simp_rw [poisson_eq_standard]
  rw [intervalIntegral.integral_const_mul]
  convert he using 1
  unfold Real.circleAverage
  congr 2
  funext θ
  change poissonKernel 0 (complexIso.symm (x : Plane))
      (complexIso.symm (complexIso (Circle.exp θ : ℂ))) =
    (poissonKernel 0 (complexIso.symm (x : Plane)) • (fun _ : ℂ => (1 : ℝ)))
      (circleMap 0 1 θ)
  simp [circleMap, Circle.coe_exp]

end StrictHotSpots.PlaneGreen
end
end BoundaryMeasureLayer
end BoundaryMeasureScalarSupportLayer

section BoundaryMeasurabilityScalarSupportLayer

section BoundaryMeasurabilityLayer
noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma poisson_continuous_boundary (x : disk) : Continuous (fun s : Boundary => poisson s x) := by
  have hn (s : Boundary) : complexIso.symm (s : Plane) - complexIso.symm (x : Plane) ≠ 0 := by
    intro he
    have hx : ‖(x : Plane)‖ < 1 := by simpa [disk] using x.property
    have he' := complexIso.symm.injective (sub_eq_zero.mp he)
    rw [← he', s.property] at hx
    exact (lt_irrefl _ hx)
  unfold poisson DiskFormula.poisson
  apply Continuous.div continuous_const
  · fun_prop
  · intro s
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hn s)))

lemma poisson_joint_measurable : Measurable (fun z : Boundary × Plane => poisson z.1 z.2) := by
  unfold poisson DiskFormula.poisson
  fun_prop

variable {ν : Measure Plane} [IsFiniteMeasure ν] {R : ℝ}
  (hR : ∀ᵐ x ∂ν, ‖x‖ ≤ R) (hR1 : R < 1)

lemma poissonRow_continuous : Continuous (poissonRow hR hR1) := by
  rw [continuous_iff_continuousAt]
  intro s
  apply L2Limits.tendsto_toLp_of_dominated
    (hb := memLp_const (1 / (2 * Real.pi * (1-R)^2)))
  · apply Eventually.of_forall
    intro t
    filter_upwards [hR] with x hx
    change ‖DiskFormula.poisson (complexIso.symm (t : Plane)) (complexIso.symm x)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg
      (DiskFormula.poisson_nonneg _ _ (by simpa using hx.trans_lt hR1))]
    exact DiskFormula.poisson_bounded _ _ (by simpa using t.property) (by simpa using hx) hR1
  · filter_upwards [hR] with x hx
    exact (poisson_continuous_boundary ⟨x, by simpa [disk] using hx.trans_lt hR1⟩).continuousAt

variable {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma smoothedRow_stronglyMeasurable : StronglyMeasurable (smoothedRow hC hν) := by
  apply stronglyMeasurable_of_tendsto atTop
    (f := fun n s => L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n)
      (cutoffSmoothedRow hC hν n s))
  · intro n
    have he : (fun s => L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n)
        (cutoffSmoothedRow hC hν n s)) =
        fun s => L2Cutoff.extension (cutoffSet n) (cutoffSet_measurable n)
          (weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))
            (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s)) := by
      funext s
      rw [compactSmoothedRow_eq]
      rfl
    rw [he]
    apply Continuous.stronglyMeasurable
    exact (L2Cutoff.extension (cutoffSet n) (cutoffSet_measurable n)).continuous.comp
      ((weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))).continuous.comp
        (poissonRow_continuous (cutoff_ae_norm n) (cutoffRadius_lt_one n)))
  · exact tendsto_pi_nhds.mpr (extendedSmoothedRow_tendsto hC hν)

lemma smoothedPoisson_joint_measurable :
    Measurable (fun z : Boundary × Plane => smoothedPoisson (ν := ν) z.1 z.2) := by
  have h1 : Measurable (fun z : (Boundary × Plane) × Plane => (z.1.2,z.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  have h2 : Measurable (fun z : (Boundary × Plane) × Plane => (z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hk := measurable_kernel.comp h1
  have hp := poisson_joint_measurable.comp h2
  dsimp only [Function.comp_def] at hk hp
  have hm := hk.mul hp
  change Measurable (fun z : Boundary × Plane =>
    ∫ y, kernel z.2 y * poisson z.1 y ∂ν)
  have hh : StronglyMeasurable (fun z : Boundary × Plane =>
      ∫ y, kernel z.2 y * poisson z.1 y ∂ν) :=
    hm.stronglyMeasurable.integral_prod_right' (ν := ν)
  exact hh.measurable

lemma fullBoundaryK_measurable (p : disk) : Measurable (fullBoundaryK hC hν p) := by
  unfold fullBoundaryK
  apply Measurable.add
  · have hm : Measurable (fun s : Boundary => (s,(p : Plane))) :=
      measurable_id.prodMk measurable_const
    have hf := (smoothedPoisson_joint_measurable (ν := ν)).comp hm
    dsimp only [Function.comp_def] at hf
    exact (poisson_continuous_boundary p).measurable.add hf
  · have hsm : StronglyMeasurable (fun s => BanachResolvent.resolvent
        (weightedIntegralOperator hC hν) (smoothedRow hC hν s)) :=
      (BanachResolvent.resolvent (weightedIntegralOperator hC hν)).continuous.comp_stronglyMeasurable
        (smoothedRow_stronglyMeasurable hC hν)
    exact (stronglyMeasurable_const.inner hsm).measurable

lemma boundaryInteraction_measurable :
    Measurable (fun z : Boundary × Boundary => boundaryInteraction z.1 z.2) := by
  unfold boundaryInteraction DiskFormula.boundaryInteraction
  fun_prop

lemma fullBoundaryN_measurable :
    Measurable (fun z : Boundary × Boundary => fullBoundaryN hC hν z.1 z.2) := by
  have hm1 : Measurable (fun z : (Boundary × Boundary) × Plane => (z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hm2 : Measurable (fun z : (Boundary × Boundary) × Plane => (z.1.2,z.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  have hp1 := poisson_joint_measurable.comp hm1
  have hp2 := poisson_joint_measurable.comp hm2
  have hs2 := (smoothedPoisson_joint_measurable (ν := ν)).comp hm2
  dsimp only [Function.comp_def] at hp1 hp2 hs2
  have hp := hp1.mul hp2
  have hs := hp1.mul hs2
  have h1 := (smoothedRow_stronglyMeasurable hC hν).comp_measurable
    (measurable_fst : Measurable (Prod.fst : Boundary × Boundary → Boundary))
  have h2 := (smoothedRow_stronglyMeasurable hC hν).comp_measurable
    (measurable_snd : Measurable (Prod.snd : Boundary × Boundary → Boundary))
  have hi : StronglyMeasurable (fun z : Boundary × Boundary =>
      inner ℝ (smoothedRow hC hν z.1) (BanachResolvent.resolvent
        (weightedIntegralOperator hC hν) (smoothedRow hC hν z.2))) :=
    h1.inner ((BanachResolvent.resolvent (weightedIntegralOperator hC hν)).continuous.comp_stronglyMeasurable h2)
  exact ((boundaryInteraction_measurable.add (hp.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable).add
    (hs.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable).add hi.measurable

end StrictHotSpots.PlaneGreen
end
end BoundaryMeasurabilityLayer
end BoundaryMeasurabilityScalarSupportLayer

section BoundaryPoissonIntegralsScalarSupportLayer

section BoundaryPoissonIntegralsLayer
noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

instance boundary_compactSpace : CompactSpace Boundary := circleBoundary.compactSpace

lemma poisson_boundary_integrable (x : disk) :
    Integrable (fun s : Boundary => poisson s x) boundaryMeasure :=
  (poisson_continuous_boundary x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

include hC hν in
lemma poisson_integrable_weighted (s : Boundary) : Integrable (poisson s) ν :=
  (poisson_memLp_three_halves_weighted hC hν s).integrable (by
    apply (ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).2
    norm_num)

include hC hν in
lemma poisson_product_boundary_integrable (s : Boundary) :
    Integrable (fun z : Boundary × Plane => poisson s z.2 * poisson z.1 z.2)
      (boundaryMeasure.prod ν) := by
  have hs : Measurable (fun z : Boundary × Plane => poisson s z.2) :=
    (poisson_measurable s).comp measurable_snd
  have hm := hs.mul poisson_joint_measurable
  apply (integrable_prod_iff' hm.aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_mem_disk hν] with x hx
    exact (poisson_boundary_integrable ⟨x,hx⟩).const_mul (poisson s x)
  · apply (poisson_integrable_weighted hC hν s).congr
    filter_upwards [ae_mem_disk hν] with x hx
    change poisson s x = ∫ t, ‖poisson s x * poisson t x‖ ∂boundaryMeasure
    rw [integral_congr_ae (Eventually.of_forall (fun t : Boundary =>
      Real.norm_of_nonneg (mul_nonneg (poisson_nonneg s ⟨x,hx⟩) (poisson_nonneg t ⟨x,hx⟩))))]
    rw [integral_const_mul, integral_poisson ⟨x,hx⟩, mul_one]

include hC hν in
lemma firstInteraction_integrable (s : Boundary) :
    Integrable (fun t : Boundary => ∫ x, poisson s x * poisson t x ∂ν) boundaryMeasure :=
  (poisson_product_boundary_integrable hC hν s).integral_prod_left

include hC hν in
lemma integral_firstInteraction (s : Boundary) :
    (∫ t, ∫ x, poisson s x * poisson t x ∂ν ∂boundaryMeasure) = ∫ x, poisson s x ∂ν := by
  rw [integral_integral_swap (poisson_product_boundary_integrable hC hν s)]
  apply integral_congr_ae
  filter_upwards [ae_mem_disk hν] with x hx
  rw [integral_const_mul, integral_poisson ⟨x,hx⟩, mul_one]


def poissonExtension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Boundary → E) (x : Plane) : E := ∫ s, poisson s x • f s ∂boundaryMeasure

lemma poissonExtension_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Boundary → E} {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) (x : disk) :
    ‖poissonExtension f x‖ ≤ B := by
  unfold poissonExtension
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ s, poisson s x * B ∂boundaryMeasure := by
      apply integral_mono_of_nonneg
      · exact Eventually.of_forall fun _ => norm_nonneg _
      · exact (poisson_boundary_integrable x).mul_const B
      · filter_upwards [] with s
        rw [norm_smul, Real.norm_of_nonneg (poisson_nonneg s x)]
        exact mul_le_mul_of_nonneg_left (hB s) (poisson_nonneg s x)
    _ = B := by rw [integral_mul_const, integral_poisson, one_mul]

end StrictHotSpots.PlaneGreen
end
end BoundaryPoissonIntegralsLayer
end BoundaryPoissonIntegralsScalarSupportLayer

section BochnerL2RowsScalarSupportLayer

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.L2Rows

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [IsFiniteMeasure μ] [IsFiniteMeasure ν]


lemma integral_eq_toLp {r : A → B → ℝ} {R : A → Lp ℝ 2 ν}
    (hR : Integrable R μ) (hr : ∀ a, R a =ᵐ[ν] r a)
    (havg : MemLp (fun x => ∫ a, r a x ∂μ) 2 ν)
    (hpair : ∀ g : Lp ℝ 2 ν, Integrable (fun z : A × B => g z.2 * r z.1 z.2) (μ.prod ν)) :
    (∫ a, R a ∂μ) = havg.toLp (fun x => ∫ a, r a x ∂μ) := by
  apply ext_inner_left ℝ
  intro g
  rw [← integral_inner hR g, L2.inner_def]
  calc
    (∫ a, inner ℝ g (R a) ∂μ) = ∫ a, ∫ x, g x * r a x ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with a
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hr a] with x hx
      simp only [hx, Real.inner_apply]
    _ = ∫ x, ∫ a, g x * r a x ∂μ ∂ν := integral_integral_swap (hpair g)
    _ = ∫ x, inner ℝ (g x) ((havg.toLp (fun x => ∫ a, r a x ∂μ)) x) ∂ν := by
      apply integral_congr_ae
      filter_upwards [havg.coeFn_toLp] with x hx
      rw [hx, integral_const_mul]
      exact (Real.inner_apply _ _).symm

lemma average_memLp {r : A → B → ℝ}
    (hm : Measurable (fun z : A × B => r z.1 z.2)) {M : ℝ}
    (hM : ∀ᵐ z ∂μ.prod ν, ‖r z.1 z.2‖ ≤ M) :
    MemLp (fun x => ∫ a, r a x ∂μ) 2 ν := by
  have hh : StronglyMeasurable (fun x => ∫ a, r a x ∂μ) :=
    hm.stronglyMeasurable.integral_prod_left'
  apply MemLp.of_bound hh.aestronglyMeasurable (M * μ.real univ)
  have hb := (Measure.ae_ae_comm (p := fun a x => ‖r a x‖ ≤ M)
    (measurableSet_le hm.norm measurable_const)).mp
    (Measure.ae_ae_of_ae_prod hM)
  filter_upwards [hb] with x hx
  exact norm_integral_le_of_norm_le_const hx

lemma integrable_pair_of_bound {r : A → B → ℝ}
    (hm : Measurable (fun z : A × B => r z.1 z.2)) {M : ℝ}
    (hM : ∀ᵐ z ∂μ.prod ν, ‖r z.1 z.2‖ ≤ M) (g : Lp ℝ 2 ν) :
    Integrable (fun z : A × B => g z.2 * r z.1 z.2) (μ.prod ν) := by
  have hg : Integrable (fun z : A × B => ‖g z.2‖ * M) (μ.prod ν) :=
    ((Lp.memLp g).integrable (by norm_num)).norm.comp_snd μ |>.mul_const M
  apply hg.mono' ((Lp.memLp g).aestronglyMeasurable.comp_snd.mul hm.aestronglyMeasurable)
  filter_upwards [hM] with z hz
  change ‖g z.2 * r z.1 z.2‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)

lemma integral_eq_toLp_of_bound {r : A → B → ℝ} {R : A → Lp ℝ 2 ν}
    (hR : Integrable R μ) (hr : ∀ a, R a =ᵐ[ν] r a)
    (hm : Measurable (fun z : A × B => r z.1 z.2)) {M : ℝ}
    (hM : ∀ᵐ z ∂μ.prod ν, ‖r z.1 z.2‖ ≤ M) :
    (∫ a, R a ∂μ) = (average_memLp hm hM).toLp (fun x => ∫ a, r a x ∂μ) :=
  integral_eq_toLp hR hr (average_memLp hm hM) (integrable_pair_of_bound hm hM)

end StrictHotSpots.L2Rows
end BochnerL2RowsScalarSupportLayer

section BoundaryExtensionScalarSupportLayer

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma poissonExtension_measurable {f : Boundary → ℝ} (hf : Measurable f) :
    Measurable (poissonExtension f) := by
  have hm : Measurable (fun z : Boundary × Plane => poisson z.1 z.2 * f z.1) :=
    poisson_joint_measurable.mul (hf.comp measurable_fst)
  exact hm.stronglyMeasurable.integral_prod_left'.measurable

include hν in
lemma poissonExtension_memLp {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) : MemLp (poissonExtension f) 2 ν := by
  apply MemLp.of_bound (poissonExtension_measurable hf).aestronglyMeasurable B
  filter_upwards [ae_mem_disk hν] with x hx
  exact poissonExtension_norm_le hB ⟨x,hx⟩



def poissonL2 {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) : Lp ℝ 2 ν :=
  (poissonExtension_memLp hν hf hB).toLp (poissonExtension f)

lemma smoothedRow_uniform_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ s, ‖smoothedRow hC hν s‖ ≤ M := by
  obtain ⟨B,hB,h⟩ := green_poisson_uniform_bound hC hν
  refine ⟨(measureUnivNNReal ν : ℝ) ^ (2 : ℝ)⁻¹ * B, by positivity, fun s => ?_⟩
  apply Lp.norm_le_of_ae_bound hB
  filter_upwards [(smoothedPoisson_memLp hC hν s).coeFn_toLp, ae_mem_disk hν] with x hx hxd
  rw [show smoothedRow hC hν s x = smoothedPoisson (ν := ν) s x from hx]
  exact h x hxd s

lemma smoothedRow_integrable {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    Integrable (fun s => f s • smoothedRow hC hν s) boundaryMeasure := by
  obtain ⟨M,hM,h⟩ := smoothedRow_uniform_bound hC hν
  apply Integrable.of_bound (hf.aestronglyMeasurable.smul
    (smoothedRow_stronglyMeasurable hC hν).aestronglyMeasurable) (B*M)
  filter_upwards [] with s
  change ‖f s • smoothedRow hC hν s‖ ≤ B*M
  rw [norm_smul]
  exact mul_le_mul (hB s) (h s) (norm_nonneg _) (le_trans (norm_nonneg (f s)) (hB s))

include hC hν in
lemma green_poisson_boundary_integrable (p : disk) :
    Integrable (fun z : Boundary × Plane => kernel p z.2 * poisson z.1 z.2)
      (boundaryMeasure.prod ν) := by
  have hm : Measurable (fun z : Boundary × Plane => kernel p z.2 * poisson z.1 z.2) :=
    (measurable_kernel.comp (measurable_const.prodMk measurable_snd)).mul poisson_joint_measurable
  apply (integrable_prod_iff' hm.aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_mem_disk hν] with x hx
    exact (poisson_boundary_integrable ⟨x,hx⟩).const_mul (kernel p x)
  · apply ((kernel_memLp_weighted hC hν p p.property).integrable (by norm_num)).norm.congr
    filter_upwards [ae_mem_disk hν] with x hx
    rw [show (∫ s, ‖kernel p x * poisson s x‖ ∂boundaryMeasure) = ‖kernel p x‖ by
      simp_rw [norm_mul, Real.norm_of_nonneg (poisson_nonneg _ ⟨x,hx⟩)]
      rw [integral_const_mul, integral_poisson ⟨x,hx⟩, mul_one]]

include hC hν in
lemma green_poisson_data_integrable (p : disk) {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    Integrable (fun z : Boundary × Plane => kernel p z.2 * poisson z.1 z.2 * f z.1)
      (boundaryMeasure.prod ν) := by
  apply ((green_poisson_boundary_integrable hC hν p).norm.mul_const B).mono'
    (((measurable_kernel.comp (measurable_const.prodMk measurable_snd)).mul
      poisson_joint_measurable).mul (hf.comp measurable_fst)).aestronglyMeasurable
  filter_upwards [] with z
  change ‖kernel p z.2 * poisson z.1 z.2 * f z.1‖ ≤ ‖kernel p z.2 * poisson z.1 z.2‖ * B
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB z.1) (norm_nonneg (kernel p z.2 * poisson z.1 z.2))

include hC hν in
lemma smoothedPoisson_average (p : disk) {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    (∫ s, f s * smoothedPoisson (ν := ν) s p ∂boundaryMeasure) =
      ∫ x, kernel p x * poissonExtension f x ∂ν := by
  calc
    _ = ∫ s, ∫ x, kernel p x * poisson s x * f s ∂ν ∂boundaryMeasure := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [integral_mul_const]
      exact mul_comm _ _
    _ = ∫ x, ∫ s, kernel p x * poisson s x * f s ∂boundaryMeasure ∂ν :=
      integral_integral_swap (green_poisson_data_integrable hC hν p hf hB)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [poissonExtension,smul_eq_mul, mul_assoc, integral_const_mul]

lemma smoothedRow_average {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    (∫ s, f s • smoothedRow hC hν s ∂boundaryMeasure) =
      weightedIntegralOperator hC hν (poissonL2 hν hf hB) := by
  obtain ⟨M,_,hM⟩ := green_poisson_uniform_bound hC hν
  have hm : Measurable (fun z : Boundary × Plane => f z.1 * smoothedPoisson (ν := ν) z.1 z.2) :=
    (hf.comp measurable_fst).mul smoothedPoisson_joint_measurable
  have hb : ∀ᵐ z ∂boundaryMeasure.prod ν,
      ‖f z.1 * smoothedPoisson (ν := ν) z.1 z.2‖ ≤ B*M := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.norm measurable_const)).2
    filter_upwards [] with s
    filter_upwards [ae_mem_disk hν] with x hx
    change ‖f s * smoothedPoisson (ν := ν) s x‖ ≤ B*M
    rw [norm_mul]
    exact mul_le_mul (hB s) (hM x hx s) (norm_nonneg _)
      (le_trans (norm_nonneg (f s)) (hB s))
  have hr (s : Boundary) : (f s • smoothedRow hC hν s) =ᵐ[ν]
      (fun x => f s * smoothedPoisson (ν := ν) s x) := by
    filter_upwards [Lp.coeFn_smul (f s) (smoothedRow hC hν s),
      (smoothedPoisson_memLp hC hν s).coeFn_toLp] with x hx hpx
    rw [hx]
    change f s * smoothedRow hC hν s x = _
    rw [show smoothedRow hC hν s x = smoothedPoisson (ν := ν) s x from hpx]
  rw [L2Rows.integral_eq_toLp_of_bound (r := fun s x => f s * smoothedPoisson (ν := ν) s x)
    (smoothedRow_integrable hC hν hf hB) hr hm hb]
  · apply Lp.ext
    filter_upwards [(L2Rows.average_memLp (r := fun s x => f s * smoothedPoisson (ν := ν) s x) hm hb).coeFn_toLp,
      weightedIntegralOperator_ae hC hν (poissonL2 hν hf hB),ae_mem_disk hν] with x hx ht hxd
    rw [hx,ht,smoothedPoisson_average hC hν ⟨x,hxd⟩ hf hB]
    apply integral_congr_ae
    filter_upwards [(poissonExtension_memLp hν hf hB).coeFn_toLp] with y hy
    rw [show poissonL2 hν hf hB y = poissonExtension f y from hy]
end StrictHotSpots.PlaneGreen
end BoundaryExtensionScalarSupportLayer

section BoundaryKRepresentationScalarSupportLayer
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

omit [IsFiniteMeasure ν] in
lemma inner_row (p : disk) (g : Lp ℝ 2 ν) :
    inner ℝ (row hC hν p) g = ∫ x, kernel p x * g x ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(column_memLp hC hν p).coeFn_toLp] with x hx
  change inner ℝ (row hC hν p x) (g x) = _
  rw [show row hC hν p x = kernel x p from hx,kernel_symm x p,Real.inner_apply]

lemma inner_row_poissonL2 (p : disk) {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    inner ℝ (row hC hν p) (poissonL2 hν hf hB) =
      ∫ x, kernel p x * poissonExtension f x ∂ν := by
  rw [inner_row]
  apply integral_congr_ae
  filter_upwards [(poissonExtension_memLp hν hf hB).coeFn_toLp] with x hx
  rw [show poissonL2 hν hf hB x = poissonExtension f x from hx]


def fullExtension {f : Boundary → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B)
    (p : disk) : ℝ := poissonExtension f p + inner ℝ (row hC hν p)
      (BanachResolvent.resolvent (weightedIntegralOperator hC hν) (poissonL2 hν hf hB))

lemma fullBoundaryK_data_integrable (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (p : disk) {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    Integrable (fun s => fullBoundaryK hC hν p s * f s) boundaryMeasure := by
  obtain ⟨M,_,hM⟩ := fullBoundaryK_bounded hC hν p
  apply Integrable.of_bound ((fullBoundaryK_measurable hC hν p).mul hf).aestronglyMeasurable (M*B)
  filter_upwards [] with s
  change ‖fullBoundaryK hC hν p s * f s‖ ≤ M*B
  rw [norm_mul,Real.norm_of_nonneg (fullBoundaryK_pos hC hν hT p s).le]
  exact mul_le_mul (hM s) (hB s) (norm_nonneg _) (by linarith [fullBoundaryK_pos hC hν hT p s])

lemma fullBoundaryK_representation (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (p : disk) {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    (∫ s, fullBoundaryK hC hν p s * f s ∂boundaryMeasure) =
      fullExtension hC hν hf hB p := by
  let T := weightedIntegralOperator hC hν
  let R := BanachResolvent.resolvent T
  have hI := smoothedRow_integrable hC hν hf hB
  have hRI := R.integrable_comp hI
  have htail : (∫ s, f s * inner ℝ (row hC hν p) (R (smoothedRow hC hν s)) ∂boundaryMeasure) =
      inner ℝ (row hC hν p) (R (T (poissonL2 hν hf hB))) := by
    calc
      _ = ∫ s, inner ℝ (row hC hν p) (R (f s • smoothedRow hC hν s)) ∂boundaryMeasure := by
        apply integral_congr_ae
        filter_upwards [] with s
        rw [map_smul,inner_smul_right]
      _ = _ := by rw [integral_inner hRI, R.integral_comp_comm hI,smoothedRow_average hC hν hf hB]
  have htailI : Integrable (fun s => f s * inner ℝ (row hC hν p) (R (smoothedRow hC hν s))) boundaryMeasure := by
    convert hRI.const_inner (row hC hν p) using 1
    funext s
    rw [map_smul,inner_smul_right]
  have hP : Integrable (fun s => poisson s p * f s) boundaryMeasure := by
    apply ((poisson_boundary_integrable p).norm.mul_const B).mono'
      ((poisson_continuous_boundary p).measurable.mul hf).aestronglyMeasurable
    filter_upwards [] with s
    change ‖poisson s p * f s‖ ≤ ‖poisson s p‖ * B
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB s) (norm_nonneg _)
  have hF : Integrable (fun s => f s * smoothedPoisson (ν := ν) s p) boundaryMeasure := by
    have h := (green_poisson_data_integrable hC hν p hf hB).integral_prod_left
    convert h using 1
    funext s
    change f s * smoothedPoisson (ν := ν) s p = ∫ x, kernel p x * poisson s x * f s ∂ν
    rw [integral_mul_const]
    exact mul_comm _ _
  calc
    _ = (∫ s, poisson s p * f s ∂boundaryMeasure) +
        (∫ s, f s * smoothedPoisson (ν := ν) s p ∂boundaryMeasure) +
        (∫ s, f s * inner ℝ (row hC hν p) (R (smoothedRow hC hν s)) ∂boundaryMeasure) := by
      have hPF : Integrable (fun s => poisson s p * f s + f s * smoothedPoisson (ν := ν) s p) boundaryMeasure := hP.add hF
      rw [← integral_add hP hF,← integral_add hPF htailI]
      apply integral_congr_ae
      filter_upwards [] with s
      unfold fullBoundaryK
      dsimp only [R,T]
      ring
    _ = fullExtension hC hν hf hB p := by
      rw [smoothedPoisson_average hC hν p hf hB, htail, ← inner_row_poissonL2 hC hν p hf hB]
      change poissonExtension f p + inner ℝ (row hC hν p) _ + inner ℝ (row hC hν p) _ = _
      have hr := BanachResolvent.apply_eq_add (weightedIntegralOperator hC hν) hT (poissonL2 hν hf hB)
      rw [fullExtension,hr,inner_add_right]
      ring
end StrictHotSpots.PlaneGreen
end BoundaryKRepresentationScalarSupportLayer

section PoissonFubiniScalarSupportLayer
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hν : ν ≤ C • volume.restrict disk)

include hν in
lemma poisson_pair_integrable {g : Plane → ℝ} (hg : Integrable g ν) :
    Integrable (fun z : Boundary × Plane => poisson z.1 z.2 * g z.2) (boundaryMeasure.prod ν) := by
  have hm : AEStronglyMeasurable (fun z : Boundary × Plane => poisson z.1 z.2 * g z.2) (boundaryMeasure.prod ν) :=
    poisson_joint_measurable.aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_snd
  apply (integrable_prod_iff' hm).2
  constructor
  · filter_upwards [ae_mem_disk hν] with x hx
    exact (poisson_boundary_integrable ⟨x,hx⟩).mul_const (g x)
  · apply hg.norm.congr
    filter_upwards [ae_mem_disk hν] with x hx
    change ‖g x‖ = ∫ s, ‖poisson s x * g x‖ ∂boundaryMeasure
    simp_rw [norm_mul,Real.norm_of_nonneg (poisson_nonneg _ ⟨x,hx⟩)]
    rw [integral_mul_const,integral_poisson ⟨x,hx⟩,one_mul]

include hν in
lemma poisson_data_pair_integrable {g : Plane → ℝ} (hg : Integrable g ν)
    {f : Boundary → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    Integrable (fun z : Boundary × Plane => poisson z.1 z.2 * g z.2 * f z.1) (boundaryMeasure.prod ν) := by
  apply ((poisson_pair_integrable hν hg).norm.mul_const B).mono'
    ((poisson_joint_measurable.aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_snd).mul
      (hf.aestronglyMeasurable.comp_fst))
  filter_upwards [] with z
  change ‖poisson z.1 z.2 * g z.2 * f z.1‖ ≤ ‖poisson z.1 z.2 * g z.2‖ * B
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB z.1) (norm_nonneg _)

include hν in
lemma poisson_average_pairing {g : Plane → ℝ} (hg : Integrable g ν)
    {f : Boundary → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    (∫ s, f s * (∫ x, poisson s x * g x ∂ν) ∂boundaryMeasure) =
      ∫ x, poissonExtension f x * g x ∂ν := by
  calc
    _ = ∫ s, ∫ x, poisson s x * g x * f s ∂ν ∂boundaryMeasure := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [integral_mul_const,mul_comm]
    _ = ∫ x, ∫ s, poisson s x * g x * f s ∂boundaryMeasure ∂ν :=
      integral_integral_swap (poisson_data_pair_integrable hν hg hf hB)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      unfold poissonExtension
      simp only [smul_eq_mul]
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with s
      ring

lemma poissonL2_pairing (g : Lp ℝ 2 ν)
    {f : Boundary → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    (∫ s, f s * (∫ x, poisson s x * g x ∂ν) ∂boundaryMeasure) =
      inner ℝ (poissonL2 hν hf hB) g := by
  rw [poisson_average_pairing hν ((Lp.memLp g).integrable (by norm_num)) hf hB, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(poissonExtension_memLp hν hf hB).coeFn_toLp] with x hx
  rw [Real.inner_apply,show poissonL2 hν hf hB x = poissonExtension f x from hx]

end StrictHotSpots.PlaneGreen
end PoissonFubiniScalarSupportLayer

section BoundaryInteractionPartsScalarSupportLayer
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

def firstInteraction (s t : Boundary) : ℝ := ∫ x, poisson s x * poisson t x ∂ν

def secondInteraction (s t : Boundary) : ℝ := ∫ x, poisson s x * smoothedPoisson (ν := ν) t x ∂ν

def tailInteraction (s t : Boundary) : ℝ := inner ℝ (smoothedRow hC hν s)
  (BanachResolvent.resolvent (weightedIntegralOperator hC hν) (smoothedRow hC hν t))

def fullBoundaryR (s t : Boundary) : ℝ := firstInteraction (ν := ν) s t +
  secondInteraction (ν := ν) s t + tailInteraction hC hν s t

lemma firstInteraction_measurable : Measurable (fun z : Boundary × Boundary => firstInteraction (ν := ν) z.1 z.2) := by
  have hm1 : Measurable (fun z : (Boundary × Boundary) × Plane => (z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hm2 : Measurable (fun z : (Boundary × Boundary) × Plane => (z.1.2,z.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  exact ((poisson_joint_measurable.comp hm1).mul
    (poisson_joint_measurable.comp hm2)).stronglyMeasurable.integral_prod_right'.measurable

lemma secondInteraction_measurable : Measurable (fun z : Boundary × Boundary => secondInteraction (ν := ν) z.1 z.2) := by
  have hm1 : Measurable (fun z : (Boundary × Boundary) × Plane => (z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hm2 : Measurable (fun z : (Boundary × Boundary) × Plane => (z.1.2,z.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  exact ((poisson_joint_measurable.comp hm1).mul
    (smoothedPoisson_joint_measurable.comp hm2)).stronglyMeasurable.integral_prod_right'.measurable

lemma tailInteraction_measurable : Measurable (fun z : Boundary × Boundary => tailInteraction hC hν z.1 z.2) := by
  have h1 := (smoothedRow_stronglyMeasurable hC hν).comp_measurable
    (measurable_fst : Measurable (Prod.fst : Boundary × Boundary → Boundary))
  have h2 := (smoothedRow_stronglyMeasurable hC hν).comp_measurable
    (measurable_snd : Measurable (Prod.snd : Boundary × Boundary → Boundary))
  exact (h1.inner ((BanachResolvent.resolvent (weightedIntegralOperator hC hν)).continuous.comp_stronglyMeasurable h2)).measurable

include hν in
omit [IsFiniteMeasure ν] in
lemma firstInteraction_nonneg (s t : Boundary) : 0 ≤ firstInteraction (ν := ν) s t := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_mem_disk hν] with x hx
  exact mul_nonneg (poisson_nonneg s ⟨x,hx⟩) (poisson_nonneg t ⟨x,hx⟩)

include hν in
omit [IsFiniteMeasure ν] in
lemma secondInteraction_nonneg (s t : Boundary) : 0 ≤ secondInteraction (ν := ν) s t := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_mem_disk hν] with x hx
  exact mul_nonneg (poisson_nonneg s ⟨x,hx⟩) (smoothedPoisson_nonneg hν t hx)

lemma tailInteraction_nonneg (hT : ‖weightedIntegralOperator hC hν‖ < 1) (s t : Boundary) :
    0 ≤ tailInteraction hC hν s t := by
  exact L2Limits.inner_nonneg (smoothedRow_nonneg hC hν s)
    (BanachResolvent.resolvent_nonneg _ hT (weightedIntegralOperator_order_nonneg hC hν) (smoothedRow_nonneg hC hν t))

lemma fullBoundaryR_nonneg (hT : ‖weightedIntegralOperator hC hν‖ < 1) (s t : Boundary) :
    0 ≤ fullBoundaryR hC hν s t :=
  add_nonneg (add_nonneg (firstInteraction_nonneg hν s t) (secondInteraction_nonneg hν s t))
    (tailInteraction_nonneg hC hν hT s t)

include hν in
lemma massPoisson_integrable : Integrable (fun s : Boundary => ∫ x, poisson s x ∂ν) boundaryMeasure := by
  have h := (poisson_pair_integrable hν (integrable_const (1 : ℝ))).integral_prod_left
  simpa only [mul_one] using h

include hC hν in
lemma firstInteraction_prod_integrable :
    Integrable (fun z : Boundary × Boundary => firstInteraction (ν := ν) z.1 z.2) (boundaryMeasure.prod boundaryMeasure) := by
  apply (integrable_prod_iff firstInteraction_measurable.aestronglyMeasurable).2
  constructor
  · exact Eventually.of_forall (firstInteraction_integrable hC hν)
  · apply (massPoisson_integrable hν).congr
    filter_upwards [] with s
    change (∫ x, poisson s x ∂ν) = ∫ t, ‖firstInteraction (ν := ν) s t‖ ∂boundaryMeasure
    simp_rw [Real.norm_of_nonneg (firstInteraction_nonneg hν s _)]
    exact (integral_firstInteraction hC hν s).symm

include hC hν in
lemma secondInteraction_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ s t : Boundary,
    ‖secondInteraction (ν := ν) s t‖ ≤ M * (∫ x, poisson s x ∂ν) := by
  obtain ⟨M,hM,h⟩ := green_poisson_uniform_bound hC hν
  refine ⟨M,hM,fun s t => ?_⟩
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ x, M * poisson s x ∂ν := by
      apply integral_mono_of_nonneg
      · exact Eventually.of_forall fun _ => norm_nonneg _
      · exact (poisson_integrable_weighted hC hν s).const_mul M
      · filter_upwards [ae_mem_disk hν] with x hx
        rw [norm_mul,Real.norm_of_nonneg (poisson_nonneg s ⟨x,hx⟩),mul_comm M]
        exact mul_le_mul_of_nonneg_left (h x hx t) (poisson_nonneg s ⟨x,hx⟩)
    _ = _ := integral_const_mul _ _

include hC hν in
lemma secondInteraction_prod_integrable :
    Integrable (fun z : Boundary × Boundary => secondInteraction (ν := ν) z.1 z.2) (boundaryMeasure.prod boundaryMeasure) := by
  obtain ⟨M,_,hM⟩ := secondInteraction_bound hC hν
  apply ((massPoisson_integrable hν).comp_fst boundaryMeasure |>.const_mul M).mono'
    secondInteraction_measurable.aestronglyMeasurable
  exact Eventually.of_forall fun z => hM z.1 z.2

lemma tailInteraction_prod_integrable :
    Integrable (fun z : Boundary × Boundary => tailInteraction hC hν z.1 z.2) (boundaryMeasure.prod boundaryMeasure) := by
  obtain ⟨M,hM,h⟩ := smoothedRow_uniform_bound hC hν
  apply Integrable.of_bound (tailInteraction_measurable hC hν).aestronglyMeasurable
    (M * (‖BanachResolvent.resolvent (weightedIntegralOperator hC hν)‖ * M))
  filter_upwards [] with z
  change ‖inner ℝ (smoothedRow hC hν z.1) (BanachResolvent.resolvent _ (smoothedRow hC hν z.2))‖ ≤ _
  apply (norm_inner_le_norm _ _).trans
  exact mul_le_mul (h z.1) ((ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_left (h z.2) (norm_nonneg _))) (norm_nonneg _) hM

lemma fullBoundaryR_integrable : Integrable (fun z : Boundary × Boundary => fullBoundaryR hC hν z.1 z.2)
    (boundaryMeasure.prod boundaryMeasure) :=
  ((firstInteraction_prod_integrable hC hν).add (secondInteraction_prod_integrable hC hν)).add
    (tailInteraction_prod_integrable hC hν)

end StrictHotSpots.PlaneGreen
end BoundaryInteractionPartsScalarSupportLayer

section BoundaryRAveragingScalarSupportLayer
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)
include hC hν

lemma firstInteraction_average (s : Boundary) {g : Boundary → ℝ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ t, ‖g t‖ ≤ B) :
    (∫ t, firstInteraction (ν := ν) s t * g t ∂boundaryMeasure) =
      ∫ x, poisson s x * poissonExtension g x ∂ν := by
  have h := poisson_average_pairing hν (poisson_integrable_weighted hC hν s) hg hB
  convert h using 1
  · apply integral_congr_ae
    filter_upwards [] with t
    unfold firstInteraction
    rw [mul_comm]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    exact mul_comm _ _
  · apply integral_congr_ae
    filter_upwards [] with x
    exact mul_comm _ _

lemma firstInteraction_pairing {f g : Boundary → ℝ} (hf : Measurable f) (hg : Measurable g)
    {A B : ℝ} (hA : ∀ s, ‖f s‖ ≤ A) (hB : ∀ t, ‖g t‖ ≤ B) :
    (∫ s, f s * (∫ t, firstInteraction (ν := ν) s t * g t ∂boundaryMeasure) ∂boundaryMeasure) =
      inner ℝ (poissonL2 hν hf hA) (poissonL2 hν hg hB) := by
  simp_rw [firstInteraction_average hC hν _ hg hB]
  rw [poisson_average_pairing hν ((poissonExtension_memLp hν hg hB).integrable (by norm_num)) hf hA,
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(poissonExtension_memLp hν hf hA).coeFn_toLp,
    (poissonExtension_memLp hν hg hB).coeFn_toLp] with x hx hy
  rw [Real.inner_apply,show poissonL2 hν hf hA x = poissonExtension f x from hx,
    show poissonL2 hν hg hB x = poissonExtension g x from hy]

lemma smoothed_average_ae {g : Boundary → ℝ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ t, ‖g t‖ ≤ B) :
    (fun x => ∫ t, g t * smoothedPoisson (ν := ν) t x ∂boundaryMeasure) =ᵐ[ν]
      weightedIntegralOperator hC hν (poissonL2 hν hg hB) := by
  filter_upwards [ae_mem_disk hν, weightedIntegralOperator_ae hC hν (poissonL2 hν hg hB)] with x hx ht
  rw [smoothedPoisson_average hC hν ⟨x,hx⟩ hg hB,ht]
  apply integral_congr_ae
  filter_upwards [(poissonExtension_memLp hν hg hB).coeFn_toLp] with y hy
  rw [show poissonL2 hν hg hB y = poissonExtension g y from hy]

lemma smoothed_data_pair_integrable {a : Plane → ℝ} (ha : Integrable a ν)
    {g : Boundary → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ t, ‖g t‖ ≤ B) :
    Integrable (fun z : Boundary × Plane => a z.2 * smoothedPoisson (ν := ν) z.1 z.2 * g z.1)
      (boundaryMeasure.prod ν) := by
  obtain ⟨M,hM,h⟩ := green_poisson_uniform_bound hC hν
  have hm : AEStronglyMeasurable
      (fun z : Boundary × Plane => a z.2 * smoothedPoisson (ν := ν) z.1 z.2 * g z.1)
      (boundaryMeasure.prod ν) :=
    (ha.aestronglyMeasurable.comp_snd.mul smoothedPoisson_joint_measurable.aestronglyMeasurable).mul
      hg.aestronglyMeasurable.comp_fst
  apply (((ha.norm.comp_snd boundaryMeasure).mul_const M).mul_const B).mono' hm
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := boundaryMeasure)).ae (ae_mem_disk hν)] with z hz
  change ‖a z.2 * smoothedPoisson (ν := ν) z.1 z.2 * g z.1‖ ≤ ‖a z.2‖ * M * B
  rw [norm_mul,norm_mul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (h z.2 hz z.1) (norm_nonneg _))
    (hB z.1) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hM)

lemma smoothed_average_pairing {a : Plane → ℝ} (ha : Integrable a ν)
    {g : Boundary → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ t, ‖g t‖ ≤ B) :
    (∫ t, g t * (∫ x, a x * smoothedPoisson (ν := ν) t x ∂ν) ∂boundaryMeasure) =
      ∫ x, a x * weightedIntegralOperator hC hν (poissonL2 hν hg hB) x ∂ν := by
  calc
    _ = ∫ t, ∫ x, a x * smoothedPoisson (ν := ν) t x * g t ∂ν ∂boundaryMeasure := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [integral_mul_const,mul_comm]
    _ = ∫ x, ∫ t, a x * smoothedPoisson (ν := ν) t x * g t ∂boundaryMeasure ∂ν :=
      integral_integral_swap (smoothed_data_pair_integrable hC hν ha hg hB)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [smoothed_average_ae hC hν hg hB] with x hx
      rw [← hx,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      ring

lemma secondInteraction_average (s : Boundary) {g : Boundary → ℝ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ t, ‖g t‖ ≤ B) :
    (∫ t, secondInteraction (ν := ν) s t * g t ∂boundaryMeasure) =
      ∫ x, poisson s x * weightedIntegralOperator hC hν (poissonL2 hν hg hB) x ∂ν := by
  convert smoothed_average_pairing hC hν (poisson_integrable_weighted hC hν s) hg hB using 1
  apply integral_congr_ae
  filter_upwards [] with t
  exact mul_comm _ _

lemma secondInteraction_pairing {f g : Boundary → ℝ} (hf : Measurable f) (hg : Measurable g)
    {A B : ℝ} (hA : ∀ s, ‖f s‖ ≤ A) (hB : ∀ t, ‖g t‖ ≤ B) :
    (∫ s, f s * (∫ t, secondInteraction (ν := ν) s t * g t ∂boundaryMeasure) ∂boundaryMeasure) =
      inner ℝ (poissonL2 hν hf hA) (weightedIntegralOperator hC hν (poissonL2 hν hg hB)) := by
  simp_rw [secondInteraction_average hC hν _ hg hB]
  exact poissonL2_pairing hν _ hf hA

lemma tailInteraction_pairing {f g : Boundary → ℝ} (hf : Measurable f) (hg : Measurable g)
    {A B : ℝ} (hA : ∀ s, ‖f s‖ ≤ A) (hB : ∀ t, ‖g t‖ ≤ B) :
    (∫ s, f s * (∫ t, tailInteraction hC hν s t * g t ∂boundaryMeasure) ∂boundaryMeasure) =
      inner ℝ (weightedIntegralOperator hC hν (poissonL2 hν hf hA))
        (BanachResolvent.resolvent (weightedIntegralOperator hC hν)
          (weightedIntegralOperator hC hν (poissonL2 hν hg hB))) := by
  let R := BanachResolvent.resolvent (weightedIntegralOperator hC hν)
  have hI := smoothedRow_integrable hC hν hg hB
  have hRI := R.integrable_comp hI
  have ht (s : Boundary) : (∫ t, tailInteraction hC hν s t * g t ∂boundaryMeasure) =
      inner ℝ (smoothedRow hC hν s) (R (weightedIntegralOperator hC hν (poissonL2 hν hg hB))) := by
    calc
      _ = ∫ t, inner ℝ (smoothedRow hC hν s) (R (g t • smoothedRow hC hν t)) ∂boundaryMeasure := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [map_smul,inner_smul_right]
        exact mul_comm _ _
      _ = _ := by rw [integral_inner hRI,R.integral_comp_comm hI,smoothedRow_average hC hν hg hB]
  simp_rw [ht]
  calc
    _ = ∫ s, inner ℝ (f s • smoothedRow hC hν s)
        (R (weightedIntegralOperator hC hν (poissonL2 hν hg hB))) ∂boundaryMeasure := by
      simp_rw [inner_smul_left,conj_trivial]
    _ = _ := by
      have hc : (fun s => inner ℝ (f s • smoothedRow hC hν s)
          (R (weightedIntegralOperator hC hν (poissonL2 hν hg hB)))) =
          (fun s => inner ℝ (R (weightedIntegralOperator hC hν (poissonL2 hν hg hB)))
            (f s • smoothedRow hC hν s)) := by
        funext s
        exact real_inner_comm _ _
      rw [hc]
      rw [integral_inner (smoothedRow_integrable hC hν hf hA),smoothedRow_average hC hν hf hA]
      exact real_inner_comm _ _
end StrictHotSpots.PlaneGreen
end BoundaryRAveragingScalarSupportLayer

section BoundaryRRepresentationScalarSupportLayer
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma boundary_data_integrable {r : Boundary × Boundary → ℝ}
    (hr : Integrable r (boundaryMeasure.prod boundaryMeasure))
    {f g : Boundary → ℝ} (hf : Measurable f) (hg : Measurable g)
    {A B : ℝ} (hA : ∀ s, ‖f s‖ ≤ A) (hB : ∀ t, ‖g t‖ ≤ B) :
    Integrable (fun z => r z * f z.1 * g z.2) (boundaryMeasure.prod boundaryMeasure) := by
  apply ((hr.norm.mul_const A).mul_const B).mono'
    ((hr.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_fst).mul hg.aestronglyMeasurable.comp_snd)
  filter_upwards [] with z
  change ‖r z * f z.1 * g z.2‖ ≤ ‖r z‖ * A * B
  rw [norm_mul,norm_mul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hA z.1) (norm_nonneg _))
    (hB z.2) (norm_nonneg _) (mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (hA z.1)))

lemma interaction_eq_iterated {r : Boundary × Boundary → ℝ}
    (hr : Integrable r (boundaryMeasure.prod boundaryMeasure))
    {f g : Boundary → ℝ} (hf : Measurable f) (hg : Measurable g)
    {A B : ℝ} (hA : ∀ s, ‖f s‖ ≤ A) (hB : ∀ t, ‖g t‖ ≤ B) :
    (∫ z, r z * f z.1 * g z.2 ∂boundaryMeasure.prod boundaryMeasure) =
      ∫ s, f s * (∫ t, r (s,t) * g t ∂boundaryMeasure) ∂boundaryMeasure := by
  rw [integral_prod _ (boundary_data_integrable hr hf hg hA hB)]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma fullBoundaryR_representation (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    {f g : Boundary → ℝ} (hf : Measurable f) (hg : Measurable g)
    {A B : ℝ} (hA : ∀ s, ‖f s‖ ≤ A) (hB : ∀ t, ‖g t‖ ≤ B) :
    (∫ z, fullBoundaryR hC hν z.1 z.2 * f z.1 * g z.2 ∂boundaryMeasure.prod boundaryMeasure) =
      inner ℝ (poissonL2 hν hf hA)
        (BanachResolvent.resolvent (weightedIntegralOperator hC hν) (poissonL2 hν hg hB)) := by
  have h1 := boundary_data_integrable (firstInteraction_prod_integrable hC hν) hf hg hA hB
  have h2 := boundary_data_integrable (secondInteraction_prod_integrable hC hν) hf hg hA hB
  have h3 := boundary_data_integrable (tailInteraction_prod_integrable hC hν) hf hg hA hB
  calc
    _ = (∫ z, firstInteraction (ν := ν) z.1 z.2 * f z.1 * g z.2 ∂boundaryMeasure.prod boundaryMeasure) +
        (∫ z, secondInteraction (ν := ν) z.1 z.2 * f z.1 * g z.2 ∂boundaryMeasure.prod boundaryMeasure) +
        (∫ z, tailInteraction hC hν z.1 z.2 * f z.1 * g z.2 ∂boundaryMeasure.prod boundaryMeasure) := by
      have h12 : Integrable (fun z : Boundary × Boundary =>
          firstInteraction (ν := ν) z.1 z.2 * f z.1 * g z.2 +
          secondInteraction (ν := ν) z.1 z.2 * f z.1 * g z.2)
          (boundaryMeasure.prod boundaryMeasure) := h1.add h2
      rw [← integral_add h1 h2,← integral_add h12 h3]
      apply integral_congr_ae
      filter_upwards [] with z
      unfold fullBoundaryR
      ring
    _ = _ := by
      rw [interaction_eq_iterated (firstInteraction_prod_integrable hC hν) hf hg hA hB,
        interaction_eq_iterated (secondInteraction_prod_integrable hC hν) hf hg hA hB,
        interaction_eq_iterated (tailInteraction_prod_integrable hC hν) hf hg hA hB,
        firstInteraction_pairing hC hν hf hg hA hB,
        secondInteraction_pairing hC hν hf hg hA hB,
        tailInteraction_pairing hC hν hf hg hA hB]
      exact (BanachResolvent.inner_two_terms _ hT (weightedIntegralOperator_symmetric hC hν) _ _).symm

lemma fullBoundaryN_eq (s t : Boundary) : fullBoundaryN hC hν s t =
    boundaryInteraction s t + fullBoundaryR hC hν s t := by
  unfold fullBoundaryN fullBoundaryR firstInteraction secondInteraction tailInteraction
  ring

end StrictHotSpots.PlaneGreen
end BoundaryRRepresentationScalarSupportLayer

section BoundaryRPropertiesScalarSupportLayer
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma boundaryInteraction_symm (s t : Boundary) : boundaryInteraction s t = boundaryInteraction t s := by
  simp only [boundaryInteraction,DiskFormula.boundaryInteraction,norm_sub_rev (complexIso.symm (t : Plane))]

lemma fullBoundaryN_symm (hT : ‖weightedIntegralOperator hC hν‖ < 1) (s t : Boundary) :
    fullBoundaryN hC hν s t = fullBoundaryN hC hν t s := by
  by_cases hst : s = t
  · subst t; rfl
  have he (n : ℕ) : cutoffN hC hν n s t = cutoffN hC hν n t s := by
    have hn : ‖weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))‖ < 1 := by
      rw [weightedIntegralOperator_restrict hC hν _ (cutoffSet_measurable n)]
      exact (L2Cutoff.restrictedOperator_norm_le _ _ _).trans_lt hT
    unfold cutoffN boundaryN
    rw [boundaryInteraction_symm s t]
    congr 1
    rw [← BanachResolvent.symmetric _ hn (weightedIntegralOperator_symmetric hC _)]
    exact real_inner_comm _ _
  exact tendsto_nhds_unique (cutoffN_tendsto hC hν hT s t hst)
    (by simpa only [he] using cutoffN_tendsto hC hν hT t s (Ne.symm hst))

lemma fullBoundaryR_symm (hT : ‖weightedIntegralOperator hC hν‖ < 1) (s t : Boundary) :
    fullBoundaryR hC hν s t = fullBoundaryR hC hν t s := by
  have hn := fullBoundaryN_symm hC hν hT s t
  rw [fullBoundaryN_eq,fullBoundaryN_eq,boundaryInteraction_symm s t] at hn
  exact add_left_cancel hn

lemma poissonL2_one_ae : poissonL2 hν (measurable_const : Measurable (fun _ : Boundary => (1:ℝ)))
    (B := 1) (by simp) =ᵐ[ν] (fun _ => (1:ℝ)) := by
  filter_upwards [(poissonExtension_memLp hν (measurable_const : Measurable (fun _ : Boundary => (1:ℝ)))
    (B := 1) (by simp)).coeFn_toLp,ae_mem_disk hν] with x hx hxd
  rw [show poissonL2 hν measurable_const (B := 1) (by simp) x = poissonExtension (fun _ => (1:ℝ)) x from hx]
  simp only [poissonExtension,smul_eq_mul,mul_one]
  exact integral_poisson ⟨x,hxd⟩

lemma poissonL2_one_norm_sq :
    ‖poissonL2 hν (measurable_const : Measurable (fun _ : Boundary => (1:ℝ)))
      (B := 1) (by simp)‖ ^ 2 = ν.real univ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  calc
    _ = ∫ _ : Plane, (1 : ℝ) ∂ν := by
      apply integral_congr_ae
      filter_upwards [poissonL2_one_ae hν] with x hx
      rw [hx]
      simp
    _ = _ := by simp

lemma fullBoundaryR_integral_le {d : ℝ} (hT : ‖weightedIntegralOperator hC hν‖ ≤ d) (hd : d < 1) :
    (∫ z, fullBoundaryR hC hν z.1 z.2 ∂boundaryMeasure.prod boundaryMeasure) ≤ ν.real univ / (1-d) := by
  let c := poissonL2 hν (measurable_const : Measurable (fun _ : Boundary => (1:ℝ))) (B := 1) (by simp)
  have hr := fullBoundaryR_representation hC hν (hT.trans_lt hd)
    (measurable_const : Measurable (fun _ : Boundary => (1:ℝ)))
    (measurable_const : Measurable (fun _ : Boundary => (1:ℝ))) (A := 1) (B := 1) (by simp) (by simp)
  simp only [mul_one] at hr
  rw [hr]
  change inner ℝ c (BanachResolvent.resolvent _ c) ≤ _
  calc
    _ ≤ ‖c‖ * ‖BanachResolvent.resolvent (weightedIntegralOperator hC hν) c‖ := real_inner_le_norm _ _
    _ ≤ ‖c‖ * ((1-d)⁻¹ * ‖c‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (BanachResolvent.resolvent_norm_le _ hT hd) (norm_nonneg _))
    _ = ‖c‖ ^ 2 / (1-d) := by ring
    _ = _ := by rw [poissonL2_one_norm_sq hν]
end StrictHotSpots.PlaneGreen
end BoundaryRPropertiesScalarSupportLayer

section BoundaryFormScalarSupportLayer



open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma boundary_continuous_bound {f : Boundary → E} (hf : Continuous f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s, ‖f s‖ ≤ M := by
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max M 0,le_max_right _ _,fun s => (hM s (mem_univ s)).trans (le_max_left _ _)⟩

lemma harmonic_boundary_bound {h k : Boundary → E} {A B : ℝ≥0}
    (hh : LipschitzWith A h) (hk : LipschitzWith B k) (s t : Boundary) :
    ‖boundaryInteraction s t * inner ℝ (h s-h t) (k s-k t)‖ ≤ (A:ℝ)*B/Real.pi := by
  rw [norm_mul,Real.norm_eq_abs,boundaryInteraction_eq_dist,abs_of_nonneg (by positivity)]
  have h1 : ‖h s-h t‖ ≤ (A:ℝ)*dist s t := by simpa only [dist_eq_norm] using hh.dist_le_mul s t
  have h2 : ‖k s-k t‖ ≤ (B:ℝ)*dist s t := by simpa only [dist_eq_norm] using hk.dist_le_mul s t
  by_cases hd : dist s t = 0
  · simp [hd]; positivity
  · calc
      _ ≤ (1/(Real.pi*dist s t^2)) * (((A:ℝ)*dist s t)*((B:ℝ)*dist s t)) := by
        gcongr
        exact (norm_inner_le_norm _ _).trans (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
      _ = _ := by field_simp

lemma harmonic_boundary_integrable {h k : Boundary → E} {A B : ℝ≥0}
    (hh : LipschitzWith A h) (hk : LipschitzWith B k) :
    Integrable (fun z : Boundary × Boundary => boundaryInteraction z.1 z.2 *
      inner ℝ (h z.1-h z.2) (k z.1-k z.2)) (boundaryMeasure.prod boundaryMeasure) := by
  apply (integrable_const ((A:ℝ)*B/Real.pi)).mono'
  · exact (boundaryInteraction_measurable.aestronglyMeasurable).mul
      (((hh.continuous.comp continuous_fst).sub (hh.continuous.comp continuous_snd)).inner
        ((hk.continuous.comp continuous_fst).sub (hk.continuous.comp continuous_snd))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => harmonic_boundary_bound hh hk z.1 z.2

lemma interaction_boundary_integrable {R : Boundary → Boundary → ℝ}
    (hR : Integrable (fun z : Boundary × Boundary => R z.1 z.2) (boundaryMeasure.prod boundaryMeasure))
    {h k : Boundary → E} (hh : Continuous h) (hk : Continuous k) :
    Integrable (fun z : Boundary × Boundary => R z.1 z.2 * inner ℝ (h z.1) (k z.2))
      (boundaryMeasure.prod boundaryMeasure) := by
  obtain ⟨A,hA,hAb⟩ := boundary_continuous_bound hh
  obtain ⟨B,hB,hBb⟩ := boundary_continuous_bound hk
  apply (hR.norm.const_mul (A*B)).mono'
  · exact hR.aestronglyMeasurable.mul
      ((hh.comp continuous_fst).inner (hk.comp continuous_snd)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro z
    simp only [norm_mul]
    calc
      _ ≤ ‖R z.1 z.2‖ * (A*B) := by
        gcongr
        exact (norm_inner_le_norm _ _).trans (mul_le_mul (hAb z.1) (hBb z.2) (norm_nonneg _) hA)
      _ = _ := mul_comm _ _

lemma curvature_boundary_integrable {c : Boundary → ℝ} (hc : Integrable c boundaryMeasure)
    {h k : Boundary → E} (hh : Continuous h) (hk : Continuous k) :
    Integrable (fun s => c s * inner ℝ (h s) (k s)) boundaryMeasure := by
  obtain ⟨A,hA,hAb⟩ := boundary_continuous_bound hh
  obtain ⟨B,hB,hBb⟩ := boundary_continuous_bound hk
  apply (hc.norm.const_mul (A*B)).mono'
  · exact hc.aestronglyMeasurable.mul (hh.inner hk).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro s
    simp only [norm_mul]
    calc
      _ ≤ ‖c s‖ * (A*B) := by
        gcongr
        exact (norm_inner_le_norm _ _).trans (mul_le_mul (hAb s) (hBb s) (norm_nonneg _) hA)
      _ = _ := mul_comm _ _


def boundaryForm (R : Boundary → Boundary → ℝ) (c : Boundary → ℝ) (h k : Boundary → E) : ℝ :=
  (1/2:ℝ) * (∫ z : Boundary × Boundary, boundaryInteraction z.1 z.2 *
      inner ℝ (h z.1-h z.2) (k z.1-k z.2) ∂boundaryMeasure.prod boundaryMeasure) -
    (∫ z : Boundary × Boundary, R z.1 z.2 * inner ℝ (h z.1) (k z.2) ∂boundaryMeasure.prod boundaryMeasure) +
    ∫ s, c s * inner ℝ (h s) (k s) ∂boundaryMeasure

lemma harmonic_multiplier_algebra (a b : ℝ) (x y : E) :
    inner ℝ (a•x-b•y) (a•x-b•y) - inner ℝ (x-y) (a^2•x-b^2•y) =
      (a-b)^2 * inner ℝ x y := by
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right]
  rw [real_inner_comm y x]
  ring

lemma boundary_smul_lipschitz {b : Boundary → ℝ} {g : Boundary → E} {A B : ℝ≥0}
    (hb : LipschitzWith A b) (hg : LipschitzWith B g) :
    ∃ L : ℝ≥0, LipschitzWith L (fun s => b s • g s) := by
  obtain ⟨M,hM,hMb⟩ := boundary_continuous_bound hb.continuous
  obtain ⟨N,hN,hNg⟩ := boundary_continuous_bound hg.continuous
  refine ⟨A * ⟨N,hN⟩ + ⟨M,hM⟩ * B,LipschitzWith.of_dist_le_mul fun s t => ?_⟩
  rw [dist_eq_norm]
  have he : b s • g s-b t • g t = (b s-b t) • g s + b t • (g s-g t) := by
    simp only [sub_smul,smul_sub]; abel
  rw [he]
  calc
    _ ≤ ‖(b s-b t) • g s‖ + ‖b t • (g s-g t)‖ := norm_add_le _ _
    _ = ‖b s-b t‖*‖g s‖ + ‖b t‖*‖g s-g t‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ ((A:ℝ)*dist s t)*N + M*((B:ℝ)*dist s t) := by
      gcongr
      · simpa only [dist_eq_norm] using hb.dist_le_mul s t
      · exact hNg s
      · exact hMb t
      · simpa only [dist_eq_norm] using hg.dist_le_mul s t
    _ = _ := by
      change ((A:ℝ)*dist s t)*N + M*((B:ℝ)*dist s t) =
        ((A:ℝ)*N+M*(B:ℝ))*dist s t
      ring

end StrictHotSpots.PlaneGreen
end BoundaryFormScalarSupportLayer
end
end LipschitzBoundaryScalarSupport


end OAI
