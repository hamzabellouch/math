import OAI.Analysis.HotSpots.GreenOperator

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section TransferLayer



open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.MeasureKernelTransfer

lemma integral_mul_eq_inner {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    (∫ x, f x * g x ∂ν) = inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp only [hx,hy, RCLike.inner_apply, conj_trivial]
  ring

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {ν : Measure X} {μ : Measure Y} (e : X → Y) (he : MeasurePreserving e ν μ)

def observe : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν :=
  (Lp.compMeasurePreservingₗᵢ ℝ e he).toContinuousLinearMap

lemma observe_ae (f : Lp ℝ 2 μ) : observe e he f =ᵐ[ν] f ∘ e :=
  Lp.coeFn_compMeasurePreserving f he

lemma observe_row {g : Y → ℝ} (hg : MemLp g 2 μ) :
    observe e he (hg.toLp g) = (hg.comp_measurePreserving he).toLp (g ∘ e) := rfl

def operator (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  ((observe e he).comp T).comp (observe e he).adjoint

lemma integral_adjoint_row {g : Y → ℝ} (hg : MemLp g 2 μ) (f : Lp ℝ 2 ν) :
    (∫ y, g y * (observe e he).adjoint f y ∂μ) = ∫ x, g (e x) * f x ∂ν := by
  rw [integral_mul_eq_inner hg (Lp.memLp _), Lp.toLp_coeFn,
    ContinuousLinearMap.adjoint_inner_right, observe_row e he hg]
  symm
  simpa only [Function.comp_apply, Lp.toLp_coeFn] using
    integral_mul_eq_inner (hg.comp_measurePreserving he) (Lp.memLp f)

lemma operator_ae (G : Y → Y → ℝ) (hrow : ∀ x, MemLp (G (e x)) 2 μ)
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hT : ∀ f : Lp ℝ 2 μ, T f =ᵐ[μ] fun y => ∫ z, G y z * f z ∂μ)
    (f : Lp ℝ 2 ν) :
    operator e he T f =ᵐ[ν] fun x => ∫ z, G (e x) (e z) * f z ∂ν := by
  filter_upwards [observe_ae e he (T ((observe e he).adjoint f)),
    he.quasiMeasurePreserving.ae_eq_comp (hT ((observe e he).adjoint f))] with x hx ht
  change observe e he (T ((observe e he).adjoint f)) x = _
  rw [hx]
  change T ((observe e he).adjoint f) (e x) = _
  rw [show T ((observe e he).adjoint f) (e x) =
    ∫ y, G (e x) y * (observe e he).adjoint f y ∂μ from ht]
  exact integral_adjoint_row e he (hrow x) f

lemma observe_norm_le : ‖observe e he‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖Lp.compMeasurePreserving e he f‖ ≤ 1 * ‖f‖
  simp

lemma operator_norm_le (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : ‖operator e he T‖ ≤ ‖T‖ := by
  calc
    ‖operator e he T‖ ≤ ‖(observe e he).comp T‖ * ‖(observe e he).adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖observe e he‖ * ‖T‖) * ‖observe e he‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖T‖) * 1 := by
      gcongr <;> exact observe_norm_le e he
    _ = ‖T‖ := by ring

end StrictHotSpots.MeasureKernelTransfer

end TransferLayer


namespace StrictHotSpots.MeasureKernelTransfer
open MeasureTheory
open scoped ENNReal InnerProductSpace
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {ν : Measure X} {μ : Measure Y} (e : X → Y) (he : MeasurePreserving e ν μ)

lemma observe_inner (f g : Lp ℝ 2 μ) :
    inner ℝ (observe e he f) (observe e he g) = inner ℝ f g :=
  (Lp.compMeasurePreservingₗᵢ ℝ e he).inner_map_map f g

lemma adjoint_observe (f : Lp ℝ 2 μ) :
    (observe e he).adjoint (observe e he f) = f := by
  have h := congrArg (fun T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => T f)
    (Lp.compMeasurePreservingₗᵢ ℝ e he).adjoint_comp_self
  exact h

lemma operator_observe (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℝ 2 μ) :
    operator e he T (observe e he f) = observe e he (T f) := by
  change observe e he (T ((observe e he).adjoint (observe e he f))) = _
  rw [adjoint_observe]

lemma resolvent_observe (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hT : ‖T‖ < 1)
    (f : Lp ℝ 2 μ) :
    BanachResolvent.resolvent (operator e he T) (observe e he f) =
      observe e he (BanachResolvent.resolvent T f) := by
  symm
  apply BanachResolvent.resolvent_solution _ ((operator_norm_le e he T).trans_lt hT)
  rw [operator_observe, ← map_sub]
  congr 1
  exact congrArg (fun A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => A f)
    (BanachResolvent.resolvent_left T hT)

lemma resolvent_inner (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hT : ‖T‖ < 1)
    (f g : Lp ℝ 2 μ) :
    inner ℝ (observe e he f) (BanachResolvent.resolvent (operator e he T) (observe e he g)) =
      inner ℝ f (BanachResolvent.resolvent T g) := by
  rw [resolvent_observe e he T hT, observe_inner]

end StrictHotSpots.MeasureKernelTransfer

section DiskCompactLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.DiskKernel
lemma green_eq_formula (x y : Disk) :
    green x y = DiskFormula.green x y := by
  unfold green h DiskFormula.green
  rw [one_div_div]
  ring

lemma regularized_symm (ε : ℝ) (x y : Disk) : regularized ε x y = regularized ε y x := by
  have hh : h x y = h y x := by simp only [h, norm_sub_rev, mul_comm]
  simp only [regularized, hh]
end StrictHotSpots.DiskKernel
namespace StrictHotSpots.PlaneGreen
lemma kernel_symm (x y : Plane) : kernel x y = kernel y x := by
  simp only [kernel, DiskFormula.green, norm_sub_rev, mul_comm]
end StrictHotSpots.PlaneGreen

namespace StrictHotSpots.DiskCompact
open PlaneGreen DiskH10
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (ν : Measure X) [IsFiniteMeasure ν]
  (e : X → Plane) (he : Continuous e) (hd : ∀ x, e x ∈ disk)

def coordinates (x : X) : DiskKernel.Disk :=
  ⟨complexIso.symm (e x), by simpa [disk] using hd x⟩

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
include he in
lemma coordinates_continuous : Continuous (coordinates e hd) :=
  ((complexIso.symm.continuous.comp he)).subtype_mk _

omit [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma coordinates_injective (hinj : Function.Injective e) : Function.Injective (coordinates e hd) := by
  intro x y h
  apply hinj
  exact complexIso.symm.injective (congrArg Subtype.val h)

def regularizationParameter (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

lemma parameter_pos (n : ℕ) : 0 < regularizationParameter n := by
  unfold regularizationParameter
  positivity
lemma parameter_le_one (n : ℕ) : regularizationParameter n ≤ 1 := by
  unfold regularizationParameter
  exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
lemma parameter_tendsto : Tendsto regularizationParameter atTop (𝓝 (0 : ℝ)) := by
  exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
lemma parameter_tendsto_gt : Tendsto regularizationParameter atTop (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_iff.mpr ⟨parameter_tendsto, Eventually.of_forall parameter_pos⟩

def regularized (n : ℕ) : C(X × X, ℝ) where
  toFun p := DiskKernel.regularized (regularizationParameter n) (coordinates e hd p.1)
    (coordinates e hd p.2)
  continuous_toFun := by
    have hfirst : Continuous (fun p : X × X => coordinates e hd p.1) :=
      (coordinates_continuous e he hd).comp continuous_fst
    have hsecond : Continuous (fun p : X × X => coordinates e hd p.2) :=
      (coordinates_continuous e he hd).comp continuous_snd
    have hr : Continuous (fun p : DiskKernel.Disk × DiskKernel.Disk =>
        DiskKernel.regularized (regularizationParameter n) p.1 p.2) :=
      DiskKernel.regularized_continuous (parameter_pos n) (parameter_le_one n)
    have hm : Continuous (fun p : X × X => (coordinates e hd p.1, coordinates e hd p.2)) :=
      hfirst.prodMk hsecond
    have hc := hr.comp hm
    simpa only [Function.comp_def] using hc

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma regularized_pos (n : ℕ) (x y : X) : 0 < regularized e he hd n (x,y) :=
  DiskKernel.regularized_pos (parameter_pos n) (parameter_le_one n) _ _
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma regularized_symm (n : ℕ) (x y : X) : regularized e he hd n (x,y) = regularized e he hd n (y,x) :=
  DiskKernel.regularized_symm _ _ _
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma regularized_onePositiveSquare {ι : Type} [Fintype ι] (n : ℕ) (s : ι → X) :
    ReciprocalKernel.OnePositiveSquare (Matrix.of fun i j => (regularized e he hd n (s i,s j))⁻¹) :=
  DiskKernel.regularized_reciprocal_onePositiveSquare (fun i => coordinates e hd (s i))
    (parameter_le_one n)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma regularized_tendsto_off (hinj : Function.Injective e) (x y : X) (hxy : x ≠ y) :
    Tendsto (fun n => regularized e he hd n (x,y)) atTop (𝓝 (kernel (e x) (e y))) := by
  have h := (DiskKernel.regularized_tendsto_offDiagonal
    (fun h => hxy (coordinates_injective e hd hinj h))).comp parameter_tendsto
  simpa only [DiskKernel.green_eq_formula, regularized, ContinuousMap.coe_mk,
    coordinates, kernel, Function.comp_def] using h
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma regularized_tendsto_diagonal (x : X) :
    Tendsto (fun n => regularized e he hd n (x,x)) atTop atTop :=
  (DiskKernel.regularized_tendsto_diagonal (coordinates e hd x)).comp parameter_tendsto_gt

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma regularized_le (hinj : Function.Injective e) (n : ℕ) (x y : X) (hxy : x ≠ y) :
    regularized e he hd n (x,y) ≤ kernel (e x) (e y) := by
  simpa only [DiskKernel.green_eq_formula, regularized, ContinuousMap.coe_mk,
    coordinates, kernel] using DiskKernel.regularized_le_green (parameter_pos n).le
      (fun h => hxy (coordinates_injective e hd hinj h))

omit [CompactSpace X] [IsFiniteMeasure ν] in
include he in
lemma preserving : MeasurePreserving e ν (Measure.map e ν) := ⟨he.measurable,rfl⟩

variable {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : Measure.map e ν ≤ C • volume.restrict disk)

omit [CompactSpace X] [IsFiniteMeasure ν] in
include he hd hC hν in
lemma kernel_memLp (x : X) : MemLp (fun z => kernel (e z) (e x)) 2 ν := by
  have h := (kernel_memLp_weighted hC hν (e x) (hd x)).comp_measurePreserving (preserving ν e he)
  simpa only [Function.comp_def, kernel_symm] using h

omit [CompactSpace X] [IsFiniteMeasure ν] in
include he hν in
lemma ae_ne (x : X) : ∀ᵐ z ∂ν, z ≠ x := by
  have h := (Measure.absolutelyContinuous_of_le_smul hν).ae_le
  have hp : ∀ᵐ y ∂Measure.map e ν, y ≠ e x :=
    (Measure.ae_ne (volume.restrict disk) (e x)).filter_mono h
  filter_upwards [(preserving ν e he).quasiMeasurePreserving.ae hp] with z hz hx
  exact hz (congrArg e hx)

def operator : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  MeasureKernelTransfer.operator e (preserving ν e he) (weightedIntegralOperator hC hν)

omit [CompactSpace X] [IsFiniteMeasure ν] in
include hd in
lemma operator_ae (f : Lp ℝ 2 ν) :
    operator ν e he hC hν f =ᵐ[ν] fun x => ∫ z, kernel (e z) (e x) * f z ∂ν := by
  simpa only [operator, kernel_symm] using MeasureKernelTransfer.operator_ae e (preserving ν e he)
    kernel (fun x => kernel_memLp_weighted hC hν (e x) (hd x))
    (weightedIntegralOperator hC hν) (weightedIntegralOperator_ae hC hν) f

omit [CompactSpace X] [IsFiniteMeasure ν] in
lemma operator_norm_le {d : ℝ} (hd0 : 0 ≤ d)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) : ‖operator ν e he hC hν‖ ≤ d :=
  (MeasureKernelTransfer.operator_norm_le e (preserving ν e he) _).trans
    (weightedIntegralOperator_norm_le hC hν hd0 hsub)




theorem reciprocal [Nonempty X] [DecidableEq X] (hinj : Function.Injective e)
    {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) {ι : Type} [Fintype ι] (s : ι → X) :
    ReciprocalKernel.OnePositiveSquare (Matrix.of fun i j => if s i = s j then 0 else
      (CompactKernel.singularResolvedKernel ν (fun x y => kernel (e x) (e y))
        (kernel_memLp ν e he hd hC hν) (operator ν e he hC hν) (s i) (s j))⁻¹) := by
  apply CompactKernel.singular_reciprocal_of_regularization ν (regularized e he hd)
    (regularized_pos e he hd) (regularized_symm e he hd)
  · intro n ι _ s
    exact regularized_onePositiveSquare e he hd n s
  · intro x y hxy
    exact DiskFormula.green_pos (coordinates e hd x).property (coordinates e hd y).property
      (fun h => hxy (hinj (complexIso.symm.injective h)))
  · intro n x
    filter_upwards [ae_ne ν e he hν x] with z hz
    exact regularized_le e he hd hinj n z x hz
  · intro x
    filter_upwards [ae_ne ν e he hν x] with z hz
    exact regularized_tendsto_off e he hd hinj z x hz
  · exact regularized_tendsto_off e he hd hinj
  · exact regularized_tendsto_diagonal e he hd
  · exact operator_ae ν e he hd hC hν
  · exact (operator_norm_le ν e he hC hν hd0 hsub).trans_lt hd1

end StrictHotSpots.DiskCompact
end
end DiskCompactLayer

section PlaneResolvedLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞)
  (hν : ν ≤ C • volume.restrict disk)

include hC hν in
lemma column_memLp (x : disk) : MemLp (fun z => kernel z x) 2 ν := by
  convert kernel_memLp_weighted hC hν x x.property using 1
  ext z
  exact kernel_symm z x

def row (x : disk) : Lp ℝ 2 ν := (column_memLp hC hν x).toLp (fun z => kernel z x)

def resolved (x y : disk) : ℝ := kernel x y + inner ℝ (row hC hν x)
  (BanachResolvent.resolvent (weightedIntegralOperator hC hν) (row hC hν y))

end StrictHotSpots.PlaneGreen
namespace StrictHotSpots.DiskCompact
open PlaneGreen DiskH10
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (ν : Measure X) [IsFiniteMeasure ν]
  (e : X → Plane) (he : Continuous e) (hd : ∀ x, e x ∈ disk)
  {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : Measure.map e ν ≤ C • volume.restrict disk)

omit [CompactSpace X] [IsFiniteMeasure ν] in
lemma observe_row (x : X) :
    MeasureKernelTransfer.observe e (preserving ν e he) (row hC hν ⟨e x,hd x⟩) =
      (kernel_memLp ν e he hd hC hν x).toLp (fun z => kernel (e z) (e x)) := rfl

omit [CompactSpace X] [IsFiniteMeasure ν] in
lemma resolved_eq {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) (x y : X) :
    CompactKernel.singularResolvedKernel ν (fun x y => kernel (e x) (e y))
      (kernel_memLp ν e he hd hC hν) (operator ν e he hC hν) x y =
      resolved hC hν ⟨e x,hd x⟩ ⟨e y,hd y⟩ := by
  unfold CompactKernel.singularResolvedKernel resolved
  rw [← observe_row ν e he hd hC hν x, ← observe_row ν e he hd hC hν y]
  exact congrArg (fun r : ℝ => kernel (e x) (e y) + r)
    (MeasureKernelTransfer.resolvent_inner e (preserving ν e he) _
      ((weightedIntegralOperator_norm_le hC hν hd0 hsub).trans_lt hd1) _ _)

include he in


theorem reciprocal_ambient [Nonempty X] [DecidableEq X] (hinj : Function.Injective e)
    {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) {ι : Type} [Fintype ι] (s : ι → X) :
    ReciprocalKernel.OnePositiveSquare (Matrix.of fun i j => if s i = s j then 0 else
      (resolved hC hν ⟨e (s i),hd (s i)⟩ ⟨e (s j),hd (s j)⟩)⁻¹) := by
  have h := reciprocal ν e he hd hC hν hinj hd0 hd1 hsub s
  simpa only [resolved_eq ν e he hd hC hν hd0 hd1 hsub] using h

include he in
lemma reciprocal_ambient_of_map [Nonempty X] [DecidableEq X] (hinj : Function.Injective e)
    (μ : Measure Plane) (hmap : Measure.map e ν = μ) (hμ : μ ≤ C • volume.restrict disk)
    {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hμ u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) {ι : Type} [Fintype ι] (s : ι → X) :
    ReciprocalKernel.OnePositiveSquare (Matrix.of fun i j => if s i = s j then 0 else
      (resolved hC hμ ⟨e (s i),hd (s i)⟩ ⟨e (s j),hd (s j)⟩)⁻¹) := by
  subst μ
  exact reciprocal_ambient ν e he hd hC hμ hinj hd0 hd1 hsub s

end StrictHotSpots.DiskCompact
end
end PlaneResolvedLayer

section PlaneCompactSupportLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable (ν : Measure Plane) [IsFiniteMeasure ν] {C : ℝ≥0∞} (hC : C ≠ ∞)
  (hν : ν ≤ C • volume.restrict disk)



theorem reciprocal_compact_support (K : Set Plane) (hK : IsCompact K) (hKd : K ⊆ disk)
    (hsupp : ν Kᶜ = 0) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) {ι : Type} [Fintype ι] (s : ι → disk) :
    ReciprocalKernel.OnePositiveSquare (Matrix.of fun i j => if s i = s j then 0 else
      (resolved hC hν (s i) (s j))⁻¹) := by
  classical
  let L : Set Plane := insert 0 (K ∪ Set.range (fun i => (s i : Plane)))
  have hc : IsCompact L := (hK.union (Set.finite_range _).isCompact).insert 0
  have hLd : L ⊆ disk := by
    intro x hx
    rcases hx with hx | hx | hx
    · rw [hx]; simp [disk]
    · exact hKd hx
    · rcases hx with ⟨i,rfl⟩; exact (s i).property
  have hKL : K ⊆ L := fun x hx => Or.inr (Or.inl hx)
  have hm : ∀ᵐ x ∂ν, x ∈ L := by
    rw [ae_iff]
    exact measure_mono_null (compl_subset_compl.mpr hKL) hsupp
  let : CompactSpace L := isCompact_iff_compactSpace.mp hc
  let : Nonempty L := ⟨⟨0,Or.inl rfl⟩⟩
  let νL : Measure L := ν.comap Subtype.val
  have hmap : Measure.map (Subtype.val : L → Plane) νL = ν := by
    rw [map_comap_subtype_coe hc.measurableSet]
    exact Measure.restrict_eq_self_of_ae_mem hm
  let t : ι → L := fun i => ⟨s i,Or.inr (Or.inr ⟨i,rfl⟩)⟩
  have hp := DiskCompact.reciprocal_ambient_of_map νL Subtype.val continuous_subtype_val
    (fun x => hLd x.property) hC Subtype.val_injective ν hmap hν hd0 hd1 hsub t
  simpa only [t, Subtype.mk.injEq, Subtype.coe_eta, Subtype.ext_iff] using hp

end StrictHotSpots.PlaneGreen
end
end PlaneCompactSupportLayer

section BoundaryRowLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.DiskFormula
variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]

lemma poisson_memLp_ae (s : ℂ) (hs : ‖s‖ = 1) (x : X → ℂ) (hm : Measurable x)
    {R : ℝ} (hR : ∀ᵐ z ∂ν, ‖x z‖ ≤ R) (hR1 : R < 1) :
    MemLp (fun z => poisson s (x z)) 2 ν := by
  refine MemLp.of_bound ?_ (1 / (2*Real.pi*(1-R)^2)) ?_
  · apply Measurable.aestronglyMeasurable
    unfold poisson
    fun_prop
  · filter_upwards [hR] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (poisson_nonneg s (x z) (hz.trans_lt hR1))]
    exact poisson_bounded s (x z) hs hz hR1

lemma radial_one_memLp_ae (s : ℂ) (hs : ‖s‖ = 1) (x : X → ℂ) (hm : Measurable x)
    {R rmin r : ℝ} (hR : ∀ᵐ z ∂ν, ‖x z‖ ≤ R) (hRmin : R < rmin)
    (hrmin : rmin ≤ r) (hr : r < 1) :
    MemLp (fun z => green (r • s) (x z)/(1-r)) 2 ν := by
  refine MemLp.of_bound ?_ ((2/(rmin-R)^2)/(4*Real.pi)) ?_
  · apply Measurable.aestronglyMeasurable
    unfold green
    fun_prop
  · filter_upwards [hR] with z hz
    obtain ⟨h0,hb⟩ := radial_one_bounded s (x z) hs hz hRmin hrmin hr
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using hb



theorem radial_one_L2_ae (s : ℂ) (hs : ‖s‖ = 1) (x : X → ℂ) (hm : Measurable x)
    {R rmin : ℝ} (hR : ∀ᵐ z ∂ν, ‖x z‖ ≤ R) (hRmin : R < rmin) (hrmin1 : rmin < 1)
    (r : ℕ → ℝ) (hrmin : ∀ n, rmin ≤ r n) (hr : ∀ n, r n < 1)
    (hlim : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => (radial_one_memLp_ae ν s hs x hm hR hRmin (hrmin n) (hr n)).toLp
      (fun z => green (r n • s) (x z) / (1-r n))) atTop
      (𝓝 ((poisson_memLp_ae ν s hs x hm hR (hRmin.trans hrmin1)).toLp
        (fun z => poisson s (x z)))) := by
  apply L2Limits.tendsto_toLp_of_dominated
    (hb := memLp_const ((2/(rmin-R)^2)/(4*Real.pi)))
  · apply Filter.Eventually.of_forall
    intro n
    filter_upwards [hR] with z hz
    obtain ⟨h0,hb⟩ := radial_one_bounded s (x z) hs hz hRmin (hrmin n) (hr n)
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using hb
  · filter_upwards [hR] with z hz
    exact (radial_one s (x z) hs (hz.trans_lt (hRmin.trans hrmin1))).comp
      (tendsto_nhdsWithin_iff.mpr ⟨hlim, Filter.Eventually.of_forall fun n => hr n⟩)

end StrictHotSpots.DiskFormula
end
end BoundaryRowLayer

section KernelPositivityLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.BanachResolvent
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
lemma symmetric (T : H →L[ℝ] H) (hT : ‖T‖ < 1)
    (hsym : ∀ f g, inner ℝ (T f) g = inner ℝ f (T g)) (f g : H) :
    inner ℝ (resolvent T f) g = inner ℝ f (resolvent T g) := by
  have hf : resolvent T f - T (resolvent T f) = f :=
    congrArg (fun A : H →L[ℝ] H => A f) (resolvent_left T hT)
  have hg : resolvent T g - T (resolvent T g) = g :=
    congrArg (fun A : H →L[ℝ] H => A g) (resolvent_left T hT)
  calc
    inner ℝ (resolvent T f) g =
      inner ℝ (resolvent T f) (resolvent T g - T (resolvent T g)) := by rw [hg]
    _ = inner ℝ (resolvent T f - T (resolvent T f)) (resolvent T g) := by
      rw [inner_sub_left, inner_sub_right, hsym]
    _ = inner ℝ f (resolvent T g) := by rw [hf]
end StrictHotSpots.BanachResolvent

namespace StrictHotSpots.L2Limits
lemma inner_nonneg {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f g : Lp ℝ 2 ν} (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ inner ℝ f g := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf, (Lp.coeFn_nonneg g).mpr hg] with x hx hy
  exact mul_nonneg hy hx
end StrictHotSpots.L2Limits

namespace StrictHotSpots.PlaneGreen
open DiskH10
lemma kernel_nonneg {x y : Plane} (hx : x ∈ disk) (hy : y ∈ disk) : 0 ≤ kernel x y := by
  by_cases he : x = y
  · subst y
    simp [kernel, DiskFormula.green]
  · exact (DiskFormula.green_pos (by simpa [disk] using hx)
      (by simpa [disk] using hy) (fun h => he (complexIso.symm.injective h))).le

variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞)
  (hν : ν ≤ C • volume.restrict disk)

include hν in
lemma ae_mem_disk : ∀ᵐ x ∂ν, x ∈ disk :=
  (ae_restrict_mem diskOpen.measurableSet).filter_mono
    (Measure.absolutelyContinuous_of_le_smul hν).ae_le

lemma row_nonneg (x : disk) : 0 ≤ row hC hν x := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [(column_memLp hC hν x).coeFn_toLp, ae_mem_disk hν] with z hz hzd
  rw [show row hC hν x z = kernel z x from hz]
  exact kernel_nonneg hzd x.property

lemma weightedIntegralOperator_order_nonneg (f : Lp ℝ 2 ν) (hf : 0 ≤ f) :
    0 ≤ weightedIntegralOperator hC hν f := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [weightedIntegralOperator_ae hC hν f, ae_mem_disk hν] with x hx hxd
  rw [hx]
  apply integral_nonneg_of_ae
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf, ae_mem_disk hν] with y hy hyd
  exact mul_nonneg (kernel_nonneg hxd hyd) hy

lemma resolved_ge (hn : ‖weightedIntegralOperator hC hν‖ < 1) (x y : disk) :
    kernel x y ≤ resolved hC hν x y := by
  apply le_add_of_nonneg_right
  apply L2Limits.inner_nonneg (row_nonneg hC hν x)
  exact BanachResolvent.resolvent_nonneg _ hn (weightedIntegralOperator_order_nonneg hC hν)
    (row_nonneg hC hν y)

lemma resolved_symm (hn : ‖weightedIntegralOperator hC hν‖ < 1) (x y : disk) :
    resolved hC hν x y = resolved hC hν y x := by
  unfold resolved
  rw [kernel_symm]
  congr 1
  calc
    inner ℝ (row hC hν x) (BanachResolvent.resolvent _ (row hC hν y)) =
      inner ℝ (BanachResolvent.resolvent _ (row hC hν y)) (row hC hν x) :=
        real_inner_comm _ _
    _ = _ := BanachResolvent.symmetric _ hn (weightedIntegralOperator_symmetric hC hν) _ _

end StrictHotSpots.PlaneGreen
end
end KernelPositivityLayer

section PlaneBoundaryLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
abbrev Boundary := {s : Plane // ‖s‖ = 1}

def poisson (s : Boundary) (x : Plane) : ℝ :=
  DiskFormula.poisson (complexIso.symm s) (complexIso.symm x)

def boundaryInteraction (s t : Boundary) : ℝ :=
  DiskFormula.boundaryInteraction (complexIso.symm s) (complexIso.symm t)

def radial (s : Boundary) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) : disk :=
  ⟨r • (s : Plane), by simpa [disk, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0,
    s.property] using hr1⟩

lemma poisson_nonneg (s : Boundary) (x : disk) : 0 ≤ poisson s x :=
  DiskFormula.poisson_nonneg _ _ (by simpa [disk] using x.property)

lemma poisson_pos (s : Boundary) (x : disk) : 0 < poisson s x := by
  have hx : ‖(x : Plane)‖ < 1 := by simpa [disk] using x.property
  have hne : complexIso.symm (s : Plane) - complexIso.symm (x : Plane) ≠ 0 := by
    intro h
    have he := complexIso.symm.injective (sub_eq_zero.mp h)
    have hh := s.property
    rw [he] at hh
    linarith
  unfold poisson DiskFormula.poisson
  apply div_pos
  · simp only [LinearIsometryEquiv.norm_map]
    nlinarith [norm_nonneg (x : Plane)]
  · exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hne))

lemma boundaryInteraction_pos (s t : Boundary) (hst : s ≠ t) : 0 < boundaryInteraction s t := by
  unfold boundaryInteraction DiskFormula.boundaryInteraction
  apply one_div_pos.mpr
  apply mul_pos Real.pi_pos
  exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr
    (fun h => hst (Subtype.ext (complexIso.symm.injective h)))))

variable {ν : Measure Plane} [IsFiniteMeasure ν] {R : ℝ}
  (hR : ∀ᵐ x ∂ν, ‖x‖ ≤ R) (hR1 : R < 1)

include hR hR1 in
lemma poisson_memLp (s : Boundary) : MemLp (poisson s) 2 ν := by
  exact DiskFormula.poisson_memLp_ae ν (complexIso.symm s) (by simpa using s.property) complexIso.symm
    complexIso.symm.continuous.measurable (by simpa using hR) hR1

def poissonRow (s : Boundary) : Lp ℝ 2 ν := (poisson_memLp hR hR1 s).toLp (poisson s)

lemma poissonRow_nonneg (s : Boundary) : 0 ≤ poissonRow hR hR1 s := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [(poisson_memLp hR hR1 s).coeFn_toLp, hR] with x hx hr
  rw [show poissonRow hR hR1 s x = poisson s x from hx]
  exact DiskFormula.poisson_nonneg _ _ (by simpa using hr.trans_lt hR1)

variable {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

def boundaryK (p : disk) (s : Boundary) : ℝ := poisson s p +
  inner ℝ (row hC hν p) (BanachResolvent.resolvent (weightedIntegralOperator hC hν)
    (poissonRow hR hR1 s))

def boundaryN (s t : Boundary) : ℝ := boundaryInteraction s t +
  inner ℝ (poissonRow hR hR1 s) (BanachResolvent.resolvent (weightedIntegralOperator hC hν)
    (poissonRow hR hR1 t))

lemma boundaryK_pos (hn : ‖weightedIntegralOperator hC hν‖ < 1) (p : disk) (s : Boundary) :
    0 < boundaryK hR hR1 hC hν p s := by
  apply add_pos_of_pos_of_nonneg (poisson_pos s p)
  apply L2Limits.inner_nonneg (row_nonneg hC hν p)
  exact BanachResolvent.resolvent_nonneg _ hn (weightedIntegralOperator_order_nonneg hC hν)
    (poissonRow_nonneg hR hR1 s)

lemma boundaryN_pos (hn : ‖weightedIntegralOperator hC hν‖ < 1) (s t : Boundary) (hst : s ≠ t) :
    0 < boundaryN hR hR1 hC hν s t := by
  apply add_pos_of_pos_of_nonneg (boundaryInteraction_pos s t hst)
  apply L2Limits.inner_nonneg (poissonRow_nonneg hR hR1 s)
  exact BanachResolvent.resolvent_nonneg _ hn (weightedIntegralOperator_order_nonneg hC hν)
    (poissonRow_nonneg hR hR1 t)

lemma scaled_row_eq (s : Boundary) {rmin r : ℝ} (hRmin : R < rmin)
    (hrmin : rmin ≤ r) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (1-r)⁻¹ • row hC hν (radial s r hr0 hr1) =
      (DiskFormula.radial_one_memLp_ae ν (complexIso.symm s) (by simpa using s.property) complexIso.symm
        complexIso.symm.continuous.measurable (by simpa using hR) hRmin hrmin hr1).toLp
          (fun z => DiskFormula.green (r • complexIso.symm s) (complexIso.symm z)/(1-r)) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (1-r)⁻¹ (row hC hν (radial s r hr0 hr1)),
    (column_memLp hC hν (radial s r hr0 hr1)).coeFn_toLp,
    (DiskFormula.radial_one_memLp_ae ν (complexIso.symm s) (by simpa using s.property) complexIso.symm
      complexIso.symm.continuous.measurable (by simpa using hR) hRmin hrmin hr1).coeFn_toLp]
    with z hz hg ht
  rw [hz]
  simp only [Pi.smul_apply]
  rw [show row hC hν (radial s r hr0 hr1) z = kernel z (radial s r hr0 hr1) from hg, ht,
    kernel_symm]
  simp only [kernel, radial, LinearIsometryEquiv.map_smul, smul_eq_mul, div_eq_mul_inv]
  ring

omit hR1 in
lemma scaled_row_tendsto (s : Boundary) {rmin : ℝ} (hRmin : R < rmin) (hrmin1 : rmin < 1)
    (r : ℕ → ℝ) (hrmin : ∀ n, rmin ≤ r n) (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ n, r n < 1)
    (hlim : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => (1-r n)⁻¹ • row hC hν (radial s (r n) (hr0 n) (hr1 n))) atTop
      (𝓝 (poissonRow hR (hRmin.trans hrmin1) s)) := by
  have hh := DiskFormula.radial_one_L2_ae ν (complexIso.symm s) (by simpa using s.property) complexIso.symm
    complexIso.symm.continuous.measurable (by simpa using hR) hRmin hrmin1 r hrmin hr1 hlim
  convert hh using 1
  · funext n
    exact scaled_row_eq hR hC hν s hRmin (hrmin n) (hr0 n) (hr1 n)
  · rfl

omit [IsFiniteMeasure ν] in
lemma resolved_radial_one_eq (p : disk) (s : Boundary) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    resolved hC hν p (radial s r hr0 hr1) / (1-r) = kernel p (radial s r hr0 hr1)/(1-r) +
      inner ℝ (row hC hν p) (BanachResolvent.resolvent (weightedIntegralOperator hC hν)
        ((1-r)⁻¹ • row hC hν (radial s r hr0 hr1))) := by
  simp only [resolved, map_smul, real_inner_smul_right, div_eq_mul_inv]
  ring

omit [IsFiniteMeasure ν] in
lemma resolved_radial_two_eq (s t : Boundary) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    resolved hC hν (radial s r hr0 hr1) (radial t r hr0 hr1) / (1-r)^2 =
      kernel (radial s r hr0 hr1) (radial t r hr0 hr1)/(1-r)^2 +
      inner ℝ ((1-r)⁻¹ • row hC hν (radial s r hr0 hr1))
        (BanachResolvent.resolvent (weightedIntegralOperator hC hν)
          ((1-r)⁻¹ • row hC hν (radial t r hr0 hr1))) := by
  simp only [resolved, map_smul, real_inner_smul_left, real_inner_smul_right,
    div_eq_mul_inv, ← inv_pow]
  ring

lemma resolved_radial_one_tendsto (p : disk) (s : Boundary) {rmin : ℝ}
    (hRmin : R < rmin) (hrmin1 : rmin < 1)
    (r : ℕ → ℝ) (hrmin : ∀ n, rmin ≤ r n) (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ n, r n < 1)
    (hlim : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => resolved hC hν p (radial s (r n) (hr0 n) (hr1 n)) / (1-r n))
      atTop (𝓝 (boundaryK hR hR1 hC hν p s)) := by
  have hl : Tendsto r atTop (𝓝[<] 1) := tendsto_nhdsWithin_iff.mpr
    ⟨hlim, Filter.Eventually.of_forall hr1⟩
  have hp := (DiskFormula.radial_one (complexIso.symm s) (complexIso.symm p)
    (by simpa using s.property) (by simpa [disk] using p.property)).comp hl
  have hs := scaled_row_tendsto hR hC hν s hRmin hrmin1 r hrmin hr0 hr1 hlim
  have hi : Continuous (fun f : Lp ℝ 2 ν => inner ℝ (row hC hν p)
      (BanachResolvent.resolvent (weightedIntegralOperator hC hν) f)) :=
    continuous_const.inner ((BanachResolvent.resolvent (weightedIntegralOperator hC hν)).continuous)
  have ht := (hi.tendsto (poissonRow hR hR1 s)).comp hs
  convert hp.add ht using 1
  · funext n
    rw [resolved_radial_one_eq]
    congr 1
    rw [kernel_symm]
    simp only [kernel,radial,LinearIsometryEquiv.map_smul,Function.comp_apply]
  · rfl

lemma resolved_radial_two_tendsto (s t : Boundary) (hst : s ≠ t) {rmin : ℝ}
    (hRmin : R < rmin) (hrmin1 : rmin < 1)
    (r : ℕ → ℝ) (hrmin : ∀ n, rmin ≤ r n) (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ n, r n < 1)
    (hlim : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => resolved hC hν (radial s (r n) (hr0 n) (hr1 n))
      (radial t (r n) (hr0 n) (hr1 n)) / (1-r n)^2)
      atTop (𝓝 (boundaryN hR hR1 hC hν s t)) := by
  have hl : Tendsto r atTop (𝓝[<] 1) := tendsto_nhdsWithin_iff.mpr
    ⟨hlim, Filter.Eventually.of_forall hr1⟩
  have hp := (DiskFormula.radial_two (complexIso.symm s) (complexIso.symm t)
    (by simpa using s.property) (by simpa using t.property)
    (fun h => hst (Subtype.ext (complexIso.symm.injective h)))).comp hl
  have hs := scaled_row_tendsto hR hC hν s hRmin hrmin1 r hrmin hr0 hr1 hlim
  have ht := scaled_row_tendsto hR hC hν t hRmin hrmin1 r hrmin hr0 hr1 hlim
  have hi := hs.inner (𝕜 := ℝ) ((BanachResolvent.resolvent (weightedIntegralOperator hC hν)).continuous.tendsto
    (poissonRow hR hR1 t) |>.comp ht)
  convert hp.add hi using 1
  · funext n
    rw [resolved_radial_two_eq]
    simp only [kernel,radial,LinearIsometryEquiv.map_smul,Function.comp_apply]
  · rfl

end StrictHotSpots.PlaneGreen
end
end PlaneBoundaryLayer

section BoundaryReciprocalLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {R : ℝ}
  (hR : ∀ᵐ x ∂ν, ‖x‖ ≤ R) (hR1 : R < 1)
  {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma radial_injective {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Function.Injective (fun s : Boundary => radial s r hr.le hr1) := by
  intro s t h
  apply Subtype.ext
  have he : r • (s : Plane) = r • (t : Plane) := congrArg Subtype.val h
  exact (smul_right_injective _ hr.ne') he

lemma radial_ne_anchor (p : disk) (s : Boundary) {r : ℝ} (hr : ‖(p : Plane)‖ < r)
    (hr1 : r < 1) : radial s r (norm_nonneg _ |>.trans hr.le) hr1 ≠ p := by
  intro h
  have he := congrArg (fun x : disk => ‖(x : Plane)‖) h
  simp only [radial, norm_smul, Real.norm_eq_abs, abs_of_nonneg
    (norm_nonneg _ |>.trans hr.le), s.property, mul_one] at he
  exact hr.ne' he



theorem boundary_reciprocal_compact_support (K : Set Plane) (hK : IsCompact K)
    (hKd : K ⊆ disk) (hsupp : ν Kᶜ = 0) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) (p : disk)
    {ι : Type} [Fintype ι] (s : ι → Boundary) :
    ReciprocalKernel.OnePositiveSquare (ReciprocalKernel.bordered
      (Matrix.of fun i j => if s i = s j then 0 else (boundaryN hR hR1 hC hν (s i) (s j))⁻¹)
      (fun i => (boundaryK hR hR1 hC hν p (s i))⁻¹)) := by
  classical
  have hp : ‖(p : Plane)‖ < 1 := by simpa [disk] using p.property
  obtain ⟨rmin,hm,hm1⟩ := exists_between (max_lt hR1 hp)
  have hRm : R < rmin := lt_of_le_of_lt (le_max_left _ _) hm
  have hpm : ‖(p : Plane)‖ < rmin := lt_of_le_of_lt (le_max_right _ _) hm
  have hm0 : 0 < rmin := (norm_nonneg _).trans_lt hpm
  obtain ⟨r,_,hr,hlim⟩ := exists_seq_strictMono_tendsto' hm1
  have hr0 n : 0 < r n := hm0.trans (hr n).1
  have hr1 n : r n < 1 := (hr n).2
  have hrp n : ‖(p : Plane)‖ < r n := hpm.trans (hr n).1
  let a (n : ℕ) : ι ⊕ Unit → disk := Sum.elim (fun i => radial (s i) (r n) (hr0 n).le (hr1 n))
    (fun _ => p)
  let l (n : ℕ) : ι ⊕ Unit → ℝ := Sum.elim (fun _ => 1-r n) (fun _ => 1)
  let A (n : ℕ) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ := Matrix.of fun i j =>
    l n i * (if a n i = a n j then 0 else (resolved hC hν (a n i) (a n j))⁻¹) * l n j
  have hA n : ReciprocalKernel.OnePositiveSquare (A n) :=
    ReciprocalKernel.onePositiveSquare_scale
      (reciprocal_compact_support ν hC hν K hK hKd hsupp hd0 hd1 hsub (a n)) (l n)
  have hn : ‖weightedIntegralOperator hC hν‖ < 1 :=
    (weightedIntegralOperator_norm_le hC hν hd0 hsub).trans_lt hd1
  apply ReciprocalKernel.onePositiveSquare_of_entrywise_tendsto hA
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · by_cases he : s i = s j
    · simp [A,l,a,ReciprocalKernel.bordered,he]
    · have hne n : a n (Sum.inl i) ≠ a n (Sum.inl j) :=
        fun h => he (radial_injective (hr0 n) (hr1 n) h)
      have hl := (resolved_radial_two_tendsto hR hR1 hC hν (s i) (s j) he hRm hm1
        r (fun n => (hr n).1.le) (fun n => (hr0 n).le) hr1 hlim).inv₀
        (boundaryN_pos hR hR1 hC hν hn (s i) (s j) he).ne'
      convert hl using 1
      · funext n
        change l n _ * (if a n _ = a n _ then 0 else _) * l n _ = _
        rw [ite_eq_right (hne n)]
        simp only [l, Sum.elim_inl, a, div_eq_mul_inv, mul_inv_rev, inv_inv]
        ring
      · simp [ReciprocalKernel.bordered,he]
  · have hne n : a n (Sum.inl i) ≠ a n (Sum.inr j) :=
      radial_ne_anchor p (s i) (hrp n) (hr1 n)
    have hl := (resolved_radial_one_tendsto hR hR1 hC hν p (s i) hRm hm1
      r (fun n => (hr n).1.le) (fun n => (hr0 n).le) hr1 hlim).inv₀
      (boundaryK_pos hR hR1 hC hν hn p (s i)).ne'
    convert hl using 1
    · funext n
      change l n _ * (if a n _ = a n _ then 0 else _) * l n _ = _
      rw [ite_eq_right (hne n)]
      simp only [l, Sum.elim_inl, Sum.elim_inr, a, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_one]
      rw [resolved_symm hC hν hn]
    · simp [ReciprocalKernel.bordered]
  · have hne n : a n (Sum.inr i) ≠ a n (Sum.inl j) :=
      (radial_ne_anchor p (s j) (hrp n) (hr1 n)).symm
    have hl := (resolved_radial_one_tendsto hR hR1 hC hν p (s j) hRm hm1
      r (fun n => (hr n).1.le) (fun n => (hr0 n).le) hr1 hlim).inv₀
      (boundaryK_pos hR hR1 hC hν hn p (s j)).ne'
    convert hl using 1
    · funext n
      change l n _ * (if a n _ = a n _ then 0 else _) * l n _ = _
      rw [ite_eq_right (hne n)]
      simp only [l, Sum.elim_inl, Sum.elim_inr, a, div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]
      ring
    · simp [ReciprocalKernel.bordered]
  · simp [A,l,a,ReciprocalKernel.bordered]


def distanceKernel (p : disk) (s t : Boundary) : ℝ :=
  if s = t then 0 else boundaryK hR hR1 hC hν p s * boundaryK hR hR1 hC hν p t /
    boundaryN hR hR1 hC hν s t

theorem negative_kernel_compact_support (K : Set Plane) (hK : IsCompact K)
    (hKd : K ⊆ disk) (hsupp : ν Kᶜ = 0) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) (p : disk)
    {ι : Type} [Fintype ι] (s : ι → Boundary) :
    ReciprocalKernel.ConditionallyNegative (Matrix.of fun i j =>
      distanceKernel hR hR1 hC hν p (s i) (s j)) := by
  classical
  have hn : ‖weightedIntegralOperator hC hν‖ < 1 :=
    (weightedIntegralOperator_norm_le hC hν hd0 hsub).trans_lt hd1
  have h := ReciprocalKernel.conditionalNegative_scaled_of_bordered
    (fun i => boundaryK hR hR1 hC hν p (s i))
    (fun i => (boundaryK_pos hR hR1 hC hν hn p (s i)).ne')
    (boundary_reciprocal_compact_support hR hR1 hC hν K hK hKd hsupp hd0 hd1 hsub p s)
  convert h using 1
  ext i j
  by_cases he : s i = s j
  · simp [distanceKernel,he]
  · simp only [distanceKernel,he,ite_false,Matrix.of_apply,div_eq_mul_inv]
    ring

end StrictHotSpots.PlaneGreen
end
end BoundaryReciprocalLayer

section BoundarySmoothingLayer
noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal Topology
namespace StrictHotSpots.GreenLp

lemma shifted_logPole_norm_bound_three (x : ℂ) (hx : ‖x‖ < 1) :
    eLpNorm (fun y => logPole (x-y)) 3 (volume.restrict (ball 0 1)) ≤
      eLpNorm logPole 3 (volume.restrict (ball (0 : ℂ) 2)) := by
  have hm := (measurePreserving_sub_right (volume : Measure ℂ) x).restrict_preimage
    (show MeasurableSet (ball (0 : ℂ) 2) from measurableSet_ball)
  have hs : ball (0 : ℂ) 1 ⊆ (fun y => y-x) ⁻¹' ball 0 2 := by
    intro y hy
    have hy' : ‖y‖ < 1 := by simpa using hy
    have hd := norm_sub_le y x
    change y-x ∈ ball (0 : ℂ) 2
    rw [mem_ball_zero_iff]
    linarith
  calc
    _ = eLpNorm (logPole ∘ fun y => y-x) 3 (volume.restrict (ball 0 1)) := by
      congr 1
      funext y
      simp only [Function.comp_apply, logPole, norm_sub_rev x y]
    _ ≤ eLpNorm (logPole ∘ fun y => y-x) 3
        (volume.restrict ((fun y => y-x) ⁻¹' ball 0 2)) :=
      eLpNorm_mono_measure _ (Measure.restrict_mono hs le_rfl)
    _ = _ := eLpNorm_comp_measurePreserving logPole_memLp_three.aestronglyMeasurable hm

lemma invnorm_memLp_three_halves : MemLp (fun z : ℂ => ‖z‖⁻¹) (3/2)
    (volume.restrict (ball (0 : ℂ) 2)) := by
  have hm : Measurable (fun z : ℂ => ‖z‖⁻¹) := by fun_prop
  apply (integrable_norm_rpow_iff hm.aestronglyMeasurable
    (by norm_num : (3/2 : ℝ≥0∞) ≠ 0) (ENNReal.div_ne_top (by norm_num) (by norm_num) : (3/2 : ℝ≥0∞) ≠ ∞)).1
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 3/2)
    (by norm_num : 1 ≤ Module.finrank ℝ ℂ) (by norm_num : (3/2:ℝ) < Module.finrank ℝ ℂ)
  · filter_upwards [] with z
    simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg z)),
      Real.inv_rpow (norm_nonneg z), Real.rpow_neg (norm_nonneg z), one_mul]
    rw [Real.norm_of_nonneg (by positivity)]
  · exact (hm.norm.pow_const _).aestronglyMeasurable

lemma shifted_invnorm_memLp_bound (s : ℂ) (hs : ‖s‖ = 1) :
    MemLp (fun y => ‖s-y‖⁻¹) (3/2) (volume.restrict (ball 0 1)) ∧
    eLpNorm (fun y => ‖s-y‖⁻¹) (3/2) (volume.restrict (ball 0 1)) ≤
      eLpNorm (fun z : ℂ => ‖z‖⁻¹) (3/2) (volume.restrict (ball (0 : ℂ) 2)) := by
  have hm := (measurePreserving_sub_right (volume : Measure ℂ) s).restrict_preimage
    (show MeasurableSet (ball (0 : ℂ) 2) from measurableSet_ball)
  have he : (fun y : ℂ => ‖s-y‖⁻¹) = (fun z : ℂ => ‖z‖⁻¹) ∘ (fun y => y-s) := by
    funext y
    simp only [Function.comp_apply,norm_sub_rev s y]
  have hsub : ball (0 : ℂ) 1 ⊆ (fun y => y-s) ⁻¹' ball 0 2 := by
    intro y hy
    have hy' : ‖y‖ < 1 := by simpa using hy
    have hd := norm_sub_le y s
    change y-s ∈ ball (0 : ℂ) 2
    rw [mem_ball_zero_iff]
    rw [hs] at hd
    linarith
  rw [he]
  refine ⟨(invnorm_memLp_three_halves.comp_measurePreserving hm).mono_measure
    (Measure.restrict_mono hsub le_rfl), ?_⟩
  exact (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)).trans_eq
    (eLpNorm_comp_measurePreserving invnorm_memLp_three_halves.aestronglyMeasurable hm)

end StrictHotSpots.GreenLp
namespace StrictHotSpots.DiskFormula
open GreenLp

lemma green_uniform_L3_bound : ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ x : ℂ, ‖x‖ < 1 →
    eLpNorm (green x) 3 (volume.restrict (ball 0 1)) ≤ B := by
  let C := ENNReal.ofReal (4*Real.pi)⁻¹ *
    eLpNorm logPole 3 (volume.restrict (ball (0 : ℂ) 2))
  refine ⟨C, ENNReal.mul_ne_top ENNReal.ofReal_ne_top logPole_memLp_three.eLpNorm_ne_top,
    fun x hx => ?_⟩
  calc
    _ ≤ ENNReal.ofReal (4*Real.pi)⁻¹ *
        eLpNorm (fun y => logPole (x-y)) 3 (volume.restrict (ball 0 1)) := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (measurable_green_left x).aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      have hy' : ‖y‖ ≤ 1 := (by simpa using hy : ‖y‖ < 1).le
      have hh := green_bounds hx.le hy'
      rw [Real.norm_of_nonneg hh.1, Real.norm_of_nonneg (logPole_nonneg _)]
      simpa only [div_eq_mul_inv, mul_comm] using hh.2
    _ ≤ C := by
      dsimp [C]
      gcongr
      exact shifted_logPole_norm_bound_three x hx

lemma poisson_invnorm_bound (s x : ℂ) (hs : ‖s‖ = 1) (hx : ‖x‖ < 1) :
    poisson s x ≤ Real.pi⁻¹ * ‖s-x‖⁻¹ := by
  have hn : 0 < ‖s-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => by
    rw [← h,hs] at hx; exact lt_irrefl _ hx))
  have hd : 1-‖x‖ ≤ ‖s-x‖ := by
    have ht := norm_le_norm_sub_add s x
    rw [hs] at ht
    linarith
  have hnum : 1-‖x‖^2 ≤ 2*‖s-x‖ := by
    nlinarith [norm_nonneg x]
  unfold poisson
  apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) Real.pi_pos) (sq_pos_of_pos hn))).2
  calc
    _ ≤ 2*‖s-x‖ := hnum
    _ = Real.pi⁻¹ * ‖s-x‖⁻¹ * (2*Real.pi*‖s-x‖^2) := by
      field_simp

lemma poisson_memLp_three_halves (s : ℂ) (hs : ‖s‖ = 1) :
    MemLp (poisson s) (3/2) (volume.restrict (ball 0 1)) := by
  apply ((shifted_invnorm_memLp_bound s hs).1.const_mul Real.pi⁻¹).mono
    (by
      have hm : Measurable (poisson s) := by unfold poisson; fun_prop
      exact hm.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hx' : ‖x‖ < 1 := by simpa using hx
  simpa only [Real.norm_of_nonneg (poisson_nonneg s x hx'),
    Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
      (inv_nonneg.mpr (norm_nonneg _)))] using poisson_invnorm_bound s x hs hx'

lemma poisson_uniform_L32_bound : ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ s : ℂ, ‖s‖ = 1 →
    eLpNorm (poisson s) (3/2) (volume.restrict (ball 0 1)) ≤ B := by
  let C := ENNReal.ofReal Real.pi⁻¹ *
    eLpNorm (fun z : ℂ => ‖z‖⁻¹) (3/2) (volume.restrict (ball (0 : ℂ) 2))
  refine ⟨C, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    invnorm_memLp_three_halves.eLpNorm_ne_top, fun s hs => ?_⟩
  calc
    _ ≤ ENNReal.ofReal Real.pi⁻¹ *
        eLpNorm (fun x => ‖s-x‖⁻¹) (3/2) (volume.restrict (ball 0 1)) := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (show Measurable (poisson s) by unfold poisson; fun_prop).aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      have hx' : ‖x‖ < 1 := by simpa using hx
      simpa only [Real.norm_of_nonneg (poisson_nonneg s x hx'),
        Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using
        poisson_invnorm_bound s x hs hx'
    _ ≤ C := mul_le_mul' le_rfl (shifted_invnorm_memLp_bound s hs).2

end StrictHotSpots.DiskFormula
end
end BoundarySmoothingLayer
section FullBoundarySmoothingLayer
noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

local instance holder_three_three_halves : ENNReal.HolderTriple 3 (3/2) 1 := by
  rw [ENNReal.holderTriple_iff]
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by norm_num)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]

lemma kernel_memLp_three (x : Plane) (hx : x ∈ disk) :
    MemLp (kernel x) 3 (volume.restrict disk) := by
  exact (DiskFormula.green_memLp_three _ (by simpa [disk] using hx)).comp_measurePreserving
    complexIso_disk_preserving

lemma poisson_memLp_three_halves (s : Boundary) :
    MemLp (poisson s) (3/2) (volume.restrict disk) :=
  (DiskFormula.poisson_memLp_three_halves _ (by simpa using s.property)).comp_measurePreserving
    complexIso_disk_preserving

lemma kernel_uniform_three_bound : ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ x ∈ disk,
    eLpNorm (kernel x) 3 (volume.restrict disk) ≤ B := by
  obtain ⟨B,hB,h⟩ := DiskFormula.green_uniform_L3_bound
  refine ⟨B,hB,fun x hx => ?_⟩
  change eLpNorm (DiskFormula.green (complexIso.symm x) ∘ complexIso.symm) 3 _ ≤ B
  rw [eLpNorm_comp_measurePreserving
    (DiskFormula.green_memLp_three _ (by simpa [disk] using hx)).aestronglyMeasurable
      complexIso_disk_preserving]
  exact h _ (by simpa [disk] using hx)

lemma poisson_uniform_three_halves_bound : ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ s : Boundary,
    eLpNorm (poisson s) (3/2) (volume.restrict disk) ≤ B := by
  obtain ⟨B,hB,h⟩ := DiskFormula.poisson_uniform_L32_bound
  refine ⟨B,hB,fun s => ?_⟩
  change eLpNorm (DiskFormula.poisson (complexIso.symm s) ∘ complexIso.symm) (3/2) _ ≤ B
  rw [eLpNorm_comp_measurePreserving
    (DiskFormula.poisson_memLp_three_halves _ (by simpa using s.property)).aestronglyMeasurable
      complexIso_disk_preserving]
  exact h _ (by simpa using s.property)

variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞)
  (hν : ν ≤ C • volume.restrict disk)

include hC hν in
lemma kernel_memLp_three_weighted (x : Plane) (hx : x ∈ disk) : MemLp (kernel x) 3 ν :=
  (kernel_memLp_three x hx).of_measure_le_smul hC hν

include hC hν in
lemma poisson_memLp_three_halves_weighted (s : Boundary) : MemLp (poisson s) (3/2) ν :=
  (poisson_memLp_three_halves s).of_measure_le_smul hC hν

include hC hν in
lemma product_green_poisson_integrable (x : Plane) (hx : x ∈ disk) (s : Boundary) :
    Integrable (fun y => kernel x y * poisson s y) ν :=
  (kernel_memLp_three_weighted hC hν x hx).integrable_mul
    (poisson_memLp_three_halves_weighted hC hν s)

include hC hν in
lemma kernel_uniform_three_bound_weighted : ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ x ∈ disk,
    eLpNorm (kernel x) 3 ν ≤ B := by
  obtain ⟨B,hB,h⟩ := kernel_uniform_three_bound
  refine ⟨C ^ (1/(3:ℝ≥0∞)).toReal * B, ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hC) hB,
    fun x hx => ?_⟩
  exact (eLpNorm_le_of_measure_le_smul hν).trans (mul_le_mul' le_rfl (h x hx))

include hC hν in
lemma poisson_uniform_three_halves_bound_weighted : ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ s : Boundary,
    eLpNorm (poisson s) (3/2) ν ≤ B := by
  obtain ⟨B,hB,h⟩ := poisson_uniform_three_halves_bound
  refine ⟨C ^ (1/(3/2:ℝ≥0∞)).toReal * B, ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hC) hB,
    fun s => ?_⟩
  exact (eLpNorm_le_of_measure_le_smul hν).trans (mul_le_mul' le_rfl (h s))

include hC hν in
lemma green_poisson_uniform_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ disk, ∀ s : Boundary,
    ‖∫ y, kernel x y * poisson s y ∂ν‖ ≤ B := by
  obtain ⟨B,hB,h⟩ := kernel_uniform_three_bound_weighted hC hν
  obtain ⟨D,hD,hp⟩ := poisson_uniform_three_halves_bound_weighted hC hν
  refine ⟨(B*D).toReal, ENNReal.toReal_nonneg, fun x hx s => ?_⟩
  have hg := kernel_memLp_three_weighted hC hν x hx
  have hs := poisson_memLp_three_halves_weighted hC hν s
  have he : eLpNorm (fun y => kernel x y * poisson s y) 1 ν ≤ B*D := by
    exact (eLpNorm_smul_le_mul_eLpNorm hg.aestronglyMeasurable hs.aestronglyMeasurable).trans
      (mul_le_mul' (h x hx) (hp s))
  have hh := (enorm_integral_le_lintegral_enorm (fun y => kernel x y * poisson s y)).trans
    (((eLpNorm_one_eq_lintegral_enorm
      (hg.aestronglyMeasurable.mul hs.aestronglyMeasurable)).symm.le).trans he)
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top hB hD) hh
  simpa only [enorm, ENNReal.coe_toReal, coe_nnnorm] using ht



def smoothedPoisson (s : Boundary) (x : Plane) : ℝ :=
  ∫ y, kernel x y * poisson s y ∂ν

omit hC hν in
lemma smoothedPoisson_measurable [SFinite ν] (s : Boundary) : Measurable (smoothedPoisson (ν := ν) s) := by
  have hm : Measurable (fun z : Plane × Plane => kernel z.1 z.2 * poisson s z.2) :=
    measurable_kernel.mul (by unfold poisson DiskFormula.poisson; fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

include hC hν in
lemma smoothedPoisson_memLp [IsFiniteMeasure ν] (s : Boundary) :
    MemLp (smoothedPoisson (ν := ν) s) 2 ν := by
  obtain ⟨B,_,hB⟩ := green_poisson_uniform_bound hC hν
  apply MemLp.of_bound (smoothedPoisson_measurable s).aestronglyMeasurable B
  filter_upwards [ae_mem_disk hν] with x hx
  exact hB x hx s

end StrictHotSpots.PlaneGreen
end
end FullBoundarySmoothingLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
