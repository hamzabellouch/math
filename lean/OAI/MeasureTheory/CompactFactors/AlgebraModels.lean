import OAI.MeasureTheory.CompactFactors.Separability

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal
open scoped RealInnerProductSpace BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma covariance_sub_left (φ : G →+ G) (v v' w : Func X) :
    covariance μ q φ (v-v') w = covariance μ q φ v w - covariance μ q φ v' w := by
  have h := covariance_add_left μ q φ (v-v') v' w
  rw [sub_add_cancel] at h
  rw [h]
  ext g y
  simp only [Family.sub_apply, Family.add_apply, sub_apply, add_apply]
  ring
omit [StandardBorelSpace Y] [Nonempty Y] in
lemma covariance_sub_right (φ : G →+ G) (v w w' : Func X) :
    covariance μ q φ v (w-w') = covariance μ q φ v w - covariance μ q φ v w' := by
  have h := covariance_add_right μ q φ v (w-w') w'
  rw [sub_add_cancel] at h
  rw [h]
  ext g y
  simp only [Family.sub_apply, Family.add_apply, sub_apply, add_apply]
  ring

omit [StandardBorelSpace Y] [Nonempty Y] in
include hq in
lemma covariance_norm_left (φ : G →+ G) (v w : Func X) (g : G) :
    ‖l2 (μ.map q) (covariance μ q φ v w g)‖ ≤ (2*(bound w : ℝ))*‖l2 μ v‖ := by
  have hp := conditional_norm_l2_le μ q hq v
  have h1 : ‖l2 (μ.map q) (conditional μ q (v*act (φ g) w))‖ ≤ (bound w : ℝ)*‖l2 μ v‖ :=
    (conditional_norm_l2_le μ q hq _).trans (l2_mul_norm_le μ v (act (φ g) w)
      (fun x => norm_le_bound w _))
  have h2 : ‖l2 (μ.map q) (conditional μ q v * act (φ g) (conditional μ q w))‖ ≤
      (bound w : ℝ)*‖l2 μ v‖ := by
    have h := l2_norm_mul_le (μ.map q) (act (φ g) (conditional μ q w)) (conditional μ q v)
      (fun y => expect_bound _ w (norm_le_bound w) (φ g +ᵥ y))
    rw [mul_comm (act _ _) _] at h
    exact h.trans (mul_le_mul_of_nonneg_left hp (bound w).coe_nonneg)
  rw [covariance_apply, map_sub]
  calc
    _ ≤ ‖l2 (μ.map q) (conditional μ q (v*act (φ g) w))‖ +
        ‖l2 (μ.map q) (conditional μ q v * act (φ g) (conditional μ q w))‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

variable [VAddInvariantMeasure G X μ]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
omit [StandardBorelSpace Y] [Nonempty Y] in
include hq hqcov in
lemma covariance_norm_right (φ : G →+ G) (v w : Func X) (g : G) :
    ‖l2 (μ.map q) (covariance μ q φ v w g)‖ ≤ (2*(bound v : ℝ))*‖l2 μ w‖ := by
  have hn : ‖l2 μ (act (φ g) w)‖ = ‖l2 μ w‖ := by
    rw [l2_act]
    exact (Amenable.Koopman.action μ (φ g)).norm_map _
  have h1 : ‖l2 (μ.map q) (conditional μ q (v*act (φ g) w))‖ ≤ (bound v : ℝ)*‖l2 μ w‖ := by
    have h := (conditional_norm_l2_le μ q hq (v*act (φ g) w)).trans
      (l2_norm_mul_le μ v _ (norm_le_bound v))
    rwa [hn] at h
  have hp : ‖l2 (μ.map q) (act (φ g) (conditional μ q w))‖ ≤ ‖l2 μ w‖ := by
    have he := (l2_eq_iff (μ.map q) _ _).mpr (conditional_act μ q hq hqcov (φ g) w)
    rw [← he, ← hn]
    exact conditional_norm_l2_le μ q hq _
  have h2 : ‖l2 (μ.map q) (conditional μ q v * act (φ g) (conditional μ q w))‖ ≤
      (bound v : ℝ)*‖l2 μ w‖ := by
    exact (l2_norm_mul_le (μ.map q) _ _ (expect_bound _ v (norm_le_bound v))).trans
      (mul_le_mul_of_nonneg_left hp (bound v).coe_nonneg)
  rw [covariance_apply, map_sub]
  calc
    _ ≤ ‖l2 (μ.map q) (conditional μ q (v*act (φ g) w))‖ +
        ‖l2 (μ.map q) (conditional μ q v * act (φ g) (conditional μ q w))‖ := norm_sub_le _ _
    _ ≤ _ := by linarith
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]

lemma meanNorm_zero_of_dense (M : Amenable.Mean G) (S : Set (Func X))
    (hd : ∀ f : Func X, ∀ ε : ℝ, 0<ε → ∃ h∈S, ‖l2 μ (f-h)‖ < ε)
    (T : Func X → Family G Y) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ f h : Func X, ∀ g, ‖l2 ν (T f g-T h g)‖ ≤ C*‖l2 μ (f-h)‖)
    (hS : ∀ f∈S, Family.meanNorm ν M (T f) = 0) (f : Func X) :
    Family.meanNorm ν M (T f) = 0 := by
  apply Family.meanNorm_eq_zero_of_approx
  intro ε hε
  have hden : 0 < C+1 := by linarith
  obtain ⟨h,hh,hdist⟩ := hd f (ε/(C+1)) (div_pos hε hden)
  refine ⟨T h, hS h hh, fun g => ?_⟩
  have he : ε/(C+1)*(C+1) = ε := div_mul_cancel₀ _ (ne_of_gt hden)
  have hd0 : 0 ≤ ε/(C+1) := (div_pos hε hden).le
  calc
    _ ≤ C * ‖l2 μ (f-h)‖ := hT f h g
    _ ≤ C*(ε/(C+1)) := mul_le_mul_of_nonneg_left hdist.le hC
    _ ≤ ε := by nlinarith

variable [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
  [VAddInvariantMeasure G X μ]
variable (q : X → Y) (hq : Measurable q) [IsProbabilityMeasure (μ.map q)]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
omit [StandardBorelSpace Y] [Nonempty Y] in
include hq hqcov in
lemma covariance_zero_of_dense (M : Amenable.Mean G) (S : Set (Func X))
    (hd : ∀ f : Func X, ∀ ε : ℝ, 0<ε → ∃ h∈S, ‖l2 μ (f-h)‖ < ε)
    (φ : G →+ G)
    (hS : ∀ v∈S, ∀ w∈S, Family.meanNorm (μ.map q) M (covariance μ q φ v w) = 0)
    (v w : Func X) : Family.meanNorm (μ.map q) M (covariance μ q φ v w) = 0 := by
  have hw (v : Func X) (hv : v∈S) (w : Func X) :
      Family.meanNorm (μ.map q) M (covariance μ q φ v w) = 0 := by
    apply meanNorm_zero_of_dense μ (μ.map q) M S hd (covariance μ q φ v)
      (C := 2*(bound v : ℝ)) (by positivity) _ (hS v hv) w
    intro w w' g
    have he : covariance μ q φ v w g - covariance μ q φ v w' g = covariance μ q φ v (w-w') g :=
      congrArg (fun F : Family G Y => F g) (covariance_sub_right μ q φ v w w').symm
    rw [he]
    exact covariance_norm_right μ q hq hqcov φ v (w-w') g
  apply meanNorm_zero_of_dense μ (μ.map q) M S hd (fun v => covariance μ q φ v w)
    (C := 2*(bound w : ℝ)) (by positivity) _ (fun v hv => hw v hv w) v
  intro v v' g
  have he : covariance μ q φ v w g - covariance μ q φ v' w g = covariance μ q φ (v-v') w g :=
    congrArg (fun F : Family G Y => F g) (covariance_sub_left μ q φ v v' w).symm
  rw [he]
  exact covariance_norm_left μ q hq φ (v-v') w g
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace EuclideanFiveColor.RelativeProduct
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
lemma graph_mixture (ν : Measure Y) [SFinite ν] (κ : Kernel Y X) [IsMarkovKernel κ]
    (q : X → Y) (hq : Measurable q) (hf : ∀ᵐ y ∂ν, ∀ᵐ x ∂κ y, q x = y) :
    (κ ∘ₘ ν).map (fun x => (q x,x)) = ν ⊗ₘ κ := by
  ext s hs
  rw [Measure.map_apply (show Measurable (fun x => (q x,x)) from hq.prodMk measurable_id) hs,
    Measure.bind_apply (hs.preimage (show Measurable (fun x => (q x,x)) from hq.prodMk measurable_id)) (Kernel.measurable κ).aemeasurable,
    Measure.compProd_apply hs]
  apply lintegral_congr_ae
  filter_upwards [hf] with y hy
  apply measure_congr
  filter_upwards [hy] with x hx
  change ((q x,x) ∈ s) = ((y,x) ∈ s)
  rw [hx]

lemma map_mixture (ν : Measure Y) [SFinite ν] (κ : Kernel Y X) [IsMarkovKernel κ]
    (q : X → Y) (hq : Measurable q) (hf : ∀ᵐ y ∂ν, ∀ᵐ x ∂κ y, q x = y) :
    (κ ∘ₘ ν).map q = ν := by
  have he := congrArg Measure.fst (graph_mixture ν κ q hq hf)
  change ((κ ∘ₘ ν).map (fun x => (q x,id x))).fst = (ν ⊗ₘ κ).fst at he
  simpa only [Measure.fst_map_prodMk hq measurable_id, Measure.fst_compProd] using he

variable [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

include hq in
lemma square_fiber : ∀ᵐ y ∂μ.map q,
    ∀ᵐ z ∂((condDistrib id q μ).prod (condDistrib id q μ)) y, q z.1 = y := by
  filter_upwards [ConditionalFiber.ae_in_own_fiber μ q hq] with y hy
  rw [Kernel.prod_apply]
  exact (measurePreserving_fst (μ := condDistrib id q μ y)
    (ν := condDistrib id q μ y)).quasiMeasurePreserving.ae hy

lemma law_map_base : (law μ q hq).map (q ∘ Prod.fst) = μ.map q := by
  rw [law_eq_mixture]
  exact map_mixture (μ.map q) _ _ (hq.comp measurable_fst) (square_fiber μ q hq)

lemma conditional_square :
    condDistrib id (q ∘ Prod.fst) (law μ q hq) =ᵐ[μ.map q]
      (condDistrib id q μ).prod (condDistrib id q μ) := by
  have he := graph_mixture (μ.map q) ((condDistrib id q μ).prod (condDistrib id q μ))
    (q ∘ Prod.fst) (hq.comp measurable_fst) (square_fiber μ q hq)
  rw [← law_eq_mixture μ q hq] at he
  have hc := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (hq.comp measurable_fst) measurable_id (he.trans (by rw [law_map_base]))
  rwa [law_map_base] at hc

end EuclideanFiveColor.RelativeProduct

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

omit [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G] in
lemma conditional_tensor (v w : Func X) :
    conditional (RelativeProduct.law μ q hq) (q ∘ Prod.fst) (tensor v w) =ᵐ[μ.map q]
      conditional μ q v * conditional μ q w := by
  filter_upwards [RelativeProduct.conditional_square μ q hq] with y hy
  change (∫ z, tensor v w z ∂condDistrib id (q ∘ Prod.fst) (RelativeProduct.law μ q hq) y) = _
  rw [hy, Kernel.prod_apply]
  exact integral_prod_mul v w

variable [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
  [VAddInvariantMeasure G X μ]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
omit [TopologicalSpace G] [DiscreteTopology G] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y] [IsProbabilityMeasure μ] in
include hq hqcov in
lemma factor_preserving (g : G) : MeasurePreserving (fun y : Y => g +ᵥ y) (μ.map q) (μ.map q) := by
  refine ⟨measurable_const_vadd g, ?_⟩
  rw [Measure.map_map (measurable_const_vadd g) hq]
  calc
    _ = μ.map (q ∘ (fun x => g +ᵥ x)) := Measure.map_congr (hqcov g).symm
    _ = _ := by rw [← Measure.map_map hq (measurable_const_vadd g), (measurePreserving_vadd g μ).map_eq]

omit [TopologicalSpace G] [DiscreteTopology G] in
include hqcov in
lemma covariance_tensor (φ : G →+ G) (a₁ a₂ b₁ b₂ : Func X) (g : G) :
    covariance (RelativeProduct.law μ q hq) (q ∘ Prod.fst) φ (tensor a₁ a₂) (tensor b₁ b₂) g =ᵐ[μ.map q]
      ((Family.conditional μ q (Family.const a₁ * Family.orbit φ b₁)) *
        (Family.conditional μ q (Family.const a₂ * Family.orbit φ b₂)) -
        (Family.const (conditional μ q a₁) * Family.orbit φ (conditional μ q b₁)) *
        (Family.const (conditional μ q a₂) * Family.orbit φ (conditional μ q b₂)) : Family G Y) g := by
  have ht : tensor a₁ a₂ * act (φ g) (tensor b₁ b₂) = tensor (a₁*act (φ g) b₁) (a₂*act (φ g) b₂) := by
    rw [← tensor_act, tensor_mul]
  have h₁ := conditional_tensor μ q hq a₁ a₂
  have h₂ := (factor_preserving μ q hq hqcov (φ g)).quasiMeasurePreserving.ae
    (conditional_tensor μ q hq b₁ b₂)
  have h₃ := conditional_tensor μ q hq (a₁*act (φ g) b₁) (a₂*act (φ g) b₂)
  filter_upwards [h₁,h₂,h₃] with y hy₁ hy₂ hy₃
  change conditional _ _ (tensor a₁ a₂ * act (φ g) (tensor b₁ b₂)) y -
    conditional _ _ (tensor a₁ a₂) y * conditional _ _ (tensor b₁ b₂) (φ g +ᵥ y) = _
  rw [ht, hy₁, hy₂, hy₃]
  dsimp only [Family.mul_apply, Family.sub_apply, Family.conditional_apply,
    Family.const_apply, Family.orbit_apply, mul_apply, sub_apply, act_apply, Pi.mul_apply]
  ring

variable [IsProbabilityMeasure (μ.map q)]
include hqcov in
lemma covariance_tensor_mean_zero (M : Amenable.Mean G) (hp : PairVanishing μ q hq M)
    (φ : G →+ G) (hs : Function.Surjective φ) (a₁ a₂ b₁ b₂ : Func X) :
    Family.meanNorm (μ.map q) M
      (covariance (RelativeProduct.law μ q hq) (q ∘ Prod.fst) φ (tensor a₁ a₂) (tensor b₁ b₂)) = 0 := by
  let A₁ := Family.conditional μ q (Family.const a₁ * Family.orbit φ b₁)
  let A₂ := Family.conditional μ q (Family.const a₂ * Family.orbit φ b₂)
  let B₁ := Family.const (conditional μ q a₁) * Family.orbit φ (conditional μ q b₁)
  let B₂ := Family.const (conditional μ q a₂) * Family.orbit φ (conditional μ q b₂)
  have h₁ : Family.meanNorm (μ.map q) M (A₁-B₁) = 0 := covariance_mean_zero μ q hq hqcov M hp φ hs a₁ b₁
  have h₂ : Family.meanNorm (μ.map q) M (A₂-B₂) = 0 := covariance_mean_zero μ q hq hqcov M hp φ hs a₂ b₂
  rw [Family.meanNorm_congr (μ.map q) M (covariance_tensor μ q hq hqcov φ a₁ a₂ b₁ b₂)]
  change Family.meanNorm (μ.map q) M (A₁*A₂-B₁*B₂) = 0
  have he : A₁*A₂-B₁*B₂ = (A₁-B₁)*A₂ + (A₂-B₂)*B₁ := by ring
  rw [he]
  exact Family.meanNorm_add_zero _ _ (Family.meanNorm_mul_zero _ _ h₁) (Family.meanNorm_mul_zero _ _ h₂)
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace EuclideanFiveColor.BoundedMeasurable
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
inductive FiniteTensor : Func (X×Y) → Prop
  | tensor (f : Func X) (g : Func Y) : FiniteTensor (tensor f g)
  | add {f g : Func (X×Y)} : FiniteTensor f → FiniteTensor g → FiniteTensor (f+g)

lemma FiniteTensor.zero : FiniteTensor (0 : Func (X×Y)) := by
  have he : BoundedMeasurable.tensor (0 : Func X) (0 : Func Y) = 0 := by ext z; simp
  rw [← he]
  exact .tensor _ _

lemma FiniteTensor.sum {ι : Type*} (s : Finset ι) (f : ι → Func (X×Y))
    (hf : ∀ i∈s, FiniteTensor (f i)) : FiniteTensor (∑ i∈s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using FiniteTensor.zero (X := X) (Y := Y)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact .add (hf i (Finset.mem_insert_self _ _)) (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma func_sum_apply {ι : Type*} (s : Finset ι) (f : ι → Func X) (x : X) :
    (∑ i∈s, f i) x = ∑ i∈s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

variable [MeasurableSpace.CountablyGenerated X] [MeasurableSpace.CountablyGenerated Y]
open RectangleDensity

def codeCell (n : ℕ) (c : Code n) : Func X := by
  classical
  refine ⟨fun x => if code X n x = c then (1:ℂ) else 0, ?_, 1, ?_⟩
  · exact measurable_const.piecewise ((measurable_code n) (measurableSet_singleton c)) measurable_const
  · intro x; dsimp only; split_ifs <;> simp

lemma tensor_code_finite (n : ℕ) (a : Code n × Code n → ℂ) (F : Func (X×Y))
    (he : ∀ z, F z = a (pairCode n z)) : FiniteTensor F := by
  classical
  let T : Code n × Code n → Func (X×Y) := fun c =>
    tensor (a c • codeCell (X := X) n c.1) (codeCell (X := Y) n c.2)
  have hsum : F = ∑ c, T c := by
    ext z
    rw [he, func_sum_apply]
    rw [Finset.sum_eq_single (pairCode n z)]
    · simp [T, tensor_apply, codeCell, pairCode]
    · intro c _ hc
      have hn : code X n z.1 ≠ c.1 ∨ code Y n z.2 ≠ c.2 := by
        contrapose! hc
        exact Prod.ext hc.1.symm hc.2.symm
      rcases hn with hn | hn <;> simp [T, tensor_apply, codeCell, hn]
    · simp
  rw [hsum]
  exact FiniteTensor.sum _ _ (fun _ _ => .tensor _ _)

lemma finiteTensor_dense (ν : Measure (X×Y)) [IsProbabilityMeasure ν]
    (f : Func (X×Y)) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : Func (X×Y), FiniteTensor h ∧ ‖l2 ν (f-h)‖ < ε := by
  obtain ⟨n,a,ha,_,he⟩ := bounded_rectangles ν f (measurable f) (bound f)
    (bound f).coe_nonneg (norm_le_bound f) ε hε
  let h : Func (X×Y) := ⟨fun z => a (pairCode n z),
    (measurable_of_countable a).comp (measurable_pairCode n), 2*bound f,
    fun z => by simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using ha (pairCode n z)⟩
  refine ⟨h, tensor_code_finite n a h (fun _ => rfl), ?_⟩
  have hh : ‖l2 ν (f-h)‖^2 < ε^2 := by
    rw [norm_l2_sq]
    exact he
  nlinarith [norm_nonneg (l2 ν (f-h))]
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.BoundedMeasurable

section
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
  [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (q : X → Y) (hq : Measurable q) [IsProbabilityMeasure (μ.map q)]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
include hqcov in
lemma pairVanishing_of_covariance (M : Amenable.Mean G)
    (hc : ∀ (φ : G →+ G), Function.Surjective φ → ∀ v w : Func X,
      Family.meanNorm (μ.map q) M (covariance μ q φ v w) = 0) : PairVanishing μ q hq M := by
  intro φ hs v w hw
  have he0 : l2 μ (project μ q hq w) = l2 μ 0 := hw.trans (map_zero _).symm
  have hp : project μ q hq w =ᵐ[μ] (0 : Func X) := (l2_eq_iff μ _ _).mp he0
  have he (g : G) : covariance μ q φ v w g =ᵐ[μ.map q] conditional μ q (v*act (φ g) w) := by
    apply (covariance_center μ q hq hqcov φ v w g).trans
    apply conditional_congr μ q hq
    filter_upwards [(measurePreserving_vadd (φ g) μ).quasiMeasurePreserving.ae hp] with x hx
    change v x * (w (φ g +ᵥ x) - project μ q hq w (φ g +ᵥ x)) = v x*w (φ g +ᵥ x)
    change project μ q hq w (φ g +ᵥ x) = 0 at hx
    rw [hx, sub_zero]
  have hmean := hc φ hs v w
  have hnorm : Family.meanNorm (μ.map q) M (covariance μ q φ v w) =
      Family.meanNorm (μ.map q) M (Family.conditional μ q (Family.const v * Family.orbit φ w)) :=
    Family.meanNorm_congr _ _ he
  rw [hnorm] at hmean
  have hseq : Family.toL2 (μ.map q) (Family.conditional μ q (Family.const v * Family.orbit φ w)) =
      pairSequence μ q hq φ v w := by ext g; rfl
  unfold Family.meanNorm at hmean
  rwa [hseq] at hmean
end

variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
  [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (q : X → Y) (hq : Measurable q)
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))

omit [TopologicalSpace G] [DiscreteTopology G] [VAddInvariantMeasure G X μ]
  [StandardBorelSpace Y] [Nonempty Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y] in
include hqcov in
lemma square_equivariant (g : G) :
    (fun z => (q ∘ Prod.fst) (g +ᵥ z)) =ᵐ[RelativeProduct.law μ q hq]
      (fun z => g +ᵥ (q ∘ Prod.fst) z) := by
  have hp : MeasurePreserving Prod.fst (RelativeProduct.law μ q hq) μ :=
    ⟨measurable_fst, Measure.fst_compProd μ ((condDistrib id q μ).comap q hq)⟩
  exact hp.quasiMeasurePreserving.ae (hqcov g)

variable [IsProbabilityMeasure (μ.map q)]
include hqcov in
lemma covariance_finiteTensor_mean_zero (M : Amenable.Mean G) (hp : PairVanishing μ q hq M)
    (φ : G →+ G) (hs : Function.Surjective φ) (v w : Func (X×X))
    (hv : FiniteTensor v) (hw : FiniteTensor w) :
    Family.meanNorm (μ.map q) M
      (covariance (RelativeProduct.law μ q hq) (q ∘ Prod.fst) φ v w) = 0 := by
  induction hv with
  | tensor a₁ a₂ =>
    induction hw with
    | tensor b₁ b₂ => exact covariance_tensor_mean_zero μ q hq hqcov M hp φ hs a₁ a₂ b₁ b₂
    | add _ _ ih₁ ih₂ =>
      rw [covariance_add_right]
      exact Family.meanNorm_add_zero _ _ ih₁ ih₂
  | add _ _ ih₁ ih₂ =>
    rw [covariance_add_left]
    exact Family.meanNorm_add_zero _ _ ih₁ ih₂

include hqcov in
lemma square_pairVanishing (M : Amenable.Mean G) (hp : PairVanishing μ q hq M) :
    PairVanishing (RelativeProduct.law μ q hq) (q ∘ Prod.fst) (hq.comp measurable_fst) M := by
  have : VAddInvariantMeasure G (X×X) (RelativeProduct.law μ q hq) :=
    RelativeProduct.law_invariant_add μ q hq (fun g => measurePreserving_vadd g μ) hqcov
  have : IsProbabilityMeasure ((RelativeProduct.law μ q hq).map (q ∘ Prod.fst)) := by
    rw [RelativeProduct.law_map_base μ q hq]
    infer_instance
  apply pairVanishing_of_covariance (RelativeProduct.law μ q hq) (q ∘ Prod.fst)
    (hq.comp measurable_fst) (square_equivariant μ q hq hqcov) M
  intro φ hs v w
  apply covariance_zero_of_dense (RelativeProduct.law μ q hq) (q ∘ Prod.fst)
    (hq.comp measurable_fst) (square_equivariant μ q hq hqcov) M
    {f | FiniteTensor f} (fun f ε hε => finiteTensor_dense _ f ε hε) φ _ v w
  intro v hv w hw
  simpa only [RelativeProduct.law_map_base μ q hq] using
    covariance_finiteTensor_mean_zero μ q hq hqcov M hp φ hs v w hv hw
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

omit [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G] in
lemma square_tensor_centered (f : Func X) (hf : l2 μ (project μ q hq f) = 0) :
    l2 (RelativeProduct.law μ q hq)
      (project (RelativeProduct.law μ q hq) (q ∘ Prod.fst) (hq.comp measurable_fst)
        (tensor f (bmConj f))) = 0 := by
  have he : l2 (μ.map q) (conditional μ q f) = 0 := by
    apply norm_eq_zero.mp
    rw [← norm_project_l2 μ q hq, hf, norm_zero]
  have hz : conditional μ q f =ᵐ[μ.map q] (0 : Func Y) := by
    apply (l2_eq_iff _ _ _).mp
    rw [he, map_zero]
  have ht : conditional (RelativeProduct.law μ q hq) (q ∘ Prod.fst) (tensor f (bmConj f))
      =ᵐ[μ.map q] (0 : Func Y) := by
    filter_upwards [conditional_tensor μ q hq f (bmConj f), hz] with y hy hz
    rw [hy]
    change conditional μ q f y * _ = 0
    rw [hz, zero_apply, zero_mul]
  rw [← map_zero (l2 (RelativeProduct.law μ q hq))]
  apply (l2_eq_iff _ _ _).mpr
  have ht' : conditional (RelativeProduct.law μ q hq) (q ∘ Prod.fst) (tensor f (bmConj f)) =ᵐ[(RelativeProduct.law μ q hq).map (q ∘ Prod.fst)] (0 : Func Y) := by
    simpa only [RelativeProduct.law_map_base μ q hq] using ht
  exact (ae_of_ae_map (hq.comp measurable_fst).aemeasurable ht').mono (fun z hz => hz)

variable {ι : Type*} [DecidableEq ι]
omit [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G] [StandardBorelSpace X]
  [Nonempty X] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] in
lemma tensor_prod (s : Finset ι) (f h : ι → Func X) :
    tensor (∏ i∈s, f i) (∏ i∈s, h i) = ∏ i∈s, tensor (f i) (h i) := by
  induction s using Finset.induction_on with
  | empty => ext z; simp [tensor_apply]
  | @insert i s hi ih => simp only [Finset.prod_insert hi, tensor_mul, ih]

variable [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
  [VAddInvariantMeasure G X μ]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
variable [IsProbabilityMeasure (μ.map q)]
include hqcov in
lemma centered_conditional_mean_zero (M : Amenable.Mean G) (hp : PairVanishing μ q hq M)
    (s : Finset ι) (φ : ι → G →+ G) (θ : G →+ G) (f : ι → Func X)
    (ha : Admissible s (fun i => θ + φ i))
    (hc : ∃ j∈s, l2 μ (project μ q hq (f j)) = 0) :
    Family.meanNorm (μ.map q) M (Family.conditional μ q (∏ i∈s, Family.orbit (φ i) (f i))) = 0 := by
  let ρ := RelativeProduct.law μ q hq
  have : VAddInvariantMeasure G (X×X) ρ :=
    RelativeProduct.law_invariant_add μ q hq (fun g => measurePreserving_vadd g μ) hqcov
  let t : ι → Func (X×X) := fun i => tensor (f i) (bmConj (f i))
  let F : Family G (X×X) := ∏ i∈s, Family.orbit (θ+φ i) (t i)
  have htc : ∃ j∈s, l2 ρ (project ρ (q ∘ Prod.fst) (hq.comp measurable_fst) (t j)) = 0 := by
    obtain ⟨j,hj,hf⟩ := hc
    exact ⟨j,hj,square_tensor_centered μ q hq (f j) hf⟩
  have hv : Family.avg ρ M F = 0 := avg_product_zero_of_pair ρ (q ∘ Prod.fst)
    (hq.comp measurable_fst) (square_equivariant μ q hq hqcov) M
    (square_pairVanishing μ q hq hqcov M hp) s (fun i => θ+φ i) t ha htc
  unfold Family.meanNorm
  apply M.norm_mean_zero_of_square
  have he : Amenable.Mean.squareNorm (Family.toL2 (μ.map q)
      (Family.conditional μ q (∏ i∈s, Family.orbit (φ i) (f i)))) =
      Amenable.Mean.pairing (Family.toL2 ρ F) (l2 ρ (1 : Func (X×X))) := by
    ext g
    simp only [Amenable.Mean.squareNorm_apply, Amenable.Mean.pairing_apply,
      Family.toL2_apply, Family.conditional_apply, Family.prod_apply, Family.orbit_apply]
    change ‖l2 (μ.map q) (conditional μ q (∏ i∈s, act (φ i g) (f i)))‖^2 =
      inner ℝ (l2 ρ (F g)) (l2 ρ (1 : Func (X×X)))
    have hF : F g = act (θ g) (tensor (∏ i∈s, act (φ i g) (f i))
        (bmConj (∏ i∈s, act (φ i g) (f i)))) := by
      dsimp only [F]
      rw [Family.prod_apply, conj_prod, tensor_prod, act_prod]
      apply Finset.prod_congr rfl
      intro i hi
      rw [← act_conj, tensor_act, ← act_add]
      rfl
    have hc1 : bmConj (1 : Func (X×X)) = 1 := by ext z; simp
    rw [hF, real_inner_comm, l2_inner, hc1, one_mul, integral_act,
      integral_tensor_self μ q hq]
    rfl
  rw [he, ← Family.avg_pair, hv, inner_zero_left]
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.AlgebraReplacement
variable {ι A : Type*} [DecidableEq ι] [CommRing A]
lemma prod_sub_prod (s : Finset ι) (f g : ι → A) :
    (∏ i∈s, f i) - (∏ i∈s, g i) = ∑ t∈s.powerset.erase ∅,
      (∏ i∈t, (f i-g i)) * ∏ i∈s\t, g i := by
  have he := Finset.prod_add (fun i => f i-g i) g s
  simp only [sub_add_cancel] at he
  rw [he]
  have hs := Finset.sum_erase_add s.powerset
    (fun t => (∏ i∈t, (f i-g i)) * ∏ i∈s\t, g i) (Finset.empty_mem_powerset s)
  simp only [Finset.prod_empty, Finset.sdiff_empty, one_mul] at hs
  exact sub_eq_iff_eq_add.mpr hs.symm
end EuclideanFiveColor.AlgebraReplacement
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)
variable {ι : Type*} [DecidableEq ι]
omit [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G] [StandardBorelSpace Y] [Nonempty Y] in
lemma Family.conditional_sum (s : Finset ι) (f : ι → Family G X) :
    Family.conditional μ q (∑ i∈s, f i) = ∑ i∈s, Family.conditional μ q (f i) := by
  induction s using Finset.induction_on with
  | empty => ext g y; simp [Family.conditional, conditional, expect]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Family.conditional_add, ih]

variable [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
  [VAddInvariantMeasure G X μ]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
variable [IsProbabilityMeasure (μ.map q)]
include hqcov in
lemma conditional_multiple_mean_zero (M : Amenable.Mean G) (hp : PairVanishing μ q hq M)
    (s : Finset ι) (φ : ι → G →+ G) (θ : G →+ G) (f : ι → Func X)
    (ha : Admissible s (fun i => θ + φ i)) :
    Family.meanNorm (μ.map q) M (Family.conditional μ q (∏ i∈s, Family.orbit (φ i) (f i)) -
      ∏ i∈s, Family.orbit (φ i) (conditional μ q (f i))) = 0 := by
  let a : ι → Family G X := fun i => Family.orbit (φ i) (f i)
  let b : ι → Family G X := fun i => Family.orbit (φ i) (project μ q hq (f i))
  have hb (g : G) : conditional μ q ((∏ i∈s, b i) g) =ᵐ[μ.map q]
      (∏ i∈s, Family.orbit (φ i) (conditional μ q (f i))) g := by
    simp only [Family.prod_apply, Family.orbit_apply]
    apply (conditional_congr μ q hq (f := ∏ i∈s, act (φ i g) (project μ q hq (f i)))
      (g := comp (∏ i∈s, act (φ i g) (conditional μ q (f i))) q hq) ?_).trans
      (conditional_lift μ q hq _)
    filter_upwards [prod_act_project_lift μ q hq hqcov s φ f g] with x hx
    simpa only [func_prod_apply, Finset.prod_apply] using hx
  have hrep : Family.meanNorm (μ.map q) M (Family.conditional μ q
      ((∏ i∈s, a i) - ∏ i∈s, b i)) = 0 := by
    rw [AlgebraReplacement.prod_sub_prod s a b, Family.conditional_sum]
    apply Family.meanNorm_sum_zero
    intro t ht
    have hts : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_of_mem_erase ht)
    have htn : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase ht)
    rw [AlgebraReplacement.mixed_prod s t hts]
    let w : ι → Func X := fun i => if i∈t then f i-project μ q hq (f i) else project μ q hq (f i)
    have he : (∏ i∈s, if i∈t then a i-b i else b i) = ∏ i∈s, Family.orbit (φ i) (w i) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hit : i∈t
      · simp only [hit, ↓reduceIte, w, a, b]
        apply Family.ext
        intro g
        exact (act_sub _ _ _).symm
      · simp only [hit, ↓reduceIte, w, b]
    rw [he]
    apply centered_conditional_mean_zero μ q hq hqcov M hp s φ θ w ha
    obtain ⟨j,hj⟩ := htn
    refine ⟨j,hts hj,?_⟩
    simp only [w, hj, ↓reduceIte]
    exact center_project_l2 μ q hq (f j)
  rw [Family.conditional_sub] at hrep
  rw [Family.meanNorm_congr (μ.map q) M (F := Family.conditional μ q (∏ i∈s, a i) -
      Family.conditional μ q (∏ i∈s, b i)) (H := Family.conditional μ q (∏ i∈s, a i) -
      ∏ i∈s, Family.orbit (φ i) (conditional μ q (f i))) (fun g => by
        filter_upwards [hb g] with y hy
        simp only [Family.sub_apply, sub_apply, Family.conditional_apply]
        rw [hy])] at hrep
  exact hrep
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.BoundedMeasurable
variable {G : Type*} [AddCommGroup G]
def scaleHom (n : ℤ) : G →+ G := n • AddMonoidHom.id G
@[simp] lemma scaleHom_apply (n : ℤ) (g : G) : scaleHom n g = n • g := rfl
lemma scaleHom_add (n m : ℤ) : scaleHom (G := G) (n+m) = scaleHom n + scaleHom m := add_smul _ _ _
lemma scaleHom_sub (n m : ℤ) : scaleHom (G := G) (n-m) = scaleHom n - scaleHom m := sub_smul _ _ _
variable {ι : Type*} [DecidableEq ι]
omit [DecidableEq ι] in
lemma shifted_admissible (hdiv : ∀ n : ℤ, n ≠ 0 → Function.Surjective (scaleHom (G := G) n))
    (s : Finset ι) (n : ι → ℤ) (hn : Set.InjOn n s) :
    ∃ m : ℤ, Admissible s (fun i => scaleHom (G := G) m + scaleHom (n i)) := by
  obtain ⟨m,hm⟩ := Infinite.exists_notMem_finset (s.image (fun i => -n i))
  refine ⟨m, ?_, ?_⟩
  · intro i hi
    dsimp only
    rw [← scaleHom_add]
    apply hdiv
    intro hz
    have he : m = -n i := eq_neg_of_add_eq_zero_left hz
    exact hm (Finset.mem_image.mpr ⟨i,hi,he.symm⟩)
  · intro i hi j hj hij
    have he : (scaleHom m + scaleHom (n i)) - (scaleHom m + scaleHom (n j)) =
        scaleHom (G := G) (n i-n j) := by rw [scaleHom_sub]; abel
    rw [he]
    apply hdiv
    exact sub_ne_zero.mpr (fun h => hij (hn hi hj h))
variable {X Y : Type*} [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
  [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (q : X → Y) (hq : Measurable q)
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
variable [IsProbabilityMeasure (μ.map q)]
include hqcov in
lemma conditional_integer_multiple_mean_zero
    (hdiv : ∀ n : ℤ, n ≠ 0 → Function.Surjective (scaleHom (G := G) n))
    (M : Amenable.Mean G) (hp : PairVanishing μ q hq M)
    (s : Finset ι) (n : ι → ℤ) (f : ι → Func X) (hn : Set.InjOn n s) :
    Family.meanNorm (μ.map q) M (Family.conditional μ q (∏ i∈s, Family.orbit (scaleHom (n i)) (f i)) -
      ∏ i∈s, Family.orbit (scaleHom (n i)) (conditional μ q (f i))) = 0 := by
  obtain ⟨m,hm⟩ := shifted_admissible hdiv s n hn
  exact conditional_multiple_mean_zero μ q hq hqcov M hp s (fun i => scaleHom (n i)) (scaleHom m) f hm
end EuclideanFiveColor.BoundedMeasurable

end

end OAI
