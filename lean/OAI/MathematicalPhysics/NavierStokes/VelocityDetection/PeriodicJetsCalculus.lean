import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SmoothExpressions
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicJets

namespace OAI

noncomputable section
namespace VelocityDetection.PeriodicSpace.Jets
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
open scoped Topology ContDiff ZeroAtInfty BigOperators

private theorem init_cons {α : Type*} {k : ℕ} (i : α) (w : Fin (k + 1) → α) :
    Fin.init (Fin.cons (α := fun _ => α) i w) = Fin.cons (α := fun _ => α) i (Fin.init w) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [Fin.init]
  · simp [Fin.init]

private theorem snoc_cons {α : Type*} {k : ℕ} (i j : α) (w : Fin k → α) :
    Fin.snoc (α := fun _ => α) (Fin.cons (α := fun _ => α) i w) j =
      Fin.cons (α := fun _ => α) i (Fin.snoc (α := fun _ => α) w j) := by
  funext l
  refine Fin.lastCases ?_ (fun l => ?_) l
  · simp
  · refine Fin.cases ?_ (fun l => ?_) l
    · simp
    · rw [Fin.snoc_castSucc, Fin.cons_succ, ← Fin.succ_castSucc,
        Fin.cons_succ, Fin.snoc_castSucc]

def differentiate {n a : ℕ} (i : Fin n) (J : compatibleJets n (a + 1)) : compatibleJets n a :=
  ⟨fun ⟨k,w⟩ => entry J (k.val + 1) (by omega) (Fin.snoc w i), by
    intro k w X
    have hh := J.property ⟨k.val + 1, by omega⟩ (Fin.snoc w i) X
    convert hh using 1
    · rfl
    · unfold gradient
      apply Finset.sum_congr rfl
      intro j _
      simp only [entry, snoc_cons]
      rfl⟩

@[simp] theorem differentiate_entry {n a : ℕ} (i : Fin n) (J : compatibleJets n (a + 1))
    (k : ℕ) (hk : k ≤ a) (w : Fin k → Fin n) :
    entry (differentiate i J) k hk w = entry J (k + 1) (by omega) (Fin.snoc w i) := rfl

theorem value_differentiate {n a : ℕ} (i : Fin n) (J : compatibleJets n (a + 1)) :
    value (differentiate i J) = SpatialCalculus.partialD i (value J) := by
  change (fun X => realLift (entry J 1 (by omega) (Fin.snoc Fin.elim0 i)) X) = _
  rw [entry_eq_wordPartial]
  simp [wordPartial, show Fin.snoc (α := fun _ => Fin n) Fin.elim0 i 0 = i by
    change Fin.snoc (α := fun _ => Fin n) Fin.elim0 i (Fin.last 0) = i
    exact Fin.snoc_last _ _]

theorem norm_differentiate_le {n a : ℕ} (i : Fin n) (J : compatibleJets n (a + 1)) :
    ‖differentiate i J‖ ≤ ‖J‖ := by
  change ‖(differentiate i J).val‖ ≤ ‖J.val‖
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg J.val)).mpr
  intro ⟨k,w⟩
  exact norm_le_pi_norm J.val _

def differentiateL {n a : ℕ} (i : Fin n) :
    compatibleJets n (a + 1) →L[ℝ] compatibleJets n a :=
  LinearMap.mkContinuous
    { toFun := differentiate i
      map_add' := by intros; apply Subtype.ext; rfl
      map_smul' := by intros; apply Subtype.ext; rfl }
    1 (fun J => by change ‖differentiate i J‖ ≤ 1 * ‖J‖; rw [one_mul]; exact norm_differentiate_le i J)

def glueData {n a : ℕ} (v : compatible n) (D : Fin n → compatibleJets n a) : Data n (a + 1) :=
  fun ⟨⟨k, hk⟩, w⟩ => match k, hk, w with
    | 0, _, _ => v
    | k + 1, hk, w => entry (D (w (Fin.last k))) k (by omega) (Fin.init w)

def firstGradient {n a : ℕ} (D : Fin n → compatibleJets n a) (X : Coord n) : Coord n →L[ℝ] ℝ :=
  ∑ i : Fin n, value (D i) X • ContinuousLinearMap.proj i

def glue {n a : ℕ} (v : compatible n) (D : Fin n → compatibleJets n a)
    (hd : ∀ X, HasFDerivAt (fun Y => realLift v Y) (firstGradient D X) X) :
    compatibleJets n (a + 1) :=
  ⟨glueData v D, by
    intro ⟨k,hk⟩ w X
    cases k with
    | zero =>
      have hw : w = Fin.elim0 := by ext j; exact Fin.elim0 j
      subst w
      convert hd X using 1
      · rfl
      · unfold gradient firstGradient
        apply Finset.sum_congr rfl
        intro i _
        change realLift (entry (D i) 0 (Nat.zero_le a)
          (Fin.init (Fin.cons (α := fun _ => Fin n) i Fin.elim0))) X •
            ContinuousLinearMap.proj i = _
        have he : Fin.init (Fin.cons (α := fun _ => Fin n) i Fin.elim0) = Fin.elim0 := by
          ext j; exact Fin.elim0 j
        rw [he]
        rfl
    | succ k =>
      have hh := entry_hasFDerivAt (D (w (Fin.last k))) k (by omega) (Fin.init w) X
      convert hh using 1
      · rfl
      · unfold gradient
        apply Finset.sum_congr rfl
        intro i _
        simp [glueData, entry, init_cons]⟩

@[simp] theorem glue_value {n a : ℕ} (v : compatible n) (D : Fin n → compatibleJets n a)
    (hd : ∀ X, HasFDerivAt (fun Y => realLift v Y) (firstGradient D X) X) :
    value (glue v D hd) = (fun X => realLift v X) := rfl

theorem norm_glue_le {n a : ℕ} (v : compatible n) (D : Fin n → compatibleJets n a)
    (hd : ∀ X, HasFDerivAt (fun Y => realLift v Y) (firstGradient D X) X)
    {B : ℝ} (hB : 0 ≤ B) (hv : ‖v‖ ≤ B) (hD : ∀ i, ‖D i‖ ≤ B) :
    ‖glue v D hd‖ ≤ B := by
  change ‖(glue v D hd).val‖ ≤ B
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro ⟨⟨k,hk⟩,w⟩
  cases k with
  | zero => exact hv
  | succ k => exact (norm_le_pi_norm (D (w (Fin.last k))).val _).trans (hD _)

end VelocityDetection.PeriodicSpace.Jets
end

noncomputable section
namespace VelocityDetection.PeriodicSpace.Jets
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
open scoped Topology ContDiff ZeroAtInfty BigOperators

@[simp] theorem value_add {n a : ℕ} (J K : compatibleJets n a) :
    value (J + K) = value J + value K := rfl

@[simp] theorem value_smul {n a : ℕ} (c : ℝ) (J : compatibleJets n a) :
    value (c • J) = c • value J := rfl

def ofValue {n : ℕ} (v : compatible n) : compatibleJets n 0 :=
  ⟨fun _ => v, by intro k; exact Fin.elim0 k⟩

@[simp] theorem value_ofValue {n : ℕ} (v : compatible n) :
    value (ofValue v) = (fun X => realLift v X) := rfl

theorem norm_ofValue_le {n : ℕ} (v : compatible n) : ‖ofValue v‖ ≤ ‖v‖ := by
  change ‖(ofValue v).val‖ ≤ ‖v‖
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro i
  exact le_rfl

theorem norm_entry_le {n a : ℕ} (J : compatibleJets n a) (k : ℕ) (hk : k ≤ a)
    (w : Fin k → Fin n) : ‖entry J k hk w‖ ≤ ‖J‖ := norm_le_pi_norm J.val _

theorem hasFDerivAt_value {n a : ℕ} (J : compatibleJets n (a + 1)) (X : Coord n) :
    HasFDerivAt (value J) (firstGradient (fun i => differentiate i J) X) X := by
  have hh := entry_hasFDerivAt J 0 (by omega) Fin.elim0 X
  convert hh using 1
  · rfl
  · unfold firstGradient gradient
    apply Finset.sum_congr rfl
    intro i _
    have he : Fin.snoc (α := fun _ => Fin n) Fin.elim0 i =
        Fin.cons (α := fun _ => Fin n) i Fin.elim0 := by
      funext j
      fin_cases j
      rfl
    change realLift (entry J 1 (by omega) (Fin.snoc Fin.elim0 i)) X •
      ContinuousLinearMap.proj i = realLift (entry J 1 (by omega) (Fin.cons i Fin.elim0)) X •
      ContinuousLinearMap.proj i
    rw [he]

theorem exists_product {n : ℕ} (a : ℕ) (J K : compatibleJets n a) :
    ∃ L : compatibleJets n a, value L = value J * value K ∧
      ‖L‖ ≤ (2 : ℝ)^a * ‖J‖ * ‖K‖ := by
  induction a with
  | zero =>
    let v := PeriodicSpace.mul (entry J 0 (by omega) Fin.elim0) (entry K 0 (by omega) Fin.elim0)
    refine ⟨ofValue v, rfl, ?_⟩
    calc
      ‖ofValue v‖ ≤ ‖v‖ := norm_ofValue_le v
      _ ≤ ‖entry J 0 (by omega) Fin.elim0‖ * ‖entry K 0 (by omega) Fin.elim0‖ :=
        PeriodicSpace.norm_mul_le _ _
      _ ≤ ‖J‖ * ‖K‖ := mul_le_mul (norm_entry_le J 0 (by omega) Fin.elim0)
        (norm_entry_le K 0 (by omega) Fin.elim0)
          (norm_nonneg (entry K 0 (by omega) Fin.elim0)) (norm_nonneg J)
      _ = _ := by simp only [pow_zero, one_mul]
  | succ a ih =>
    let Jr := restrict (Nat.le_succ a) J
    let Kr := restrict (Nat.le_succ a) K
    choose L hL hLn using (fun i : Fin n => ih (differentiate i J) Kr)
    choose M hM hMn using (fun i : Fin n => ih Jr (differentiate i K))
    let D := fun i : Fin n => L i + M i
    let v := PeriodicSpace.mul (entry J 0 (by omega) Fin.elim0) (entry K 0 (by omega) Fin.elim0)
    have hd (X : Coord n) : HasFDerivAt (fun Y => realLift v Y) (firstGradient D X) X := by
      have hp := (hasFDerivAt_value J X).mul (hasFDerivAt_value K X)
      convert hp using 1 <;> try rfl
      unfold firstGradient
      simp only [Finset.smul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change value (L i + M i) X • ContinuousLinearMap.proj i = _
      rw [value_add, Pi.add_apply, hL i, hM i]
      simp only [Pi.mul_apply, Jr, Kr, restrict_value, smul_smul, ← add_smul]
      congr 1
      ring
    have hnn : 0 ≤ (2 : ℝ)^a := by positivity
    have hJL (i : Fin n) : ‖L i‖ ≤ (2 : ℝ)^a * ‖J‖ * ‖K‖ := by
      apply (hLn i).trans
      exact mul_le_mul (mul_le_mul_of_nonneg_left (norm_differentiate_le i J) hnn)
        (norm_restrict_le (Nat.le_succ a) K) (norm_nonneg Kr)
        (mul_nonneg hnn (norm_nonneg J))
    have hKM (i : Fin n) : ‖M i‖ ≤ (2 : ℝ)^a * ‖J‖ * ‖K‖ := by
      apply (hMn i).trans
      exact mul_le_mul (mul_le_mul_of_nonneg_left (norm_restrict_le (Nat.le_succ a) J) hnn)
        (norm_differentiate_le i K) (norm_nonneg (differentiate i K))
        (mul_nonneg hnn (norm_nonneg J))
    refine ⟨glue v D hd, rfl, norm_glue_le v D hd (by positivity) ?_ ?_⟩
    · calc
        ‖v‖ ≤ ‖entry J 0 (by omega) Fin.elim0‖ * ‖entry K 0 (by omega) Fin.elim0‖ :=
          PeriodicSpace.norm_mul_le _ _
        _ ≤ ‖J‖ * ‖K‖ := mul_le_mul (norm_entry_le J 0 (by omega) Fin.elim0)
          (norm_entry_le K 0 (by omega) Fin.elim0)
          (norm_nonneg (entry K 0 (by omega) Fin.elim0)) (norm_nonneg J)
        _ ≤ (2 : ℝ)^(a + 1) * ‖J‖ * ‖K‖ := by
          have hp : (1 : ℝ) ≤ 2^(a + 1) := one_le_pow₀ (by norm_num)
          nlinarith [mul_nonneg (norm_nonneg J) (norm_nonneg K)]
    · intro i
      calc
        ‖D i‖ ≤ ‖L i‖ + ‖M i‖ := norm_add_le _ _
        _ ≤ (2 : ℝ)^a * ‖J‖ * ‖K‖ + (2 : ℝ)^a * ‖J‖ * ‖K‖ := add_le_add (hJL i) (hKM i)
        _ = _ := by rw [pow_succ]; ring

def product {n a : ℕ} (J K : compatibleJets n a) : compatibleJets n a :=
  (exists_product a J K).choose

@[simp] theorem value_product {n a : ℕ} (J K : compatibleJets n a) :
    value (product J K) = value J * value K := (exists_product a J K).choose_spec.1

theorem norm_product_le {n a : ℕ} (J K : compatibleJets n a) :
    ‖product J K‖ ≤ (2 : ℝ)^a * ‖J‖ * ‖K‖ := (exists_product a J K).choose_spec.2

def productLinear (n a : ℕ) : compatibleJets n a →ₗ[ℝ]
    compatibleJets n a →ₗ[ℝ] compatibleJets n a :=
  { toFun := fun J =>
      { toFun := product J
        map_add' := by
          intro K L; apply value_injective
          simp only [value_product, value_add, mul_add]
        map_smul' := by
          intro c K; apply value_injective
          ext X
          simp [value_product, mul_left_comm] }
    map_add' := by
      intro J K
      apply LinearMap.ext
      intro L
      apply value_injective
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
        value_product, value_add, add_mul]
    map_smul' := by
      intro c J
      apply LinearMap.ext
      intro K
      apply value_injective
      ext X
      simp [value_product, mul_assoc] }

def productL (n a : ℕ) : compatibleJets n a →L[ℝ]
    compatibleJets n a →L[ℝ] compatibleJets n a :=
  (productLinear n a).mkContinuous₂ (2^a) (norm_product_le (n := n) (a := a))

@[simp] theorem productL_apply {n a : ℕ} (J K : compatibleJets n a) :
    productL n a J K = product J K := rfl

theorem norm_productL_le {n a : ℕ} (J : compatibleJets n a) :
    ‖productL n a J‖ ≤ (2 : ℝ)^a * ‖J‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro K
  exact norm_product_le J K

end VelocityDetection.PeriodicSpace.Jets
end

noncomputable section
namespace VelocityDetection.PeriodicSpace.Jets
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
open scoped Topology ContDiff ZeroAtInfty BigOperators
open HeatKernels

theorem convolve_rescale {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k)
    {r : ℝ} (hr : 0 < r) (J : compatibleJets n a) :
    convolve (integrable_rescale hk hr) J = average k (-r) J := by
  have hh := Measure.integral_comp_smul_of_nonneg volume
    (fun X : Coord n => k (r⁻¹ • X) • translate (-X) J) r (hR := hr.le)
  simp only [Coord, Module.finrank_pi, Fintype.card_fin, inv_smul_smul₀ hr.ne',
    ← neg_smul] at hh
  change (∫ X, rescale k r X • translate ((-1 : ℝ) • X) J) = _
  simp only [rescale, neg_one_smul, mul_smul]
  rw [integral_smul]
  exact hh.symm

def heat {a : ℕ} (ν t : ℝ) : compatibleJets 2 a →L[ℝ] compatibleJets 2 a :=
  averageL (integrable_normal 2) (-Real.sqrt (2 * ν * t))

@[simp] theorem heat_zero {a : ℕ} (ν : ℝ) (J : compatibleJets 2 a) : heat ν 0 J = J := by
  simp [heat, averageL_apply, average_zero_scale]

theorem heat_eq_convolve {a : ℕ} {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (J : compatibleJets 2 a) : heat ν t J = convolve (integrable_kernel hν ht) J := by
  have hh := convolve_rescale (integrable_normal 2)
    (Real.sqrt_pos.mpr (show 0 < 2 * ν * t by positivity)) J
  change average (normal 2) (-Real.sqrt (2 * ν * t)) J = average (kernel ν t) (-1) J
  change average (rescale (normal 2) (Real.sqrt (2 * ν * t))) (-1) J = _ at hh
  rw [← kernel_eq_rescale hν ht] at hh
  exact hh.symm

theorem norm_heat_le {a : ℕ} (ν t : ℝ) (J : compatibleJets 2 a) : ‖heat ν t J‖ ≤ ‖J‖ :=
  norm_average_le_of_probability_kernel (integrable_normal 2) (normal_nonneg 2)
    (integral_normal 2) _ J

theorem continuous_heat {a : ℕ} (ν : ℝ) (J : compatibleJets 2 a) :
    Continuous (fun t : ℝ => heat ν t J) := by
  exact (continuous_average (integrable_normal 2) J).comp
    (Real.continuous_sqrt.comp (continuous_const.mul continuous_id)).neg

theorem value_heat {a : ℕ} {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (J : compatibleJets 2 a) (X : Coord 2) :
    value (heat ν t J) X = ∫ Y, kernel ν t Y * value J (X - Y) := by
  rw [heat_eq_convolve hν ht J, value_convolve]

end VelocityDetection.PeriodicSpace.Jets
end

noncomputable section
namespace VelocityDetection.PeriodicSpace.Jets
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
open scoped Topology ContDiff ZeroAtInfty BigOperators
open HeatKernels SpatialCalculus

def heatDerivative {a : ℕ} {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (i : Fin 2) :
    compatibleJets 2 a →L[ℝ] compatibleJets 2 a :=
  convolve (integrable_partialD_kernel hν ht i)

theorem norm_heatDerivative_le {a : ℕ} {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (i : Fin 2) (J : compatibleJets 2 a) :
    ‖heatDerivative hν ht i J‖ ≤
      (absoluteMoment i / Real.sqrt (2 * ν)) * (Real.sqrt t)⁻¹ * ‖J‖ := by
  simpa only [heatDerivative, integral_norm_partialD_kernel_eq hν ht i] using
    norm_convolve_le (integrable_partialD_kernel hν ht i) J

theorem continuous_average_joint {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k) :
    Continuous (fun p : ℝ × compatibleJets n a => average k p.1 p.2) := by
  apply continuous_prod_of_continuous_lipschitzWith' _
    ⟨∫ Y, ‖k Y‖, integral_nonneg (fun _ => norm_nonneg _)⟩
  · intro s
    have hh := AddMonoidHomClass.lipschitz_of_bound (averageL (a := a) hk s)
      (∫ Y, ‖k Y‖) (norm_average_le (a := a) hk s)
    rw [Real.toNNReal_of_nonneg (integral_nonneg (fun Y => norm_nonneg (k Y)))] at hh
    exact hh
  · exact continuous_average hk

theorem heatDerivative_eq_average {a : ℕ} {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (i : Fin 2) (J : compatibleJets 2 a) :
    heatDerivative hν ht i J = -(Real.sqrt (2 * ν * t))⁻¹ •
      average (momentKernel i) (-Real.sqrt (2 * ν * t)) J := by
  have hr : 0 < Real.sqrt (2 * ν * t) := Real.sqrt_pos.mpr (by positivity)
  have hc := convolve_rescale (integrable_momentKernel i) hr J
  change average (SpatialCalculus.partialD i (kernel ν t)) (-1) J = _
  rw [partialD_kernel_rescale hν ht]
  simp only [average, mul_smul]
  rw [integral_smul]
  exact congrArg (fun V => -(Real.sqrt (2 * ν * t))⁻¹ • V) hc

end VelocityDetection.PeriodicSpace.Jets
end

noncomputable section
namespace VelocityDetection.PeriodicSpace.Jets
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
open scoped Topology ContDiff ZeroAtInfty BigOperators
open SpatialCalculus HeatKernels

theorem norm_value_le {n a : ℕ} (J : compatibleJets n a) (X : Coord n) :
    ‖value J X‖ ≤ ‖J‖ :=
  (norm_compatible_apply_le (entry J 0 (by omega) Fin.elim0) X).trans
    (norm_entry_le J 0 (by omega) Fin.elim0)

theorem hasDerivAt_of_values {n a : ℕ} {F dF : ℝ → compatibleJets n a}
    (hdF : Continuous dF)
    (hder : ∀ t X, HasDerivAt (fun s => value (F s) X) (value (dF t) X) t) (t : ℝ) :
    HasDerivAt F (dF t) t := by
  have heq (s : ℝ) : F s = F 0 + ∫ r in (0 : ℝ)..s, dF r := by
    apply value_injective
    ext X
    change value (F s) X = evaluate X (F 0 + ∫ r in (0 : ℝ)..s, dF r)
    rw [map_add, ← (evaluate X).intervalIntegral_comp_comm (hdF.intervalIntegrable 0 s)]
    have hc : Continuous (fun r => value (dF r) X) := (evaluate X).continuous.comp hdF
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r (_ : r ∈ uIcc (0 : ℝ) s) => hder r X) (hc.intervalIntegrable 0 s)
    simp only [evaluate_apply]
    rw [hh]
    ring
  let := secondCountableTopologyEither_of_left ℝ (compatibleJets n a)
  have hm : StronglyMeasurable dF := Continuous.stronglyMeasurable hdF
  have H := (intervalIntegral.integral_hasDerivAt_right (E := compatibleJets n a)
      (hdF.intervalIntegrable 0 t) hm.stronglyMeasurableAtFilter hdF.continuousAt).const_add (F 0)
  exact H.congr_of_eventuallyEq (Eventually.of_forall heq)

def directional {n a : ℕ} (v : Coord n) (J : compatibleJets n (a + 1)) :
    compatibleJets n a := ∑ i : Fin n, v i • differentiate i J

theorem value_directional {n a : ℕ} (v : Coord n) (J : compatibleJets n (a + 1))
    (X : Coord n) : value (directional v J) X = firstGradient (fun i => differentiate i J) X v := by
  change evaluate X (∑ i, v i • differentiate i J) = _
  simp only [map_sum, map_smul, evaluate_apply, firstGradient, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem norm_directional_le {n a : ℕ} (v : Coord n) (J : compatibleJets n (a + 1)) :
    ‖directional v J‖ ≤ (∑ i : Fin n, ‖v i‖) * ‖J‖ := by
  calc
    ‖directional v J‖ ≤ ∑ i : Fin n, ‖v i • differentiate i J‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ‖v i‖ * ‖J‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (norm_differentiate_le i J) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

theorem continuous_directional {n a : ℕ} (J : compatibleJets n (a + 1)) :
    Continuous (fun v : Coord n => directional v J) := by
  apply continuous_finsetSum
  intro i _
  exact (continuous_apply i).smul continuous_const

end VelocityDetection.PeriodicSpace.Jets
end

end OAI
