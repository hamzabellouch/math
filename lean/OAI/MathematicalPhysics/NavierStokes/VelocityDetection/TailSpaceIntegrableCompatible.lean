import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailSpaceContinuousAverageJoint

namespace OAI

noncomputable section
namespace VelocityDetection.TailSpace
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology

theorem integrable_compatible {n : ℕ} (v : compatible n) :
    Integrable (fun X => v.val.1 X) := (L1.integrable_coeFn v.val.2).congr v.property

theorem norm_compatible_apply_le {n : ℕ} (v : compatible n) (X : Coord n) :
    ‖v.val.1 X‖ ≤ ‖v‖ :=
  (BoundedContinuousFunction.norm_coe_le_norm v.val.1.toBCF X).trans (norm_fst_le v.val)

theorem integrable_mul {n : ℕ} (v w : compatible n) :
    Integrable (fun X => v.val.1 X * w.val.1 X) :=
  (integrable_compatible w).bdd_mul v.val.1.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_compatible_apply_le v))

def mul {n : ℕ} (v w : compatible n) : compatible n :=
  ⟨(v.val.1 * w.val.1,
    (memLp_one_iff_integrable.mpr (integrable_mul v w)).toLp (fun X => v.val.1 X * w.val.1 X)),
    (memLp_one_iff_integrable.mpr (integrable_mul v w)).coeFn_toLp⟩

@[simp] theorem mul_apply {n : ℕ} (v w : compatible n) (X : Coord n) :
    (mul v w).val.1 X = v.val.1 X * w.val.1 X := rfl

theorem integral_norm_eq {n : ℕ} (v : compatible n) :
    (∫ X, ‖v.val.1 X‖) = ‖v.val.2‖ := by
  rw [L1.norm_eq_integral_norm]
  have hv : (fun X => v.val.2 X) =ᵐ[volume] (fun X => v.val.1 X) := v.property
  exact integral_congr_ae (hv.symm.fun_comp norm)

theorem norm_mul_le {n : ℕ} (v w : compatible n) : ‖mul v w‖ ≤ ‖v‖ * ‖w‖ := by
  change max ‖(mul v w).val.1‖ ‖(mul v w).val.2‖ ≤ _
  apply max_le
  · change ‖(mul v w).val.1.toBCF‖ ≤ _
    apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg v) (norm_nonneg w))).mpr
    intro X
    change ‖v.val.1 X * w.val.1 X‖ ≤ ‖v‖ * ‖w‖
    rw [norm_mul]
    exact mul_le_mul (norm_compatible_apply_le v X) (norm_compatible_apply_le w X)
      (norm_nonneg _) (norm_nonneg v)
  · rw [← integral_norm_eq]
    calc
      (∫ X, ‖(mul v w).val.1 X‖) ≤ ∫ X, ‖v‖ * ‖w.val.1 X‖ := by
        apply integral_mono (integrable_mul v w).norm ((integrable_compatible w).norm.const_mul _)
        intro X
        change ‖v.val.1 X * w.val.1 X‖ ≤ ‖v‖ * ‖w.val.1 X‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_compatible_apply_le v X) (norm_nonneg _)
      _ = ‖v‖ * ‖w.val.2‖ := by rw [integral_const_mul, integral_norm_eq]
      _ ≤ ‖v‖ * ‖w‖ := mul_le_mul_of_nonneg_left (norm_snd_le w.val) (norm_nonneg v)

end VelocityDetection.TailSpace
end

noncomputable section
namespace VelocityDetection.TailSpace.Jets
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology

def restrict {n a b : ℕ} (hab : a ≤ b) (J : compatibleJets n b) : compatibleJets n a :=
  ⟨fun ⟨k, w⟩ => entry J k.val (by omega) w, by
    intro k w X
    exact J.property ⟨k.val, by omega⟩ w X⟩

@[simp] theorem restrict_entry {n a b : ℕ} (hab : a ≤ b) (J : compatibleJets n b)
    (k : ℕ) (hk : k ≤ a) (w : Fin k → Fin n) :
    entry (restrict hab J) k hk w = entry J k (hk.trans hab) w := rfl

@[simp] theorem restrict_value {n a b : ℕ} (hab : a ≤ b) (J : compatibleJets n b) :
    value (restrict hab J) = value J := rfl

theorem norm_restrict_le {n a b : ℕ} (hab : a ≤ b) (J : compatibleJets n b) :
    ‖restrict hab J‖ ≤ ‖J‖ := by
  change ‖(restrict hab J).val‖ ≤ ‖J.val‖
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg J.val)).mpr
  intro ⟨k,w⟩
  exact norm_le_pi_norm J.val _

def restrictL {n a b : ℕ} (hab : a ≤ b) : compatibleJets n b →L[ℝ] compatibleJets n a :=
  LinearMap.mkContinuous
    { toFun := restrict hab
      map_add' := by intros; apply value_injective; rfl
      map_smul' := by intros; apply value_injective; rfl }
    1 (fun J => by simpa using norm_restrict_le hab J)

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
  change (fun X => (entry J 1 (by omega) (Fin.snoc Fin.elim0 i)).val.1 X) = _
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
    1 (fun J => by simpa using norm_differentiate_le i J)

def glueData {n a : ℕ} (v : compatible n) (D : Fin n → compatibleJets n a) : Data n (a + 1) :=
  fun ⟨⟨k, hk⟩, w⟩ => match k, hk, w with
    | 0, _, _ => v
    | k + 1, hk, w => entry (D (w (Fin.last k))) k (by omega) (Fin.init w)

def firstGradient {n a : ℕ} (D : Fin n → compatibleJets n a) (X : Coord n) : Coord n →L[ℝ] ℝ :=
  ∑ i : Fin n, value (D i) X • ContinuousLinearMap.proj i

def glue {n a : ℕ} (v : compatible n) (D : Fin n → compatibleJets n a)
    (hd : ∀ X, HasFDerivAt (fun Y => v.val.1 Y) (firstGradient D X) X) :
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
        change (entry (D i) 0 (Nat.zero_le a)
          (Fin.init (Fin.cons (α := fun _ => Fin n) i Fin.elim0))).val.1 X •
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
    (hd : ∀ X, HasFDerivAt (fun Y => v.val.1 Y) (firstGradient D X) X) :
    value (glue v D hd) = (fun X => v.val.1 X) := rfl

theorem norm_glue_le {n a : ℕ} (v : compatible n) (D : Fin n → compatibleJets n a)
    (hd : ∀ X, HasFDerivAt (fun Y => v.val.1 Y) (firstGradient D X) X)
    {B : ℝ} (hB : 0 ≤ B) (hv : ‖v‖ ≤ B) (hD : ∀ i, ‖D i‖ ≤ B) :
    ‖glue v D hd‖ ≤ B := by
  change ‖(glue v D hd).val‖ ≤ B
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro ⟨⟨k,hk⟩,w⟩
  cases k with
  | zero => exact hv
  | succ k => exact (norm_le_pi_norm (D (w (Fin.last k))).val _).trans (hD _)

end VelocityDetection.TailSpace.Jets
end

noncomputable section
namespace VelocityDetection.TailSpace.Jets
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology

@[simp] theorem value_add {n a : ℕ} (J K : compatibleJets n a) :
    value (J + K) = value J + value K := rfl

@[simp] theorem value_smul {n a : ℕ} (c : ℝ) (J : compatibleJets n a) :
    value (c • J) = c • value J := rfl

def ofValue {n : ℕ} (v : compatible n) : compatibleJets n 0 :=
  ⟨fun _ => v, by intro k; exact Fin.elim0 k⟩

@[simp] theorem value_ofValue {n : ℕ} (v : compatible n) :
    value (ofValue v) = (fun X => v.val.1 X) := rfl

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
    change (entry J 1 (by omega) (Fin.snoc Fin.elim0 i)).val.1 X •
      ContinuousLinearMap.proj i = (entry J 1 (by omega) (Fin.cons i Fin.elim0)).val.1 X •
      ContinuousLinearMap.proj i
    rw [he]

theorem exists_product {n : ℕ} (a : ℕ) (J K : compatibleJets n a) :
    ∃ L : compatibleJets n a, value L = value J * value K ∧
      ‖L‖ ≤ (2 : ℝ)^a * ‖J‖ * ‖K‖ := by
  induction a with
  | zero =>
    let v := TailSpace.mul (entry J 0 (by omega) Fin.elim0) (entry K 0 (by omega) Fin.elim0)
    refine ⟨ofValue v, rfl, ?_⟩
    calc
      ‖ofValue v‖ ≤ ‖v‖ := norm_ofValue_le v
      _ ≤ ‖entry J 0 (by omega) Fin.elim0‖ * ‖entry K 0 (by omega) Fin.elim0‖ :=
        TailSpace.norm_mul_le _ _
      _ ≤ ‖J‖ * ‖K‖ := mul_le_mul (norm_entry_le J 0 (by omega) Fin.elim0)
        (norm_entry_le K 0 (by omega) Fin.elim0)
          (norm_nonneg (entry K 0 (by omega) Fin.elim0)) (norm_nonneg J)
      _ = _ := by simp
  | succ a ih =>
    let Jr := restrict (Nat.le_succ a) J
    let Kr := restrict (Nat.le_succ a) K
    choose L hL hLn using (fun i : Fin n => ih (differentiate i J) Kr)
    choose M hM hMn using (fun i : Fin n => ih Jr (differentiate i K))
    let D := fun i : Fin n => L i + M i
    let v := TailSpace.mul (entry J 0 (by omega) Fin.elim0) (entry K 0 (by omega) Fin.elim0)
    have hd (X : Coord n) : HasFDerivAt (fun Y => v.val.1 Y) (firstGradient D X) X := by
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
          TailSpace.norm_mul_le _ _
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

end VelocityDetection.TailSpace.Jets
end

noncomputable section
namespace VelocityDetection.TailSpace.Jets
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open HeatKernels SpatialCalculus

def heatGradient {a : ℕ} (ν t : ℝ) (i : Fin 2) :
    compatibleJets 2 a →L[ℝ] compatibleJets 2 a :=
  -(Real.sqrt (2 * ν * t))⁻¹ •
    averageL (a := a) (integrable_momentKernel i) (-Real.sqrt (2 * ν * t))

theorem heatGradient_eq {a : ℕ} {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (i : Fin 2) (J : compatibleJets 2 a) :
    heatGradient ν t i J = heatDerivative hν ht i J :=
  (heatDerivative_eq_average hν ht i J).symm

theorem norm_heatGradient_le {a : ℕ} {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (i : Fin 2) (J : compatibleJets 2 a) :
    ‖heatGradient ν t i J‖ ≤
      (absoluteMoment i / Real.sqrt (2 * ν)) * (Real.sqrt t)⁻¹ * ‖J‖ := by
  rw [heatGradient_eq hν ht]
  exact norm_heatDerivative_le hν ht i J

theorem continuous_heat_joint {a : ℕ} (ν : ℝ) :
    Continuous (fun p : ℝ × compatibleJets 2 a => heat ν p.1 p.2) := by
  exact (continuous_average_joint (integrable_normal 2)).comp
    (((Real.continuous_sqrt.comp (continuous_const.mul continuous_fst)).neg).prodMk continuous_snd)

theorem continuousOn_heatGradient_joint {a : ℕ} {ν : ℝ} (hν : 0 < ν) (i : Fin 2) :
    ContinuousOn (fun p : ℝ × compatibleJets 2 a => heatGradient ν p.1 i p.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  have hs : Continuous (fun p : ℝ × compatibleJets 2 a => Real.sqrt (2 * ν * p.1)) :=
    Real.continuous_sqrt.comp (continuous_const.mul continuous_fst)
  have hi : ContinuousOn (fun p : ℝ × compatibleJets 2 a => (Real.sqrt (2 * ν * p.1))⁻¹)
      (Ioi (0 : ℝ) ×ˢ univ) := hs.continuousOn.inv₀ (fun p hp =>
        (Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) hν) hp.1)).ne')
  have hc := (continuous_average_joint (a := a) (integrable_momentKernel i)).comp
    (hs.neg.prodMk continuous_snd)
  exact hi.neg.smul hc.continuousOn

end VelocityDetection.TailSpace.Jets
end

end OAI
