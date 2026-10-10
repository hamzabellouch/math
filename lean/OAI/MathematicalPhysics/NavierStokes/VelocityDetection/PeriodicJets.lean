import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailSpaceIntegrableCompatible
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicSpace

namespace OAI

noncomputable section
namespace VelocityDetection.PeriodicSpace.Jets
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
open scoped Topology ContDiff ZeroAtInfty BigOperators

abbrev Index (n a : ℕ) := Σ k : Fin (a + 1), Fin k.val → Fin n

abbrev Data (n a : ℕ) := Index n a → compatible n

def gradient {n a : ℕ} (J : Data n a) (k : Fin a)
    (w : Fin k.val → Fin n) (X : Coord n) : Coord n →L[ℝ] ℝ :=
  ∑ i : Fin n, realLift (J ⟨k.succ, Fin.cons i w⟩) X • ContinuousLinearMap.proj i

@[simp] theorem gradient_zero {n a : ℕ} (k : Fin a)
    (w : Fin k.val → Fin n) (X : Coord n) : gradient (0 : Data n a) k w X = 0 := by
  simp [gradient]

@[simp] theorem gradient_add {n a : ℕ} (J K : Data n a) (k : Fin a)
    (w : Fin k.val → Fin n) (X : Coord n) :
    gradient (J + K) k w X = gradient J k w X + gradient K k w X := by
  simp [gradient, add_smul, Finset.sum_add_distrib]

@[simp] theorem gradient_smul {n a : ℕ} (c : ℝ) (J : Data n a) (k : Fin a)
    (w : Fin k.val → Fin n) (X : Coord n) :
    gradient (c • J) k w X = c • gradient J k w X := by
  simp [gradient, Finset.smul_sum, smul_smul]

def compatibleJets (n a : ℕ) : Submodule ℝ (Data n a) where
  carrier := {J | ∀ (k : Fin a) (w : Fin k.val → Fin n) (X : Coord n),
    HasFDerivAt (fun Y => realLift (J ⟨k.castSucc, w⟩) Y) (gradient J k w X) X}
  zero_mem' := by
    intro k w X
    simpa using hasFDerivAt_const (c := (0 : ℝ)) X
  add_mem' := by
    intro J K hJ hK k w X
    rw [gradient_add]
    convert (hJ k w X).add (hK k w X) using 1; rfl
  smul_mem' := by
    intro c J hJ k w X
    rw [gradient_smul]
    convert (hJ k w X).const_smul c using 1; rfl

theorem gradient_sub {n a : ℕ} (J K : Data n a) (k : Fin a)
    (w : Fin k.val → Fin n) (X : Coord n) :
    gradient (J - K) k w X = gradient J k w X - gradient K k w X := by
  simp only [gradient, Pi.sub_apply, realLift_sub, BoundedContinuousFunction.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact sub_smul (realLift (J ⟨k.succ, Fin.cons i w⟩) X)
    (realLift (K ⟨k.succ, Fin.cons i w⟩) X)
    (ContinuousLinearMap.proj i : Coord n →L[ℝ] ℝ)

theorem norm_gradient_le {n a : ℕ} (J : Data n a) (k : Fin a)
    (w : Fin k.val → Fin n) (X : Coord n) :
    ‖gradient J k w X‖ ≤ (n : ℝ) * ‖J‖ := by
  apply (norm_sum_le _ _).trans
  calc
    ∑ i : Fin n, ‖realLift (J ⟨k.succ, Fin.cons i w⟩) X •
        (ContinuousLinearMap.proj i : Coord n →L[ℝ] ℝ)‖ ≤ ∑ _i : Fin n, ‖J‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      have he : ‖realLift (J ⟨k.succ, Fin.cons i w⟩) X‖ ≤ ‖J‖ :=
        (BoundedContinuousFunction.norm_coe_le_norm (realLift (J ⟨k.succ, Fin.cons i w⟩)) X).trans
          (by simpa using (norm_le_pi_norm J ⟨k.succ, Fin.cons i w⟩))
      have hp : ‖(ContinuousLinearMap.proj i : Coord n →L[ℝ] ℝ)‖ ≤ 1 := by
        apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro v
        simpa using norm_le_pi_norm v i
      exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans (by simpa using he)
    _ = (n : ℝ) * ‖J‖ := by simp

theorem gradient_tendstoUniformly {n a : ℕ} {F : ℕ → Data n a} {f : Data n a}
    (hF : Tendsto F atTop (𝓝 f)) (k : Fin a) (w : Fin k.val → Fin n) :
    TendstoUniformly (fun j X => gradient (F j) k w X) (gradient f k w) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hh := (Metric.tendsto_nhds.mp hF) (ε / (n + 1)) (div_pos hε hn)
  filter_upwards [hh] with j hj X
  rw [dist_comm, dist_eq_norm, ← gradient_sub]
  calc
    ‖gradient (F j - f) k w X‖ ≤ (n : ℝ) * ‖F j - f‖ := norm_gradient_le _ _ _ _
    _ ≤ ((n : ℝ) + 1) * ‖F j - f‖ := by gcongr; linarith
    _ < ((n : ℝ) + 1) * (ε / (n + 1)) := by
      apply mul_lt_mul_of_pos_left _ hn
      rw [@dist_eq_norm (Data n a) _ (F j) f] at hj
      exact hj
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hn)

theorem component_tendstoUniformly {n a : ℕ} {F : ℕ → Data n a} {f : Data n a}
    (hF : Tendsto F atTop (𝓝 f)) (i : Index n a) :
    TendstoUniformly (fun j X => realLift (F j i) X) (fun X => realLift (f i) X) atTop := by
  apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
  exact (realLiftLI.continuous.tendsto (f i)).comp
    ((continuous_apply i).tendsto f |>.comp hF)

theorem compatibleJets_closed (n a : ℕ) : IsClosed (compatibleJets n a : Set (Data n a)) := by
  apply IsSeqClosed.isClosed
  intro F f hF hlim k w X
  exact hasFDerivAt_of_tendstoUniformly (gradient_tendstoUniformly hlim k w)
    (fun j Y => hF j k w Y)
    (fun Y => (component_tendstoUniformly hlim ⟨k.castSucc, w⟩).tendsto_at Y) X

instance (n a : ℕ) : CompleteSpace (compatibleJets n a) :=
  (compatibleJets_closed n a).isComplete.completeSpace_coe

def entry {n a : ℕ} (J : compatibleJets n a) (k : ℕ) (hk : k ≤ a)
    (w : Fin k → Fin n) : compatible n := J.val ⟨⟨k, by omega⟩, w⟩

def value {n a : ℕ} (J : compatibleJets n a) : Coord n → ℝ :=
  fun X => realLift (entry J 0 (Nat.zero_le a) Fin.elim0) X

def wordPartial {n : ℕ} : {k : ℕ} → (Fin k → Fin n) → (Coord n → ℝ) → Coord n → ℝ
  | 0, _, f => f
  | _k + 1, w, f => SpatialCalculus.partialD (w 0) (wordPartial (Fin.tail w) f)

@[simp] theorem wordPartial_nil {n : ℕ} (w : Fin 0 → Fin n) (f : Coord n → ℝ) :
    wordPartial w f = f := rfl

@[simp] theorem wordPartial_cons {n k : ℕ} (i : Fin n) (w : Fin k → Fin n)
    (f : Coord n → ℝ) : wordPartial (Fin.cons i w) f =
      SpatialCalculus.partialD i (wordPartial w f) := by simp [wordPartial]

theorem entry_hasFDerivAt {n a : ℕ} (J : compatibleJets n a) (k : ℕ) (hk : k < a)
    (w : Fin k → Fin n) (X : Coord n) :
    HasFDerivAt (fun Y => realLift (entry J k hk.le w) Y)
      (gradient J.val ⟨k, hk⟩ w X) X := J.property ⟨k, hk⟩ w X

theorem entry_partialD {n a : ℕ} (J : compatibleJets n a) (k : ℕ) (hk : k < a)
    (w : Fin k → Fin n) (i : Fin n) (X : Coord n) :
    SpatialCalculus.partialD i (fun Y => realLift (entry J k hk.le w) Y) X =
      realLift (entry J (k + 1) (by omega) (Fin.cons i w)) X := by
  rw [SpatialCalculus.partialD_eq_fderiv i
    (fun Y => (entry_hasFDerivAt J k hk w Y).differentiableAt),
    (entry_hasFDerivAt J k hk w X).fderiv]
  classical
  simp [gradient, entry, ContinuousLinearMap.proj_apply, Pi.single_apply]

theorem entry_eq_wordPartial {n a : ℕ} (J : compatibleJets n a) (k : ℕ)
    (hk : k ≤ a) (w : Fin k → Fin n) :
    (fun X => realLift (entry J k hk w) X) = wordPartial w (value J) := by
  induction k with
  | zero =>
    have hw : w = Fin.elim0 := by ext x; exact Fin.elim0 x
    subst w
    rfl
  | succ k ih =>
    have hka : k < a := by omega
    rw [← Fin.cons_self_tail w, wordPartial_cons]
    rw [← ih hka.le (Fin.tail w)]
    funext X
    exact (entry_partialD J k hka (Fin.tail w) (w 0) X).symm

theorem contDiff_entry {n a : ℕ} (J : compatibleJets n a) (r k : ℕ)
    (hkr : k + r ≤ a) (w : Fin k → Fin n) :
    ContDiff ℝ r (fun X => realLift (entry J k (by omega) w) X) := by
  induction r generalizing k with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact (realLift (entry J k (by omega) w)).continuous
  | succ r ih =>
    have hka : k < a := by omega
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_hasFDerivAt]
    refine ⟨gradient J.val ⟨k, hka⟩ w, ?_, entry_hasFDerivAt J k hka w⟩
    apply ContDiff.sum
    intro i _
    have hh := ih (k + 1) (by omega) (Fin.cons i w)
    exact hh.smul contDiff_const

theorem contDiff_value {n a : ℕ} (J : compatibleJets n a) : ContDiff ℝ a (value J) :=
  contDiff_entry J a 0 (by omega) Fin.elim0

theorem compatible_ext {n : ℕ} {f g : compatible n}
    (he : ∀ X, realLift f X = realLift g X) : f = g := ext_fun he

theorem value_injective {n a : ℕ} : Function.Injective (@value n a) := by
  intro J K hjk
  apply Subtype.ext
  funext ⟨⟨k, hk⟩, w⟩
  apply compatible_ext
  intro X
  change realLift (entry J k (by omega) w) X = realLift (entry K k (by omega) w) X
  rw [congrFun (entry_eq_wordPartial J k (by omega) w) X,
    congrFun (entry_eq_wordPartial K k (by omega) w) X, hjk]

instance (n a : ℕ) : NormedAddCommGroup (compatibleJets n a) := by
  exact @Submodule.normedAddCommGroup ℝ (Data n a) _ _ _ (compatibleJets n a)

instance (n a : ℕ) : NormedSpace ℝ (compatibleJets n a) := by
  exact Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) (E := Data n a) (compatibleJets n a)

def translate {n a : ℕ} (Y : Coord n) (J : compatibleJets n a) : compatibleJets n a :=
  ⟨fun i => PeriodicSpace.translate Y (J.val i), by
    intro k w X
    have hh := (J.property k w (X + Y)).comp X ((hasFDerivAt_id X).add_const Y)
    simp only [ContinuousLinearMap.comp_id] at hh
    convert hh using 1 <;> rfl⟩

@[simp] theorem translate_entry {n a : ℕ} (Y : Coord n) (J : compatibleJets n a)
    (k : ℕ) (hk : k ≤ a) (w : Fin k → Fin n) :
    entry (translate Y J) k hk w = PeriodicSpace.translate Y (entry J k hk w) := rfl

@[simp] theorem translate_value {n a : ℕ} (Y : Coord n) (J : compatibleJets n a)
    (X : Coord n) : value (translate Y J) X = value J (X + Y) := rfl

@[simp] theorem translate_zero {n a : ℕ} (J : compatibleJets n a) : translate 0 J = J := by
  apply value_injective
  funext X
  simp

@[simp] theorem translate_add {n a : ℕ} (Y Z : Coord n) (J : compatibleJets n a) :
    translate (Y + Z) J = translate Y (translate Z J) := by
  apply value_injective
  funext X
  simp [add_assoc]

@[simp] theorem norm_translate {n a : ℕ} (Y : Coord n) (J : compatibleJets n a) :
    ‖translate Y J‖ = ‖J‖ := by
  change ‖fun i => PeriodicSpace.translate Y (J.val i)‖ = ‖J.val‖
  simp only [Pi.norm_def, nnnorm, PeriodicSpace.norm_translate]

def translateLI {n a : ℕ} (Y : Coord n) : compatibleJets n a →ₗᵢ[ℝ] compatibleJets n a where
  toFun := translate Y
  map_add' := by
    intro J K
    apply value_injective
    rfl
  map_smul' := by
    intro c J
    apply value_injective
    rfl
  norm_map' := norm_translate Y

theorem continuous_translate {n a : ℕ} (J : compatibleJets n a) :
    Continuous (fun Y : Coord n => translate Y J) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact PeriodicSpace.continuous_translate (J.val i)

end VelocityDetection.PeriodicSpace.Jets
end

noncomputable section
namespace VelocityDetection.PeriodicSpace.Jets
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
open scoped Topology ContDiff ZeroAtInfty BigOperators

def evaluate {n a : ℕ} (X : Coord n) : compatibleJets n a →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun J => value J X
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    1 (by
      intro J
      have hb := BoundedContinuousFunction.norm_coe_le_norm
        (realLift (entry J 0 (Nat.zero_le a) Fin.elim0)) X
      change ‖value J X‖ ≤ 1 * ‖J.val‖
      rw [one_mul]
      convert hb.trans (by simpa [entry] using (norm_le_pi_norm J.val ⟨⟨0, Nat.zero_lt_succ a⟩, Fin.elim0⟩)) using 1; rfl)

@[simp] theorem evaluate_apply {n a : ℕ} (X : Coord n) (J : compatibleJets n a) :
    evaluate X J = value J X := rfl

theorem integrable_average {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k)
    (s : ℝ) (J : compatibleJets n a) :
    Integrable (fun Y => k Y • translate (s • Y) J) := by
  let : SecondCountableTopologyEither (Coord n) (compatibleJets n a) :=
    secondCountableTopologyEither_of_left _ _
  have hs : Continuous (fun Y : Coord n => s • Y) := continuous_id.const_smul s
  have ht : Continuous (fun Y : Coord n => translate (s • Y) J) :=
    (continuous_translate J).comp hs
  have hm : AEStronglyMeasurable (fun Y : Coord n => translate (s • Y) J) volume :=
    ht.aestronglyMeasurable
  apply (hk.norm.mul_const ‖J‖).mono'
  · exact hk.aestronglyMeasurable.smul hm
  · filter_upwards [] with Y
    simp only [norm_smul, norm_translate, le_refl]

def average {n a : ℕ} (k : Coord n → ℝ) (s : ℝ) (J : compatibleJets n a) :
    compatibleJets n a := ∫ Y, k Y • translate (s • Y) J

theorem norm_average_le {n a : ℕ} {k : Coord n → ℝ} (_hk : Integrable k)
    (s : ℝ) (J : compatibleJets n a) :
    ‖average k s J‖ ≤ (∫ Y, ‖k Y‖) * ‖J‖ := by
  calc
    ‖average k s J‖ ≤ ∫ Y, ‖k Y • translate (s • Y) J‖ := norm_integral_le_integral_norm _
    _ = (∫ Y, ‖k Y‖) * ‖J‖ := by
      simp only [norm_smul, norm_translate]
      exact integral_mul_const ‖J‖ (fun Y => ‖k Y‖)

theorem value_average {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k)
    (s : ℝ) (J : compatibleJets n a) (X : Coord n) :
    value (average k s J) X = ∫ Y, k Y * value J (X + s • Y) := by
  have hh := (evaluate (a := a) X).integral_comp_comm (integrable_average hk s J)
  simpa only [evaluate_apply, map_smul, translate_value, smul_eq_mul, average] using hh.symm

def averageL {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k) (s : ℝ) :
    compatibleJets n a →L[ℝ] compatibleJets n a :=
  LinearMap.mkContinuous
    { toFun := average k s
      map_add' := by
        intro J K
        simp only [average, show ∀ Y, translate (s • Y) (J + K) =
          translate (s • Y) J + translate (s • Y) K from fun Y => (translateLI (s • Y)).map_add J K,
          smul_add]
        exact integral_add (integrable_average hk s J) (integrable_average hk s K)
      map_smul' := by
        intro c J
        simp only [average, show ∀ Y, translate (s • Y) (c • J) =
          c • translate (s • Y) J from fun Y => (translateLI (s • Y)).map_smul c J,
          smul_comm (k _) c]
        exact integral_smul c _ }
    (∫ Y, ‖k Y‖) (norm_average_le hk s)

@[simp] theorem averageL_apply {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k)
    (s : ℝ) (J : compatibleJets n a) : averageL hk s J = average k s J := rfl

def convolve {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k) :
    compatibleJets n a →L[ℝ] compatibleJets n a := averageL hk (-1)

theorem value_convolve {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k)
    (J : compatibleJets n a) (X : Coord n) :
    value (convolve hk J) X = ∫ Y, k Y * value J (X - Y) := by
  simpa [convolve, neg_one_smul, sub_eq_add_neg] using value_average hk (-1) J X

theorem norm_convolve_le {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k)
    (J : compatibleJets n a) : ‖convolve hk J‖ ≤ (∫ Y, ‖k Y‖) * ‖J‖ :=
  norm_average_le hk (-1) J

theorem continuous_average {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k)
    (J : compatibleJets n a) : Continuous (fun s : ℝ => average k s J) := by
  apply continuous_of_dominated (bound := fun Y => ‖k Y‖ * ‖J‖)
  · intro s
    exact (integrable_average hk s J).aestronglyMeasurable
  · intro s
    filter_upwards [] with Y
    simp only [norm_smul, norm_translate, le_refl]
  · exact hk.norm.mul_const ‖J‖
  · filter_upwards [] with Y
    have hs : Continuous (fun s : ℝ => s • Y) := continuous_id.smul continuous_const
    have ht : Continuous (fun s : ℝ => translate (s • Y) J) :=
      (continuous_translate J).comp hs
    exact ht.const_smul (k Y)

@[simp] theorem average_zero_scale {n a : ℕ} (k : Coord n → ℝ)
    (J : compatibleJets n a) : average k 0 J = (∫ Y, k Y) • J := by
  simp only [average, zero_smul, translate_zero, integral_smul_const]

theorem average_tendsto_identity {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k)
    (hm : ∫ Y, k Y = 1) (J : compatibleJets n a) :
    Tendsto (fun s : ℝ => average k s J) (𝓝 0) (𝓝 J) := by
  have hh := (continuous_average hk J).tendsto 0
  simpa only [average_zero_scale, hm, one_smul] using hh

theorem norm_average_le_of_probability_kernel {n a : ℕ} {k : Coord n → ℝ}
    (hk : Integrable k) (hn : ∀ Y, 0 ≤ k Y) (hm : ∫ Y, k Y = 1)
    (s : ℝ) (J : compatibleJets n a) : ‖average k s J‖ ≤ ‖J‖ := by
  have he : (∫ Y, ‖k Y‖) = 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _)] using hm
  simpa only [he, one_mul] using norm_average_le hk s J

end VelocityDetection.PeriodicSpace.Jets
end

noncomputable section
namespace VelocityDetection.PeriodicSpace
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
open scoped Topology ContDiff ZeroAtInfty BigOperators

theorem norm_compatible_apply_le {n : ℕ} (v : compatible n) (X : Coord n) :
    ‖realLift v X‖ ≤ ‖v‖ := ContinuousMap.norm_coe_le_norm v (cover X)

def mul {n : ℕ} (v w : compatible n) : compatible n := v * w

@[simp] theorem mul_apply {n : ℕ} (v w : compatible n) (X : Coord n) :
    realLift (mul v w) X = realLift v X * realLift w X := rfl

theorem norm_mul_le {n : ℕ} (v w : compatible n) : ‖mul v w‖ ≤ ‖v‖ * ‖w‖ :=
  _root_.norm_mul_le v w

end VelocityDetection.PeriodicSpace
end

noncomputable section
namespace VelocityDetection.PeriodicSpace.Jets
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
open scoped Topology ContDiff ZeroAtInfty BigOperators

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
    1 (fun J => by change ‖restrict hab J‖ ≤ 1 * ‖J‖; rw [one_mul]; exact norm_restrict_le hab J)

end VelocityDetection.PeriodicSpace.Jets
end

end OAI
