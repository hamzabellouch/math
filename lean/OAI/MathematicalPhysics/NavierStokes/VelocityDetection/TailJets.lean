import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SpatialCalculus
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailSpaceToC0

namespace OAI

noncomputable section
namespace VelocityDetection.TailSpace.Jets
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators

abbrev Index (n a : ℕ) := Σ k : Fin (a + 1), Fin k.val → Fin n

abbrev Data (n a : ℕ) := Index n a → compatible n

def gradient {n a : ℕ} (J : Data n a) (k : Fin a)
    (w : Fin k.val → Fin n) (X : Coord n) : Coord n →L[ℝ] ℝ :=
  ∑ i : Fin n, (J ⟨k.succ, Fin.cons i w⟩).val.1 X • ContinuousLinearMap.proj i

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
    HasFDerivAt (fun Y => (J ⟨k.castSucc, w⟩).val.1 Y) (gradient J k w X) X}
  zero_mem' := by
    intro k w X
    simpa using hasFDerivAt_const (c := (0 : ℝ)) X
  add_mem' := by
    intro J K hJ hK k w X
    rw [gradient_add]
    convert (hJ k w X).add (hK k w X) using 1
  smul_mem' := by
    intro c J hJ k w X
    rw [gradient_smul]
    convert (hJ k w X).const_smul c using 1

theorem gradient_sub {n a : ℕ} (J K : Data n a) (k : Fin a)
    (w : Fin k.val → Fin n) (X : Coord n) :
    gradient (J - K) k w X = gradient J k w X - gradient K k w X := by
  simp only [gradient, Pi.sub_apply, Submodule.coe_sub, Prod.fst_sub,
    ZeroAtInftyContinuousMap.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact sub_smul ((J ⟨k.succ, Fin.cons i w⟩).val.1 X)
    ((K ⟨k.succ, Fin.cons i w⟩).val.1 X)
    (ContinuousLinearMap.proj i : Coord n →L[ℝ] ℝ)

theorem norm_gradient_le {n a : ℕ} (J : Data n a) (k : Fin a)
    (w : Fin k.val → Fin n) (X : Coord n) :
    ‖gradient J k w X‖ ≤ (n : ℝ) * ‖J‖ := by
  apply (norm_sum_le _ _).trans
  calc
    ∑ i : Fin n, ‖(J ⟨k.succ, Fin.cons i w⟩).val.1 X •
        (ContinuousLinearMap.proj i : Coord n →L[ℝ] ℝ)‖ ≤ ∑ _i : Fin n, ‖J‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      have he : ‖(J ⟨k.succ, Fin.cons i w⟩).val.1 X‖ ≤ ‖J‖ :=
        (BoundedContinuousFunction.norm_coe_le_norm (J ⟨k.succ, Fin.cons i w⟩).val.1.toBCF X).trans
          ((norm_fst_le (J ⟨k.succ, Fin.cons i w⟩).val).trans (norm_le_pi_norm J _))
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
    TendstoUniformly (fun j X => (F j i).val.1 X) (fun X => (f i).val.1 X) atTop := by
  apply ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly.mp
  exact ((continuous_fst.comp continuous_subtype_val).tendsto (f i)).comp
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
  fun X => (entry J 0 (Nat.zero_le a) Fin.elim0).val.1 X

def wordPartial {n : ℕ} : {k : ℕ} → (Fin k → Fin n) → (Coord n → ℝ) → Coord n → ℝ
  | 0, _, f => f
  | _ + 1, w, f => SpatialCalculus.partialD (w 0) (wordPartial (Fin.tail w) f)

@[simp] theorem wordPartial_nil {n : ℕ} (w : Fin 0 → Fin n) (f : Coord n → ℝ) :
    wordPartial w f = f := rfl

@[simp] theorem wordPartial_cons {n k : ℕ} (i : Fin n) (w : Fin k → Fin n)
    (f : Coord n → ℝ) : wordPartial (Fin.cons i w) f =
      SpatialCalculus.partialD i (wordPartial w f) := by simp [wordPartial]

theorem entry_hasFDerivAt {n a : ℕ} (J : compatibleJets n a) (k : ℕ) (hk : k < a)
    (w : Fin k → Fin n) (X : Coord n) :
    HasFDerivAt (fun Y => (entry J k hk.le w).val.1 Y)
      (gradient J.val ⟨k, hk⟩ w X) X := J.property ⟨k, hk⟩ w X

theorem entry_partialD {n a : ℕ} (J : compatibleJets n a) (k : ℕ) (hk : k < a)
    (w : Fin k → Fin n) (i : Fin n) (X : Coord n) :
    SpatialCalculus.partialD i (fun Y => (entry J k hk.le w).val.1 Y) X =
      (entry J (k + 1) (by omega) (Fin.cons i w)).val.1 X := by
  rw [SpatialCalculus.partialD_eq_fderiv i
    (fun Y => (entry_hasFDerivAt J k hk w Y).differentiableAt),
    (entry_hasFDerivAt J k hk w X).fderiv]
  classical
  simp [gradient, entry, ContinuousLinearMap.proj_apply, Pi.single_apply]

theorem entry_eq_wordPartial {n a : ℕ} (J : compatibleJets n a) (k : ℕ)
    (hk : k ≤ a) (w : Fin k → Fin n) :
    (fun X => (entry J k hk w).val.1 X) = wordPartial w (value J) := by
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
    ContDiff ℝ r (fun X => (entry J k (by omega) w).val.1 X) := by
  induction r generalizing k with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    convert (entry J k (by omega) w).val.1.continuous using 1
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
    (he : ∀ X, f.val.1 X = g.val.1 X) : f = g := by
  apply Subtype.ext
  apply Prod.ext
  · ext X; exact he X
  · apply Lp.ext
    filter_upwards [f.property, g.property] with X hf hg
    rw [hf, hg, he X]

theorem value_injective {n a : ℕ} : Function.Injective (@value n a) := by
  intro J K hjk
  apply Subtype.ext
  funext ⟨⟨k, hk⟩, w⟩
  apply compatible_ext
  intro X
  change (entry J k (by omega) w).val.1 X = (entry K k (by omega) w).val.1 X
  rw [congrFun (entry_eq_wordPartial J k (by omega) w) X,
    congrFun (entry_eq_wordPartial K k (by omega) w) X, hjk]

theorem derivative_tails {n a : ℕ} (J : compatibleJets n a) (k : ℕ) (hk : k ≤ a)
    (w : Fin k → Fin n) :
    Integrable (wordPartial w (value J)) ∧
      Tendsto (wordPartial w (value J)) (cocompact (Coord n)) (𝓝 0) := by
  rw [← entry_eq_wordPartial J k hk w]
  exact ⟨(L1.integrable_coeFn (entry J k hk w).val.2).congr
    (entry J k hk w).property, (entry J k hk w).val.1.zero_at_infty'⟩

end VelocityDetection.TailSpace.Jets
end

noncomputable section
namespace VelocityDetection.TailSpace
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators

def translate {n : ℕ} (Y : Coord n) (v : compatible n) : compatible n :=
  ⟨(v.val.1.comp (Homeomorph.addRight Y).toCocompactMap,
    Lp.compMeasurePreserving (fun X => X + Y) (measurePreserving_add_right volume Y) v.val.2), by
    exact (Lp.coeFn_compMeasurePreserving v.val.2 (measurePreserving_add_right volume Y)).trans
      ((measurePreserving_add_right volume Y).quasiMeasurePreserving.ae v.property)⟩

@[simp] theorem translate_apply {n : ℕ} (Y : Coord n) (v : compatible n) (X : Coord n) :
    (translate Y v).val.1 X = v.val.1 (X + Y) := rfl

@[simp] theorem translate_zero {n : ℕ} (v : compatible n) : translate 0 v = v := by
  apply ext_fun
  intro X
  simp

@[simp] theorem translate_add {n : ℕ} (Y Z : Coord n) (v : compatible n) :
    translate (Y + Z) v = translate Y (translate Z v) := by
  apply ext_fun
  intro X
  simp [add_assoc]

theorem norm_translate_le {n : ℕ} (Y : Coord n) (v : compatible n) :
    ‖translate Y v‖ ≤ ‖v‖ := by
  change max ‖(translate Y v).val.1‖ ‖(translate Y v).val.2‖ ≤ ‖v.val‖
  apply max_le
  · change ‖(translate Y v).val.1.toBCF‖ ≤ ‖v.val‖
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro X
    exact (BoundedContinuousFunction.norm_coe_le_norm v.val.1.toBCF (X + Y)).trans
      (norm_fst_le v.val)
  · exact (Lp.norm_compMeasurePreserving v.val.2 (measurePreserving_add_right volume Y)) ▸
      norm_snd_le v.val

@[simp] theorem norm_translate {n : ℕ} (Y : Coord n) (v : compatible n) :
    ‖translate Y v‖ = ‖v‖ := by
  apply le_antisymm (norm_translate_le _ _) 
  have he : translate (-Y) (translate Y v) = v := by
    rw [← translate_add, neg_add_cancel, translate_zero]
  simpa only [he] using norm_translate_le (-Y) (translate Y v)

def translateLI {n : ℕ} (Y : Coord n) : compatible n →ₗᵢ[ℝ] compatible n where
  toFun := translate Y
  map_add' := by
    intro v w
    apply ext_fun
    intro X
    rfl
  map_smul' := by
    intro c v
    apply ext_fun
    intro X
    rfl
  norm_map' := norm_translate Y

theorem continuous_translate_C0 {n : ℕ} (v : C₀(Coord n, ℝ)) :
    Continuous (fun Y : Coord n => v.comp (Homeomorph.addRight Y).toCocompactMap) := by
  apply continuous_iff_continuousAt.mpr
  intro Y
  apply ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly.mpr
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp
    (ZeroAtInftyContinuousMap.uniformContinuous v) ε hε
  filter_upwards [Metric.ball_mem_nhds Y hδ] with Z hZ X
  apply hd
  simpa [dist_comm] using hZ

theorem continuous_translate {n : ℕ} (v : compatible n) :
    Continuous (fun Y : Coord n => translate Y v) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact continuous_translate_C0 v.val.1
  · apply Continuous.compMeasurePreservingLp continuous_const
      (ContinuousMap.continuous_of_continuous_uncurry
        (fun Y : Coord n => ⟨fun X => X + Y, continuous_id.add_const Y⟩) ?_)
      (fun Y => measurePreserving_add_right volume Y) (by simp)
    exact continuous_snd.add continuous_fst

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

instance (n a : ℕ) : NormedAddCommGroup (compatibleJets n a) := by
  exact @Submodule.normedAddCommGroup ℝ (Data n a) _ _ _ (compatibleJets n a)

instance (n a : ℕ) : NormedSpace ℝ (compatibleJets n a) := by
  exact Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) (E := Data n a) (compatibleJets n a)

def translate {n a : ℕ} (Y : Coord n) (J : compatibleJets n a) : compatibleJets n a :=
  ⟨fun i => TailSpace.translate Y (J.val i), by
    intro k w X
    have hh := (J.property k w (X + Y)).comp X ((hasFDerivAt_id X).add_const Y)
    simp only [ContinuousLinearMap.comp_id] at hh
    convert hh using 1 <;> rfl⟩

@[simp] theorem translate_entry {n a : ℕ} (Y : Coord n) (J : compatibleJets n a)
    (k : ℕ) (hk : k ≤ a) (w : Fin k → Fin n) :
    entry (translate Y J) k hk w = TailSpace.translate Y (entry J k hk w) := rfl

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
  change ‖fun i => TailSpace.translate Y (J.val i)‖ = ‖J.val‖
  simp only [Pi.norm_def, nnnorm, TailSpace.norm_translate]

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
  exact TailSpace.continuous_translate (J.val i)

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

def evaluate {n a : ℕ} (X : Coord n) : compatibleJets n a →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun J => value J X
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    1 (by
      intro J
      have hb := BoundedContinuousFunction.norm_coe_le_norm
        (entry J 0 (Nat.zero_le a) Fin.elim0).val.1.toBCF X
      change ‖value J X‖ ≤ 1 * ‖J.val‖
      rw [one_mul]
      convert hb.trans ((norm_fst_le _).trans (norm_le_pi_norm J.val _)) using 1
      rfl)

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

end VelocityDetection.TailSpace.Jets
end

end OAI
