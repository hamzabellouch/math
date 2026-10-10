import Mathlib

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped BoundedContinuousFunction Topology ContDiff
open Set Filter
section

variable (X E : Type*) [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Pairs := {p : X × X // p.1 ≠ p.2}

abbrev Ambient := (X →ᵇ E) × (Pairs X →ᵇ E)

def graph (α : ℝ) : Submodule ℝ (Ambient X E) where
  carrier := {u | ∀ p : Pairs X,
    u.2 p = (dist p.val.1 p.val.2 ^ α)⁻¹ • (u.1 p.val.1 - u.1 p.val.2)}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv p
    simp only [Prod.fst_add, Prod.snd_add, BoundedContinuousFunction.add_apply,
      hu p, hv p]
    rw [show u.1 p.val.1 + v.1 p.val.1 - (u.1 p.val.2 + v.1 p.val.2) =
      (u.1 p.val.1 - u.1 p.val.2) + (v.1 p.val.1 - v.1 p.val.2) by abel, smul_add]
  smul_mem' := by
    intro c u hu p
    change c • u.2 p = (dist p.val.1 p.val.2 ^ α)⁻¹ •
      (c • u.1 p.val.1 - c • u.1 p.val.2)
    rw [hu p, ← smul_sub, smul_comm]

lemma graph_closed (α : ℝ) : IsClosed (graph X E α : Set (Ambient X E)) := by
  change IsClosed {u : Ambient X E | ∀ p : Pairs X, _}
  simp only [← Set.iInter_ofPred]
  apply isClosed_iInter
  intro p
  exact isClosed_eq
    ((BoundedContinuousFunction.evalCLM ℝ p).continuous.comp continuous_snd)
    ((((BoundedContinuousFunction.evalCLM ℝ p.val.1).continuous.comp continuous_fst).sub
      ((BoundedContinuousFunction.evalCLM ℝ p.val.2).continuous.comp continuous_fst)).const_smul _)

abbrev Holder (α : ℝ) := graph X E α

instance (α : ℝ) [CompleteSpace E] : CompleteSpace (Holder X E α) :=
  (graph_closed X E α).completeSpace_coe

variable {X E}

def valueCLM (α : ℝ) : Holder X E α →L[ℝ] (X →ᵇ E) :=
  (ContinuousLinearMap.fst ℝ (X →ᵇ E) (Pairs X →ᵇ E)).comp (graph X E α).subtypeL

def incrementCLM (α : ℝ) : Holder X E α →L[ℝ] (Pairs X →ᵇ E) :=
  (ContinuousLinearMap.snd ℝ (X →ᵇ E) (Pairs X →ᵇ E)).comp (graph X E α).subtypeL

variable {α : ℝ}

@[simp] lemma valueCLM_apply (u : Holder X E α) (x : X) :
    valueCLM α u x = u.val.1 x := rfl

@[simp] lemma incrementCLM_apply (u : Holder X E α) (p : Pairs X) :
    incrementCLM α u p = u.val.2 p := rfl

lemma increment_eq (u : Holder X E α) (p : Pairs X) :
    incrementCLM α u p = (dist p.val.1 p.val.2 ^ α)⁻¹ •
      (valueCLM α u p.val.1 - valueCLM α u p.val.2) := u.property p

lemma value_norm_le (u : Holder X E α) : ‖valueCLM α u‖ ≤ ‖u‖ :=
  le_max_left _ _

lemma increment_norm_le (u : Holder X E α) : ‖incrementCLM α u‖ ≤ ‖u‖ :=
  le_max_right _ _

lemma norm_value_le (u : Holder X E α) (x : X) : ‖valueCLM α u x‖ ≤ ‖u‖ :=
  (BoundedContinuousFunction.norm_coe_le_norm _ _).trans (value_norm_le u)

lemma norm_increment_le (u : Holder X E α) (p : Pairs X) :
    ‖incrementCLM α u p‖ ≤ ‖u‖ :=
  (BoundedContinuousFunction.norm_coe_le_norm _ _).trans (increment_norm_le u)

lemma norm_sub_value_le (u : Holder X E α) (x y : X) :
    ‖valueCLM α u x - valueCLM α u y‖ ≤ ‖u‖ * dist x y ^ α := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero]
    positivity
  have hd : 0 < dist x y ^ α := Real.rpow_pos_of_pos (dist_pos.mpr hxy) α
  have h := norm_increment_le u ⟨(x,y),hxy⟩
  rw [increment_eq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le)] at h
  change (dist x y ^ α)⁻¹ * ‖valueCLM α u x - valueCLM α u y‖ ≤ ‖u‖ at h
  have hh := mul_le_mul_of_nonneg_right h hd.le
  simpa only [mul_assoc, mul_left_comm (dist x y ^ α)⁻¹, inv_mul_cancel₀ hd.ne', mul_one] using hh

@[ext] lemma value_ext {u v : Holder X E α}
    (h : ∀ x, valueCLM α u x = valueCLM α v x) : u = v := by
  apply Subtype.ext
  apply Prod.ext
  · exact BoundedContinuousFunction.ext h
  · apply BoundedContinuousFunction.ext
    intro p
    rw [← incrementCLM_apply, ← incrementCLM_apply, increment_eq, increment_eq, h, h]

def ofBound (f : X → E) (hf : Continuous f) (M H : ℝ)
    (hM : ∀ x, ‖f x‖ ≤ M) (_hH : 0 ≤ H)
    (hh : ∀ x y, ‖f x - f y‖ ≤ H * dist x y ^ α) : Holder X E α := by
  let g : Pairs X → E := fun p => (dist p.val.1 p.val.2 ^ α)⁻¹ • (f p.val.1 - f p.val.2)
  have hg : Continuous g := by
    have hd : Continuous (fun p : Pairs X => dist p.val.1 p.val.2) :=
      (continuous_fst.comp continuous_subtype_val).dist
        (continuous_snd.comp continuous_subtype_val)
    exact ((hd.rpow_const (fun p => Or.inl (dist_ne_zero.mpr p.property))).inv₀
      (fun p => (Real.rpow_pos_of_pos (dist_pos.mpr p.property) α).ne')).smul
        ((hf.comp (continuous_fst.comp continuous_subtype_val)).sub
          (hf.comp (continuous_snd.comp continuous_subtype_val)))
  have hgM : ∀ p, ‖g p‖ ≤ H := by
    intro p
    have hp : 0 < dist p.val.1 p.val.2 ^ α := Real.rpow_pos_of_pos (dist_pos.mpr p.property) α
    dsimp [g]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
    calc
      _ ≤ (dist p.val.1 p.val.2 ^ α)⁻¹ * (H * dist p.val.1 p.val.2 ^ α) :=
        mul_le_mul_of_nonneg_left (hh _ _) (inv_nonneg.mpr hp.le)
      _ = H := by field_simp
  exact ⟨(BoundedContinuousFunction.ofNormedAddCommGroup f hf M hM,
    BoundedContinuousFunction.ofNormedAddCommGroup g hg H hgM),fun p => rfl⟩

@[simp] lemma ofBound_value (f : X → E) (hf : Continuous f) (M H : ℝ)
    (hM : ∀ x, ‖f x‖ ≤ M) (hH : 0 ≤ H)
    (hh : ∀ x y, ‖f x - f y‖ ≤ H * dist x y ^ α) (x : X) :
    valueCLM α (ofBound f hf M H hM hH hh) x = f x := rfl

lemma ofBound_norm_le (f : X → E) (hf : Continuous f) (M H : ℝ)
    (hM0 : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M) (hH : 0 ≤ H)
    (hh : ∀ x y, ‖f x - f y‖ ≤ H * dist x y ^ α) :
    ‖ofBound f hf M H hM hH hh‖ ≤ max M H := by
  change max _ _ ≤ max M H
  apply max_le_max
  · exact (BoundedContinuousFunction.norm_le hM0).mpr hM
  · apply (BoundedContinuousFunction.norm_le hH).mpr
    intro p
    have hp : 0 < dist p.val.1 p.val.2 ^ α := Real.rpow_pos_of_pos (dist_pos.mpr p.property) α
    change ‖(dist p.val.1 p.val.2 ^ α)⁻¹ • (f p.val.1 - f p.val.2)‖ ≤ H
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
    calc
      _ ≤ (dist p.val.1 p.val.2 ^ α)⁻¹ * (H * dist p.val.1 p.val.2 ^ α) :=
        mul_le_mul_of_nonneg_left (hh _ _) (inv_nonneg.mpr hp.le)
      _ = H := by field_simp

lemma norm_le_of_bounds (u : Holder X E α) {M H : ℝ} (hM0 : 0 ≤ M) (hH0 : 0 ≤ H)
    (hM : ∀ x, ‖valueCLM α u x‖ ≤ M)
    (hH : ∀ x y, ‖valueCLM α u x - valueCLM α u y‖ ≤ H * dist x y ^ α) :
    ‖u‖ ≤ max M H := by
  have he : u = ofBound (valueCLM α u) (valueCLM α u).continuous M H hM hH0 hH := by
    apply value_ext
    intro x
    rfl
  rw [he]
  exact ofBound_norm_le _ _ _ _ hM0 _ _ _

section LinearOperations
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def mapCLM (α : ℝ) (L : E →L[ℝ] F) : Holder X E α →L[ℝ] Holder X F α :=
  (((L.compLeftContinuousBounded X).prodMap (L.compLeftContinuousBounded (Pairs X))).comp
    (graph X E α).subtypeL).codRestrict (graph X F α) (by
      intro u p
      change L (u.val.2 p) = (dist p.val.1 p.val.2 ^ α)⁻¹ •
        (L (u.val.1 p.val.1) - L (u.val.1 p.val.2))
      rw [u.property p, map_smul, map_sub])

@[simp] lemma mapCLM_value (L : E →L[ℝ] F) (u : Holder X E α) (x : X) :
    valueCLM α (mapCLM α L u) x = L (valueCLM α u x) := rfl

def const (α : ℝ) (e : E) : Holder X E α :=
  ⟨(BoundedContinuousFunction.const X e, 0), by intro p; simp⟩

@[simp] lemma const_value (e : E) (x : X) : valueCLM α (const α e) x = e := rfl

lemma const_norm_le (e : E) : ‖(const (X := X) α e)‖ ≤ ‖e‖ := by
  change max ‖BoundedContinuousFunction.const X e‖ ‖(0 : Pairs X →ᵇ E)‖ ≤ ‖e‖
  rw [norm_zero]
  exact max_le (BoundedContinuousFunction.norm_const_le e) (norm_nonneg e)

end LinearOperations

section Bilinear
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma bilin_sub_bound (B : E →L[ℝ] F →L[ℝ] G)
    (u : Holder X E α) (v : Holder X F α) (x y : X) :
    ‖B (valueCLM α u x) (valueCLM α v x) - B (valueCLM α u y) (valueCLM α v y)‖ ≤
      (2 * ‖B‖ * ‖u‖ * ‖v‖) * dist x y ^ α := by
  have he : B (valueCLM α u x) (valueCLM α v x) - B (valueCLM α u y) (valueCLM α v y) =
    B (valueCLM α u x - valueCLM α u y) (valueCLM α v x) +
      B (valueCLM α u y) (valueCLM α v x - valueCLM α v y) := by
    simp only [map_sub, sub_apply]
    abel
  rw [he]
  calc
    _ ≤ ‖B (valueCLM α u x - valueCLM α u y) (valueCLM α v x)‖ +
        ‖B (valueCLM α u y) (valueCLM α v x - valueCLM α v y)‖ := norm_add_le _ _
    _ ≤ (‖B‖ * ‖valueCLM α u x - valueCLM α u y‖) * ‖valueCLM α v x‖ +
        (‖B‖ * ‖valueCLM α u y‖) * ‖valueCLM α v x - valueCLM α v y‖ :=
      add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
    _ ≤ (‖B‖ * (‖u‖ * dist x y ^ α)) * ‖v‖ +
        (‖B‖ * ‖u‖) * (‖v‖ * dist x y ^ α) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left (norm_sub_value_le u x y) (norm_nonneg B))
          (norm_value_le v x) (norm_nonneg _) (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left (norm_value_le u y) (norm_nonneg B))
          (norm_sub_value_le v x y) (norm_nonneg _) (by positivity)
    _ = _ := by ring

def bilin (B : E →L[ℝ] F →L[ℝ] G) (u : Holder X E α) (v : Holder X F α) : Holder X G α :=
  ofBound (fun x => B (valueCLM α u x) (valueCLM α v x))
    ((B.continuous.comp (valueCLM α u).continuous).clm_apply (valueCLM α v).continuous)
    (‖B‖ * ‖u‖ * ‖v‖) (2 * ‖B‖ * ‖u‖ * ‖v‖)
    (fun x => (B.le_opNorm₂ _ _).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (norm_value_le u x) (norm_nonneg B))
        (norm_value_le v x) (norm_nonneg _) (by positivity)))
    (by positivity) (bilin_sub_bound B u v)

@[simp] lemma bilin_value (B : E →L[ℝ] F →L[ℝ] G)
    (u : Holder X E α) (v : Holder X F α) (x : X) :
    valueCLM α (bilin B u v) x = B (valueCLM α u x) (valueCLM α v x) := rfl

lemma bilin_norm (B : E →L[ℝ] F →L[ℝ] G) (u : Holder X E α) (v : Holder X F α) :
    ‖bilin B u v‖ ≤ (2 * ‖B‖) * ‖u‖ * ‖v‖ := by
  unfold bilin
  refine (ofBound_norm_le _ _ _ _ (by positivity) _ _ _).trans ?_
  apply max_le
  · nlinarith [mul_nonneg (mul_nonneg (norm_nonneg B) (norm_nonneg u)) (norm_nonneg v)]
  · exact le_rfl

def bilinCLM (B : E →L[ℝ] F →L[ℝ] G) :
    Holder X E α →L[ℝ] Holder X F α →L[ℝ] Holder X G α :=
  LinearMap.mkContinuous₂
    { toFun := fun u =>
        { toFun := bilin B u
          map_add' := fun v w => by
            apply value_ext
            intro x
            simp only [bilin_value, map_add, BoundedContinuousFunction.add_apply]
          map_smul' := fun c v => by
            apply value_ext
            intro x
            simp only [bilin_value, map_smul, BoundedContinuousFunction.smul_apply,
              RingHom.id_apply] }
      map_add' := fun u v => by
        apply LinearMap.ext
        intro w
        apply value_ext
        intro x
        change valueCLM α (bilin B (u+v) w) x =
          valueCLM α (bilin B u w + bilin B v w) x
        simp only [bilin_value, map_add, BoundedContinuousFunction.add_apply, add_apply]
      map_smul' := fun c u => by
        apply LinearMap.ext
        intro v
        apply value_ext
        intro x
        change valueCLM α (bilin B (c • u) v) x = valueCLM α (c • bilin B u v) x
        simp only [bilin_value, map_smul, BoundedContinuousFunction.smul_apply, smul_apply] }
    (2 * ‖B‖) (bilin_norm B)

@[simp] lemma bilinCLM_value (B : E →L[ℝ] F →L[ℝ] G)
    (u : Holder X E α) (v : Holder X F α) (x : X) :
    valueCLM α (bilinCLM B u v) x = B (valueCLM α u x) (valueCLM α v x) := rfl

end Bilinear

variable (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D]

abbrev JetAmbient (α : ℝ) := Holder D E α × Holder D (D →L[ℝ] E) α

def jetGraph (α : ℝ) : Submodule ℝ (JetAmbient (E := E) D α) where
  carrier := {u | ∀ x, HasFDerivAt (valueCLM α u.1) (valueCLM α u.2 x) x}
  zero_mem' := by
    intro x
    convert! hasFDerivAt_const (𝕜 := ℝ) (0 : E) x using 1
  add_mem' := by
    intro u v hu hv x
    exact (hu x).add (hv x)
  smul_mem' := by
    intro c u hu x
    exact (hu x).const_smul c

lemma jetGraph_closed (α : ℝ) : IsClosed (jetGraph (E := E) D α : Set (JetAmbient (E := E) D α)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u v hu huv x
  have hv0 : Tendsto (fun n => valueCLM α (u n).1) atTop (𝓝 (valueCLM α v.1)) :=
    ((valueCLM α).continuous.comp continuous_fst).tendsto v |>.comp huv
  have hv1 : Tendsto (fun n => valueCLM α (u n).2) atTop (𝓝 (valueCLM α v.2)) :=
    ((valueCLM α).continuous.comp continuous_snd).tendsto v |>.comp huv
  have huni := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hv1
  exact hasFDerivAt_of_tendstoUniformly huni (fun n => hu n)
    (fun y => (BoundedContinuousFunction.evalCLM ℝ y).continuous.tendsto _ |>.comp hv0) x

abbrev COneHolder (α : ℝ) := jetGraph (E := E) D α

instance (α : ℝ) [CompleteSpace E] : CompleteSpace (COneHolder (E := E) D α) :=
  (jetGraph_closed (E := E) D α).completeSpace_coe

variable {D}

def jetValueCLM (α : ℝ) : COneHolder (E := E) D α →L[ℝ] Holder D E α :=
  (ContinuousLinearMap.fst ℝ _ _).comp (jetGraph (E := E) D α).subtypeL

def jetDerivCLM (α : ℝ) : COneHolder (E := E) D α →L[ℝ] Holder D (D →L[ℝ] E) α :=
  (ContinuousLinearMap.snd ℝ _ _).comp (jetGraph (E := E) D α).subtypeL

lemma hasFDerivAt (u : COneHolder (E := E) D α) (x : D) :
    HasFDerivAt (valueCLM α (jetValueCLM α u))
      (valueCLM α (jetDerivCLM α u) x) x := u.property x

lemma contDiff_one (u : COneHolder (E := E) D α) :
    ContDiff ℝ 1 (valueCLM α (jetValueCLM α u)) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (hasFDerivAt u x).differentiableAt, ?_⟩
  have he : fderiv ℝ (valueCLM α (jetValueCLM α u)) = valueCLM α (jetDerivCLM α u) :=
    funext fun x => (hasFDerivAt u x).fderiv
  rw [he]
  exact (valueCLM α (jetDerivCLM α u)).continuous

lemma jetValue_norm_le (u : COneHolder (E := E) D α) : ‖jetValueCLM α u‖ ≤ ‖u‖ :=
  le_max_left _ _

lemma jetDeriv_norm_le (u : COneHolder (E := E) D α) : ‖jetDerivCLM α u‖ ≤ ‖u‖ :=
  le_max_right _ _

lemma jet_norm_value_le (u : COneHolder (E := E) D α) (x : D) :
    ‖valueCLM α (jetValueCLM α u) x‖ ≤ ‖u‖ :=
  (norm_value_le _ _).trans (jetValue_norm_le u)

lemma jet_norm_deriv_le (u : COneHolder (E := E) D α) (x : D) :
    ‖valueCLM α (jetDerivCLM α u) x‖ ≤ ‖u‖ :=
  (norm_value_le _ _).trans (jetDeriv_norm_le u)

def markedJets (α : ℝ) (marks : Set D) : Submodule ℝ (COneHolder (E := E) D α) :=
  ⨅ x ∈ marks, ((BoundedContinuousFunction.evalCLM ℝ x).comp
    ((valueCLM α).comp (jetValueCLM α))).ker

lemma markedJets_closed (α : ℝ) (marks : Set D) :
    IsClosed (markedJets (E := E) α marks : Set (COneHolder (E := E) D α)) := by
  simp only [markedJets, Submodule.coe_iInf]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro _
  exact ContinuousLinearMap.isClosed_ker _

instance (α : ℝ) (marks : Set D) [CompleteSpace E] :
    CompleteSpace (markedJets (E := E) α marks) :=
  (markedJets_closed α marks).completeSpace_coe

lemma mem_markedJets (u : COneHolder (E := E) D α) (marks : Set D) :
    u ∈ markedJets α marks ↔ ∀ x ∈ marks, valueCLM α (jetValueCLM α u) x = 0 := by
  simp [markedJets]

end
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

lemma norm_sub_le_of_deriv_bound {f : E → F} (hf : Differentiable ℝ f)
    {M : ℝ} (hM : ∀ x, ‖fderiv ℝ f x‖ ≤ M) (x y : E) :
    ‖f x - f y‖ ≤ M * ‖x - y‖ :=
  Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hf z)
    (fun z _ => hM z) convex_univ (mem_univ y) (mem_univ x)

lemma taylor_remainder_quadratic {f : E → F} (hf : Differentiable ℝ f)
    {M : ℝ} (hM : 0 ≤ M)
    (hdf : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ M * ‖x-y‖) (x h : E) :
    ‖f (x+h) - f x - fderiv ℝ f x h‖ ≤ M * ‖h‖ ^ 2 := by
  have hball : x + h ∈ Metric.closedBall x ‖h‖ := by
    simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, le_refl]
  have hb (z : E) (hz : z ∈ Metric.closedBall x ‖h‖) :
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ M * ‖h‖ := by
    apply (hdf z x).trans
    apply mul_le_mul_of_nonneg_left _ hM
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have he := (convex_closedBall x ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z _ => (hf z).hasFDerivAt.hasFDerivWithinAt) hb
    (Metric.mem_closedBall_self (norm_nonneg h)) hball
  simpa only [add_sub_cancel_left, pow_two, mul_assoc] using he

lemma hasFDerivAt_of_quadratic_remainder {g : E → F} (L : E →L[ℝ] F) (x : E)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ h, ‖g (x+h)-g x-L h‖ ≤ C*‖h‖^2) : HasFDerivAt g L x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hδ : 0 < c / (C+1) := div_pos hc (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with h hh
  have hn : ‖h‖ < c / (C+1) := by simpa only [Metric.mem_ball, dist_zero_right] using hh
  have hsmall : C*‖h‖ ≤ c := by
    have ht := (lt_div_iff₀ (show 0 < C+1 by positivity)).mp hn
    nlinarith [norm_nonneg h]
  exact (hb h).trans (by nlinarith [mul_le_mul_of_nonneg_right hsmall (norm_nonneg h)])

structure BoundedCThree (f : E → F) : Prop where
  smooth : ContDiff ℝ ∞ f
  bounded : ∃ M : ℝ, 0 ≤ M ∧ (∀ x, ‖f x‖ ≤ M) ∧
    (∀ x, ‖fderiv ℝ f x‖ ≤ M) ∧
    (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) ∧
    (∀ x, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖ ≤ M)

lemma boundedCThree_of_compactSupport {f : E → F} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : BoundedCThree f := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have h2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := h1.fderiv_right (by simp)
  have h3 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) := h2.fderiv_right (by simp)
  obtain ⟨M0,h0⟩ := hf.continuous.bounded_above_of_compact_support hc
  obtain ⟨M1,h1b⟩ := h1.continuous.bounded_above_of_compact_support (hc.fderiv (𝕜 := ℝ))
  obtain ⟨M2,h2b⟩ := h2.continuous.bounded_above_of_compact_support
    (hc.fderiv (𝕜 := ℝ) |>.fderiv (𝕜 := ℝ))
  obtain ⟨M3,h3b⟩ := h3.continuous.bounded_above_of_compact_support
    (hc.fderiv (𝕜 := ℝ) |>.fderiv (𝕜 := ℝ) |>.fderiv (𝕜 := ℝ))
  refine ⟨hf, max 0 (max M0 (max M1 (max M2 M3))), le_max_left _ _, ?_, ?_, ?_, ?_⟩
  · intro x; exact (h0 x).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro x; exact (h1b x).trans ((le_max_left _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  · intro x; exact (h2b x).trans ((le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  · intro x; exact (h3b x).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))

lemma BoundedCThree.add_const {f : E → F} (hf : BoundedCThree f) (c : F) :
    BoundedCThree (fun x => f x + c) := by
  obtain ⟨M,hM,h0,h1,h2,h3⟩ := hf.bounded
  have he : fderiv ℝ (fun x => f x + c) = fderiv ℝ f := by
    ext x v
    simp only [fderiv_add_const]
  refine ⟨hf.smooth.add contDiff_const, M + ‖c‖, by positivity, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (norm_add_le _ _).trans (add_le_add_left (h0 x) _)
  · intro x; rw [he]; exact (h1 x).trans (le_add_of_nonneg_right (norm_nonneg c))
  · intro x; rw [he]; exact (h2 x).trans (le_add_of_nonneg_right (norm_nonneg c))
  · intro x; rw [he]; exact (h3 x).trans (le_add_of_nonneg_right (norm_nonneg c))

lemma boundedCThree_of_compactPerturbation {f : E → F} (hf : ContDiff ℝ ∞ f)
    (c : F) (hc : HasCompactSupport (fun x => f x - c)) : BoundedCThree f := by
  have h := (boundedCThree_of_compactSupport (hf.sub contDiff_const) hc).add_const c
  simpa only [sub_add_cancel] using h

namespace BoundedCThree
variable {f : E → F}

def bound (hf : BoundedCThree f) : ℝ := Classical.choose hf.bounded

lemma bound_nonneg (hf : BoundedCThree f) : 0 ≤ hf.bound :=
  (Classical.choose_spec hf.bounded).1

lemma norm_le (hf : BoundedCThree f) (x : E) : ‖f x‖ ≤ hf.bound :=
  (Classical.choose_spec hf.bounded).2.1 x

lemma norm_fderiv_le (hf : BoundedCThree f) (x : E) : ‖fderiv ℝ f x‖ ≤ hf.bound :=
  (Classical.choose_spec hf.bounded).2.2.1 x

lemma norm_fderiv₂_le (hf : BoundedCThree f) (x : E) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ hf.bound :=
  (Classical.choose_spec hf.bounded).2.2.2.1 x

lemma norm_fderiv₃_le (hf : BoundedCThree f) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖ ≤ hf.bound :=
  (Classical.choose_spec hf.bounded).2.2.2.2 x

lemma fderiv_smooth (hf : BoundedCThree f) : ContDiff ℝ ∞ (fderiv ℝ f) :=
  hf.smooth.fderiv_right (by simp)

lemma fderiv₂_smooth (hf : BoundedCThree f) : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) :=
  hf.fderiv_smooth.fderiv_right (by simp)

lemma norm_sub_le (hf : BoundedCThree f) (x y : E) :
    ‖f x - f y‖ ≤ hf.bound * ‖x-y‖ :=
  norm_sub_le_of_deriv_bound (hf.smooth.differentiable (by simp)) hf.norm_fderiv_le x y

lemma norm_fderiv_sub_le (hf : BoundedCThree f) (x y : E) :
    ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ hf.bound * ‖x-y‖ :=
  norm_sub_le_of_deriv_bound (hf.fderiv_smooth.differentiable (by simp)) hf.norm_fderiv₂_le x y

lemma norm_fderiv₂_sub_le (hf : BoundedCThree f) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ hf.bound * ‖x-y‖ :=
  norm_sub_le_of_deriv_bound (hf.fderiv₂_smooth.differentiable (by simp)) hf.norm_fderiv₃_le x y

lemma remainder_bound (hf : BoundedCThree f) (x h : E) :
    ‖f (x+h) - f x - fderiv ℝ f x h‖ ≤ hf.bound * ‖h‖^2 :=
  taylor_remainder_quadratic (hf.smooth.differentiable (by simp)) hf.bound_nonneg
    hf.norm_fderiv_sub_le x h

lemma fderiv_remainder_bound (hf : BoundedCThree f) (x h : E) :
    ‖fderiv ℝ f (x+h) - fderiv ℝ f x - fderiv ℝ (fderiv ℝ f) x h‖ ≤ hf.bound * ‖h‖^2 :=
  taylor_remainder_quadratic (hf.fderiv_smooth.differentiable (by simp)) hf.bound_nonneg
    hf.norm_fderiv₂_sub_le x h

end BoundedCThree

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {f : E → F} (hf : BoundedCThree f) {t h : D → E} {x : D}

include hf in
lemma fderiv_composed_remainder (ht : DifferentiableAt ℝ t x) (hh : DifferentiableAt ℝ h x) (v : D) :
    fderiv ℝ (fun z => f (t z + h z) - f (t z) - fderiv ℝ f (t z) (h z)) x v =
      (fderiv ℝ f (t x + h x) - fderiv ℝ f (t x) - fderiv ℝ (fderiv ℝ f) (t x) (h x))
        (fderiv ℝ t x v) +
      (fderiv ℝ f (t x + h x) - fderiv ℝ f (t x)) (fderiv ℝ h x v) := by
  have hc := (((hf.smooth.differentiable (by simp) (t x+h x)).hasFDerivAt.comp x
    (ht.hasFDerivAt.add hh.hasFDerivAt)).sub
      ((hf.smooth.differentiable (by simp) (t x)).hasFDerivAt.comp x ht.hasFDerivAt)).sub
    (((hf.fderiv_smooth.differentiable (by simp) (t x)).hasFDerivAt.comp x ht.hasFDerivAt).clm_apply
      hh.hasFDerivAt)
  have hc' : HasFDerivAt
      (fun z => f (t z+h z)-f (t z)-fderiv ℝ f (t z) (h z))
      ((fderiv ℝ f (t x+h x)).comp (fderiv ℝ t x + fderiv ℝ h x) -
        (fderiv ℝ f (t x)).comp (fderiv ℝ t x) -
        ((fderiv ℝ f (t x)).comp (fderiv ℝ h x) +
          ((fderiv ℝ (fderiv ℝ f) (t x)).comp (fderiv ℝ t x)).flip (h x))) x := by
    convert! hc using 1
  rw [hc'.fderiv]
  simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    map_add]
  rw [(hf.smooth.contDiffAt.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)).eq
    (fderiv ℝ t x v) (h x)]
  abel

lemma norm_fderiv_composed_remainder (ht : DifferentiableAt ℝ t x)
    (hh : DifferentiableAt ℝ h x) :
    ‖fderiv ℝ (fun z => f (t z+h z)-f (t z)-fderiv ℝ f (t z) (h z)) x‖ ≤
      hf.bound * ‖h x‖^2 * ‖fderiv ℝ t x‖ + hf.bound * ‖h x‖ * ‖fderiv ℝ h x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [hf.bound_nonneg])
  intro v
  rw [fderiv_composed_remainder hf ht hh]
  calc
    _ ≤ ‖(fderiv ℝ f (t x+h x)-fderiv ℝ f (t x)-fderiv ℝ (fderiv ℝ f) (t x) (h x))
          (fderiv ℝ t x v)‖ +
        ‖(fderiv ℝ f (t x+h x)-fderiv ℝ f (t x)) (fderiv ℝ h x v)‖ := norm_add_le _ _
    _ ≤ (hf.bound * ‖h x‖^2) * (‖fderiv ℝ t x‖ * ‖v‖) +
        (hf.bound * ‖h x‖) * (‖fderiv ℝ h x‖ * ‖v‖) := by
      apply add_le_add
      · exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hf.fderiv_remainder_bound (t x) (h x))
            (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _) (by positivity [hf.bound_nonneg]))
      · have hd := hf.norm_fderiv_sub_le (t x+h x) (t x)
        simp only [add_sub_cancel_left] at hd
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul hd (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
            (mul_nonneg hf.bound_nonneg (norm_nonneg _)))
    _ = _ := by ring

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
