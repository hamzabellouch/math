import OAI.Analysis.FreeGroupFactor.Taylor

namespace OAI

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

open scoped ENNReal

def hilbertReindex {G : Type uG} {H : Type uH} (e : G ≃ H) :
    GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H where
  toFun ξ := ⟨fun h => ξ (e.symm h), by
    apply memℓp_gen
    exact e.symm.summable_iff.mpr ((lp.memℓp ξ).summable (by norm_num))⟩
  invFun η := ⟨fun g => η (e g), by
    apply memℓp_gen
    exact e.summable_iff.mpr ((lp.memℓp η).summable (by norm_num))⟩
  left_inv ξ := by ext g; simp
  right_inv η := by ext h; simp
  map_add' ξ η := by rfl
  map_smul' c ξ := by rfl
  norm_map' ξ := by
    simp only [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    change (∑' h : H, ‖ξ (e.symm h)‖ ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal) =
      (∑' g : G, ‖ξ g‖ ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal)
    exact congrArg (fun t : ℝ => t ^ (1 / (2 : ℝ≥0∞).toReal))
      (e.symm.tsum_eq (fun g => ‖ξ g‖ ^ (2 : ℝ≥0∞).toReal))

@[simp] theorem hilbertReindex_apply {G : Type uG} {H : Type uH} (e : G ≃ H)
    (ξ : GroupHilbert G) (h : H) : hilbertReindex e ξ h = ξ (e.symm h) := rfl

def leftRegular {G : Type uG} [Group G] (g : G) : GroupOperator G :=
  (hilbertReindex (Equiv.mulLeft g)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem leftRegular_apply {G : Type uG} [Group G] (g : G)
    (ξ : GroupHilbert G) (h : G) : leftRegular g ξ h = ξ (g⁻¹ * h) := rfl

@[simp] theorem leftRegular_one {G : Type uG} [Group G] :
    leftRegular (1 : G) = 1 := by
  ext ξ h
  simp

@[simp] theorem leftRegular_mul {G : Type uG} [Group G] (g h : G) :
    leftRegular (g * h) = leftRegular g * leftRegular h := by
  ext ξ b
  simp [mul_assoc]

theorem leftRegular_mem_leftTranslations {G : Type uG} [Group G] (g : G) :
    leftRegular g ∈ leftTranslations G := ⟨g, fun _ _ => rfl⟩

theorem leftTranslations_eq_range (G : Type uG) [Group G] :
    leftTranslations G = Set.range (leftRegular (G := G)) := by
  ext T
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    ext ξ h
    exact (hg ξ h).symm
  · rintro ⟨g, rfl⟩
    exact leftRegular_mem_leftTranslations g

def groupVonNeumannBundled (G : Type uG) [Group G] : VonNeumannAlgebra (GroupHilbert G) where
  toStarSubalgebra := groupVonNeumann G
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (groupVonNeumann G : Set (GroupOperator G))) =
      (groupVonNeumann G : Set (GroupOperator G))
    simp only [groupVonNeumann, StarSubalgebra.coe_centralizer_centralizer,
      Set.centralizer_centralizer_centralizer]

@[simp] theorem leftRegular_star {G : Type uG} [Group G] (g : G) :
    star (leftRegular g) = leftRegular g⁻¹ := by
  change star ((hilbertReindex (Equiv.mulLeft g)) : GroupOperator G) = _
  rw [LinearIsometryEquiv.star_eq_symm]
  ext ξ b
  change ξ (g * b) = ξ ((g⁻¹)⁻¹ * b)
  simp

def rightRegular {G : Type uG} [Group G] (g : G) : GroupOperator G :=
  (hilbertReindex (Equiv.mulRight g⁻¹)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem rightRegular_apply {G : Type uG} [Group G] (g : G)
    (ξ : GroupHilbert G) (h : G) : rightRegular g ξ h = ξ (h * g) := by
  simp [rightRegular]

@[simp] theorem rightRegular_star {G : Type uG} [Group G] (g : G) :
    star (rightRegular g) = rightRegular g⁻¹ := by
  change star ((hilbertReindex (Equiv.mulRight g⁻¹)) : GroupOperator G) = _
  rw [LinearIsometryEquiv.star_eq_symm]
  ext ξ b
  change ξ (b * g⁻¹) = rightRegular g⁻¹ ξ b
  rw [rightRegular_apply]

theorem left_right_commute {G : Type uG} [Group G] (g h : G) :
    leftRegular g * rightRegular h = rightRegular h * leftRegular g := by
  ext ξ b
  simp [mul_assoc]

theorem rightRegular_mem_commutant {G : Type uG} [Group G] (g : G) :
    rightRegular g ∈ StarSubalgebra.centralizer ℂ (leftTranslations G) := by
  rw [StarSubalgebra.mem_centralizer_iff, leftTranslations_eq_range]
  rintro _ ⟨h, rfl⟩
  exact ⟨left_right_commute h g, by simp only [leftRegular_star]; exact left_right_commute _ _⟩

theorem groupVN_commute_right {G : Type uG} [Group G] (T : groupVonNeumann G) (g : G) :
    rightRegular g * (T : GroupOperator G) = (T : GroupOperator G) * rightRegular g :=
  ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _ (rightRegular_mem_commutant g)).1

theorem groupVN_separating {G : Type uG} [Group G] [DecidableEq G] (T : groupVonNeumann G)
    (hT : (T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ)) = 0) : T = 0 := by
  classical
  have hr (g : G) : rightRegular g⁻¹ (lp.single 2 (1 : G) (1 : ℂ)) = lp.single 2 g 1 := by
    ext b
    simp [lp.single_apply, Pi.single_apply, mul_inv_eq_one]
  have hsingle (g : G) : (T : GroupOperator G) (lp.single 2 g 1) = 0 := by
    rw [← hr g]
    have hc := congrArg (fun f : GroupOperator G => f (lp.single 2 (1 : G) (1 : ℂ)))
      (groupVN_commute_right T g⁻¹)
    simpa [hT] using hc.symm
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro ξ
  have hs := ((lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ).mapL (T : GroupOperator G))
  have hz (g : G) : (T : GroupOperator G) (lp.single 2 g (ξ g)) = 0 := by
    have he : lp.single (E := fun _ : G => ℂ) 2 g (ξ g) = (ξ g) • lp.single (E := fun _ : G => ℂ) 2 g (1 : ℂ) := by
      ext b
      simp [lp.single_apply, Pi.single_apply]
    rw [he, map_smul, hsingle, smul_zero]
  simp only [hz] at hs
  exact HasSum.unique hs hasSum_zero

theorem canonicalTrace_eq_inner {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) :
    canonicalTrace T = inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
      ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))) := by
  classical
  simp only [canonicalTrace, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
  apply congrArg (fun v : GroupHilbert G => ((T : GroupOperator G) v) 1)
  ext b
  simp [lp.single_apply, Pi.single_apply]

theorem canonicalTrace_star_mul {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) :
    canonicalTrace (star T * T) =
      (‖(T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖ ^ 2 : ℂ) := by
  rw [canonicalTrace_eq_inner]
  change inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
    (star (T : GroupOperator G) ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ)))) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq_to_K _

theorem canonicalTrace_faithful {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) (hT : canonicalTrace (star T * T) = 0) : T = 0 := by
  rw [canonicalTrace_star_mul] at hT
  have hnorm : ‖(T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖ = 0 := by
    exact Complex.ofReal_eq_zero.mp (eq_zero_of_pow_eq_zero hT)
  exact groupVN_separating T (norm_eq_zero.mp hnorm)

def canonicalTraceLinear {G : Type uG} [Group G] : groupVonNeumann G →ₗ[ℂ] ℂ where
  toFun := canonicalTrace
  map_add' T U := by simp [canonicalTrace]
  map_smul' c T := by simp [canonicalTrace]

theorem norm_canonicalTrace_le {G : Type uG} [Group G] (T : groupVonNeumann G) :
    ‖canonicalTrace T‖ ≤ ‖T‖ := by
  classical
  rw [canonicalTrace_eq_inner]
  calc
    ‖inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
        ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ)))‖ ≤
        ‖lp.single (E := fun _ : G => ℂ) 2 (1 : G) (1 : ℂ)‖ *
        ‖(T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖ := norm_inner_le_norm _ _
    _ ≤ ‖lp.single (E := fun _ : G => ℂ) 2 (1 : G) (1 : ℂ)‖ *
        (‖(T : GroupOperator G)‖ * ‖lp.single (E := fun _ : G => ℂ) 2 (1 : G) (1 : ℂ)‖) := by
      gcongr
      exact (T : GroupOperator G).le_opNorm _
    _ = ‖T‖ := by simp

def canonicalTraceCLM {G : Type uG} [Group G] : groupVonNeumann G →L[ℂ] ℂ :=
  canonicalTraceLinear.mkContinuous 1 (fun T => by
    change ‖canonicalTrace T‖ ≤ 1 * ‖T‖
    simpa only [one_mul] using norm_canonicalTrace_le T)

@[simp] theorem canonicalTraceCLM_apply {G : Type uG} [Group G] (T : groupVonNeumann G) :
    canonicalTraceCLM T = canonicalTrace T := rfl

theorem leftRegular_unitary {G : Type uG} [Group G] (g : G) :
    leftRegular g ∈ unitary (GroupOperator G) := by
  rw [Unitary.mem_iff]
  constructor <;> simp [← leftRegular_mul, leftRegular_star, leftRegular_one]

theorem leftRegular_mem_groupVN {G : Type uG} [Group G] (g : G) :
    leftRegular g ∈ groupVonNeumann G := by
  rw [groupVonNeumann, StarSubalgebra.mem_centralizer_iff]
  intro S hS
  have hs := (StarSubalgebra.mem_centralizer_iff ℂ).mp hS
  constructor
  · exact (hs _ (by rw [leftTranslations_eq_range]; exact ⟨g, rfl⟩)).1.symm
  · have hh := congrArg star (hs _ (by rw [leftTranslations_eq_range]; exact ⟨g⁻¹, rfl⟩)).1
    simpa only [star_mul, leftRegular_star, inv_inv] using hh

def groupUnitary {G : Type uG} [Group G] (g : G) : groupVonNeumann G :=
  ⟨leftRegular g, leftRegular_mem_groupVN g⟩

@[simp] theorem canonicalTrace_groupUnitary {G : Type uG} [Group G] [DecidableEq G] (g : G) :
    canonicalTrace (groupUnitary g) = if g = 1 then 1 else 0 := by
  classical
  simp [canonicalTrace, groupUnitary, lp.single_apply, Pi.single_apply]

end FreeGroupFactorMain

end

end OAI
