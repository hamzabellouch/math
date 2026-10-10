import Mathlib

namespace OAI

/-! Balancing, collapsed circles and singular homology of conic blocks. -/

namespace AmbientMultiplicity.InnerGeometry
noncomputable section
open Filter Topology

 
def scaleTo (r : ℝ) (z : ℂ) : ℂ := (r / ‖z‖) • z

lemma scaleTo_zero (r : ℝ) : scaleTo r 0 = 0 := by
  simp [scaleTo]

lemma norm_scaleTo (r : ℝ) {z : ℂ} (hz : z ≠ 0) : ‖scaleTo r z‖ = ‖r‖ := by
  rw [scaleTo, norm_smul, norm_div, norm_norm,
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz)]

lemma norm_scaleTo_le (r : ℝ) (z : ℂ) : ‖scaleTo r z‖ ≤ ‖r‖ := by
  by_cases hz : z = 0
  · simp [hz, scaleTo]
  · rw [norm_scaleTo r hz]

lemma scaleTo_norm (z : ℂ) : scaleTo ‖z‖ z = z := by
  by_cases hz : z = 0
  · simp [hz, scaleTo]
  · simp [scaleTo, norm_ne_zero_iff.mpr hz]

 

lemma continuous_scaleTo {X : Type*} [TopologicalSpace X] {r : X → ℝ} {z : X → ℂ}
    (hr : Continuous r) (hz : Continuous z) (hzero : ∀ x, z x = 0 → r x = 0) :
    Continuous (fun x => scaleTo (r x) (z x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : z x = 0
  · change Tendsto (fun x => scaleTo (r x) (z x)) (𝓝 x)
      (𝓝 (scaleTo (r x) (z x)))
    rw [hx, scaleTo_zero]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun x => norm_scaleTo_le (r x) (z x))
    simpa [hzero x hx] using (hr.continuousAt (x := x)).norm.tendsto
  · exact (hr.continuousAt.div hz.continuousAt.norm
      (norm_ne_zero_iff.mpr hx)).smul hz.continuousAt

 
def discriminant (t a b : ℝ) : ℝ :=
  Real.sqrt (((1-t)*(a-b))^2 + 4*a*b)

 
def mass (t a b : ℝ) : ℝ :=
  (discriminant t a b + (1-t)*(a-b))/2

lemma discriminant_swap (t a b : ℝ) : discriminant t b a = discriminant t a b := by
  unfold discriminant
  congr 1
  ring

lemma discriminant_sq (t : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    discriminant t a b ^ 2 = ((1-t)*(a-b))^2 + 4*a*b := by
  apply Real.sq_sqrt
  positivity

lemma mass_nonneg (t : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ mass t a b := by
  have h : -((1-t)*(a-b)) ≤ discriminant t a b := by
    apply Real.le_sqrt_of_sq_le
    have : 0 ≤ 4*a*b := by positivity
    nlinarith
  unfold mass
  linarith

lemma mass_difference (t a b : ℝ) :
    mass t a b - mass t b a = (1-t)*(a-b) := by
  unfold mass
  rw [discriminant_swap]
  ring

lemma mass_product (t : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    mass t a b * mass t b a = a*b := by
  have hd := discriminant_sq t ha hb
  unfold mass
  rw [discriminant_swap t a b]
  nlinarith

lemma mass_at_zero {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : mass 0 a b = a := by
  have h : (a-b)^2+4*a*b = (a+b)^2 := by ring
  simp only [mass, discriminant, sub_zero, one_mul, h, Real.sqrt_sq (add_nonneg ha hb)]
  ring

lemma mass_at_one {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    mass 1 a b = Real.sqrt (a*b) := by
  have h0 := mass_nonneg 1 ha hb
  have h1 := mass_product 1 ha hb
  have h2 := mass_difference 1 a b
  have h3 := Real.sq_sqrt (mul_nonneg ha hb)
  have h4 := Real.sqrt_nonneg (a*b)
  simp only [sub_self, zero_mul] at h2
  nlinarith

lemma mass_zero_left {t b : ℝ} (ht : t ≤ 1) (hb : 0 ≤ b) : mass t 0 b = 0 := by
  have h : (1-t)*(-b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  simp only [mass, discriminant, zero_sub, mul_zero, zero_mul, add_zero,
    Real.sqrt_sq_eq_abs, abs_of_nonpos h]
  ring

lemma mass_same (t a : ℝ) (ha : 0 ≤ a) : mass t a a = a := by
  have h : 4*a*a = (2*a)^2 := by ring
  simp only [mass, discriminant, sub_self, mul_zero, zero_pow (by decide : 2 ≠ 0),
    zero_add, h, Real.sqrt_sq (by linarith : 0 ≤ 2*a), add_zero]
  ring

lemma discriminant_le_add {t a b : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : discriminant t a b ≤ a+b := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg ha hb, ?_⟩
  have ht : (1-t)^2 ≤ 1 := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have h := mul_le_mul_of_nonneg_right ht (sq_nonneg (a-b))
  nlinarith

lemma mass_le_max {t a b : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : mass t a b ≤ max a b := by
  have hd := discriminant_le_add ht0 ht1 ha hb
  unfold mass
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
    have h : (1-t)*(a-b) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith
  · rw [max_eq_left hba]
    have h : (1-t)*(a-b) ≤ a-b := by
      nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hba)]
    linarith

 
def radius (t a b : ℝ) : ℝ := Real.sqrt (mass t (a^2) (b^2))

lemma radius_nonneg (t a b : ℝ) : 0 ≤ radius t a b := Real.sqrt_nonneg _

lemma radius_sq (t a b : ℝ) : radius t a b ^ 2 = mass t (a^2) (b^2) := by
  exact Real.sq_sqrt (mass_nonneg t (sq_nonneg _) (sq_nonneg _))

lemma radius_at_zero {a b : ℝ} (ha : 0 ≤ a) : radius 0 a b = a := by
  rw [radius, mass_at_zero (sq_nonneg _) (sq_nonneg _), Real.sqrt_sq ha]

lemma radius_same (t : ℝ) {a : ℝ} (ha : 0 ≤ a) : radius t a a = a := by
  rw [radius, mass_same t _ (sq_nonneg _), Real.sqrt_sq ha]

lemma radius_zero_left {t b : ℝ} (ht : t ≤ 1) : radius t 0 b = 0 := by
  simp only [radius, zero_pow (by decide : 2 ≠ 0),
    mass_zero_left ht (sq_nonneg b), Real.sqrt_zero]

lemma radius_product (t : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    radius t a b * radius t b a = a*b := by
  have hp : (a^2)*(b^2) = (a*b)^2 := by ring
  rw [radius, radius, ← Real.sqrt_mul (mass_nonneg t (sq_nonneg a) (sq_nonneg b)),
    mass_product t (sq_nonneg a) (sq_nonneg b), hp, Real.sqrt_sq (mul_nonneg ha hb)]

lemma radius_at_one_swap (a b : ℝ) : radius 1 a b = radius 1 b a := by
  simp only [radius, mass_at_one (sq_nonneg _) (sq_nonneg _), mul_comm]

lemma radius_le_max {t a b : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : radius t a b ≤ max a b := by
  have h := mass_le_max ht0 ht1 (sq_nonneg a) (sq_nonneg b)
  apply Real.sqrt_le_iff.mpr
  refine ⟨le_trans ha (le_max_left _ _), ?_⟩
  calc mass t (a^2) (b^2) ≤ max (a^2) (b^2) := h
       _ ≤ (max a b)^2 := max_le
         (by nlinarith [le_max_left a b]) (by nlinarith [le_max_right a b])

lemma continuous_radius : Continuous (fun p : ℝ × ℝ × ℝ => radius p.1 p.2.1 p.2.2) := by
  unfold radius mass discriminant
  fun_prop

open scoped unitInterval

 
def balance (t : I) (p : ℂ × ℂ) : ℂ × ℂ :=
  (scaleTo (radius t ‖p.1‖ ‖p.2‖) p.1,
   scaleTo (radius t ‖p.2‖ ‖p.1‖) p.2)

lemma balance_zero (p : ℂ × ℂ) : balance 0 p = p := by
  simp [balance, radius_at_zero (norm_nonneg _), scaleTo_norm]

lemma norm_balance_fst (t : I) (p : ℂ × ℂ) :
    ‖(balance t p).1‖ = radius t ‖p.1‖ ‖p.2‖ := by
  by_cases hy : p.1 = 0
  · simp [balance, hy, radius_zero_left t.property.2, scaleTo_zero]
  · simp only [balance, norm_scaleTo _ hy, Real.norm_eq_abs,
      abs_of_nonneg (radius_nonneg _ _ _)]

lemma norm_balance_snd (t : I) (p : ℂ × ℂ) :
    ‖(balance t p).2‖ = radius t ‖p.2‖ ‖p.1‖ := by
  by_cases hz : p.2 = 0
  · simp [balance, hz, radius_zero_left t.property.2, scaleTo_zero]
  · simp only [balance, norm_scaleTo _ hz, Real.norm_eq_abs,
      abs_of_nonneg (radius_nonneg _ _ _)]

lemma balance_one_equal_norms (p : ℂ × ℂ) :
    ‖(balance 1 p).1‖ = ‖(balance 1 p).2‖ := by
  rw [norm_balance_fst, norm_balance_snd]
  exact radius_at_one_swap _ _

lemma balance_fixed (t : I) {p : ℂ × ℂ} (hp : ‖p.1‖ = ‖p.2‖) : balance t p = p := by
  apply Prod.ext
  · change scaleTo (radius t ‖p.1‖ ‖p.2‖) p.1 = p.1
    rw [← hp, radius_same t (norm_nonneg _), scaleTo_norm]
  · change scaleTo (radius t ‖p.2‖ ‖p.1‖) p.2 = p.2
    rw [hp, radius_same t (norm_nonneg _), scaleTo_norm]

lemma balance_product (t : I) (p : ℂ × ℂ) :
    (balance t p).1 * (balance t p).2 = p.1*p.2 := by
  by_cases hy : p.1 = 0
  · simp [balance, hy, scaleTo_zero]
  by_cases hz : p.2 = 0
  · simp [balance, hz, scaleTo_zero]
  have hyn : ‖p.1‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hzn : ‖p.2‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hrad := radius_product (t : ℝ) (norm_nonneg p.1) (norm_nonneg p.2)
  have hscale : (radius t ‖p.1‖ ‖p.2‖ / ‖p.1‖) *
      (radius t ‖p.2‖ ‖p.1‖ / ‖p.2‖) = 1 := by
    rw [div_mul_div_comm, hrad, div_self (mul_ne_zero hyn hzn)]
  change ((radius t ‖p.1‖ ‖p.2‖ / ‖p.1‖) • p.1) *
    ((radius t ‖p.2‖ ‖p.1‖ / ‖p.2‖) • p.2) = _
  rw [smul_mul_smul_comm, hscale, one_smul]

lemma balance_bound (t : I) {p : ℂ × ℂ} {M : ℝ}
    (hy : ‖p.1‖ ≤ M) (hz : ‖p.2‖ ≤ M) :
    ‖(balance t p).1‖ ≤ M ∧ ‖(balance t p).2‖ ≤ M := by
  rw [norm_balance_fst, norm_balance_snd]
  exact ⟨(radius_le_max t.property.1 t.property.2 (norm_nonneg _) (norm_nonneg _)).trans
    (max_le hy hz),
    (radius_le_max t.property.1 t.property.2 (norm_nonneg _) (norm_nonneg _)).trans
    (max_le hz hy)⟩

lemma continuous_balance : Continuous (fun p : I × (ℂ × ℂ) => balance p.1 p.2) := by
  have ht : Continuous (fun p : I × (ℂ × ℂ) => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hy : Continuous (fun p : I × (ℂ × ℂ) => p.2.1) := continuous_snd.fst
  have hz : Continuous (fun p : I × (ℂ × ℂ) => p.2.2) := continuous_snd.snd
  have hr1 : Continuous (fun p : I × (ℂ × ℂ) => radius p.1 ‖p.2.1‖ ‖p.2.2‖) :=
    continuous_radius.comp (ht.prodMk (hy.norm.prodMk hz.norm))
  have hr2 : Continuous (fun p : I × (ℂ × ℂ) => radius p.1 ‖p.2.2‖ ‖p.2.1‖) :=
    continuous_radius.comp (ht.prodMk (hz.norm.prodMk hy.norm))
  have hc1 := continuous_scaleTo hr1 hy (by
    intro p hp
    simp [hp, radius_zero_left p.1.property.2])
  have hc2 := continuous_scaleTo hr2 hz (by
    intro p hp
    simp [hp, radius_zero_left p.1.property.2])
  exact hc1.prodMk hc2

 
def coreCoords (c : ℂ) (u : Circle) : ℂ × ℂ :=
  ((Real.sqrt ‖c‖) • (u : ℂ), scaleTo (Real.sqrt ‖c‖) c * (u : ℂ)⁻¹)

lemma coreCoords_zero (u : Circle) : coreCoords 0 u = (0, 0) := by
  simp [coreCoords, scaleTo_zero]

lemma coreCoords_norm_fst (c : ℂ) (u : Circle) :
    ‖(coreCoords c u).1‖ = Real.sqrt ‖c‖ := by
  simp [coreCoords, Circle.norm_coe, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

lemma coreCoords_norm_snd (c : ℂ) (u : Circle) :
    ‖(coreCoords c u).2‖ = Real.sqrt ‖c‖ := by
  by_cases hc : c = 0
  · simp [hc, coreCoords_zero]
  · simp [coreCoords, norm_inv, norm_scaleTo _ hc,
      Circle.norm_coe, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

lemma coreCoords_product (c : ℂ) (u : Circle) :
    (coreCoords c u).1 * (coreCoords c u).2 = c := by
  by_cases hc : c = 0
  · simp [hc, coreCoords_zero]
  have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have ha : Real.sqrt ‖c‖ * (Real.sqrt ‖c‖ / ‖c‖) = 1 := by
    rw [← mul_div_assoc, ← pow_two, Real.sq_sqrt (norm_nonneg c), div_self hn]
  change (Real.sqrt ‖c‖ • (u : ℂ)) *
    (((Real.sqrt ‖c‖ / ‖c‖) • c) * (u : ℂ)⁻¹) = c
  rw [← mul_assoc, smul_mul_smul_comm, smul_mul_assoc, ha, one_smul]
  rw [mul_comm (u : ℂ) c, mul_assoc, mul_inv_cancel₀ (Circle.coe_ne_zero u), mul_one]

lemma continuous_coreCoords : Continuous (fun p : ℂ × Circle => coreCoords p.1 p.2) := by
  have ha : Continuous (fun p : ℂ × Circle => Real.sqrt ‖p.1‖) := continuous_fst.norm.sqrt
  have hu : Continuous (fun p : ℂ × Circle => (p.2 : ℂ)) :=
    continuous_subtype_val.comp continuous_snd
  have hs := continuous_scaleTo ha continuous_fst (by
    intro p hp
    simp [hp])
  exact (ha.smul hu).prodMk (hs.mul (hu.inv₀ (fun p => Circle.coe_ne_zero p.2)))

lemma coreCoords_eq_iff (c : ℂ) (u v : Circle) :
    coreCoords c u = coreCoords c v ↔ c = 0 ∨ u = v := by
  by_cases hc : c = 0
  · simp [hc, coreCoords_zero]
  · have ha : Real.sqrt ‖c‖ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (norm_pos_iff.mpr hc))
    constructor
    · intro h
      right
      apply Circle.ext
      have hf : Real.sqrt ‖c‖ • (u : ℂ) = Real.sqrt ‖c‖ • (v : ℂ) :=
        congrArg Prod.fst h
      have hi := congrArg (fun z : ℂ => (Real.sqrt ‖c‖)⁻¹ • z) hf
      simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using hi
    · rintro (h | rfl)
      · exact (hc h).elim
      · rfl

lemma coreCoords_surj {c : ℂ} (p : ℂ × ℂ)
    (hp : p.1*p.2 = c) (hn : ‖p.1‖ = ‖p.2‖) : ∃ u : Circle, coreCoords c u = p := by
  have hc : ‖c‖ = ‖p.1‖^2 := by rw [← hp, norm_mul, ← hn, pow_two]
  have ha : Real.sqrt ‖c‖ = ‖p.1‖ := by rw [hc, Real.sqrt_sq (norm_nonneg _)]
  by_cases hy : p.1 = 0
  · have hz : p.2 = 0 := norm_eq_zero.mp (by simpa [hy] using hn.symm)
    have hc0 : c = 0 := by simp [hy] at hp; exact hp.symm
    refine ⟨1, ?_⟩
    apply Prod.ext <;> simp [hc0, coreCoords_zero, hy, hz]
  · have hyn : ‖p.1‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    let u : Circle := ⟨‖p.1‖⁻¹ • p.1, mem_sphere_zero_iff_norm.mpr (by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hyn])⟩
    have hfirst : (coreCoords c u).1 = p.1 := by
      change Real.sqrt ‖c‖ • (‖p.1‖⁻¹ • p.1) = p.1
      rw [ha, ← mul_smul, mul_inv_cancel₀ hyn, one_smul]
    refine ⟨u, Prod.ext hfirst ?_⟩
    apply mul_left_cancel₀ hy
    rw [← hfirst, coreCoords_product]
    simpa only [hfirst] using hp.symm

section Blocks
variable {G : Type*} [TopologicalSpace G]

 

abbrev ConicBlock (R : G → ℂ) (M : ℝ) :=
  {p : G × (ℂ × ℂ) // p.2.1 * p.2.2 = R p.1 ∧ ‖p.2.1‖ ≤ M ∧ ‖p.2.2‖ ≤ M}

abbrev BalancedBlock (R : G → ℂ) (M : ℝ) :=
  {p : ConicBlock R M // ‖p.val.2.1‖ = ‖p.val.2.2‖}

variable (R : G → ℂ) (M : ℝ)

def balanceBlock (t : I) (p : ConicBlock R M) : ConicBlock R M :=
  ⟨(p.val.1, balance t p.val.2), by
    refine ⟨?_, balance_bound t p.property.2.1 p.property.2.2⟩
    exact (balance_product t p.val.2).trans p.property.1⟩

lemma continuous_balanceBlock :
    Continuous (fun p : I × ConicBlock R M => balanceBlock R M p.1 p.2) := by
  have hc : Continuous (fun p : I × ConicBlock R M => p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hp : Continuous (fun p : I × ConicBlock R M => (p.1, p.2.val.2)) :=
    continuous_fst.prodMk hc.snd
  have hb := continuous_balance.comp hp
  exact (hc.fst.prodMk hb).subtype_mk _

omit [TopologicalSpace G] in
lemma balanceBlock_zero (p : ConicBlock R M) : balanceBlock R M 0 p = p := by
  apply Subtype.ext
  change (p.val.1, balance 0 p.val.2) = p.val
  rw [balance_zero]

omit [TopologicalSpace G] in
lemma balanceBlock_fixed (t : I) {p : ConicBlock R M}
    (hp : ‖p.val.2.1‖ = ‖p.val.2.2‖) : balanceBlock R M t p = p := by
  apply Subtype.ext
  change (p.val.1, balance t p.val.2) = p.val
  rw [balance_fixed t hp]

 
def coreInclusion : C(BalancedBlock R M, ConicBlock R M) :=
  ⟨Subtype.val, continuous_subtype_val⟩

 
def coreRetraction : C(ConicBlock R M, BalancedBlock R M) where
  toFun p := ⟨balanceBlock R M 1 p, balance_one_equal_norms p.val.2⟩
  continuous_toFun := (continuous_balanceBlock R M |>.comp
    (continuous_const.prodMk continuous_id)).subtype_mk _

lemma coreRetraction_inclusion (p : BalancedBlock R M) :
    coreRetraction R M (coreInclusion R M p) = p := by
  apply Subtype.ext
  exact balanceBlock_fixed R M 1 p.property

 
def blockHomotopy : ContinuousMap.Homotopy (ContinuousMap.id (ConicBlock R M))
    ((coreInclusion R M).comp (coreRetraction R M)) where
  toFun p := balanceBlock R M p.1 p.2
  continuous_toFun := continuous_balanceBlock R M
  map_zero_left := balanceBlock_zero R M
  map_one_left _ := rfl

 

lemma blockHomotopy_fixed (t : I) (p : BalancedBlock R M) :
    blockHomotopy R M (t, coreInclusion R M p) = coreInclusion R M p :=
  balanceBlock_fixed R M t p.property

 
def blockCoreHomotopyEquiv : ContinuousMap.HomotopyEquiv (ConicBlock R M) (BalancedBlock R M) where
  toFun := coreRetraction R M
  invFun := coreInclusion R M
  left_inv := ⟨(blockHomotopy R M).symm⟩
  right_inv := by
    have h : (coreRetraction R M).comp (coreInclusion R M) =
        ContinuousMap.id (BalancedBlock R M) := by
      apply ContinuousMap.ext
      intro p
      exact coreRetraction_inclusion R M p
    rw [h]

 

def collapseSetoid : Setoid (G × Circle) where
  r p q := p.1 = q.1 ∧ (R p.1 = 0 ∨ p.2 = q.2)
  iseqv := {
    refl := fun _ => ⟨rfl, Or.inr rfl⟩
    symm := by
      rintro p q ⟨hb, hc⟩
      refine ⟨hb.symm, ?_⟩
      rcases hc with hc | hc
      · exact Or.inl (hb ▸ hc)
      · exact Or.inr hc.symm
    trans := by
      rintro p q r ⟨hb1, hc1⟩ ⟨hb2, hc2⟩
      refine ⟨hb1.trans hb2, ?_⟩
      rcases hc1 with hc1 | hc1
      · exact Or.inl hc1
      rcases hc2 with hc2 | hc2
      · exact Or.inl (hb1 ▸ hc2)
      · exact Or.inr (hc1.trans hc2) }

abbrev CircleCollapse := Quotient (collapseSetoid R)

variable (hbound : ∀ g, Real.sqrt ‖R g‖ ≤ M)

 
def coreParam (p : G × Circle) : BalancedBlock R M :=
  ⟨⟨(p.1, coreCoords (R p.1) p.2), by
    refine ⟨coreCoords_product _ _, ?_, ?_⟩
    · rw [coreCoords_norm_fst]; exact hbound p.1
    · rw [coreCoords_norm_snd]; exact hbound p.1⟩, by
    exact (coreCoords_norm_fst _ _).trans (coreCoords_norm_snd _ _).symm⟩

lemma continuous_coreParam (hR : Continuous R) : Continuous (coreParam R M hbound) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_fst.prodMk (continuous_coreCoords.comp
    ((hR.comp continuous_fst).prodMk continuous_snd))

omit [TopologicalSpace G] in
lemma coreParam_eq_iff (p q : G × Circle) :
    coreParam R M hbound p = coreParam R M hbound q ↔ collapseSetoid R p q := by
  constructor
  · intro h
    have hb : p.1 = q.1 := congrArg (fun x : BalancedBlock R M => x.val.val.1) h
    have hc : coreCoords (R p.1) p.2 = coreCoords (R q.1) q.2 :=
      congrArg (fun x : BalancedBlock R M => x.val.val.2) h
    refine ⟨hb, ?_⟩
    rw [← hb] at hc
    exact (coreCoords_eq_iff _ _ _).mp hc
  · rintro ⟨hb, hc⟩
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · exact hb
    change coreCoords (R p.1) p.2 = coreCoords (R q.1) q.2
    rw [← hb]
    exact (coreCoords_eq_iff _ _ _).mpr hc

omit [TopologicalSpace G] in
lemma coreParam_surjective : Function.Surjective (coreParam R M hbound) := by
  intro p
  obtain ⟨u, hu⟩ := coreCoords_surj p.val.val.2 p.val.property.1 p.property
  refine ⟨(p.val.val.1, u), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext rfl hu

 
def collapseToCore : CircleCollapse R → BalancedBlock R M :=
  Quotient.lift (coreParam R M hbound)
    (fun p q h => (coreParam_eq_iff R M hbound p q).mpr h)

lemma continuous_collapseToCore (hR : Continuous R) :
    Continuous (collapseToCore R M hbound) :=
  (continuous_coreParam R M hbound hR).quotient_lift _

omit [TopologicalSpace G] in
lemma collapseToCore_bijective : Function.Bijective (collapseToCore R M hbound) := by
  constructor
  · intro p q
    induction p using Quotient.inductionOn with | h p =>
      induction q using Quotient.inductionOn with | h q =>
        intro h
        exact Quotient.sound ((coreParam_eq_iff R M hbound p q).mp h)
  · intro p
    obtain ⟨q, hq⟩ := coreParam_surjective R M hbound p
    exact ⟨Quotient.mk _ q, hq⟩

 

def collapseCoreHomeomorph [CompactSpace G] [T2Space G] (hR : Continuous R) :
    CircleCollapse R ≃ₜ BalancedBlock R M :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (collapseToCore R M hbound) (collapseToCore_bijective R M hbound))
    (continuous_collapseToCore R M hbound hR)

 

def blockCollapseHomotopyEquiv [CompactSpace G] [T2Space G] (hR : Continuous R) :
    ContinuousMap.HomotopyEquiv (ConicBlock R M) (CircleCollapse R) :=
  (blockCoreHomotopyEquiv R M).trans (collapseCoreHomeomorph R M hbound hR).symm.toHomotopyEquiv

 
abbrev WeightedConicBlock (scale : ℝ) :=
  {p : G × (ℂ × ℂ) // p.2.1*p.2.2 = R p.1 ∧
    ‖p.2.1‖ ≤ scale*M ∧ ‖p.2.2‖ ≤ scale⁻¹*M}

 

def normalizeBlock (scale : ℝ) (hscale : 0 < scale) :
    WeightedConicBlock R M scale ≃ₜ ConicBlock R M where
  toFun p := ⟨(p.val.1, scale⁻¹ • p.val.2.1, scale • p.val.2.2), by
    refine ⟨?_, ?_, ?_⟩
    · rw [smul_mul_smul_comm, inv_mul_cancel₀ hscale.ne', one_smul]
      exact p.property.1
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hscale)]
      have hh := mul_le_mul_of_nonneg_left p.property.2.1 (inv_nonneg.mpr hscale.le)
      simpa only [← mul_assoc, inv_mul_cancel₀ hscale.ne', one_mul] using hh
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hscale]
      have hh := mul_le_mul_of_nonneg_left p.property.2.2 hscale.le
      simpa only [← mul_assoc, mul_inv_cancel₀ hscale.ne', one_mul] using hh⟩
  invFun p := ⟨(p.val.1, scale • p.val.2.1, scale⁻¹ • p.val.2.2), by
    refine ⟨?_, ?_, ?_⟩
    · rw [smul_mul_smul_comm, mul_inv_cancel₀ hscale.ne', one_smul]
      exact p.property.1
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hscale]
      exact mul_le_mul_of_nonneg_left p.property.2.1 hscale.le
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hscale)]
      exact mul_le_mul_of_nonneg_left p.property.2.2 (inv_nonneg.mpr hscale.le)⟩
  left_inv p := by
    apply Subtype.ext
    simp only [← mul_smul, mul_inv_cancel₀ hscale.ne', inv_mul_cancel₀ hscale.ne', one_smul]
  right_inv p := by
    apply Subtype.ext
    simp only [← mul_smul, mul_inv_cancel₀ hscale.ne', inv_mul_cancel₀ hscale.ne', one_smul]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.fst.prodMk
      ((continuous_subtype_val.snd.fst.const_smul scale⁻¹).prodMk
        (continuous_subtype_val.snd.snd.const_smul scale))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.fst.prodMk
      ((continuous_subtype_val.snd.fst.const_smul scale).prodMk
        (continuous_subtype_val.snd.snd.const_smul scale⁻¹))

 

def weightedBlockCollapseHomotopyEquiv [CompactSpace G] [T2Space G]
    (hR : Continuous R) (scale : ℝ) (hscale : 0 < scale) :
    ContinuousMap.HomotopyEquiv (WeightedConicBlock R M scale) (CircleCollapse R) :=
  (normalizeBlock R M scale hscale).toHomotopyEquiv.trans
    (blockCollapseHomotopyEquiv R M hbound hR)

end Blocks

section SingularHomology
open CategoryTheory AlgebraicTopology

 

abbrev integralHomologyFunctor (n : ℕ) : TopCat ⥤ ModuleCat ℤ :=
  (singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)

abbrev IntegralHomology (n : ℕ) (X : Type) [TopologicalSpace X] : ModuleCat ℤ :=
  (integralHomologyFunctor n).obj (TopCat.of X)

lemma integralHomologyMap_eq_of_homotopic {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X,Y)}
    (h : f.Homotopic g) (n : ℕ) :
    (integralHomologyFunctor n).map (TopCat.ofHom f) =
      (integralHomologyFunctor n).map (TopCat.ofHom g) := by
  obtain ⟨H⟩ := h
  exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (f := TopCat.ofHom f) (g := TopCat.ofHom g) H (ModuleCat.of ℤ ℤ) n

 

def integralHomologyIso {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    IntegralHomology n X ≅ IntegralHomology n Y where
  hom := (integralHomologyFunctor n).map (TopCat.ofHom e.toFun)
  inv := (integralHomologyFunctor n).map (TopCat.ofHom e.invFun)
  hom_inv_id := by
    rw [← Functor.map_comp]
    change (integralHomologyFunctor n).map (TopCat.ofHom (e.invFun.comp e.toFun)) = _
    rw [integralHomologyMap_eq_of_homotopic e.left_inv]
    exact (integralHomologyFunctor n).map_id _
  inv_hom_id := by
    rw [← Functor.map_comp]
    change (integralHomologyFunctor n).map (TopCat.ofHom (e.toFun.comp e.invFun)) = _
    rw [integralHomologyMap_eq_of_homotopic e.right_inv]
    exact (integralHomologyFunctor n).map_id _

 

def weightedBlockHomologyIso {G : Type} [TopologicalSpace G] [CompactSpace G]
    [T2Space G] (R : G → ℂ) (hR : Continuous R) (M : ℝ)
    (hbound : ∀ g, Real.sqrt ‖R g‖ ≤ M) (scale : ℝ) (hscale : 0 < scale) (n : ℕ) :
    IntegralHomology n (WeightedConicBlock R M scale) ≅
      IntegralHomology n (CircleCollapse R) :=
  integralHomologyIso (weightedBlockCollapseHomotopyEquiv R M hbound hR scale hscale) n

end SingularHomology
end
end AmbientMultiplicity.InnerGeometry

end OAI
