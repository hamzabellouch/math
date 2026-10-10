import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Model

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

namespace ShearFlows
def shearX (a : ℝ) (v : Plane) : Plane := ![v 0 + a * v 1, v 1]
def shearY (a : ℝ) (v : Plane) : Plane := ![v 0, v 1 + a * v 0]

def scalingEndpoints (lam : ℝ) (v : Plane) : Fin 5 → Plane :=
  ![v,
    ![v 0, v 1 - lam * v 0],
    ![lam * v 0 + (lam⁻¹ - 1) * v 1, v 1 - lam * v 0],
    ![lam * v 0 + (lam⁻¹ - 1) * v 1, v 1 / lam],
    ![lam * v 0, v 1 / lam]]

def partialShear (lam : ℝ) (k : Fin 4) (θ : ℝ) : Plane → Plane :=
  ![shearY (θ * (-lam)), shearX (θ * (lam⁻¹ - 1)),
    shearY θ, shearX (θ * (lam - 1))] k

theorem four_shears {lam : ℝ} (hlam : lam ≠ 0) (v : Plane) :
    shearX (lam - 1) (shearY 1 (shearX (lam⁻¹ - 1) (shearY (-lam) v))) =
      ![lam * v 0, v 1 / lam] := by
  ext j
  fin_cases j <;> simp [shearX, shearY] <;> field_simp <;> ring

theorem partial_shear_is_segment {lam : ℝ} (hlam : lam ≠ 0)
    (v : Plane) (k : Fin 4) (θ : ℝ) :
    partialShear lam k θ (scalingEndpoints lam v k.castSucc) =
      (1 - θ) • scalingEndpoints lam v k.castSucc +
        θ • scalingEndpoints lam v k.succ := by
  ext j
  fin_cases k <;> fin_cases j <;>
    simp [partialShear, scalingEndpoints, shearX, shearY, Pi.smul_apply,
      smul_eq_mul] <;> field_simp <;> ring

theorem reciprocal_correction_bound {lam s h : ℝ} (hlam : 0 < lam)
    (hs : |s| ≤ h) (hslam : |s / lam| ≤ h) :
    |(lam⁻¹ - 1) * s| ≤ h := by
  have heq : (lam⁻¹ - 1) * s = s / lam - s := by ring
  rw [heq, abs_le]
  obtain ⟨hslo, hshi⟩ := abs_le.mp hs
  obtain ⟨hqlo, hqhi⟩ := abs_le.mp hslam
  rcases le_total 0 s with hsign | hsign
  · have hq : 0 ≤ s / lam := div_nonneg hsign hlam.le
    constructor <;> linarith
  · have hq : s / lam ≤ 0 := div_nonpos_of_nonpos_of_nonneg hsign hlam.le
    constructor <;> linarith

theorem norm_segment_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E} {R θ : ℝ} (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R)
    (hθ : θ ∈ Icc (0 : ℝ) 1) :
    ‖(1 - θ) • a + θ • b‖ ≤ R := by
  have hnonneg : 0 ≤ 1 - θ := sub_nonneg.mpr hθ.2
  calc
    ‖(1 - θ) • a + θ • b‖ ≤ ‖(1 - θ) • a‖ + ‖θ • b‖ := norm_add_le _ _
    _ = (1 - θ) * ‖a‖ + θ * ‖b‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hθ.1]
    _ ≤ (1 - θ) * R + θ * R :=
      add_le_add (mul_le_mul_of_nonneg_left ha hnonneg)
        (mul_le_mul_of_nonneg_left hb hθ.1)
    _ = R := by ring

theorem scaling_endpoints_bound {lam h : ℝ} (hlam : 0 < lam) (hh : 0 ≤ h)
    (v : Plane) (hr : |v 0| ≤ h) (hs : |v 1| ≤ h)
    (hlamr : |lam * v 0| ≤ h) (hslam : |v 1 / lam| ≤ h) :
    ∀ k, ‖scalingEndpoints lam v k‖ ≤ 2 * h := by
  have hc := reciprocal_correction_bound hlam hs hslam
  have hx : |lam * v 0 + (lam⁻¹ - 1) * v 1| ≤ 2 * h :=
    (abs_add_le _ _).trans (by linarith)
  have hy : |v 1 - lam * v 0| ≤ 2 * h :=
    (abs_sub _ _).trans (by linarith)
  intro k
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * h)).2
  intro j
  simp only [abs_mul, abs_div] at hlamr hslam
  fin_cases k <;> fin_cases j <;>
    simp [scalingEndpoints, Real.norm_eq_abs] <;> linarith

theorem excursion {lam h : ℝ} (hlam : 0 < lam) (hh : 0 < h)
    (v : Plane) (hr : |v 0| ≤ h) (hs : |v 1| ≤ h)
    (hlamr : |lam * v 0| ≤ h) (hslam : |v 1 / lam| ≤ h) :
    shearX (lam - 1) (shearY 1 (shearX (lam⁻¹ - 1) (shearY (-lam) v))) =
        ![lam * v 0, v 1 / lam] ∧
      (∀ k, ‖scalingEndpoints lam v k‖ ≤ 2 * h) ∧
      (∀ (k : Fin 4) (θ : ℝ), θ ∈ Icc (0 : ℝ) 1 →
        ‖partialShear lam k θ (scalingEndpoints lam v k.castSucc)‖ ≤ 2 * h) := by
  have hb := scaling_endpoints_bound hlam hh.le v hr hs hlamr hslam
  refine ⟨four_shears hlam.ne' v, hb, ?_⟩
  intro k θ hθ
  rw [partial_shear_is_segment hlam.ne']
  exact norm_segment_le (hb _) (hb _) hθ

namespace RationalBox

theorem mem_iff_abs_sub_center_le {n : ℕ} (B : RationalBox n) (x : Fin n → ℝ) :
    x ∈ B.carrier ↔ ∀ j, |x j - B.center j| ≤ B.halfWidth j := by
  constructor
  · intro hx j
    obtain ⟨hlo, hhi⟩ := hx j
    change |x j - ((B.lower j : ℝ) + (B.upper j : ℝ)) / 2| ≤
      ((B.upper j : ℝ) - (B.lower j : ℝ)) / 2
    rw [abs_le]
    constructor <;> linarith
  · intro hx j
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hx j)
    change -(((B.upper j : ℝ) - (B.lower j : ℝ)) / 2) ≤
      x j - ((B.lower j : ℝ) + (B.upper j : ℝ)) / 2 at hlo
    change x j - ((B.lower j : ℝ) + (B.upper j : ℝ)) / 2 ≤
      ((B.upper j : ℝ) - (B.lower j : ℝ)) / 2 at hhi
    constructor <;> linarith

end RationalBox

theorem instruction_offset_bounds {d : Input} (hd : ValidInput d)
    {b : Instruction} (hb : b ∈ d.instructions)
    {X : Plane} (hX : X ∈ b.source.carrier) :
    |X 0 - b.source.center 0| ≤ (d.h : ℝ) ∧
    |X 1 - b.source.center 1| ≤ (d.h : ℝ) ∧
    |(b.factor : ℝ) * (X 0 - b.source.center 0)| ≤ (d.h : ℝ) ∧
    |(X 1 - b.source.center 1) / (b.factor : ℝ)| ≤ (d.h : ℝ) := by
  have hs := (b.source.mem_iff_abs_sub_center_le X).mp hX
  have hF : b.affine X ∈ b.target.carrier := by
    rw [← hd.image_eq b hb]
    exact ⟨X, hX, rfl⟩
  have ht := (b.target.mem_iff_abs_sub_center_le (b.affine X)).mp hF
  refine ⟨(hs 0).trans (hd.halfWidths b hb 0).1,
    (hs 1).trans (hd.halfWidths b hb 1).1, ?_, ?_⟩
  · simpa [Instruction.affine] using (ht 0).trans (hd.halfWidths b hb 0).2
  · simpa [Instruction.affine] using (ht 1).trans (hd.halfWidths b hb 1).2

def scalingStage (b : Instruction) (k : Fin 4) (θ : ℝ) (X : Plane) : Plane :=
  b.source.center + partialShear b.factor k θ
    (scalingEndpoints b.factor (X - b.source.center) k.castSucc)

theorem scalingStage_bound {d : Input} (hd : ValidInput d)
    {b : Instruction} (hb : b ∈ d.instructions)
    {X : Plane} (hX : X ∈ b.source.carrier)
    (k : Fin 4) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    ‖scalingStage b k θ X - b.source.center‖ ≤ 2 * (d.h : ℝ) := by
  obtain ⟨hr, hs, hlamr, hslam⟩ := instruction_offset_bounds hd hb hX
  have hlam : (0 : ℝ) < b.factor := by exact_mod_cast hd.factor_pos b hb
  have hh : (0 : ℝ) < d.h := by exact_mod_cast hd.h_pos
  have h := (excursion hlam hh (X - b.source.center) hr hs hlamr hslam).2.2 k θ hθ
  simpa [scalingStage, add_sub_cancel_left] using h

theorem scaledOffset_bound {d : Input} (hd : ValidInput d)
    {b : Instruction} (hb : b ∈ d.instructions)
    {X : Plane} (hX : X ∈ b.source.carrier) :
    ‖scaledOffset b X‖ ≤ (d.h : ℝ) := by
  obtain ⟨_, _, hr, hs⟩ := instruction_offset_bounds hd hb hX
  apply (pi_norm_le_iff_of_nonneg (by exact_mod_cast hd.h_pos.le)).2
  intro j
  fin_cases j
  · change ‖(b.factor : ℝ) * (X 0 - b.source.center 0)‖ ≤ (d.h : ℝ)
    simpa only [Real.norm_eq_abs] using hr
  · change ‖(X 1 - b.source.center 1) / (b.factor : ℝ)‖ ≤ (d.h : ℝ)
    simpa only [Real.norm_eq_abs] using hs

theorem center_segment_mem {d : Input} (hd : ValidInput d)
    {b : Instruction} (hb : b ∈ d.instructions)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    (1 - θ) • b.source.center + θ • b.target.center ∈ d.centers.carrier := by
  intro j
  obtain ⟨hp₁, hp₂⟩ := hd.source_centers b hb j
  obtain ⟨hq₁, hq₂⟩ := hd.target_centers b hb j
  have hθ' : 0 ≤ 1 - θ := sub_nonneg.mpr hθ.2
  change (d.centers.lower j : ℝ) ≤
      (1 - θ) * b.source.center j + θ * b.target.center j ∧
    (1 - θ) * b.source.center j + θ * b.target.center j ≤ (d.centers.upper j : ℝ)
  constructor
  · have hp := mul_le_mul_of_nonneg_left hp₁ hθ'
    have hq := mul_le_mul_of_nonneg_left hq₁ hθ.1
    nlinarith
  · have hp := mul_le_mul_of_nonneg_left hp₂ hθ'
    have hq := mul_le_mul_of_nonneg_left hq₂ hθ.1
    nlinarith

theorem within_margin_in_planar_chart {d : Input} (hd : ValidInput d)
    {p X : Plane} (hp : p ∈ d.centers.carrier)
    (hX : ‖X - p‖ ≤ 2 * (d.h : ℝ)) : d.inPlanarChart X := by
  have hh : (0 : ℝ) < d.h := by exact_mod_cast hd.h_pos
  have hcoord := (pi_norm_le_iff_of_nonneg
    (show 0 ≤ 2 * (d.h : ℝ) by linarith)).mp hX
  intro j
  have hj : |X j - p j| ≤ 2 * (d.h : ℝ) := by simpa using hcoord j
  obtain ⟨hm₁, hm₂⟩ := hd.chartMargin j
  obtain ⟨hp₁, hp₂⟩ := hp j
  obtain ⟨hlo, hhi⟩ := abs_le.mp hj
  constructor <;> linarith

theorem scalingStage_in_chart {d : Input} (hd : ValidInput d)
    {b : Instruction} (hb : b ∈ d.instructions)
    {X : Plane} (hX : X ∈ b.source.carrier)
    (k : Fin 4) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    d.inPlanarChart (scalingStage b k θ X) :=
  within_margin_in_planar_chart hd (hd.source_centers b hb)
    (scalingStage_bound hd hb hX k hθ)

theorem translation_in_chart {d : Input} (hd : ValidInput d)
    {b : Instruction} (hb : b ∈ d.instructions)
    {X : Plane} (hX : X ∈ b.source.carrier)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    d.inPlanarChart ((1 - θ) • b.source.center + θ • b.target.center +
      scaledOffset b X) := by
  apply within_margin_in_planar_chart hd (center_segment_mem hd hb hθ)
  have hh : (0 : ℝ) < d.h := by exact_mod_cast hd.h_pos
  simpa only [add_sub_cancel_left] using
    (scaledOffset_bound hd hb hX).trans (show (d.h : ℝ) ≤ 2 * (d.h : ℝ) by linarith)

def prefixBound (lam : ℝ) : ℝ := 2 * (1 + lam + lam⁻¹)

theorem prefixBound_ge_one {lam : ℝ} (hlam : 0 < lam) : 1 ≤ prefixBound lam := by
  have hi : 0 < lam⁻¹ := inv_pos.mpr hlam
  unfold prefixBound
  linarith

theorem scalingEndpoints_sub (lam : ℝ) (v w : Plane) (k : Fin 5) :
    scalingEndpoints lam (v - w) k =
      scalingEndpoints lam v k - scalingEndpoints lam w k := by
  ext j
  fin_cases k <;> fin_cases j <;> simp [scalingEndpoints] <;> ring

theorem scalingEndpoints_lipschitz {lam : ℝ} (hlam : 0 < lam)
    (v w : Plane) (k : Fin 5) :
    ‖scalingEndpoints lam v k - scalingEndpoints lam w k‖ ≤
      prefixBound lam * ‖v - w‖ := by
  let R := ‖v - w‖
  let A := 1 + lam + lam⁻¹
  have hR : 0 ≤ R := norm_nonneg _
  have hi : 0 ≤ lam⁻¹ := (inv_pos.mpr hlam).le
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h1 : 1 ≤ A := by dsimp [A]; linarith
  have hlA : lam ≤ A := by dsimp [A]; linarith
  have hiA : lam⁻¹ ≤ A := by dsimp [A]; linarith
  have hRle : R ≤ A * R := by nlinarith
  have habs (j : Fin 2) : |(v - w) j| ≤ R := norm_le_pi_norm (v-w) j
  have h0 : |(v - w) 0| ≤ A * R := (habs 0).trans hRle
  have h1' : |(v - w) 1| ≤ A * R := (habs 1).trans hRle
  have hmul : |lam * (v - w) 0| ≤ A * R := by
    rw [abs_mul, abs_of_pos hlam]
    exact (mul_le_mul_of_nonneg_left (habs 0) hlam.le).trans
      (mul_le_mul_of_nonneg_right hlA hR)
  have hdiv : |(v - w) 1 / lam| ≤ A * R := by
    rw [div_eq_mul_inv, abs_mul, abs_of_nonneg hi]
    calc
      |(v - w) 1| * lam⁻¹ ≤ R * lam⁻¹ := mul_le_mul_of_nonneg_right (habs 1) hi
      _ ≤ R * A := mul_le_mul_of_nonneg_left hiA hR
      _ = A * R := mul_comm _ _
  rw [← scalingEndpoints_sub]
  have hbound := scaling_endpoints_bound hlam (mul_nonneg hA hR)
    (v - w) h0 h1' hmul hdiv k
  simpa only [prefixBound, R, A, mul_assoc] using hbound

theorem scalingStage_lipschitz {b : Instruction} (hb : 0 < b.factor)
    (X Y : Plane) (k : Fin 4) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    ‖scalingStage b k θ X - scalingStage b k θ Y‖ ≤
      prefixBound b.factor * ‖X - Y‖ := by
  have hlam : (0 : ℝ) < b.factor := by exact_mod_cast hb
  let v := X - b.source.center
  let w := Y - b.source.center
  have hdiff : v - w = X - Y := by dsimp [v, w]; abel
  have heq : scalingStage b k θ X - scalingStage b k θ Y =
      (1 - θ) • (scalingEndpoints b.factor v k.castSucc -
        scalingEndpoints b.factor w k.castSucc) +
      θ • (scalingEndpoints b.factor v k.succ - scalingEndpoints b.factor w k.succ) := by
    simp only [scalingStage, partial_shear_is_segment hlam.ne', smul_sub]
    dsimp [v, w]
    abel
  rw [heq]
  have h₀ := scalingEndpoints_lipschitz hlam v w k.castSucc
  have h₁ := scalingEndpoints_lipschitz hlam v w k.succ
  rw [hdiff] at h₀ h₁
  exact norm_segment_le h₀ h₁ hθ

theorem prefixBound_rational (r : ℚ) :
    prefixBound (r : ℝ) = ((2 * (1 + r + r⁻¹) : ℚ) : ℝ) := by
  simp [prefixBound]

theorem scalingStage_start {b : Instruction} (hb : b.factor ≠ 0)
    (X : Plane) (k : Fin 4) :
    scalingStage b k 0 X = b.source.center +
      scalingEndpoints b.factor (X - b.source.center) k.castSucc := by
  have h : (b.factor : ℝ) ≠ 0 := by exact_mod_cast hb
  simp [scalingStage, partial_shear_is_segment h]

theorem scalingStage_finish {b : Instruction} (hb : b.factor ≠ 0)
    (X : Plane) (k : Fin 4) :
    scalingStage b k 1 X = b.source.center +
      scalingEndpoints b.factor (X - b.source.center) k.succ := by
  have h : (b.factor : ℝ) ≠ 0 := by exact_mod_cast hb
  simp [scalingStage, partial_shear_is_segment h]

theorem affine_eq_target_add_scaledOffset (b : Instruction) (X : Plane) :
    b.affine X = b.target.center + scaledOffset b X := by
  ext j
  fin_cases j <;> rfl

theorem scaling_final_endpoint {b : Instruction} (hb : b.factor ≠ 0) (X : Plane) :
    scalingStage b 3 1 X = b.source.center + scaledOffset b X := by
  rw [scalingStage_finish hb]
  rfl

end ShearFlows

end

end OAI
