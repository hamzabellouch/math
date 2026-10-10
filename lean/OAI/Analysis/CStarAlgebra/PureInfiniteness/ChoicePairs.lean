import OAI.Analysis.CStarAlgebra.PureInfiniteness.Cutoffs

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance choicePairsPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance choicePairsStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

lemma norm_sqrt_le_one {d : A} (hd : 0 ≤ d) (hn : ‖d‖ ≤ 1) : ‖CFC.sqrt d‖ ≤ 1 := by
  have hh : ‖CFC.sqrt d‖ ^ 2 = ‖d‖ := by
    rw [pow_two, ← CStarRing.norm_star_mul_self,
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg d)).star_eq, CFC.sqrt_mul_sqrt_self d hd]
  nlinarith [norm_nonneg (CFC.sqrt d)]

lemma fixed_left_of_modulus {b z : A} (h : b * (z * star z) = z * star z) : b*z=z := by
  apply sub_eq_zero.mp
  apply (CStarRing.mul_star_self_eq_zero_iff _).mp
  have hs := congrArg star h
  simp only [star_mul, star_star] at hs
  calc
    (b*z-z) * star (b*z-z) = b*(z*star z)*star b - (z*star z)*star b - b*(z*star z) + z*star z := by
      simp only [star_sub, star_mul]; noncomm_ring
    _ = 0 := by rw [h]; noncomm_ring

lemma carrier_mem_Her {n : ℕ} {h v k : A} (S : OrthogonalSlots n h v)
    (hv : v ∈ Her k) (i : Fin n) (e : Her h) (he : (e : A) ∈ Her k) :
    S.carrier i e ∈ Her k := by
  apply mem_Her_of_moduli
  · exact Her_mono_of_mem hv (S.outer i i e e)
  · rw [S.inner, ite_eq_left rfl]
    exact (Her k).mul_mem ((Her k).star_mem' he) he

theorem first_pair_choice {d v k : A} (hd : 0 ≤ d) (hv : 0 ≤ v)
    (hdv : FiniteCuntzLE (diagonalCorner 2 d) (scalarCorner v))
    (hdk : d ∈ Her k) (hvk : v ∈ Her k) {η : ℝ} (hη : 0 < η) :
    ∃ T : Fin 2 → A,
      (∀ i, ‖T i‖ ≤ 1) ∧ (∀ i, T i ∈ Her k) ∧
      (∀ i j, T i * star (T j) = if i=j then ramp d η (2*η) else 0) ∧
      (∀ i j, star (T i) * T j ∈ Her v) := by
  let D := ramp d η (2*η)
  have hDpos : 0 ≤ D := ramp_nonneg d (by linarith)
  have hDmem : D ∈ Her (cut d η) := ramp_mem_Her_cut hd hη.le
  let e : Her (cut d η) := ⟨CFC.sqrt D, sqrt_mem_Her hDmem hDpos⟩
  obtain ⟨S⟩ := orthogonalSlots_of_comparison hd hv hdv hη
  have hnorm : ‖(e : A)‖ ≤ 1 := norm_sqrt_le_one hDpos (norm_ramp_le_one d (by linarith))
  have he : (e : A) ∈ Her k :=
    Her_mono_of_mem hdk (Her_mono_of_mem (cut_mem_Her hd η) e.property)
  have hsa : star (e : A) = (e : A) := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg D)).star_eq
  refine ⟨fun i => star (S.carrier i e), ?_, ?_, ?_, ?_⟩
  · intro i
    rw [norm_star, S.norm_carrier]
    exact hnorm
  · intro i
    exact (Her k).star_mem' (carrier_mem_Her S hvk i e he)
  · intro i j
    rw [star_star, S.inner, hsa]
    split_ifs
    · exact CFC.sqrt_mul_sqrt_self D hDpos
    · rfl
  · intro i j
    rw [star_star]
    exact S.outer i j e e

theorem last_pair_choice {R k : A} (hR : 0 ≤ R) (hRk : R ∈ Her k)
    {η : ℝ} (hη : 0 < η) (hp : ProperlyInfinite (cut R η)) :
    ∃ T : Fin 2 → A,
      (∀ i, ‖T i‖ ≤ 1) ∧ (∀ i, T i ∈ Her k) ∧
      (∀ i j, star (T i) * T j = if i=j then ramp R (2*η) (4*η) * ramp R (2*η) (4*η) else 0) ∧
      (∀ i j, T i * star (T j) ∈ Her (cut R η)) ∧
      (∀ {B : Type*} [NonUnitalCStarAlgebra B] (π : A →⋆ₙₐ[ℂ] B),
        4*η ≤ ‖π R‖ → ∀ i, ‖π (T i)‖ = 1) := by
  let t := ramp R (2*η) (4*η)
  have ht : t ∈ Her (cut (cut R η) η) := by
    rw [cut_cut hR hη.le hη.le, ← two_mul η]
    exact ramp_mem_Her_cut hR (by positivity)
  let e : Her (cut (cut R η) η) := ⟨t, ht⟩
  obtain ⟨S⟩ := hp.orthogonalSlots (cut_nonneg R η) 2 hη
  have hcut : cut R η ∈ Her k := Her_mono_of_mem hRk (cut_mem_Her hR η)
  have htk : t ∈ Her k := Her_mono_of_mem hRk
    (Her_mono_of_mem (cut_mem_Her hR (2*η)) (ramp_mem_Her_cut hR (by positivity)))
  refine ⟨fun i => S.carrier i e, ?_, ?_, ?_, (fun i j => S.outer i j e e), ?_⟩
  · intro i
    rw [S.norm_carrier]
    exact norm_ramp_le_one R (by linarith)
  · intro i
    exact carrier_mem_Her S hcut i e htk
  · intro i j
    rw [S.inner, (IsSelfAdjoint.of_nonneg (ramp_nonneg R (by linarith : 2*η ≤ 4*η))).star_eq]
  · intro B _ π hnorm i
    let : PartialOrder B := CStarAlgebra.spectralOrder B
    let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
    rw [S.represented_norm]
    change ‖π (ramp R (2*η) (4*η))‖ = 1
    rw [map_ramp π hR (by positivity)]
    exact norm_ramp_eq_one (map_nonneg π hR) (by positivity) (by linarith) hnorm

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def firstSandwich (U V : A) (η : ℝ) (E : Finset A) : A :=
  cut U η * (∑ w ∈ E, w * V * star w) * cut U η

lemma firstSandwich_nonneg {U V : A} (hV : 0 ≤ V) (η : ℝ) (E : Finset A) :
    0 ≤ firstSandwich U V η E := by
  have hsum : 0 ≤ ∑ w ∈ E, w * V * star w :=
    Finset.sum_nonneg (fun w _ => star_right_conjugate_nonneg hV w)
  simpa only [firstSandwich, IsSelfAdjoint.of_nonneg (cut_nonneg U η) |>.star_eq] using
    star_right_conjugate_nonneg hsum (cut U η)

lemma firstSandwich_mem (U V : A) (η : ℝ) (E : Finset A) :
    firstSandwich U V η E ∈ Her (cut U η) := by
  simpa only [firstSandwich, IsSelfAdjoint.of_nonneg (cut_nonneg U η) |>.star_eq] using
    sandwich_mem_Her (cut U η) (∑ w ∈ E, w * V * star w)

lemma firstSandwich_two_cuntzLE {U V : A} (hV : ProperlyInfinite V)
    (η : ℝ) (E : Finset A) :
    FiniteCuntzLE (diagonalCorner 2 (firstSandwich U V η E)) (scalarCorner V) := by
  have heq : firstSandwich U V η E =
      ∑ w ∈ E, star (star w * cut U η) * V * (star w * cut U η) := by
    simp only [firstSandwich, Finset.mul_sum, Finset.sum_mul, star_mul, star_star,
      IsSelfAdjoint.of_nonneg (cut_nonneg U η) |>.star_eq]
    apply Finset.sum_congr rfl
    intro w _
    noncomm_ring
  rw [heq]
  exact finsetSum_cuntzLE hV E _

lemma norm_ramp_bound {d : A} (hd : 0 ≤ d) {η h : ℝ} (hη : 0 < η)
    (hh0 : 0 ≤ h) (hh : h < 1) (hbound : ramp d η (2*η) ≤ h • (1 : A)) : ‖d‖ < 2*η := by
  by_contra! hnorm
  have hone := norm_ramp_eq_one hd hη.le (by linarith) hnorm
  have hD := ramp_nonneg d (by linarith : η ≤ 2*η)
  have hnle : ‖ramp d η (2*η)‖ ≤ h := by
    exact (CStarAlgebra.norm_le_iff_le_algebraMap _ hh0 hD).mpr (by
      simpa only [Algebra.algebraMap_eq_smul_one] using hbound)
  linarith

end MainGap

namespace MainGap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def scalingComplement (H : A) : A := CFC.sqrt (1 - H * H)

def scalingIsometry (H r : A) : A := r + scalingComplement H

def scalingDefect (H r : A) : A := 1 - scalingIsometry H r * star (scalingIsometry H r)

lemma complement_nonneg {H : A} (hH : IsSelfAdjoint H) (hnorm : ‖H‖ ≤ 1) :
    0 ≤ 1 - H * H := by
  apply sub_nonneg.mpr
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg (H * H) ?_).mp
  · calc
      ‖H * H‖ = ‖H‖ ^ 2 := hH.norm_mul_self
      _ ≤ 1 := (sq_le_one_iff₀ (norm_nonneg H)).mpr hnorm
  · simpa only [hH.star_eq] using star_mul_self_nonneg H

lemma scalingComplement_mul_self {H : A} (hH : IsSelfAdjoint H) (hnorm : ‖H‖ ≤ 1) :
    scalingComplement H * scalingComplement H = 1 - H * H :=
  CFC.sqrt_mul_sqrt_self _ (complement_nonneg hH hnorm)

lemma scalingComplement_selfAdjoint (H : A) : IsSelfAdjoint (scalingComplement H) :=
  IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)

lemma scalingComplement_mul_eq_zero {H r : A} (hH : IsSelfAdjoint H)
    (hnorm : ‖H‖ ≤ 1) (hHr : H * r = r) : scalingComplement H * r = 0 := by
  apply (CStarRing.star_mul_self_eq_zero_iff _).mp
  rw [star_mul, (scalingComplement_selfAdjoint H).star_eq]
  calc
    star r * scalingComplement H * (scalingComplement H * r) =
        star r * (scalingComplement H * scalingComplement H) * r := by noncomm_ring
    _ = star r * (1 - H * H) * r := by rw [scalingComplement_mul_self hH hnorm]
    _ = 0 := by simp only [mul_sub, sub_mul, mul_one, mul_assoc, hHr, sub_self]

lemma scalingIsometry_star_mul_self {H r : A} (hH : IsSelfAdjoint H)
    (hnorm : ‖H‖ ≤ 1) (hHr : H * r = r) (hrr : star r * r = H * H) :
    star (scalingIsometry H r) * scalingIsometry H r = 1 := by
  have hbr := scalingComplement_mul_eq_zero hH hnorm hHr
  have hrb : star r * scalingComplement H = 0 := by
    simpa only [star_mul, star_zero, (scalingComplement_selfAdjoint H).star_eq] using
      congrArg star hbr
  simp only [scalingIsometry, star_add, (scalingComplement_selfAdjoint H).star_eq,
    add_mul, mul_add, hbr, hrb, hrr, scalingComplement_mul_self hH hnorm]
  noncomm_ring

lemma scalingDefect_projection {H r : A} (hH : IsSelfAdjoint H)
    (hnorm : ‖H‖ ≤ 1) (hHr : H * r = r) (hrr : star r * r = H * H) :
    IsStarProjection (scalingDefect H r) := by
  apply IsStarProjection.one_sub
  constructor
  · change (scalingIsometry H r * star (scalingIsometry H r)) *
        (scalingIsometry H r * star (scalingIsometry H r)) =
      scalingIsometry H r * star (scalingIsometry H r)
    rw [mul_assoc, ← mul_assoc (star (scalingIsometry H r)),
      scalingIsometry_star_mul_self hH hnorm hHr hrr, one_mul]
  · exact IsSelfAdjoint.mul_star_self _

lemma scalingDefect_fixes_second {H r₁ r₂ : A} (hH : IsSelfAdjoint H)
    (hnorm : ‖H‖ ≤ 1) (hHr₂ : H * r₂ = r₂) (hcross : star r₁ * r₂ = 0) :
    scalingDefect H r₁ * r₂ = r₂ := by
  have hvr : star (scalingIsometry H r₁) * r₂ = 0 := by
    simp only [scalingIsometry, star_add, add_mul,
      (scalingComplement_selfAdjoint H).star_eq, hcross,
      scalingComplement_mul_eq_zero hH hnorm hHr₂, add_zero]
  simp only [scalingDefect, sub_mul, one_mul, mul_assoc, hvr, mul_zero, sub_zero]

lemma scalingDefect_ne_zero {H r₁ r₂ : A} (hH : IsSelfAdjoint H)
    (hnorm : ‖H‖ ≤ 1) (hHne : H ≠ 0) (hHr₂ : H * r₂ = r₂)
    (hcross : star r₁ * r₂ = 0) (hr₂ : star r₂ * r₂ = H * H) :
    scalingDefect H r₁ ≠ 0 := by
  intro hP
  have hr₂zero : r₂ = 0 := by
    have := scalingDefect_fixes_second hH hnorm hHr₂ hcross
    simpa only [hP, zero_mul, eq_comm] using this
  apply hHne
  apply (CStarRing.star_mul_self_eq_zero_iff H).mp
  rw [hH.star_eq, ← hr₂, hr₂zero, star_zero, zero_mul]

omit [PartialOrder A] [StarOrderedRing A] in
lemma last_pair_kills_defect {P B₃ B₄ : A} {h : ℝ} (hh : h ≠ 0)
    (hPB₄ : P * B₄ = B₄) (hcross : star B₃ * B₄ = 0)
    (hmod : star B₃ * B₃ = star B₄ * B₄)
    (hD : (B₃ * star B₃) * P = h • P) : P = 0 := by
  have hB₄ : h • B₄ = 0 := by
    calc
      h • B₄ = (h • P) * B₄ := by rw [smul_mul_assoc, hPB₄]
      _ = ((B₃ * star B₃) * P) * B₄ := by rw [hD]
      _ = B₃ * (star B₃ * B₄) := by rw [mul_assoc, hPB₄, mul_assoc]
      _ = 0 := by rw [hcross, mul_zero]
  have hB₄zero : B₄ = 0 := (smul_eq_zero.mp hB₄).resolve_left hh
  have hB₃zero : B₃ = 0 := (CStarRing.star_mul_self_eq_zero_iff B₃).mp (by
    rw [hmod, hB₄zero, star_zero, zero_mul])
  have hP : h • P = 0 := by simpa only [hB₃zero, zero_mul] using hD.symm
  exact (smul_eq_zero.mp hP).resolve_left hh

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
local instance : PartialOrder A := CStarAlgebra.spectralOrder A
local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

def deficiency (d : A) : A := cfc (fun t : ℝ => max ((1/2 : ℝ)-t) 0) d

def firstX (X : A) : A := cut X (1/16)
def firstV (X : A) : A := cut X (1/8)
def firstU (X B : A) : A := firstX X * deficiency (B * star B) *
  deficiency (B * star B) * firstX X

def firstH (X : A) : A := ramp X (3/32) (1/8)
def firstK (X : A) : A := ramp X (3/64) (1/16)
def firstR (X B : A) : A := (Real.sqrt 2) • (star B * firstH X)
def prospectiveDefect (X B : A) : A :=
  ramp (firstK X * scalingDefect (firstH X) (firstR X B) * firstK X) 0 1

def lastX (X B : A) : A := cut (prospectiveDefect X B) (1/2)
def lastR (X B₁ B₃ : A) : A := lastX X B₁ * deficiency (B₃ * star B₃) *
  deficiency (B₃ * star B₃) * lastX X B₁

def fourHer (X : A) : NonUnitalStarSubalgebra ℂ A := Her (cut X (1/32))

lemma deficiency_nonneg (d : A) : 0 ≤ deficiency d := cfc_nonneg (fun _ _ => le_max_right _ _)
lemma deficiency_selfAdjoint (d : A) : IsSelfAdjoint (deficiency d) := IsSelfAdjoint.cfc

lemma squareSandwich_nonneg {x : A} (hx : IsSelfAdjoint x) (Q : A) (hQ : IsSelfAdjoint Q) :
    0 ≤ x * Q * Q * x := by
  have := star_mul_self_nonneg (Q*x)
  simpa only [star_mul, hx.star_eq, hQ.star_eq, mul_assoc] using this

lemma squareSandwich_mem {x : A} (hx : IsSelfAdjoint x) (Q : A) :
    x * Q * Q * x ∈ Her x := by
  simpa only [hx.star_eq, mul_assoc] using sandwich_mem_Her x (Q*Q)

lemma cut_mem_cutHer {X : A} (hX : 0 ≤ X) {l u : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) :
    cut X u ∈ Her (cut X l) := by
  have heq : cut X u = cut (cut X l) (u-l) := by
    rw [cut_cut hX hl (sub_nonneg.mpr hlu)]
    congr 1
    ring
  rw [heq]
  exact cut_mem_Her (cut_nonneg X l) _

lemma firstX_mem {X : A} (hX : 0 ≤ X) : firstX X ∈ fourHer X :=
  cut_mem_cutHer hX (by norm_num) (by norm_num)
lemma firstV_mem {X : A} (hX : 0 ≤ X) : firstV X ∈ fourHer X :=
  cut_mem_cutHer hX (by norm_num) (by norm_num)
lemma firstU_nonneg (X B : A) : 0 ≤ firstU X B :=
  squareSandwich_nonneg (.of_nonneg (cut_nonneg X _)) _ (deficiency_selfAdjoint _)
lemma firstU_mem {X : A} (hX : 0 ≤ X) (B : A) : firstU X B ∈ fourHer X :=
  Her_mono_of_mem (firstX_mem hX) (squareSandwich_mem (.of_nonneg (cut_nonneg X _)) _)

lemma firstK_mem {X : A} (hX : 0 ≤ X) : firstK X ∈ fourHer X := by
  exact Her_mono_of_mem (cut_mem_cutHer hX (by norm_num : (0:ℝ) ≤ 1/32)
    (by norm_num : (1/32:ℝ) ≤ 3/64)) (ramp_mem_Her_cut hX (by norm_num))

lemma prospectiveDefect_nonneg (X B : A) : 0 ≤ prospectiveDefect X B :=
  ramp_nonneg _ (by norm_num)
lemma prospectiveDefect_norm (X B : A) : ‖prospectiveDefect X B‖ ≤ 1 :=
  norm_ramp_le_one _ (by norm_num)
lemma prospectiveDefect_mem {X : A} (hX : 0 ≤ X) (B : A) :
    prospectiveDefect X B ∈ fourHer X := by
  change cfcₙ _ _ ∈ Her (cut X (1/32))
  apply cfcₙ_mem (𝕜' := ℂ)
  have h := Her_sandwich (firstK_mem hX) (scalingDefect (firstH X) (firstR X B))
  simpa only [firstK, IsSelfAdjoint.of_nonneg (ramp_nonneg X (by norm_num : (3/64:ℝ) ≤ 1/16)) |>.star_eq] using h

lemma lastX_nonneg (X B : A) : 0 ≤ lastX X B := cut_nonneg _ _
lemma lastX_mem {X : A} (hX : 0 ≤ X) (B : A) : lastX X B ∈ fourHer X :=
  Her_mono_of_mem (prospectiveDefect_mem hX B) (cut_mem_Her (prospectiveDefect_nonneg X B) _)
lemma lastR_nonneg (X B₁ B₃ : A) : 0 ≤ lastR X B₁ B₃ :=
  squareSandwich_nonneg (.of_nonneg (lastX_nonneg X B₁)) _ (deficiency_selfAdjoint _)
lemma lastR_mem {X : A} (hX : 0 ≤ X) (B₁ B₃ : A) : lastR X B₁ B₃ ∈ fourHer X :=
  Her_mono_of_mem (lastX_mem hX B₁) (squareSandwich_mem (.of_nonneg (lastX_nonneg X B₁)) _)

end MainGap

end

end OAI
