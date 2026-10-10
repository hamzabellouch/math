import OAI.Geometry.CylinderCovering.Ruled.ZeroDiagonal

namespace OAI

noncomputable section
open Set
namespace RuledApproximation.OrthogonalRetention

def affineVelocity (p v₀ : Plane) (A : Plane →L[ℝ] Plane) (w : Plane) : Plane :=
  v₀ + A (w - p)

def center (p : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane) (ell : ℝ) (ij : ℤ × ℤ) : Plane :=
  p + ell • R (vec2 (ij.1 : ℝ) (ij.2 : ℝ))

def square (p : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane) (ell : ℝ)
    (ij : ℤ × ℤ) : Set Plane :=
  (fun u => center p R ell ij + ell • R u) '' unitSquare

lemma square_isSquareTile (p : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane)
    {ell : ℝ} (hell : 0 < ell) (ij : ℤ × ℤ) :
    IsSquareTile (square p R ell ij) :=
  ⟨center p R ell ij, R, ell, hell, rfl⟩

lemma inverse_bound (A : Plane →L[ℝ] Plane) {κ t : ℝ}
    (hA : ‖A‖ ≤ κ) (ht : |t| ≤ 1) (z : Plane) :
    (1 - κ) * ‖z‖ ≤ ‖z + t • A z‖ := by
  have hκ : 0 ≤ κ := (norm_nonneg A).trans hA
  have hAz : ‖t • A z‖ ≤ κ * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |t| * ‖A z‖ ≤ 1 * ‖A z‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
      _ ≤ κ * ‖z‖ := by
        simpa using (A.le_opNorm z).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg z))
  have hz : ‖z‖ ≤ ‖z + t • A z‖ + ‖t • A z‖ := by
    calc
      ‖z‖ = ‖(z + t • A z) - t • A z‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  nlinarith

lemma retention_bound (p v₀ w c : Plane) (A : Plane →L[ℝ] Plane)
    (v : Plane → Plane) {κ t ell error : ℝ}
    (hA : ‖A‖ ≤ κ) (hκ : κ < 1) (ht : |t| ≤ 1)
    (herror : ‖v w - affineVelocity p v₀ A w‖ ≤ error)
    (hclose : ‖(c + t • affineVelocity p v₀ A c) - (w + t • v w)‖ ≤ ell) :
    ‖c - w‖ ≤ (ell + error) / (1 - κ) := by
  have herr : ‖t • (v w - affineVelocity p v₀ A w)‖ ≤ error := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right ht (norm_nonneg _)).trans (by simpa using herror)
  have heq : (c - w) + t • A (c - w) =
      ((c + t • affineVelocity p v₀ A c) - (w + t • v w)) +
      t • (v w - affineVelocity p v₀ A w) := by
    simp only [affineVelocity, map_sub, smul_add, smul_sub]
    module
  have hupper : ‖(c - w) + t • A (c - w)‖ ≤ ell + error := by
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add hclose herr)
  apply (le_div_iff₀ (by linarith : 0 < 1 - κ)).2
  nlinarith [inverse_bound A hA ht (c - w)]

lemma plane_cover (p v₀ : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (A : Plane →L[ℝ] Plane) {b c κ ell t : ℝ}
    (hframe : ∀ z : Plane, R.symm (A (R z)) = vec2 (b * z 1) (c * z 0))
    (hbc : 0 ≤ b * c) (hb : |b| ≤ κ) (hc : |c| ≤ κ)
    (hκ : κ < 1) (hell : 0 < ell) (ht : |t| ≤ 1) (x : Plane) :
    ∃ ij : ℤ × ℤ, ∃ u ∈ unitSquare,
      x = center p R ell ij + ell • R u +
        t • affineVelocity p v₀ A (center p R ell ij) := by
  have hκ0 : 0 ≤ κ := (abs_nonneg b).trans hb
  have htB : |t * b| ≤ κ := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right ht (abs_nonneg b)).trans (by simpa using hb)
  have htC : |t * c| ≤ κ := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right ht (abs_nonneg c)).trans (by simpa using hc)
  have hprod : 0 ≤ (t * b) * (t * c) := by
    calc
      0 ≤ t ^ 2 * (b * c) := mul_nonneg (sq_nonneg t) hbc
      _ = _ := by ring
  have hprod' : (t * b) * (t * c) < 1 := by
    have hle : (t * b) * (t * c) ≤ κ * κ := by
      calc
        _ ≤ |(t * b) * (t * c)| := le_abs_self _
        _ = |t * b| * |t * c| := abs_mul _ _
        _ ≤ _ := mul_le_mul htB htC (abs_nonneg _) hκ0
    nlinarith
  let z : Plane := ell⁻¹ • R.symm (x - p - t • v₀)
  obtain ⟨i, j, hi, hj⟩ := asymmetric_lattice_cover (t * b) (t * c)
    hprod hprod' (z 0) (z 1)
  let q : Plane := vec2 (i : ℝ) (j : ℝ)
  let u : Plane := z - q - t • R.symm (A (R q))
  have hu : u ∈ unitSquare := by
    intro k
    fin_cases k
    · simpa [u, q, hframe, vec2, sub_add_eq_sub_sub, mul_assoc] using hi
    · convert hj using 1
      simp [u, q, hframe, vec2]
      congr 1
      ring
  refine ⟨(i,j), u, hu, ?_⟩
  have hscale : ell • R z = x - p - t • v₀ := by
    simp [z, map_smul, smul_smul, hell.ne']
  have huR : R u = R z - R q - t • A (R q) := by
    simp [u, map_sub, map_smul]
  change x = (p + ell • R q) + ell • R u +
    t • (v₀ + A ((p + ell • R q) - p))
  rw [huR]
  simp only [add_sub_cancel_left, map_smul, smul_add, smul_sub, smul_smul]
  rw [hscale]
  module

lemma square_error_bound (R : Plane ≃ₗᵢ[ℝ] Plane) {ell : ℝ}
    (hell : 0 ≤ ell) {u : Plane} (hu : u ∈ unitSquare) :
    ‖ell • R u‖ ≤ ell := by
  have hnorm : ‖u‖ ≤ 1 := by
    exact (plane_norm_le_sum u).trans (by linarith [hu 0, hu 1])
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hell, R.norm_map]
  simpa using mul_le_mul_of_nonneg_left hnorm hell

def indexBox (K : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(K : ℤ)) K).product (Finset.Icc (-(K : ℤ)) K)

lemma indexBox_card (K : ℕ) : (indexBox K).card = (2 * K + 1) ^ 2 := by
  simp only [indexBox, Finset.product_eq_sprod, Finset.card_product, Int.card_Icc]
  have heq : (K : ℤ) + 1 - -(K : ℤ) = ((2 * K + 1 : ℕ) : ℤ) := by omega
  rw [heq]
  simp only [Int.toNat_natCast, pow_two]

lemma mem_indexBox_of_norm_bound (p : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane)
    {ell M radius : ℝ} (hell : 0 < ell) {ij : ℤ × ℤ} {w : Plane}
    (hw : ‖w - p‖ ≤ M) (hc : ‖center p R ell ij - w‖ ≤ radius) :
    ij ∈ indexBox ⌈(M + radius) / ell⌉₊ := by
  have hq : ‖vec2 (ij.1 : ℝ) (ij.2 : ℝ)‖ ≤ (M + radius) / ell := by
    apply (le_div_iff₀ hell).2
    have hnorm : ‖center p R ell ij - p‖ =
        ell * ‖vec2 (ij.1 : ℝ) (ij.2 : ℝ)‖ := by
      simp [center, norm_smul, abs_of_pos hell]
    have htriangle : ‖center p R ell ij - p‖ ≤ radius + M := by
      calc
        _ ≤ ‖center p R ell ij - w‖ + ‖w - p‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ _ := add_le_add hc hw
    rw [hnorm] at htriangle
    linarith
  have hb (k : Fin 2) : |(vec2 (ij.1 : ℝ) (ij.2 : ℝ)) k| ≤
      (⌈(M + radius) / ell⌉₊ : ℝ) :=
    (plane_coordinate_le _ k).trans (hq.trans (Nat.le_ceil _))
  have hi : -(⌈(M + radius) / ell⌉₊ : ℤ) ≤ ij.1 ∧
      ij.1 ≤ (⌈(M + radius) / ell⌉₊ : ℤ) := by
    have h := abs_le.mp (hb 0)
    simp [vec2] at h
    exact_mod_cast h
  have hj : -(⌈(M + radius) / ell⌉₊ : ℤ) ≤ ij.2 ∧
      ij.2 ≤ (⌈(M + radius) / ell⌉₊ : ℤ) := by
    have h := abs_le.mp (hb 1)
    simp [vec2] at h
    exact_mod_cast h
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hi, Finset.mem_Icc.mpr hj⟩

def retained (S : Set Plane) (p : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (ell M radius : ℝ) : Finset (ℤ × ℤ) := by
  classical
  exact (indexBox ⌈(M + radius) / ell⌉₊).filter
    (fun ij => ∃ w ∈ S, ‖center p R ell ij - w‖ ≤ radius)

lemma mem_retained_iff {S : Set Plane} (p : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane)
    {ell M radius : ℝ} (hell : 0 < ell) (hM : ∀ w ∈ S, ‖w - p‖ ≤ M)
    (ij : ℤ × ℤ) :
    ij ∈ retained S p R ell M radius ↔
      ∃ w ∈ S, ‖center p R ell ij - w‖ ≤ radius := by
  classical
  simp only [retained, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨w, hw, hc⟩ := h
    exact ⟨mem_indexBox_of_norm_bound p R hell (hM w hw) hc, w, hw, hc⟩

lemma retained_card_le (S : Set Plane) (p : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (ell M radius : ℝ) :
    (retained S p R ell M radius).card ≤
      (2 * ⌈(M + radius) / ell⌉₊ + 1) ^ 2 := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (indexBox_card _)

lemma retained_empty (p : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane) (ell M radius : ℝ) :
    retained ∅ p R ell M radius = ∅ := by
  classical
  simp [retained]

theorem retained_cover_in_frame {S : Set Plane} (p v₀ : Plane)
    (R : Plane ≃ₗᵢ[ℝ] Plane) (A : Plane →L[ℝ] Plane) (v : Plane → Plane)
    {b c κ ell error M : ℝ}
    (hframe : ∀ z : Plane, R.symm (A (R z)) = vec2 (b * z 1) (c * z 0))
    (hbc : 0 ≤ b * c) (hb : |b| ≤ κ) (hc : |c| ≤ κ)
    (hA : ‖A‖ ≤ κ) (hκ : κ < 1) (hell : 0 < ell)
    (hM : ∀ w ∈ S, ‖w - p‖ ≤ M)
    (herror : ∀ w ∈ S, ‖v w - affineVelocity p v₀ A w‖ ≤ error) :
    ∀ w ∈ S, ∀ t : ℝ, |t| ≤ 1 →
      ∃ ij ∈ retained S p R ell M ((ell + error) / (1 - κ)),
        w + t • (v w - affineVelocity p v₀ A (center p R ell ij)) ∈
          square p R ell ij := by
  intro w hw t ht
  obtain ⟨ij, u, hu, heq⟩ := plane_cover p v₀ R A hframe hbc hb hc hκ hell ht
    (w + t • v w)
  have hclose : ‖(center p R ell ij +
        t • affineVelocity p v₀ A (center p R ell ij)) - (w + t • v w)‖ ≤ ell := by
    rw [heq]
    have he : (center p R ell ij + t • affineVelocity p v₀ A (center p R ell ij)) -
        (center p R ell ij + ell • R u +
          t • affineVelocity p v₀ A (center p R ell ij)) = -(ell • R u) := by module
    rw [he, norm_neg]
    exact square_error_bound R hell.le hu
  have hdist := retention_bound p v₀ w (center p R ell ij) A v hA hκ ht
    (herror w hw) hclose
  refine ⟨ij, (mem_retained_iff p R hell hM ij).mpr ⟨w, hw, hdist⟩, u, hu, ?_⟩
  have haux : w + t • (v w - affineVelocity p v₀ A (center p R ell ij)) =
      (w + t • v w) - t • affineVelocity p v₀ A (center p R ell ij) := by module
  rw [haux, heq]
  module

theorem finite_retained_cover {S : Set Plane} (p v₀ : Plane)
    (A : Plane →L[ℝ] Plane) (v : Plane → Plane) {κ ell error M : ℝ}
    (htrace : LinearMap.trace ℝ Plane A.toLinearMap = 0)
    (hdet : LinearMap.det A.toLinearMap < 0)
    (hA : ‖A‖ ≤ κ) (hκ : κ < 1) (hell : 0 < ell)
    (hM : ∀ w ∈ S, ‖w - p‖ ≤ M)
    (herror : ∀ w ∈ S, ‖v w - affineVelocity p v₀ A w‖ ≤ error) :
    ∃ R : Plane ≃ₗᵢ[ℝ] Plane,
      ∀ w ∈ S, ∀ t : ℝ, |t| ≤ 1 →
        ∃ ij ∈ retained S p R ell M ((ell + error) / (1 - κ)),
          w + t • (v w - affineVelocity p v₀ A (center p R ell ij)) ∈
            square p R ell ij := by
  obtain ⟨R, b, c, hframe, _, hbc, hb, hc⟩ := orthogonalZeroDiagonal_proof A htrace hdet
  exact ⟨R, retained_cover_in_frame p v₀ R A v hframe hbc.le
    (hb.trans hA) (hc.trans hA) hA hκ hell hM herror⟩

def physicalFamily (h : ℝ) (p v₀ : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (A : Plane →L[ℝ] Plane) (ell : ℝ) (F : Finset (ℤ × ℤ)) : Fin F.card → Cylinder :=
  fun i => projectedCylinder h
    (affineVelocity p v₀ A (center p R ell (F.equivFin.symm i)))
    (square p R ell (F.equivFin.symm i))

lemma physicalFamily_parallelogram {h ell : ℝ} (hh : 0 < h) (hell : 0 < ell)
    (p v₀ : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane) (A : Plane →L[ℝ] Plane)
    (F : Finset (ℤ × ℤ)) (i : Fin F.card) :
    (physicalFamily h p v₀ R A ell F i).parallelogram :=
  projectedCylinder_parallelogram hh _ (square_isSquareTile p R hell _).parallelogram

lemma physicalFamily_area {h : ℝ} (hh : 0 < h) (p v₀ : Plane)
    (R : Plane ≃ₗᵢ[ℝ] Plane) (A : Plane →L[ℝ] Plane) (ell : ℝ)
    (F : Finset (ℤ × ℤ)) (i : Fin F.card) :
    (physicalFamily h p v₀ R A ell F i).area =
      h * MeasureTheory.volume.real (square p R ell (F.equivFin.symm i)) *
        physicalWeight h (affineVelocity p v₀ A (center p R ell (F.equivFin.symm i))) :=
  projectedCylinder_area hh _ _

theorem physical_finite_retained_cover {S : Set Plane} (p v₀ : Plane)
    (A : Plane →L[ℝ] Plane) (v : Plane → Plane) {κ ell error M h : ℝ}
    (htrace : LinearMap.trace ℝ Plane A.toLinearMap = 0)
    (hdet : LinearMap.det A.toLinearMap < 0)
    (hA : ‖A‖ ≤ κ) (hκ : κ < 1) (hell : 0 < ell) (hh : 0 < h)
    (hM : ∀ w ∈ S, ‖w - p‖ ≤ M)
    (herror : ∀ w ∈ S, ‖v w - affineVelocity p v₀ A w‖ ≤ error) :
    ∃ R : Plane ≃ₗᵢ[ℝ] Plane,
      let F := retained S p R ell M ((ell + error) / (1 - κ))
      (∀ i, (physicalFamily h p v₀ R A ell F i).parallelogram) ∧
      physicalRuled h S v 1 ⊆ familySet (physicalFamily h p v₀ R A ell F) ∧
      F.card ≤ (2 * ⌈(M + (ell + error) / (1 - κ)) / ell⌉₊ + 1) ^ 2 := by
  classical
  obtain ⟨R, hcover⟩ := finite_retained_cover p v₀ A v htrace hdet hA hκ hell hM herror
  let F := retained S p R ell M ((ell + error) / (1 - κ))
  refine ⟨R, (fun i => physicalFamily_parallelogram hh hell p v₀ R A F i), ?_,
    retained_card_le S p R ell M _⟩
  rintro z ⟨w, hw, t, ht, rfl⟩
  obtain ⟨ij, hij, hmem⟩ := hcover w hw t ht
  let j : F := ⟨ij, hij⟩
  apply Set.mem_iUnion.mpr
  refine ⟨F.equivFin j, ?_⟩
  change _ ∈ (physicalFamily h p v₀ R A ell F (F.equivFin j)).carrier
  simpa only [physicalFamily, Equiv.symm_apply_apply] using
    physicalRuled_mem_projectedCylinder h v w
      (affineVelocity p v₀ A (center p R ell ij)) t hmem

end RuledApproximation.OrthogonalRetention

end

end OAI
