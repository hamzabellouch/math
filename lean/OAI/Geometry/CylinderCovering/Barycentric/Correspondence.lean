import OAI.Geometry.CylinderCovering.Radial.Coordinates
import OAI.Geometry.CylinderCovering.Barycentric.SweepsDefinitions
import OAI.Geometry.CylinderCovering.Barycentric.SweepCompact

namespace OAI

open Set

noncomputable section
namespace RadialCoordinates

theorem firstSweepImagePoint_sum (k S t p : ℝ) : ∑ i, firstSweepImagePoint k S t p i = 1 :=
  barycentricPoint_sum _ _ _

theorem firstSweepImagePoint_first (k S t p : ℝ) :
    firstSweepImagePoint k S t p 0 = S * t + k * p * t ^ 2 := by
  simp [firstSweepImagePoint, barycentricPoint, angular]
  ring

theorem firstSweepImagePoint_second (k S t p : ℝ) :
    firstSweepImagePoint k S t p 1 = S * (1 - t) - k * p * (1 - t) ^ 2 := by
  simp [firstSweepImagePoint, barycentricPoint, angular]
  ring

theorem firstSweepImagePoint_free (k S t p : ℝ) :
    firstSweepImagePoint k S t p 2 - firstSweepImagePoint k S t p 3 = p := by
  simp [firstSweepImagePoint, barycentricPoint]
  ring

theorem secondSweepImagePoint_sum (k T r q : ℝ) : ∑ i, secondSweepImagePoint k T r q i = 1 :=
  barycentricPoint_sum _ _ _

theorem secondSweepImagePoint_third (k T r q : ℝ) :
    secondSweepImagePoint k T r q 2 = T * r - k * q * r ^ 2 := by
  simp [secondSweepImagePoint, barycentricPoint, angular]
  ring

theorem secondSweepImagePoint_fourth (k T r q : ℝ) :
    secondSweepImagePoint k T r q 3 = T * (1 - r) + k * q * (1 - r) ^ 2 := by
  simp [secondSweepImagePoint, barycentricPoint, angular]
  ring

theorem secondSweepImagePoint_free (k T r q : ℝ) :
    secondSweepImagePoint k T r q 0 - secondSweepImagePoint k T r q 1 = q := by
  simp [secondSweepImagePoint, barycentricPoint]
  ring

theorem firstSweepImagePoint_reconstruct {v : BarycentricSpace} {k S t : ℝ}
    (hsum : ∑ i, v i = 1)
    (ha : v 0 = S * t + k * (v 2 - v 3) * t ^ 2)
    (hb : v 1 = S * (1 - t) - k * (v 2 - v 3) * (1 - t) ^ 2) :
    v = firstSweepImagePoint k S t (v 2 - v 3) := by
  have hs : v 0 + v 1 = S + k * (v 2 - v 3) * angular t := by
    rw [ha, hb]; unfold angular; ring
  have hq : v 0 - v 1 = S * angular t +
      k * (v 2 - v 3) * (t ^ 2 + (1 - t) ^ 2) := by
    rw [ha, hb]; unfold angular; ring
  calc
    v = barycentricPoint (v 0 + v 1) (v 0 - v 1) (v 2 - v 3) :=
      (barycentricPoint_reconstruct hsum).symm
    _ = _ := by rw [hs, hq]; rfl

theorem secondSweepImagePoint_reconstruct {v : BarycentricSpace} {k T r : ℝ}
    (hsum : ∑ i, v i = 1)
    (hc : v 2 = T * r - k * (v 0 - v 1) * r ^ 2)
    (hd : v 3 = T * (1 - r) + k * (v 0 - v 1) * (1 - r) ^ 2) :
    v = secondSweepImagePoint k T r (v 0 - v 1) := by
  have hsum' : v 0 + v 1 + v 2 + v 3 = 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  have hcd : v 2 + v 3 = T - k * (v 0 - v 1) * angular r := by
    rw [hc, hd]; unfold angular; ring
  have hs : v 0 + v 1 = 1 - T + k * (v 0 - v 1) * angular r := by linarith
  have hp : v 2 - v 3 = T * angular r -
      k * (v 0 - v 1) * (r ^ 2 + (1 - r) ^ 2) := by
    rw [hc, hd]; unfold angular; ring
  calc
    v = barycentricPoint (v 0 + v 1) (v 0 - v 1) (v 2 - v 3) :=
      (barycentricPoint_reconstruct hsum).symm
    _ = _ := by rw [hs, hp]; rfl

theorem firstSweep_eq_parametrizedImage (k : ℝ) : firstSweep k = firstSweepImage k := by
  ext v
  constructor
  · rintro ⟨hsum, t, S, ht, hS, hcap, hp, ha, hb⟩
    exact ⟨t, ht, S, ⟨hS, hcap⟩, v 2 - v 3, abs_le.mp hp,
      firstSweepImagePoint_reconstruct hsum ha hb⟩
  · rintro ⟨t, ht, S, hS, p, hp, rfl⟩
    refine ⟨firstSweepImagePoint_sum k S t p, t, S, ht, hS.1, hS.2, ?_, ?_, ?_⟩
    · rw [firstSweepImagePoint_free]; exact abs_le.mpr hp
    · rw [firstSweepImagePoint_free]; exact firstSweepImagePoint_first k S t p
    · rw [firstSweepImagePoint_free]; exact firstSweepImagePoint_second k S t p

theorem secondSweep_eq_parametrizedImage (k : ℝ) : secondSweep k = secondSweepImage k := by
  ext v
  constructor
  · rintro ⟨hsum, r, T, hr, hT, hcap, hq, hc, hd⟩
    exact ⟨r, hr, T, ⟨hT, hcap⟩, v 0 - v 1, abs_le.mp hq,
      secondSweepImagePoint_reconstruct hsum hc hd⟩
  · rintro ⟨r, hr, T, hT, q, hq, rfl⟩
    refine ⟨secondSweepImagePoint_sum k T r q, r, T, hr, hT.1, hT.2, ?_, ?_, ?_⟩
    · rw [secondSweepImagePoint_free]; exact abs_le.mpr hq
    · rw [secondSweepImagePoint_free]; exact secondSweepImagePoint_third k T r q
    · rw [secondSweepImagePoint_free]; exact secondSweepImagePoint_fourth k T r q

theorem firstSweepImagePoint_eq (k S t p : ℝ) :
    firstSweepImagePoint k S t p = firstSweepPoint k t S p := by
  ext i
  fin_cases i <;> simp [firstSweepImagePoint, firstSweepPoint, barycentricPoint, angular] <;> ring

theorem secondSweepImagePoint_eq (k T r q : ℝ) :
    secondSweepImagePoint k T r q = secondSweepPoint k r T q := by
  ext i
  fin_cases i <;> simp [secondSweepImagePoint, secondSweepPoint, barycentricPoint, angular] <;> ring

theorem firstSweepWithCap_eq_image (k : ℝ) :
    firstSweepWithCap k (cap k) = firstSweepImage k :=
  (firstSweep_eq_withCap k).symm.trans (firstSweep_eq_parametrizedImage k)

theorem secondSweepWithCap_eq_image (k : ℝ) :
    secondSweepWithCap k (cap k) = secondSweepImage k :=
  (secondSweep_eq_withCap k).symm.trans (secondSweep_eq_parametrizedImage k)

theorem firstSweep_canonical_dictionary (k S t p : ℝ) :
    canonicalPoint (S + k * p * angular t)
      (S * angular t + k * p * (t ^ 2 + (1 - t) ^ 2)) p =
      (!₂[2 * S * angular t + k * (2 * p) * ((1 + angular t ^ 2) / 2),
        2 * p, Real.sqrt 2 * (-1 + 2 * S + k * (2 * p) * angular t)] : Space) := by
  ext i
  fin_cases i <;> simp [canonicalPoint, angular] <;> ring

theorem secondSweep_canonical_dictionary (k T r q : ℝ) :
    canonicalPoint (1 - T + k * q * angular r) q
      (T * angular r - k * q * (r ^ 2 + (1 - r) ^ 2)) =
      (!₂[2 * q, 2 * T * angular r - k * (2 * q) * ((1 + angular r ^ 2) / 2),
        Real.sqrt 2 * (1 - 2 * T + k * (2 * q) * angular r)] : Space) := by
  ext i
  fin_cases i <;> simp [canonicalPoint, angular] <;> ring

theorem cap_canonical_dictionary (k t : ℝ) :
    2 * cap k t = 1 + k ^ 2 * ((angular t ^ 2 + angular t ^ 4) / 2 + 1 / 500) := by
  unfold cap capPolynomial
  ring

theorem speedSquared_canonical_dictionary (t : ℝ) :
    speedSquared t = 2 * angular t ^ 2 + ((1 + angular t ^ 2) / 2) ^ 2 := by
  unfold speedSquared angular
  ring

end RadialCoordinates

end

end OAI
