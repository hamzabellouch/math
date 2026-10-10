import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceIndexedSites
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactPolynomialGeometry

namespace OAI

/-! The actual indexed source array inherits the exact separation and
polynomial norm estimates of its rational contact construction. -/

noncomputable section
namespace ContinuumCoulomb.SourceNuclearProgram
open SourceMetadataProgram ContactMediator

theorem contactSpacing_positive {c : ℚ} (hc : 0 < c) (k : ℕ) (d : BinaryHeisenberg) :
    0 < contactSpacing c k d :=
  AutomaticCalibration.spacing_positive hc k _
    (lt_of_lt_of_le (by decide : 0 < 2) (CalibrationMesh.base_ge_two (SourceContactProgram.size_ge_two d)))

theorem contactLengths_near_one (rho C : ℕ) {eps c : ℚ} (heps : 0 ≤ eps) (hc : 0 < c)
    (htol : (eps:ℝ)/2 ≤ contactLengthTolerance) (s p k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) (e : GlobalEdge (geometricSource s d hd)) :
    (contactLengths rho C eps c s p k A B d hd e:ℝ) ∈
      Set.Icc (1-contactLengthTolerance) (1+contactLengthTolerance) :=
  CalibratedContactProgram.graphLengths_near_one rho heps hc htol k A B
    (CalibrationMesh.base (SourceContactProgram.size d))
    (PrefactorCalibration.precision C (SourceContactProgram.size d^p))
    (lt_of_lt_of_le (by decide : 0 < 2) (CalibrationMesh.base_ge_two (SourceContactProgram.size_ge_two d)))
    (geometricSource s d hd) _ e

private theorem source_coordinate_bound (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid)
    (hp : d.PolynomialPromise s) (j : Fin (geometricSource s d hd).vertices) (i : Fin 2) :
    |(contactGridAxis ((geometricSource s d hd).coordinate j) i:ℝ)| ≤
      (SourceContactProgram.size d:ℝ)^s := by
  have hN : (SourceContactProgram.size d:ℝ)=(binaryHeisenbergCodec.encode d).length+2 := by
    unfold SourceContactProgram.size SourceMetadataProgram.size
    push_cast
    ring
  rw [hN]
  exact geometricSource_coordinates s d hd hp j i

theorem raw_diameter_bound (rho C : ℕ) {eps c : ℚ} (heps : 0 ≤ eps) (hc : 0 < c)
    (htol : (eps:ℝ)/2 ≤ contactLengthTolerance) (s p h k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) (hp : d.PolynomialPromise s)
    (hk : 1100 ≤ k) (hP : 7200 ≤ SourceContactProgram.size d^h)
    (hqhi : (contactSpacing c k d:ℝ) ≤ 31*(k:ℝ)*Real.log (SourceContactProgram.size d))
    (x y : GlobalSite (geometricSource s d hd)) :
    ‖ContactCalibratedGeometry.point (geometricSource s d hd) (SourceContactProgram.size d^h)
        (contactSpacing c k d) (contactLengths rho C eps c s p k A B d hd) x-
      ContactCalibratedGeometry.point (geometricSource s d hd) (SourceContactProgram.size d^h)
        (contactSpacing c k d) (contactLengths rho C eps c s p k A B d hd) y‖ ≤
      2*(SourceContactProgram.size d:ℝ)^(s+k/100+13) := by
  have hn (j : GlobalSite (geometricSource s d hd)) :=
    ContactCalibratedGeometry.polynomial_norm (geometricSource s d hd)
      (SourceContactProgram.size_ge_two d) hk (contactSpacing_positive hc k d) hqhi _ hP
      (contactLengths_near_one rho C heps hc htol s p k A B d hd)
      (source_coordinate_bound s d hd hp) j
  have hs := (norm_sub_le _ _).trans (add_le_add (hn x) (hn y))
  simpa only [Nat.add_comm (k/100) s,two_mul] using hs

theorem indexed_norm_bound (rho C : ℕ) {eps c : ℚ} (heps : 0 ≤ eps) (hc : 0 < c)
    (htol : (eps:ℝ)/2 ≤ contactLengthTolerance) (s p h k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) (hp : d.PolynomialPromise s)
    (hk : 1100 ≤ k) (hP : 7200 ≤ SourceContactProgram.size d^h)
    (hqhi : (contactSpacing c k d:ℝ) ≤ 31*(k:ℝ)*Real.log (SourceContactProgram.size d))
    {m : ℕ} (hm : (SourcePositiveProgram.output s d).vertices=m+1) (i : Fin (m+1)) :
    ‖PlanarForcingProgram.position (indexedCoordinates rho C eps c s p h k A B d hd hm i)‖ ≤
      (SourceContactProgram.size d:ℝ)^(k/100+s+13) := by
  rw [indexed_position]
  exact ContactCalibratedGeometry.polynomial_norm (geometricSource s d hd)
    (SourceContactProgram.size_ge_two d) hk (contactSpacing_positive hc k d) hqhi _ hP
    (contactLengths_near_one rho C heps hc htol s p k A B d hd)
    (source_coordinate_bound s d hd hp) _

theorem indexed_separation (rho C : ℕ) {eps c : ℚ} (heps : 0 ≤ eps) (hc : 0 < c)
    (htol : (eps:ℝ)/2 ≤ contactLengthTolerance) (s p h k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid)
    (hP : 7200 ≤ SourceContactProgram.size d^h)
    (hqlo : (59/2:ℝ)*(k:ℝ)*Real.log (SourceContactProgram.size d) ≤ contactSpacing c k d)
    {m : ℕ} (hm : (SourcePositiveProgram.output s d).vertices=m+1)
    (i j : Fin (m+1)) (hij : i ≠ j) :
    25*(k:ℝ)*Real.log (SourceContactProgram.size d) ≤
      ‖PlanarForcingProgram.position (indexedCoordinates rho C eps c s p h k A B d hd hm i)-
        PlanarForcingProgram.position (indexedCoordinates rho C eps c s p h k A B d hd hm j)‖ := by
  rw [indexed_position,indexed_position]
  exact ContactCalibratedGeometry.polynomial_separation (geometricSource s d hd)
    (SourcePositiveProgram.sourceBound s d) (size d^s) (SourceContactProgram.size d^h)
    (SourceContactProgram.size d) k (SourceContactProgram.size_ge_two d)
    (contactSpacing_positive hc k d) hqlo _ hP
    (contactLengths_near_one rho C heps hc htol s p k A B d hd) _ _
    (fun he => hij ((SourcePositiveProgram.indexedSites s d hd hm).symm.injective he))

end ContinuumCoulomb.SourceNuclearProgram

end

end OAI
