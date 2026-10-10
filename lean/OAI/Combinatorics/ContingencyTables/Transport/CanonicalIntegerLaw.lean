import OAI.Combinatorics.ContingencyTables.Transport.CanonicalDrawTabulation
import OAI.Combinatorics.ContingencyTables.Transport.IntegerEquivLaw

namespace OAI

/-! # The exact finite integer law of the normalized Boolean sampler -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits ResidualMixture FirstSuccess
open scoped BigOperators Classical
noncomputable section

variable {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
variable (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
variable (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)

def canonicalCounts : IntegerLaw (Table R P) (2^normalizedDrawBits R P d h) :=
  let E : Table R P ≃ Table (normalizedMargin R) (normalizedMargin P) :=
    tableReindex (indexPermutation (marginPosition R)) (indexPermutation (marginPosition P)) R P
  (denseDrawCounts (normalizedMargin R) (normalizedMargin P) d hd
    (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP) finProdFinEquiv
    (by rw [normalizedMargin_total,normalizedMargin_total]; exact htotal) h
    (canonicalOrigin (m*n) d (by omega)) (E (canonicalFallback R P htotal))).equiv E.symm

theorem canonicalCounts_law :
    (canonicalCounts R P hd hR hP htotal h).toRational (by positivity)=
      mapLaw (uniformLaw (α := Fin (normalizedDrawBits R P d h) → Bool))
        (normalizedBooleanDraw R P hd hR hP htotal h
          (canonicalOrigin (m*n) d (by omega)) (canonicalFallback R P htotal)) := by
  let E : Table R P ≃ Table (normalizedMargin R) (normalizedMargin P) :=
    tableReindex (indexPermutation (marginPosition R)) (indexPermutation (marginPosition P)) R P
  let a := canonicalOrigin (m*n) d (show 0<d by omega)
  let ht : (∑ i,normalizedMargin R i)=∑ j,normalizedMargin P j := by
    rw [normalizedMargin_total,normalizedMargin_total]
    exact htotal
  let p : IntegerLaw (Table (normalizedMargin R) (normalizedMargin P))
      (2^normalizedDrawBits R P d h) :=
    denseDrawCounts (normalizedMargin R) (normalizedMargin P) d hd
      (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP)
      finProdFinEquiv ht h a (E (canonicalFallback R P htotal))
  let draw : (Fin (normalizedDrawBits R P d h) → Bool) →
      Table (normalizedMargin R) (normalizedMargin P) :=
    denseBooleanDraw (normalizedMargin R) (normalizedMargin P) d hd
      (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP)
      finProdFinEquiv ht h a (E (canonicalFallback R P htotal))
  have hp : p.toRational (by positivity)=
      mapLaw (uniformLaw (α := Fin (normalizedDrawBits R P d h) → Bool)) draw :=
    denseDrawCounts_law (normalizedMargin R) (normalizedMargin P) d hd
      (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP)
      finProdFinEquiv ht h a (E (canonicalFallback R P htotal))
  change (p.equiv E.symm).toRational (by positivity)=
    mapLaw (uniformLaw (α := Fin (normalizedDrawBits R P d h) → Bool))
      (fun bits => E.symm (draw bits))
  exact (IntegerLaw.toRational_equiv p E.symm (by positivity)).trans
    ((congrArg (equivLaw E.symm) hp).trans (mapLaw_equiv_output E.symm _ draw).symm)

theorem canonicalCounts_computed (hq : m*n≤d) (X : Table R P) :
    (canonicalDrawCounts ((marginCode R,marginCode P),(d,h))).getD
      (canonicalTableIndex (((marginCode R,marginCode P),(d,h)),tableOutput X)) 0=
      (canonicalCounts R P hd hR hP htotal h).count X :=
  canonicalDrawCounts_at R P hd hq hR hP htotal h X

/-- A reserved word contributes a power of two for its unused suffix. -/
def paddedCanonicalCounts (N : ℕ) (hN : normalizedDrawBits R P d h≤N) :
    IntegerLaw (Table R P) (2^N) :=
  ((canonicalCounts R P hd hR hP htotal h).scale
    (2^(N-normalizedDrawBits R P d h))).rebase (by rw [←pow_add,Nat.add_sub_of_le hN])

theorem paddedCanonicalCounts_law (N : ℕ) (hN : normalizedDrawBits R P d h≤N) :
    (paddedCanonicalCounts R P hd hR hP htotal h N hN).toRational (by positivity)=
      mapLaw (uniformLaw (α := Fin N → Bool))
        (fun bits => normalizedBooleanDraw R P hd hR hP htotal h
          (canonicalOrigin (m*n) d (by omega)) (canonicalFallback R P htotal)
          (prefixWord hN bits)) := by
  unfold paddedCanonicalCounts
  rw [IntegerLaw.toRational_rebase,IntegerLaw.toRational_scale,canonicalCounts_law]
  exact (padded_draw_law hN _).symm
  all_goals positivity

end
end ContingencyTables.DensePrograms

end OAI
