import OAI.Algebra.Finitistic.Ordinary.OrdinaryFiniteConeReindex

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.FiniteColumnComplex
universe u
variable {R : Type u} [Ring R] {l : ℕ}
variable (K L : Fin l → CochainComplex (ModuleCat.{u} R) ℤ)
variable (δ : Differential K) (ε : Differential L)
variable (f : ∀ i, K i ⟶ L i)
variable (hc : ∀ n,
    (ε.d n).comp (componentMap K L f n) = (componentMap K L f (n+1)).comp (δ.d n))

abbrev coneSource (n : ℤ) (z : term (coneColumn K L f) n) : term K (n+1) :=
  fun i => (ConeCoordinates.coordinateEquiv (f i) n (z i)).1
abbrev coneTarget (n : ℤ) (z : term (coneColumn K L f) n) : term L n :=
  fun i => (ConeCoordinates.coordinateEquiv (f i) n (z i)).2

theorem coneEquiv_symm_pair (n : ℤ) (z : term (coneColumn K L f) n) :
    ConeCoordinates.coordinateEquiv (complexMap K L δ ε f hc) n
      ((coneEquiv K L δ ε f hc n).symm z) = (coneSource K L f n z,coneTarget K L f n z) := by
  apply Prod.ext
  · funext i
    exact congrArg Prod.fst (coneEquiv_symm_coordinate K L δ ε f hc n z i)
  · funext i
    exact congrArg Prod.snd (coneEquiv_symm_coordinate K L δ ε f hc n z i)

/-- The conjugated genuine cone differential has the expected finite-column formula. -/
theorem coneDifferential_coordinate (n : ℤ) (z : term (coneColumn K L f) n) (i : Fin l) :
    ConeCoordinates.coordinateEquiv (f i) (n+1) (coneDifferential K L δ ε f hc n z i) =
      (-(δ.d (n+1) (coneSource K L f n z)) i,
       ((f i).f (n+1)).hom (coneSource K L f n z i) + (ε.d n (coneTarget K L f n z)) i) := by
  change ConeCoordinates.coordinateEquiv (f i) (n+1)
    (coneEquiv K L δ ε f hc (n+1)
      (((totalCone K L δ ε f hc).d n (n+1)).hom ((coneEquiv K L δ ε f hc n).symm z)) i) = _
  rw [coneEquiv_coordinate,ConeCoordinates.differential_fst,ConeCoordinates.differential_snd,
    coneEquiv_symm_pair]
  simp only [complex_d_hom]
  rfl

/-- The cone of a componentwise total map is triangular with the actual column cones on its diagonal. -/
def coneTriangular : Differential (coneColumn K L f) where
  d := coneDifferential K L δ ε f hc
  square := coneDifferential_square K L δ ε f hc
  triangular n i z hz := by
    apply (ConeCoordinates.coordinateEquiv (f i) (n+1)).injective
    rw [coneDifferential_coordinate]
    have hSource : ∀ j : Fin l, j.val < i.val → coneSource K L f n z j = 0 := by
      intro j hj
      simp only [coneSource,hz j hj,map_zero,Prod.fst_zero]
    have hTarget : ∀ j : Fin l, j.val < i.val → coneTarget K L f n z j = 0 := by
      intro j hj
      simp only [coneTarget,hz j hj,map_zero,Prod.snd_zero]
    rw [δ.triangular (n+1) i _ hSource,ε.triangular n i _ hTarget]
    apply Prod.ext
    · exact (ConeCoordinates.differential_fst (f i) n (z i)).symm
    · exact (ConeCoordinates.differential_snd (f i) n (z i)).symm

/-- The triangular cone model is isomorphic to the native cone, not an assumed cone replacement. -/
def coneIso : totalCone K L δ ε f hc ≅ complex (coneColumn K L f) (coneTriangular K L δ ε f hc) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (coneEquiv K L δ ε f hc n).toModuleIso) (by
    intro n m h
    change n+1=m at h
    subst m
    rw [complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change coneEquiv K L δ ε f hc (n+1)
      (((totalCone K L δ ε f hc).d n (n+1)).hom
        ((coneEquiv K L δ ε f hc n).symm (coneEquiv K L δ ε f hc n z))) =
      coneEquiv K L δ ε f hc (n+1) (((totalCone K L δ ε f hc).d n (n+1)).hom z)
    rw [LinearEquiv.symm_apply_apply])

/-- Quasi-isomorphisms in every column induce a quasi-isomorphism of the actual finite totals. -/
theorem complexMap_quasiIso [∀ i, QuasiIso (f i)] : QuasiIso (complexMap K L δ ε f hc) := by
  apply (LittleFinitistic.quasiIso_iff_mappingCone_acyclic _).mpr
  have ha := acyclic (coneColumn K L f) (coneTriangular K L δ ε f hc)
    (fun i => (LittleFinitistic.quasiIso_iff_mappingCone_acyclic (f i)).mp inferInstance)
  intro n
  exact (exactAt_iff_of_quasiIsoAt (coneIso K L δ ε f hc).hom n).mpr (ha n)
end LittleFinitistic.FiniteColumnComplex

end

end OAI
