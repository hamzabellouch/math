import OAI.LinearAlgebra.MatrixMultiplication.Recovery.GroupOrbitProjection

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

namespace MatrixMultiplication.RecoveryOrbitDecisions

theorem orbitSet_instances {G X : Type*} [Group G] [MulAction G X]
    (f₁ f₂ : Fintype G) (d₁ d₂ : DecidableEq X) (x : X) :
    @OrbitCounting.orbitSet G X _ _ f₁ d₁ x =
      @OrbitCounting.orbitSet G X _ _ f₂ d₂ x := by
  apply Finset.ext
  intro y
  simp only [OrbitCounting.orbitSet, Finset.mem_image, Finset.mem_univ, true_and]

theorem orbitSet_eq_transportedOrbit {G X Y : Type*} [Group G] [MulAction G Y]
    (fRaw fCanonical : Fintype G) (d : DecidableEq X) (e : X ≃ Y) (x : X) :
    @OrbitCounting.orbitSet G X _ (EquivOrbitTransport.action e) fRaw d x =
      @GroupOrbitProjection.transportedOrbit G X Y _ fCanonical _ e x := by
  unfold GroupOrbitProjection.transportedOrbit
  exact @orbitSet_instances G X _ (EquivOrbitTransport.action e)
    fRaw fCanonical d _ x

theorem transportedOrbit_eq_orbitSet {G X Y : Type*} [Group G] [MulAction G Y]
    (fCanonical fRaw : Fintype G) (d : DecidableEq X) (e : X ≃ Y) (x : X) :
    @GroupOrbitProjection.transportedOrbit G X Y _ fCanonical _ e x =
      @OrbitCounting.orbitSet G X _ (EquivOrbitTransport.action e) fRaw d x :=
  (orbitSet_eq_transportedOrbit fRaw fCanonical d e x).symm

end MatrixMultiplication.RecoveryOrbitDecisions

end OAI
