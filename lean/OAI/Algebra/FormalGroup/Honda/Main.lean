import OAI.Algebra.FormalGroup.Honda.HeightTransport

namespace OAI

universe uK

noncomputable section

namespace HeightThree.HondaTarget
open HeightThree.HondaConstruction HeightThree.HondaCoordinates HeightThree.HondaSpecialFiber
open HeightThree.CanonicalUniversality HeightThree.HondaClassification
open HeightThree.CoordinateTransport HeightThree.UniversalTransport HeightThree.HeightTransport

theorem universal_framed_honda_height_coordinates
    (p : ℕ) [Fact p.Prime] (_ : 5 ≤ p)
    (K : Type uK) [Field K] [Finite K] [CharP K p]
    (_ : Nonempty (GaloisField p 6 →+* K))
    (Γ : FormalGroup K) [Γ.IsComm]
    (hΓ : multiplicationSeries Γ p = PowerSeries.X ^ (p^3)) :
    HasUniversalHeightCoordinates p Γ := by
  obtain ⟨e,he⟩ := strict_honda_isomorphic p 3 Γ (hondaLaw p K) hΓ (integralSpecial_honda p K)
  let c := Coordinate.ofIso e
  let cB := c.map (algebraMap K (Base K))
  have hc : c.transport (hondaLaw p K)=Γ := Coordinate.transport_ofIso e
  have hcB : cB.map MvPowerSeries.constantCoeff=c := by
    rw [show cB=c.map (algebraMap K (Base K)) from rfl,coordinate_map_map]
    have hh : MvPowerSeries.constantCoeff.comp (algebraMap K (Base K))=RingHom.id K := by
      ext a
      simp [MvPowerSeries.algebraMap_apply]
    rw [hh,coordinate_map_id]
  have hs : cB.series.coeff 1=1 := strict_map c he _
  refine ⟨cB.transport (reducedHonda p K),inferInstance,?_,?_,?_⟩
  · rw [cB.transport_map,hcB,reducedHonda_specialFiber,hc]
  · have hh := isUniversal_transport (hondaLaw p K) (reducedHonda p K)
      (reducedHonda_isUniversal p K) c
    rwa [hc] at hh
  · exact heightCoordinates_transport p _ (reducedHonda_heightCoordinates p K) cB hs

end HeightThree.HondaTarget

end

end OAI
