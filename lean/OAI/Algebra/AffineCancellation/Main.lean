import OAI.Algebra.AffineCancellation.Dimension
import OAI.Algebra.AffineCancellation.EquivariantLift

namespace OAI

noncomputable section

namespace ComplexCancellation
/-- The hypersurface algebra is not a polynomial algebra over ℂ. -/
theorem nonpolynomiality : ¬ Nonempty (A ≃ₐ[ℂ] MvPolynomial (Fin 4) ℂ) := by
  rintro ⟨e⟩
  obtain ⟨i,r,D,hi,hrn,hr,hD,hDn,hDr⟩ := Rees.positive_invariant_of_polynomial e
  obtain ⟨c,E,hcn,hE,hEn,he,hcomm⟩ := PolynomialTorsor.exists_equivariant_lift D hD hDn
  let w := Bundle.pullback r
  have hw : w ≠ 0 := by
    intro hz
    apply hrn
    exact Bundle.pullback_injective (by simpa only [map_zero] using hz)
  have hwg : w ∈ Bundle.valuationPieces i := Bundle.pullback_graded i r hr
  have hEw : E w=0 := by rw [he,hDr,mul_zero,map_zero]
  obtain ⟨j,hjn,_hb,hjln⟩ := GradedLND.highest Bundle.valuationPieces E hEn hE
  have hcw : GradedLND.component Bundle.valuationPieces E j w=0 := by
    rw [GradedLND.component_of_mem Bundle.valuationPieces E j hwg,hEw,map_zero]
  exact Bundle.no_positive_invariant (GradedLND.component Bundle.valuationPieces E j)
    hjln hjn j
    (fun _ _ hz => GradedLND.component_homogeneous Bundle.valuationPieces E j hz)
    (GradedLND.component_commute Bundle.valuationPieces E Bundle.fiberEuler
      Bundle.fiberEuler_homogeneous hcomm j)
    w hw i hi hwg hcw

/-- A four-dimensional complex domain with polynomial cylinder, but not itself polynomial. -/
theorem main : MainStatement :=
  ⟨finiteType,domain,dimension,stabilization,nonpolynomiality⟩
end ComplexCancellation

end

end OAI
