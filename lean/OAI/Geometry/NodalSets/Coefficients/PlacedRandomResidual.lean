import OAI.Geometry.NodalSets.Coefficients.LatticeResidualSupport
import OAI.Geometry.NodalSets.Coefficients.PlacedEnvelopeResidualWaves

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Yau.Probability Set Metric Filter
open scoped ContDiff Topology
noncomputable section

theorem PlacedEnvelopeData.random_residual {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T) (ha : 0 ≤ a)
    (hg : ContDiffOn ℝ ∞ g seedCoordBranch)
    (hs : ∀ x ∈ seedCoordBranch, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ seedCoordBranch, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiffOn ℝ ∞ w seedCoordBranch)
    (hwp : ∀ x ∈ seedCoordBranch, 0 < w x) (k0 K' : ℕ) :
    ∃ b : LocalCompactWaveData g w d.S (closure d.U)
        (3*(K'+3)+4*k0+6) ((K'+3)+k0+1) (K'+3) k0,
      b.E ⊆ d.V ∧ ∃ C > 0, ∃ Q : Set Coord,
        IsCompact Q ∧ Q ⊆ d.Ω ∧ closure d.U ⊆ interior Q ∧
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n),
          letI := hfin
          ∀ coeff : ((SourceGrid d.U n × Fin 3) × Fin 2) → ℝ,
            let u := gaussianWaveField
              (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff
            let residual := fun x ↦ sourceWeightedOperator g w (fun z ↦ (u z:ℂ)) x+
              ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*(u x:ℂ)
            tsupport u ⊆ Q ∧ tsupport residual ⊆ Q ∧
            (∀ x ∉ Q, ∀ k : ℕ, iteratedFDeriv ℝ k residual x = 0) ∧
            (coeff ∈ coefficientEvent (n:ℝ) → ContDiff ℝ ∞ residual ∧
              ∀ x : Coord, DerivativeBound k0 residual x
                (C*(n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*d.S x))) := by
  obtain ⟨b,hb⟩ := d.waves_in_domain ha hg hs hp w hw hwp k0 (K'+3)
  have hUb : Bornology.IsBounded d.U := d.compact_closure_U.isBounded.subset subset_closure
  have hbwp : ∀ x ∈ b.E, w x ≠ 0 := fun x hx ↦ ne_of_gt (hwp x (d.V_branch (hb hx)))
  obtain ⟨C,hC,hbound⟩ := b.lattice_residual_accuracy K' hbwp subset_closure hUb
  obtain ⟨Q,hQ,hQΩ,hUQ,hsupport⟩ := b.lattice_residual_support d.compact_closure_U
    subset_closure hUb d.open_Ω d.closure_U_Ω
  refine ⟨b,hb,C,hC,Q,hQ,hQΩ,hUQ,?_⟩
  filter_upwards [hbound,hsupport] with n hn hsupp
  obtain ⟨hfin,hn⟩ := hn
  obtain ⟨hfin',hsupp⟩ := hsupp
  have he : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  refine ⟨hfin,?_⟩
  intro coeff
  exact ⟨(hsupp coeff).1,(hsupp coeff).2.1,(hsupp coeff).2.2,hn coeff⟩

end
end Yau.Target

end OAI
