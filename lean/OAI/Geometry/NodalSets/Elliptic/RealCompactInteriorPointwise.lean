import OAI.Geometry.NodalSets.Elliptic.CompactSmoothExtension
import OAI.Geometry.NodalSets.Elliptic.PartialJetGerm
import OAI.Geometry.NodalSets.Elliptic.RealCompactTestDerivative
import OAI.Geometry.NodalSets.Elliptic.RealFiniteJetSquare
import OAI.Geometry.NodalSets.Elliptic.RealSmoothCutoffJetBound

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Filter Yau.Analysis
open scoped ContDiff Topology
noncomputable section

theorem real_compact_interior_pointwise {K Q : Set Yau.Jets.Coord}
    (hK : IsCompact K) (hQ : IsCompact Q) (hKQ : K ⊆ interior Q) (n : ℕ) :
    ∃ A > 0, ∀ W : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ W →
      ∀ ds : List (Fin 4), ds.length ≤ n → ∀ x ∈ K,
        (partialJet W ds x)^2 ≤ A*(∫ y in Q, realFiniteJetSquare W (n+5) y) := by
  obtain ⟨eta,he,hc,hs,hr,hone⟩ := compact_smooth_cutoff hK isOpen_interior hKQ
  obtain ⟨A,hA,ha⟩ := Yau.real_smooth_cutoff_jet_bound hQ eta he hc hs n
  refine ⟨A,hA,fun W hW ds hds x hx ↦ ?_⟩
  let U := partialJet W
  have hU (es : List (Fin 4)) : MemLp (U es) 2 (volume.restrict Q) :=
    Yau.real_continuous_memLp_compact hQ _ (partialJet_smooth W hW es).continuous
  have hw : ∀ es : List (Fin 4), es.length ≤ n+4 → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ y in Q, U es y*Yau.coordPartial psi y i) = -(∫ y in Q, U (i::es) y*psi y) := by
    intro es _ i psi hp hpc hps
    have hh := (Yau.real_compact_test_derivative (U es) psi
      (partialJet_smooth W hW es) hp hpc i Q hps).2.2
    simpa only [U,partialJet,Yau.coordPartial,neg_neg] using congrArg Neg.neg hh.symm
  have hi : IntegrableOn (realFiniteJetSquare W (n+5)) Q :=
    (realFiniteJetSquare_smooth W hW (n+5)).continuous.continuousOn.integrableOn_compact hQ
  have hE : 0 ≤ ∫ y in Q, realFiniteJetSquare W (n+5) y :=
    integral_nonneg (fun y ↦ realFiniteJetSquare_nonneg W (n+5) y)
  have hbound (es : List (Fin 4)) (hes : es.length ≤ n+4) :
      (∫ y in Q, (U es y)^2) ≤ ∫ y in Q, realFiniteJetSquare W (n+5) y := by
    exact integral_mono (hU es).integrable_sq hi
      (fun y ↦ partialJet_sq_le_realFiniteJetSquare W (n+5) es (by omega) y)
  let v := fun y ↦ eta y*W y
  have hv : ContDiff ℝ ∞ v := he.mul hW
  have hvc : HasCompactSupport v := hc.mul_right
  have hvW : v =ᶠ[𝓝 x] W := by
    filter_upwards [hone x hx] with y hy
    simp [v,hy]
  have h := ha U (fun es _ ↦ hU es) hw _ hE hbound v hv hvc
    (Filter.Eventually.of_forall (fun _ ↦ rfl)) ds hds x
  rw [partialJet_germ_eq v W x hvW ds] at h
  exact h

end
end Yau.Geometry

end OAI
