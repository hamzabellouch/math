import OAI.Geometry.NodalSets.Coefficients.FiniteResidualBound
import OAI.Geometry.NodalSets.Elliptic.SeedDerivativeBounds
import OAI.Geometry.NodalSets.Elliptic.SeedLogExtension

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Filter Manifold
open scoped ContDiff Topology
noncomputable section

def seedCoordinateField (N : ℕ) : Coord → ℝ :=
  ambientRealSeed N ∘ seedChartAmbient ∘ seedCoordEquiv

lemma seedCoordinateField_literal (N : ℕ) (x : Coord) :
    seedCoordinateField N x = sphericalSeed N
      ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)) := rfl

lemma seedCoordinateField_smooth (N : ℕ) : ContDiff ℝ ∞ (seedCoordinateField N) :=
  (ambientRealSeed_contDiff N).comp (seedChartAmbient_smooth.comp seedCoordEquiv.contDiff)

lemma seedCoordinateField_log (N : ℕ) {x : Coord} (hx : x ∈ seedCoordBranch) :
    seedCoordinateField N x = oscillatorySeed seedCoordReal seedCoordImag (N:ℝ) x :=
  ambientSeed_log_trigonometric N hx

lemma seedCoordinateField_log_germ (N : ℕ) {x : Coord} (hx : x ∈ seedCoordBranch)
    (S0 T0 : Coord → ℝ) (hS : S0 =ᶠ[𝓝 x] seedCoordReal)
    (hT : T0 =ᶠ[𝓝 x] seedCoordImag) :
    seedCoordinateField N =ᶠ[𝓝 x] oscillatorySeed S0 T0 (N:ℝ) := by
  filter_upwards [seedCoordBranch_open.mem_nhds hx,hS,hT] with z hz hs ht
  rw [seedCoordinateField_log N hz]
  simp only [oscillatorySeed,hs,ht]

theorem seedCoordinateField_derivative_bound {Q : Set Coord}
    (hQ : IsCompact Q) (hQB : Q ⊆ seedCoordBranch) (k : ℕ) :
    ∃ C > 0, ∀ N : ℕ, 0 < N → ∀ x ∈ Q,
      ‖iteratedFDeriv ℝ k (seedCoordinateField N) x‖ ≤
        C*(N:ℝ)^k*Real.exp ((N:ℝ)*seedCoordReal x) := by
  obtain ⟨S0,T0,hS,hT,_,_,_,_,he⟩ := seed_log_compact_extensions hQ hQB
  obtain ⟨C,hC,hbound⟩ := oscillatorySeed_derivative_bound S0 T0 hS hT hQ k
  refine ⟨C,hC,?_⟩
  intro N hN x hx
  have hlog := seedCoordinateField_log_germ N (hQB hx) S0 T0 (he x hx).1 (he x hx).2
  rw [(hlog.iteratedFDeriv ℝ k).eq_of_nhds]
  simpa only [(he x hx).1.eq_of_nhds] using hbound (N:ℝ) (by exact_mod_cast hN) x hx

theorem seedCoordinateField_derivativeBound {Q : Set Coord}
    (hQ : IsCompact Q) (hQB : Q ⊆ seedCoordBranch) (k : ℕ) :
    ∃ C > 0, ∀ N : ℕ, 0 < N → ∀ x ∈ Q,
      DerivativeBound k (fun z ↦ (seedCoordinateField N z:ℂ)) x
        (C*(N:ℝ)^k*Real.exp ((N:ℝ)*seedCoordReal x)) := by
  have hb (j : Fin (k+1)) := seedCoordinateField_derivative_bound hQ hQB j.val
  choose b hb hbound using hb
  let C : ℝ := ∑ j, b j
  have hC : 0 < C := (hb ⟨0,by omega⟩).trans_le
    (Finset.single_le_sum (fun j _ ↦ (hb j).le) (Finset.mem_univ _))
  refine ⟨C,hC,?_⟩
  intro N hN x hx j hj
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hbj : b ⟨j,by omega⟩ ≤ C :=
    Finset.single_le_sum (fun j _ ↦ (hb j).le) (Finset.mem_univ _)
  exact (complexified_iterated_norm_le _ (seedCoordinateField_smooth N) j x).trans
    ((hbound ⟨j,by omega⟩ N hN x hx).trans (by gcongr))

end
end Yau.Target

end OAI
