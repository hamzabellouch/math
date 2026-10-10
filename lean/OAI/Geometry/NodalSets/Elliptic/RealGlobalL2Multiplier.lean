import OAI.Geometry.NodalSets.Elliptic.RealCompactL2MapLemmas
import OAI.Geometry.NodalSets.Elliptic.RealL2DifferenceLimit

namespace OAI

namespace Yau
open MeasureTheory Set
noncomputable section

def realL2RestrictLinear {n : ℕ} (K : Set (Fin n → ℝ)) :
    RealEuclideanL2 n →ₗ[ℝ] Lp ℝ 2 (volume.restrict K) where
  toFun u := ((Lp.memLp u).mono_measure Measure.restrict_le_self).toLp u
  map_add' u v :=
    (MemLp.toLp_congr _ _ (ae_restrict_of_ae (Lp.coeFn_add u v))).trans
      (MemLp.toLp_add ((Lp.memLp u).mono_measure Measure.restrict_le_self)
        ((Lp.memLp v).mono_measure Measure.restrict_le_self))
  map_smul' t u :=
    (MemLp.toLp_congr _ _ (ae_restrict_of_ae (Lp.coeFn_smul t u))).trans
      (MemLp.toLp_const_smul t ((Lp.memLp u).mono_measure Measure.restrict_le_self))

theorem realL2RestrictLinear_bound {n : ℕ} (K : Set (Fin n → ℝ)) (u : RealEuclideanL2 n) :
    ‖realL2RestrictLinear K u‖ ≤ 1*‖u‖ := by
  change ‖((Lp.memLp u).mono_measure Measure.restrict_le_self).toLp u‖ ≤ _
  rw [one_mul,Lp.norm_toLp,Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp u).ne (eLpNorm_mono_measure u Measure.restrict_le_self)

def realL2RestrictMap {n : ℕ} (K : Set (Fin n → ℝ)) :
    RealEuclideanL2 n →L[ℝ] Lp ℝ 2 (volume.restrict K) :=
  (realL2RestrictLinear K).mkContinuous 1 (realL2RestrictLinear_bound K)

theorem realL2RestrictMap_ae {n : ℕ} (K : Set (Fin n → ℝ)) (u : RealEuclideanL2 n) :
    (realL2RestrictMap K u : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict K] u :=
  ((Lp.memLp u).mono_measure Measure.restrict_le_self).coeFn_toLp

def realGlobalCompactMap {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (eta : (Fin n → ℝ) → ℝ) (he : Continuous eta) (hs : tsupport eta ⊆ K) :
    RealEuclideanL2 n →L[ℝ] RealEuclideanL2 n :=
  (realCompactL2Map hK eta he hs).comp (realL2RestrictMap K)

theorem realGlobalCompactMap_ae {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (eta : (Fin n → ℝ) → ℝ) (he : Continuous eta) (hs : tsupport eta ⊆ K)
    (u : RealEuclideanL2 n) (v : (Fin n → ℝ) → ℝ)
    (hv : (u : (Fin n → ℝ) → ℝ) =ᵐ[volume] v) :
    (realGlobalCompactMap hK eta he hs u : (Fin n → ℝ) → ℝ) =ᵐ[volume] (fun x ↦ eta x*v x) :=
  (realCompactL2Map_ae hK eta he hs _).trans
    (real_compact_mul_ae hK.measurableSet eta _ _ hs
      ((realL2RestrictMap_ae K u).trans (ae_restrict_of_ae hv)))

end
end Yau

end OAI
