import OAI.Analysis.KadisonKastler.RemoteSiteDoubling
import OAI.Analysis.KadisonKastler.SpatialStateScaling
import OAI.Analysis.KadisonKastler.PointedCyclicEquivalence
import OAI.Analysis.KadisonKastler.PointedMatrixSum
import OAI.Analysis.KadisonKastler.TwoRatioFiniteMatrix

namespace OAI

/-! # A state-preserving copy beyond each finite product stage -/

namespace KadisonKastler

open Generator UnitalTomsWinter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

def remoteDoubleUnitary (n : ℕ) : SpatialHilbert H H ≃ₗᵢ[ℂ] H :=
  (S.sum S).reindexEquivalence S (remoteTwoRatioDoubling n)
    (remoteTwoRatioDoubling_parameter n)

theorem remoteDoubleUnitary_vector (n : ℕ) :
    S.remoteDoubleUnitary n (tensorVector Ω Ω)=Ω :=
  (S.sum S).reindexEquivalence_vector S _ _

theorem remoteDoubleUnitary_algebra (n : ℕ) :
    spatialTransportAlgebra (S.remoteDoubleUnitary n) (spatialProductAlgebra M M)=M :=
  (S.sum S).reindexEquivalence_algebra S _ _

def remoteCopy (n : ℕ) : Algebra M →⋆ₐ[ℂ] Algebra M :=
  (((S.remoteDoubleUnitary n).conjStarAlgEquiv.toStarAlgHom.comp
    (spatialLeft (K := H))).comp M.toStarSubalgebra.subtype).codRestrict M.toStarSubalgebra
      (by
        intro a
        have hm : (S.remoteDoubleUnitary n).conjStarAlgEquiv (spatialLeft a.val) ∈
            spatialTransportAlgebra (S.remoteDoubleUnitary n) (spatialProductAlgebra M M) := by
          apply (mem_spatialTransportAlgebra _ _ _).mpr
          rw [StarAlgEquiv.symm_apply_apply]
          exact spatialLeft_mem_product M M a.property
        rwa [S.remoteDoubleUnitary_algebra n] at hm)

theorem remoteCopy_val (n : ℕ) (a : Algebra M) :
    (S.remoteCopy n a).val=
      (S.remoteDoubleUnitary n).conjStarAlgEquiv (spatialLeft a.val) := rfl

theorem remoteCopy_scales (n : ℕ) (a : Algebra M) {r : ℝ}
    (ha : StateScales M Ω r a.val) : StateScales M Ω r (S.remoteCopy n a).val := by
  have hh := (ha.spatialLeft (N := M) (ξ := Ω)).spatial_conjugate (S.remoteDoubleUnitary n)
  rw [S.remoteDoubleUnitary_vector,S.remoteDoubleUnitary_algebra] at hh
  exact hh

theorem remoteCopy_commutes_site (n : ℕ) (a : Algebra M) (i : TwoRatioSite)
    (hi : i ∈ twoRatioFiniteSites n) (b c : Fin 2) :
    Commute ((S.site i).entry b c) (S.remoteCopy n a).val := by
  let U := S.remoteDoubleUnitary n
  have he : U.conjStarAlgEquiv (spatialRight ((S.site i).entry b c)) =
      (S.site i).entry b c := by
    have hh := (S.sum S).reindexEquivalence_conjugate_site S
      (remoteTwoRatioDoubling n) (remoteTwoRatioDoubling_parameter n) (Sum.inr i) b c
    rw [remoteTwoRatioDoubling_prefix hi] at hh
    exact hh
  have hc : Commute (spatialRight (H := H) ((S.site i).entry b c))
      (spatialLeft (K := H) a.val) := by
    change spatialTensorOp 1 ((S.site i).entry b c)*spatialTensorOp a.val 1 =
      spatialTensorOp a.val 1*spatialTensorOp 1 ((S.site i).entry b c)
    rw [← spatialTensorOp_mul,← spatialTensorOp_mul]
    simp only [one_mul,mul_one]
  have hh := hc.map U.conjStarAlgEquiv.toMonoidHom
  change Commute (U.conjStarAlgEquiv (spatialRight ((S.site i).entry b c)))
    (U.conjStarAlgEquiv (spatialLeft a.val)) at hh
  rw [he] at hh
  exact hh

theorem remoteCopy_commutes_stage (n : ℕ) (a : Algebra M)
    (b : H →L[ℂ] H) (hb : b ∈ (S.twoRatioMatrix n).algebra) :
    Commute b (S.remoteCopy n a).val := by
  rw [S.twoRatioMatrix_algebra] at hb
  apply ((S.finiteBlock (twoRatioFiniteSites n) (twoRatioFiniteSites_nodup n)).commute_algebra_iff
    (S.remoteCopy n a).val).mpr ?_ b hb
  intro r c
  change Commute (S.blockEntry (twoRatioFiniteSites n) r c) (S.remoteCopy n a).val
  have hall : ∀ (l : List TwoRatioSite) (r c : MatrixSiteBlockIndex l),
      (∀ i ∈ l, i ∈ twoRatioFiniteSites n) →
      Commute (S.blockEntry l r c) (S.remoteCopy n a).val := by
    intro l
    induction l with
    | nil => intro r c hi; exact Commute.one_left _
    | cons i l ih =>
      intro r c hi
      exact (S.remoteCopy_commutes_site n a i (hi i (by simp)) r.1 c.1).mul_left
        (ih r.2 c.2 (fun j hj => hi j (List.mem_cons_of_mem i hj)))
  exact hall _ r c (fun _ h => h)

end PointedMatrixSites

end

end KadisonKastler

end OAI
