import OAI.Geometry.NodalSets.Elliptic.RealJetProductExpansion

namespace OAI

namespace Yau.Geometry
open Yau.Analysis
open scoped ContDiff
noncomputable section

lemma realJetErrorSource_expansion (V W : Yau.Jets.Coord → ℝ)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (ds : List (Fin 4)) :
    realJetErrorSource V W ds = fun x ↦
      -realJetProductSum V W (realJetErrorTerms [] ds) x := by
  induction ds with
  | nil => funext x; simp [realJetErrorSource,realJetErrorTerms,realJetProductSum]
  | cons l ds ih =>
    funext x
    rw [realJetErrorSource,ih,realJetProductSum_error_cons V W hV hW]
    simp only [List.nil_append,Yau.coordPartial,fderiv_fun_neg,_root_.neg_apply]
    ring

lemma realJetErrorFlux_expansion (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (W : Yau.Jets.Coord → ℝ) (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j))
    (hW : ContDiff ℝ ∞ W) (ds : List (Fin 4)) :
    realJetErrorFlux C W ds = fun x i ↦
      -∑ j, realJetProductSum (fun y ↦ C y i j) W (realJetErrorTerms [j] ds) x := by
  induction ds with
  | nil => funext x i; simp [realJetErrorFlux,realJetErrorTerms,realJetProductSum]
  | cons l ds ih =>
    funext x i
    rw [realJetErrorFlux,ih]
    dsimp only
    have hn (H : Yau.Jets.Coord → ℝ) :
        Yau.coordPartial (fun y ↦ -H y) x l = -Yau.coordPartial H x l := by
      simp [Yau.coordPartial]
    rw [hn,Yau.real_coordPartial_sum _ (fun j ↦
      realJetProductSum_smooth _ W (hC i j) hW (realJetErrorTerms [j] ds))]
    simp_rw [realJetProductSum_error_cons _ W (hC i _) hW]
    simp only [List.singleton_append,Finset.sum_add_distrib,realDerivativeErrorFlux,
      partialJet,Yau.coordPartial]
    ring

end
end Yau.Geometry

end OAI
