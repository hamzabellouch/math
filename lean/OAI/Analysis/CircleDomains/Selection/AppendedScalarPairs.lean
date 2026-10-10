import OAI.Analysis.CircleDomains.Rigidity.LipschitzTracePairs

namespace OAI

/-! Pair-nullity for the exact finite list obtained by adjoining two
scalar tests. The first two coordinates are the new tests. -/
open Set Function MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem trace_pair_null_symm {X : Type*} {S : Set X} {u v : X → ℝ}
    (h : volume ((fun x => (u x, v x)) '' S) = 0) :
    volume ((fun x => (v x, u x)) '' S) = 0 := by
  have he : (fun x : ℝ × ℝ => (x.2,x.1)) = Prod.swap := by
    funext x
    cases x
    rfl
  have hs : LipschitzWith (1 : ℝ≥0) (Prod.swap : ℝ × ℝ → ℝ × ℝ) := by
    rw [← he]
    simpa only [max_self] using (LipschitzWith.prod_snd (α := ℝ) (β := ℝ)).prodMk LipschitzWith.prod_fst
  have hh := lipschitz_plane_image_null hs h
  simpa only [image_image, Function.comp_def, Prod.swap_prod_mk] using hh

 def appendScalarPair {X : Type*} {m : ℕ} (u : Fin m → X → ℝ) (p q : X → ℝ) :
    Fin (m+2) → X → ℝ := Fin.cases q (Fin.cases p u)

 theorem appendScalarPair_pair_null {X : Type*} {S : Set X} {m : ℕ}
    (u : Fin m → X → ℝ) (p q : X → ℝ)
    (hu : ∀ i j, i ≠ j → volume ((fun x => (u i x,u j x)) '' S) = 0)
    (hp : ∀ i, volume ((fun x => (u i x,p x)) '' S) = 0)
    (hq : ∀ i, volume ((fun x => (u i x,q x)) '' S) = 0)
    (hqp : volume ((fun x => (q x,p x)) '' S) = 0) :
    ∀ i j, i ≠ j → volume ((fun x =>
      (appendScalarPair u p q i x,appendScalarPair u p q j x)) '' S) = 0 := by
  intro i j hij
  refine Fin.cases ?_ (fun a => ?_) i hij
  · refine Fin.cases (fun h => (h rfl).elim) (fun b _ => ?_) j
    refine Fin.cases ?_ (fun k => ?_) b
    · exact hqp
    · exact trace_pair_null_symm (hq k)
  · refine Fin.cases (fun _ => ?_) (fun b hab => ?_) j
    · refine Fin.cases ?_ (fun k => ?_) a
      · exact trace_pair_null_symm hqp
      · exact hq k
    · refine Fin.cases ?_ (fun k => ?_) a hab
      · refine Fin.cases (fun h => (h rfl).elim) (fun l _ => ?_) b
        exact trace_pair_null_symm (hp l)
      · refine Fin.cases (fun _ => ?_) (fun l h => ?_) b
        · exact hp k
        · exact hu k l (fun he => h (congrArg (fun n => n.succ.succ) he))

end CircleDomainRigidity

end

end OAI
