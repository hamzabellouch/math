import OAI.Probability.DilutedSpin.MarkerNormalization

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
noncomputable local instance markerRootIdentityDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Z C : Type} [MeasurableSpace Z] [Fintype C] {n : ℕ}

/-- A marker identity controls the covariance of two whole overlaps, not
just a selected coordinate or a conditional covariance. All constants and
both actual finite-tree marginals are explicitly retained. -/
theorem marker_root_covariance (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S T Q : PrescribedTree n) (a : S.Leaf) (e : C ≃ S.Leaf)
    (q : Option C → T.Leaf) (hq : Function.Bijective q)
    (qold : S.Leaf → Q.Leaf) (qfresh : C → Q.Leaf)
    (hqQ : Function.Bijective (Sum.elim qold qfresh))
    (hold : ∀ d b, splitDepth S d b=splitDepth Q (qold d) (qold b))
    (hfresh : ∀ c d, splitDepth S (e c) (e d)=splitDepth Q (qfresh c) (qfresh d))
    (hmarker : ∀ x y, splitDepth T (q x) (q y)=
      splitDepth Q (Option.elim' (qold a) qfresh x) (Option.elim' (qold a) qfresh y))
    (hsep : ∀ c d, splitDepth Q (qfresh c) (qold a)<splitDepth Q (qold a) (qold d))
    (K : (z : Z) → KernelTower (Ω z) n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n)=1)
    (cs : List C) (hcs : cs.Nodup) (hfull : cs.toFinset=Finset.univ)
    (F : (z : Z) → (S.Leaf → FinitePath (Ω z) n) → ℝ) :
    matrixRootCovariance μ Ω T S q K m (cs.map some) a
      (fun z x => F z (fun d => x (some (e.symm d))))
      (fun z w => F z (fun d => S.pathAt d w)) =
    partialKappa T m (Finset.univ.image q) *
      ((∫ z, (Q.sampleLaw (K z)).expect (fun w =>
        F z (fun d => Q.pathAt (qold d) w) *
        F z (fun d => Q.pathAt (qfresh (e.symm d)) w)) ∂μ) -
      (∫ z, (S.sampleLaw (K z)).expect (fun w => F z (fun d => S.pathAt d w)) ∂μ)^2) := by
  classical
  have hmem (c : C) : c ∈ cs := by
    have : c ∈ cs.toFinset := by rw [hfull]; simp
    simpa using this
  have hmarg (z : Z) :
      (T.sampleLaw (K z)).expect (fun w => F z (fun d => T.pathAt (q (some (e.symm d))) w)) =
      (S.sampleLaw (K z)).expect (fun w => F z (fun d => S.pathAt d w)) := by
    have h := matrix_paths_expect S T id Function.surjective_id
      (fun d => q (some (e.symm d))) (by
        intro d b
        rw [hmarker]
        dsimp only [Option.elim',id_eq]
        rw [← hfresh,e.apply_symm_apply,e.apply_symm_apply]) (K z) (F z)
    exact h
  have holdHist (z : Z) := marker_history_joint S T Q a q hq qold qfresh hqQ hold
    hmarker hsep (K z) m hm hp hend cs hcs hfull (F z)
    (fun x => F z (fun d => x (some (e.symm d))))
  have honeHist (z : Z) := weightedMatrixHistory_one T q hq (K z) m hm hp hend none
    (cs.map some) (hcs.map (Option.some_injective C)) (by simp)
    (by ext x; cases x <;> simp [hmem]) S a
    (fun x => F z (fun d => x (some (e.symm d))))
  unfold matrixRootCovariance matrixObservableHistory
  simp_rw [holdHist,honeHist]
  simp only [Option.elim'_some]
  simp_rw [hmarg]
  rw [integral_const_mul,integral_const_mul]
  ring

end DilutedSpinGlass.PrescribedTree

end

end OAI
