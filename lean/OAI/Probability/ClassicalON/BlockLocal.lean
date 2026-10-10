import OAI.Probability.ClassicalON.SpinReindex

namespace OAI

universe uE uF uK uV uW

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {W : Type uW} {E : Type uE} {F : Type uF} {K : Type uK} [Fintype V] [Fintype W] [Fintype E] [Fintype F] [Fintype K]

omit [Fintype K] in
theorem blockBondMean_local (l r : E → V) (b : E → ℝ) (B : Set V) (label : V → K)
    (elabel : E → K) (k : K) (l' r' : F → W) (b' : F → ℝ) (B' : Set W)
    (ev : BlockVertex B label k ≃ ↥(B'ᶜ)) (ee : {e // elabel e=k} ≃ F)
    (hb : ∀ e,b' (ee e)=b e.val)
    (hl : ∀ (s : ↥(B'ᶜ) → Spin 3) e,
      glueFamily B' (fun _ => poleSpin true) s (l' (ee e))=
        blockSpin B label k (fun v => s (ev v)) (l e.val))
    (hr : ∀ (s : ↥(B'ᶜ) → Spin 3) e,
      glueFamily B' (fun _ => poleSpin true) s (r' (ee e))=
        blockSpin B label k (fun v => s (ev v)) (r e.val))
    (f : (F → Bool) → ℝ) :
    poleBondMean l' r' b' B' (fun _ => true) f=
      blockBondMean l r b B label elabel k (fun η => f (arrowEquiv ee η)) := by
  rw [poleBondMean_collapse]
  have he (s : ↥(B'ᶜ) → Spin 3) :
      freeSpinEnergy 3 l' r' b' (glueFamily B' (fun _ => poleSpin true) s)=
        blockEnergy l r b B label elabel k (fun v => s (ev v)) :=
    freeSpinEnergy_edgeEquiv 3 ee _ _ _ _ _ _ _ _ hb (hl s) (hr s)
  have hs (s : ↥(B'ᶜ) → Spin 3) :
      (∑ η,spinBondWeight l' r' b' (glueFamily B' (fun _ => poleSpin true) s) η*f η)=
        ∑ η,blockBondWeight l r b B label elabel k (fun v => s (ev v)) η*f (arrowEquiv ee η) := by
    have h := sum_spinBondWeight_edgeEquiv ee (fun e => l e.val) (fun e => r e.val) l' r'
      (fun e => b e.val) b' (blockSpin B label k (fun v => s (ev v)))
      (glueFamily B' (fun _ => poleSpin true) s) hb (hl s) (hr s)
      (fun η => f (arrowEquiv ee η))
    simp only [arrowEquiv,Equiv.coe_fn_mk,Equiv.apply_symm_apply] at h
    convert h using 1; congr!
  simp_rw [he,hs]
  unfold blockBondMean
  convert weightedMean_pi_reindex ev (fun _ => sphereProbability 3)
    (fun s => Real.exp (blockEnergy l r b B label elabel k s))
    (fun s => ∑ η,blockBondWeight l r b B label elabel k s η*f (arrowEquiv ee η)) using 1

end ClassicalON

end

end OAI
