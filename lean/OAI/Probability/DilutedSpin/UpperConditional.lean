import OAI.Probability.DilutedSpin.UpperFreshLocal

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma freshRoot_true (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (f : FinitePath Ω n → ℝ) (a : UpperDatum p N R) :
    freshRoot T U V x m f (fun _ => true) a =
      backwardLog n T m (fun y => f y+a.1.1 (fun d => V y (a.2.1 d))) := by
  unfold freshRoot mixedTreeEnergy
  simp only [mixedEnergy_true]
  exact backwardLog_prod_fst n T (piTower n (fun d : Fin p => U (a.2.2 d))) m
    (fun y => f y+a.1.1 (fun d => V y (a.2.1 d)))

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma datumRoot_fresh_true (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ)
    (z : RootPath (UpperDatum p N R) k) (w : RootPath (UpperDatum p N R) l)
    (a : UpperDatum p N R) :
    freshRoot (cavityTower T U l (rootMap (fun a => a.2.2) l w)) U
      (fun y => V (pathMap (cavityProject l) n y)) x m
      (cavityEnergy V x j l (rootMap (fun a => a.2.2) l w)
        (rootMap (fun a => a.2.1) l w) (rootMap Prod.fst l w)
        (realCountEnergy V k (rootMap (fun a => a.2.1) k z) (rootMap Prod.fst k z) f))
      (fun _ => true) a = datumRoot T U V x m j f (k+1) l (a,z) w := by
  rw [freshRoot_true,datumRoot_real_succ]

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma datumRoot_fresh_selected (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ)
    (z : RootPath (UpperDatum p N R) k) (w : RootPath (UpperDatum p N R) l)
    (a : UpperDatum p N R) :
    freshRoot (cavityTower T U l (rootMap (fun a => a.2.2) l w)) U
      (fun y => V (pathMap (cavityProject l) n y)) x m
      (cavityEnergy V x j l (rootMap (fun a => a.2.2) l w)
        (rootMap (fun a => a.2.1) l w) (rootMap Prod.fst l w)
        (realCountEnergy V k (rootMap (fun a => a.2.1) k z) (rootMap Prod.fst k z) f))
      (fun d => decide (d=j)) a = datumRoot T U V x m j f k (l+1) z (a,w) := rfl

lemma datumRoot_conditional_replacement (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ d,0 ≤ m d)
    (hstrict : ∀ d : Fin n,0 < m d.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ)
    (z : RootPath (UpperDatum p N R) k) (w : RootPath (UpperDatum p N R) l)
    {C : ℝ} (hC : ∀ᵐ a ∂M.disorder.toMeasure,‖a.1‖≤C) :
    (∫ a,datumRoot T U V x (fun d => m d.succ) j f (k+1) l (a,z) w ∂upperDatumLaw M Q)+
      ((p-1:ℕ):ℝ)*datumRoot T U V x (fun d => m d.succ) j f k l z w ≤
      (p:ℝ)*(∫ a,datumRoot T U V x (fun d => m d.succ) j f k (l+1) z (a,w) ∂upperDatumLaw M Q)-
      ((p-1:ℕ):ℝ)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure) := by
  let F := cavityEnergy V x j l (rootMap (fun a => a.2.2) l w)
        (rootMap (fun a => a.2.1) l w) (rootMap Prod.fst l w)
        (realCountEnergy V k (rootMap (fun a => a.2.1) k z) (rootMap Prod.fst k z) f)
  have h := freshRoot_replacement M hM
    (cavityTower T U l (rootMap (fun a => a.2.2) l w)) Q U
    (fun y => V (pathMap (cavityProject l) n y)) x m hm hpos hstrict hroot hend F j
    (fun y => norm_le_pi_norm F y) hC
  dsimp only [F] at h
  simp only [datumRoot_fresh_true,datumRoot_fresh_selected] at h
  exact h

end DilutedSpinGlass.PrescribedTree

end

end OAI
