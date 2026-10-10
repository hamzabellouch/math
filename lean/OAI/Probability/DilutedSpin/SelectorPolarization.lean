import OAI.Probability.DilutedSpin.HistorySelector

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

/-- The exact signed constrained history sum for an anchored old tree. -/
noncomputable def constrainedHistory {n k : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (a b : R → Option (Fin k)) (d : R → Fin n)
    (spinColor : Option (Fin k) → FinitePath Ω n → ℝ)
    (S : PrescribedTree n) (anchor : S.Leaf) (f : Sample Ω S → ℝ) : ℝ := by
  classical
  exact labeledHistory m (fun S pos f =>
    (S.sampleLaw T).expect (fun x => f x * ∏ c, spinColor c (S.pathAt (pos c) x)) *
    ∏ r, if (d r).val+1 ≤ splitDepth S (pos (a r)) (pos (b r)) then (1:ℝ) else 0)
    (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse S
    (Finset.univ.erase anchor) id (fun _ => anchor) f

/-- Polarization and the actual tree mark selector identify the constrained
history sum with diagonal canceled-anchor coefficients. The factorial cancels
exactly, leaving k^k/2^k times the signed finite sum of Taylor coefficients. -/
theorem constrainedHistory_polarization {n k : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (hk : 0 < k) (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (a b : R → Option (Fin k)) (d : R → Fin n)
    (spinColor : Option (Fin k) → FinitePath Ω n → ℝ)
    (S : PrescribedTree n) (anchor : S.Leaf) (f : Sample Ω S → ℝ) :
    let T' := KernelTower.prod n T (markPrior n (fun _ => FiniteLaw.pi (fun _ : R => MarkSelector.rademacher)))
    let D := fun c (y : FinitePath (Ω×(R→Bool)) n) =>
      spinColor c (KernelTower.pathFst n y) * MarkSelector.pathColor a b d c (KernelTower.pathSnd n y)
    let G := fun x => f (sampleFst S x) * D none (S.pathAt anchor x)
    constrainedHistory T m a b d spinColor S anchor f =
      ((k:ℝ)^k/2^k) * ∑ ε : Fin k → Bool, (∏ j, Polarization.sign (ε j)) *
        anchorCoefficient S T' m (Polarization.averageDirection ε (fun j => D (some j))) anchor G k := by
  classical
  dsimp only
  let D := fun c (y : FinitePath (Ω×(R→Bool)) n) =>
    spinColor c (KernelTower.pathFst n y) * MarkSelector.pathColor a b d c (KernelTower.pathSnd n y)
  let T' := KernelTower.prod n T (markPrior n (fun _ => FiniteLaw.pi (fun _ : R => MarkSelector.rademacher)))
  let G := fun x => f (sampleFst S x) * D none (S.pathAt anchor x)
  let cs := (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse
  have hcs : cs.Nodup := by
    rw [List.nodup_reverse,List.nodup_ofFn]
    exact Option.some_injective _
  have hdis : ∀ c ∈ cs, c ∉ ({none} : Finset (Option (Fin k))) := by
    intro c hc
    simp only [cs,List.mem_reverse,List.mem_ofFn] at hc
    obtain ⟨j,rfl⟩ := hc
    simp
  have hfull : ({none} : Finset (Option (Fin k))) ∪ cs.toFinset = Finset.univ := by
    ext c
    cases c with
    | none => simp
    | some j => simp [cs,List.mem_ofFn]
  have hsel := coloredAt_mark_selector T m hm a b d spinColor cs hcs {none} hdis hfull
    S (Finset.univ.erase anchor) id (fun _ => anchor) f
  have hmapped : cs.map D = (List.ofFn (fun j => D (some j))).reverse := by simp [cs,Function.comp_def]
  change coloredAt T' m (cs.map D) S (Finset.univ.erase anchor) _ _ _ = _ at hsel
  simp only [Finset.prod_singleton,id_eq] at hsel
  rw [hmapped] at hsel
  rw [← show coloredAt T' m (List.ofFn (fun j => D (some j))).reverse S
      (Finset.univ.erase anchor) (S.pathAt) G (fun _ => 1) =
      constrainedHistory T m a b d spinColor S anchor f from hsel]
  rw [coloredAt_polarization T' m hm hroot hend hk]
  simp only [anchorCoefficient,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ε _
  dsimp only [T',G,D]
  ring

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
