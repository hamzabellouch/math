import OAI.Probability.DilutedSpin.FullSelectedError

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- Every prescribed old leaf has exactly the one-path marginal, including
through shared prefixes and arbitrary (possibly unary) stretches. -/
theorem pathAt_expect {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (T : KernelTower Ω n) (f : FinitePath Ω n → ℝ) :
    (S.sampleLaw T).expect (fun x => f (S.pathAt a x)) = (KernelTower.law n T).expect f := by
  induction S with
  | leaf =>
    change KernelTower.unitLaw.expect (fun _ => f ()) = _
    change KernelTower.unitLaw.expect (fun _ => f ()) = KernelTower.unitLaw.expect f
    apply FiniteLaw.expect_congr
    intro x
    cases x
    rfl
  | @node n k C ih =>
    rcases T with ⟨P,Q⟩
    rcases a with ⟨i,a⟩
    change (FiniteLaw.pi (fun i : Fin k => P.bind (fun z => sampleLaw (C i) (Q z)))).expect
      (fun x => f ((x i).1, (C i).pathAt a (x i).2)) = _
    have he := FiniteLaw.expect_pi_marginal
      (fun i : Fin k => P.bind (fun z => sampleLaw (C i) (Q z))) i
      (fun y => f (y.1, (C i).pathAt a y.2))
    refine he.trans ?_
    erw [FiniteLaw.expect_bind,KernelTower.law_succ_expect]
    apply P.expect_congr
    intro z
    exact ih i a (Q z) (fun y => f (z,y))

/-- The anchor-marginal argument in `pert:score-identity`, before root
averaging. It uses the actual old-tree joint law, not independent replicas. -/
theorem anchor_centered_bound {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (T : KernelTower Ω n) (f : Sample Ω S → ℝ) (g : FinitePath Ω n → ℝ)
    {B center : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B) :
    |(S.sampleLaw T).expect (fun x => f x * g (S.pathAt a x)) -
      (S.sampleLaw T).expect f * center| ≤
      B * (KernelTower.law n T).expect (fun y => |g y-center|) := by
  have heq : (S.sampleLaw T).expect (fun x => f x * g (S.pathAt a x)) -
      (S.sampleLaw T).expect f * center =
      (S.sampleLaw T).expect (fun x => f x * (g (S.pathAt a x)-center)) := by
    simp only [mul_sub,FiniteLaw.expect_sub,FiniteLaw.expect_mul_right]
  rw [heq]
  have habs : |(S.sampleLaw T).expect (fun x => f x * (g (S.pathAt a x)-center))| ≤
      (S.sampleLaw T).expect (fun x => |f x * (g (S.pathAt a x)-center)|) := by
    apply abs_le.mpr
    constructor
    · have hh := (S.sampleLaw T).expect_mono (fun x => neg_abs_le (f x * (g (S.pathAt a x)-center)))
      simpa only [FiniteLaw.expect_neg] using hh
    · exact (S.sampleLaw T).expect_mono (fun x => le_abs_self _)
  apply habs.trans
  calc
    _ ≤ (S.sampleLaw T).expect (fun x => B * |g (S.pathAt a x)-center|) :=
      FiniteLaw.expect_mono _ (fun x => by
        rw [abs_mul]
        exact mul_le_mul (hf x) le_rfl (abs_nonneg _) hB)
    _ = _ := by
      rw [FiniteLaw.expect_mul_left]
      exact congrArg (fun z => B*z) (pathAt_expect S a T (fun y => |g y-center|))

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
