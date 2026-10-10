import OAI.NumberTheory.DirichletL.Reflection.ThreeBlocks

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance ramifiedFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def ramifiedBlock [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) (u : Eisˣ) (m : ℕ) : ℂ :=
  ∏ i ∈ S, unitArgumentFactor (actualSextic (Ideal.span {p i}) (hg i)) (j i)
    (Ideal.Quotient.mk _ (u.val*λ₀^m))

theorem ramifiedPhase_three_blocks [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F) (hu : (R ∪ P) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hPj : ∀ i ∈ P, j i = 0)
    (u : Eisˣ) (m : ℕ) :
    ramifiedBranchPhase (fun i => Ideal.span {p i}) hg j u m =
      ramifiedBlock hg (fun _ => 1) R u m * ramifiedBlock hg (fun _ => 0) P u m *
      ramifiedBlock hg j F u m := by
  have hh : ramifiedBranchPhase (fun i => Ideal.span {p i}) hg j u m =
      ramifiedBlock hg j R u m * ramifiedBlock hg j P u m * ramifiedBlock hg j F u m := by
    unfold ramifiedBranchPhase ramifiedBlock
    rw [← Finset.prod_union hRP,← Finset.prod_union hF,hu]
    rfl
  rw [hh]
  congr 2
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hRj i hi]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hPj i hi]

theorem modelRowPhase_three_blocks [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, λ₀^2 ∣ p i-1) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F) (hu : (R ∪ P) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hPj : ∀ i ∈ P, j i = 0)
    (u : Eisˣ) (m : ℕ) :
    D.modelRowPhase s hp hg j u m =
      (residualWithFrozen hp hg c R F * ramifiedBlock hg (fun _ => 1) R
        (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)) *
      (markedWithFrozen hp hg c P F * ramifiedBlock hg (fun _ => 0) P
        (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)) *
      (star D.fixedFactor * frozenPhase D hp hg j F * ramifiedBlock hg j F
        (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)) := by
  dsimp only [ControlledStratumArithmetic.modelRowPhase]
  rw [activePhase_three_blocks D hp hg hcop hprimary R P F hRP hF hu j hRj hPj,
    ramifiedPhase_three_blocks hg R P F hRP hF hu j hRj hPj]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
