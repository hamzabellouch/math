import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.SplitContinuity

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision Filter
noncomputable section
variable {M ι : Type*} [AddCommGroup M]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M→+M→+ℤ)

abbrev PrecisionTest := ℕ×M×ℤ

def TestAgreement (T : Finset (PrecisionTest (M:=M)))
    (F G : PowerSeries (Torus v Ω)) : Prop :=
  ∀t∈T,Agrees t.2.2 ((coeff t.1 F) t.2.1) ((coeff t.1 G) t.2.1)

def InPrecisionClosure (A : Set (PowerSeries (Torus v Ω)))
    (F : PowerSeries (Torus v Ω)) : Prop :=
  ∀T : Finset (PrecisionTest (M:=M)),∃G∈A,TestAgreement v Ω T G F

lemma testAgreement_refl (T : Finset (PrecisionTest (M:=M))) (F : PowerSeries (Torus v Ω)) :
    TestAgreement v Ω T F F := fun _ _=>agrees_refl _ _

lemma TestAgreement.trans {T : Finset (PrecisionTest (M:=M))}
    {F G H : PowerSeries (Torus v Ω)}
    (hf : TestAgreement v Ω T F G) (hg : TestAgreement v Ω T G H) :
    TestAgreement v Ω T F H := fun t ht j hj=>(hf t ht j hj).trans (hg t ht j hj)

lemma inPrecisionClosure_self {A : Set (PowerSeries (Torus v Ω))} {F : PowerSeries (Torus v Ω)}
    (hF : F∈A) : InPrecisionClosure v Ω A F :=
  fun T=>⟨F,hF,testAgreement_refl v Ω T F⟩

lemma InPrecisionClosure.mono {A B : Set (PowerSeries (Torus v Ω))} {F : PowerSeries (Torus v Ω)}
    (hF : InPrecisionClosure v Ω A F) (hAB : A⊆B) : InPrecisionClosure v Ω B F := by
  intro T
  obtain ⟨G,hG,H⟩:=hF T
  exact ⟨G,hAB hG,H⟩

variable (l : Filter ι)
lemma SeriesConverges.testAgreement {f : ι→PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F) (T : Finset (PrecisionTest (M:=M))) :
    ∀ᶠi in l,TestAgreement v Ω T (f i) F := by
  classical
  induction T using Finset.induction_on with
  | empty=>exact Eventually.of_forall (by simp [TestAgreement])
  | @insert t T ht ih=>
    filter_upwards [ih,hf t.1 t.2.1 t.2.2] with i hi hj
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact hj
    · exact hi a ha

lemma InPrecisionClosure.of_converges [l.NeBot]
    {A : Set (PowerSeries (Torus v Ω))} {f : ι→PowerSeries (Torus v Ω)}
    {F : PowerSeries (Torus v Ω)} (hf : SeriesConverges v Ω l f F)
    (hA : ∀ᶠi in l,InPrecisionClosure v Ω A (f i)) : InPrecisionClosure v Ω A F := by
  intro T
  obtain ⟨i,hi,hAi⟩:=((hf.testAgreement v Ω l T).and hA).exists
  obtain ⟨G,hG,H⟩:=hAi T
  exact ⟨G,hG,H.trans v Ω hi⟩

variable {A : Set (PowerSeries (Torus v Ω))} {F : PowerSeries (Torus v Ω)}
variable (hF : InPrecisionClosure v Ω A F)
def precisionApprox (T : Finset (PrecisionTest (M:=M))) : PowerSeries (Torus v Ω) :=
  Classical.choose (hF T)

lemma precisionApprox_mem (T : Finset (PrecisionTest (M:=M))) : precisionApprox v Ω hF T∈A :=
  (Classical.choose_spec (hF T)).1

lemma precisionApprox_agrees (T : Finset (PrecisionTest (M:=M))) :
    TestAgreement v Ω T (precisionApprox v Ω hF T) F :=
  (Classical.choose_spec (hF T)).2

lemma precisionApprox_converges :
    SeriesConverges v Ω (atTop : Filter (Finset (PrecisionTest (M:=M))))
      (precisionApprox v Ω hF) F := by
  classical
  intro n m N
  apply eventually_atTop.mpr
  refine ⟨{(n,m,N)},fun T hT=>?_⟩
  exact precisionApprox_agrees v Ω hF T (n,m,N) (hT (by simp))
end
end ElementaryPositivity.QuantumTorus

end

end OAI
