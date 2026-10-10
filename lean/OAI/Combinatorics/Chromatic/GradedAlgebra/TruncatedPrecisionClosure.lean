import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.RootTruncation
import OAI.Combinatorics.Chromatic.Walls.HNTorusFactor
import OAI.Combinatorics.Chromatic.GradedAlgebra.SeriesApproximation
import OAI.Combinatorics.Chromatic.Walls.RootClosureFacts

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation LaurentPrecision Filter WallUnits
noncomputable section
variable {M I J : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M→+M→+ℤ)
abbrev RootClosedThrough (N : ℕ) (A : Set (PowerSeries (Torus v Ω)))
    (F : PowerSeries (Torus v Ω)) : Prop :=
  InPrecisionClosure v Ω (RootTruncation.cut N '' A) (RootTruncation.cut N F)
lemma RootClosedThrough.congr {N : ℕ} {A : Set (PowerSeries (Torus v Ω))}
    {F G : PowerSeries (Torus v Ω)} (hF : RootClosedThrough v Ω N A F)
    (he : ∀n≤N,coeff n F=coeff n G) : RootClosedThrough v Ω N A G := by
  change InPrecisionClosure v Ω _ _ at hF ⊢
  rw [←cut_congr he]
  exact hF
lemma InPrecisionClosure.cut {A : Set (PowerSeries (Torus v Ω))}
    {F : PowerSeries (Torus v Ω)} (hF : InPrecisionClosure v Ω A F) (N : ℕ) :
    RootClosedThrough v Ω N A F := by
  intro T
  obtain ⟨G,hG,H⟩:=hF T
  refine ⟨RootTruncation.cut N G,⟨G,hG,rfl⟩,?_⟩
  intro t ht
  simp only [coeff_cut]
  by_cases hn : t.1≤N
  · simp only [hn,ite_true]; exact H t ht
  · simp only [hn,ite_false]; exact agrees_refl _ _
lemma rootClosedThrough_self {N : ℕ} {A : Set (PowerSeries (Torus v Ω))}
    {F : PowerSeries (Torus v Ω)} (hF : F∈A) : RootClosedThrough v Ω N A F :=
  inPrecisionClosure_self v Ω ⟨F,hF,rfl⟩
lemma RootClosedThrough.mono {N : ℕ} {A B : Set (PowerSeries (Torus v Ω))}
    {F : PowerSeries (Torus v Ω)} (hF : RootClosedThrough v Ω N A F) (hAB : A⊆B) :
    RootClosedThrough v Ω N B F := InPrecisionClosure.mono v Ω hF (Set.image_mono hAB)
variable {N : ℕ} {A : Set (PowerSeries (Torus v Ω))} {F : PowerSeries (Torus v Ω)}
lemma rootClosedThrough_approx_exists (hF : RootClosedThrough v Ω N A F)
    (T : Finset (PrecisionTest (M:=M))) :
    ∃G∈A,TestAgreement v Ω T (RootTruncation.cut N G) (RootTruncation.cut N F) := by
  obtain ⟨G,⟨G',hG,rfl⟩,H⟩:=hF T
  exact ⟨G',hG,H⟩
def rootApprox (hF : RootClosedThrough v Ω N A F)
    (T : Finset (PrecisionTest (M:=M))) : PowerSeries (Torus v Ω) :=
  Classical.choose (rootClosedThrough_approx_exists v Ω hF T)
lemma rootApprox_mem (hF : RootClosedThrough v Ω N A F)
    (T : Finset (PrecisionTest (M:=M))) : rootApprox v Ω hF T∈A :=
  (Classical.choose_spec (rootClosedThrough_approx_exists v Ω hF T)).1
lemma rootApprox_converges (hF : RootClosedThrough v Ω N A F) :
    SeriesConverges v Ω (atTop : Filter (Finset (PrecisionTest (M:=M))))
      (fun T=>RootTruncation.cut N (rootApprox v Ω hF T)) (RootTruncation.cut N F) := by
  classical
  intro n m K
  apply eventually_atTop.mpr
  refine ⟨{(n,m,K)},fun T hT=>?_⟩
  exact (Classical.choose_spec (rootClosedThrough_approx_exists v Ω hF T)).2
    (n,m,K) (hT (by simp))
lemma RootClosedThrough.of_converges (l : Filter J) [l.NeBot]
    {f : J→PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l (fun j=>RootTruncation.cut N (f j)) (RootTruncation.cut N F))
    (hA : ∀ᶠj in l,RootClosedThrough v Ω N A (f j)) : RootClosedThrough v Ω N A F :=
  InPrecisionClosure.of_converges v Ω l hf hA
end

section ZeroFactor
noncomputable section
open PowerSeries RootTruncation LaurentPrecision Filter WallUnits
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)
variable {N : ℕ} {A B : Set (PowerSeries (Torus LaurentRay.vUnit Ω))}
variable {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
lemma RootClosedThrough.zeroFactor
    (hF : RootClosedThrough LaurentRay.vUnit Ω N A F)
    (hA : ∀G∈A,SeriesGraded LaurentRay.vUnit Ω C G)
    (h : M→+ℝ)
    (hB : ∀G∈A,InPrecisionClosure LaurentRay.vUnit Ω B
      (PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
        (zeroProject LaurentRay.vUnit Ω h) G)) :
    RootClosedThrough LaurentRay.vUnit Ω N B
      (PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
        (zeroProject LaurentRay.vUnit Ω h) F) := by
  let P:=positiveProject LaurentRay.vUnit Ω h
  let Q:=zeroProject LaurentRay.vUnit Ω h
  let g:=rootApprox LaurentRay.vUnit Ω hF
  have hg:=rootApprox_converges LaurentRay.vUnit Ω hF
  have hgg : ∀T,SeriesGraded LaurentRay.vUnit Ω C (RootTruncation.cut N (g T)):=
    fun T=>(hA _ (rootApprox_mem LaurentRay.vUnit Ω hF T)).cut LaurentRay.vUnit Ω C N
  have hFG : SeriesGraded LaurentRay.vUnit Ω C (RootTruncation.cut N F):=by
    apply hF.graded Ω C
    rintro G ⟨G',hG,rfl⟩
    exact (hA G' hG).cut LaurentRay.vUnit Ω C N
  have H:=filter_factors_converge LaurentRay.vUnit Ω C Filter.atTop (fun m=>0<h m) hg hgg hFG
  have HH:=filter_factors_converge LaurentRay.vUnit Ω C Filter.atTop (fun m=>h m=0) H.2
    (fun T n=>by
      simpa only [PowerSeriesSplit.rightFactor,coeff_mk] using
        (filter_pair_graded LaurentRay.vUnit Ω C (fun m=>0<h m) (RootTruncation.cut N (g T)) (hgg T) n).2)
    (fun n=>by
      simpa only [PowerSeriesSplit.rightFactor,coeff_mk] using
        (filter_pair_graded LaurentRay.vUnit Ω C (fun m=>0<h m) (RootTruncation.cut N F) hFG n).2)
  have hc:=HH.1.cut LaurentRay.vUnit Ω Filter.atTop N
  change SeriesConverges LaurentRay.vUnit Ω Filter.atTop
    (fun T=>RootTruncation.cut N (PowerSeriesSplit.zeroFactor P Q (RootTruncation.cut N (g T))))
    (RootTruncation.cut N (PowerSeriesSplit.zeroFactor P Q (RootTruncation.cut N F))) at hc
  simp only [cut_zeroFactor] at hc
  apply RootClosedThrough.of_converges LaurentRay.vUnit Ω Filter.atTop hc
  exact Eventually.of_forall (fun T=>(hB _ (rootApprox_mem LaurentRay.vUnit Ω hF T)).cut LaurentRay.vUnit Ω N)
end
end ZeroFactor
end ElementaryPositivity.QuantumTorus

end

end OAI
