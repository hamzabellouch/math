import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Probability.IntegralForcedHits
import OAI.Combinatorics.RamseyFive.Decoding.RichCentersCard
import OAI.Combinatorics.RamseyFive.Geometry.MomentCutoffPolynomialTail

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [∀ x : ℙ K V,Fintype (RadialLine x)]

theorem captured_global_radial_moment {I : Type} [LinearOrder I]
    (F : Finset I) (hF : F.Nonempty) (P : I→Submodule K V) (X S : Finset (ℙ K V))
    (hP : ∀ i∈F,finrank K (P i)=3) (j : ℕ)
    (hS : S⊆X\remaining F hF (fun i => flatPoints (P i)) X j)
    (hj : (j:ℝ)*(Nat.card K:ℝ)≤X.card)
    (O : ℙ K V→Finset (ℙ K V))
    (hO : ∀ x,ownCell F hF (fun i => flatPoints (P i)) X j x⊆O x)
    (δ : ℝ≥0) (hδ : 0<δ) (θ : ℝ) (hθ : 8*(δ:ℝ)*(j+1)≤θ)
    (Lines : Finset (Submodule K V)) (hrank : ∀ l∈Lines,finrank K l=2)
    (Q : Finset (ℙ K V)) (hLines : ∀ x∈Q,∀ l : RadialLine x,l.val∈Lines)
    (J : ℕ) (hJ : 2≤J) :
    (∑ x : Q,∑ l : RadialLine x.val,(radialWeight x.val (outsideAt x.val S (O x.val)) δ l:ℝ)^J) ≤
      (∑ x : Q,(Fintype.card (RadialLine x.val):ℝ))*θ^J+
        ((δ:ℝ)*((Nat.card K:ℝ)+1))^(J-2)*
          (4*(Nat.clog 2 S.card+1)*(192*(δ:ℝ)^2*(X.card:ℝ)^2)) := by
  have hδ' : 0<(δ:ℝ) := hδ
  have hθ0 : 0≤θ := (by positivity : 0≤8*(δ:ℝ)*(j+1)).trans hθ
  apply global_radial_moment S O δ hδ θ _ hθ0 (by positivity) Lines Q hLines _ J hJ
  intro i hi hcut _hmax
  let a : ℝ := (δ:ℝ)*2^i
  have hscale : 4*(δ:ℝ)≤a := by
    have hj0 : (0:ℝ)≤j := Nat.cast_nonneg j
    change θ≤2*a at hcut
    nlinarith
  obtain ⟨M,hM,hlo,hhi⟩ := exists_scale hδ' hscale
  have hjM : j≤M := by
    have hjM' : (j:ℝ)≤M := by
      change θ≤2*a at hcut
      nlinarith
    exact_mod_cast hjM'
  have hm := captured_rich_centers F hF P X hP Lines hrank j M hM hjM hj O hO
    δ a hδ' hlo hhi
  have hs : (∑ l∈Lines,((richCenters S O δ a l).card:ℝ)) ≤
      ∑ l∈Lines,((richCenters (X\remaining F hF (fun i => flatPoints (P i)) X j) O δ a l).card:ℝ) := by
    apply Finset.sum_le_sum
    intro l hl
    exact Nat.cast_le.mpr (Finset.card_le_card (richCenters_mono S _ O O δ a δ.coe_nonneg hS
      (fun _ => Finset.Subset.refl _) l))
  exact (mul_le_mul_of_nonneg_right hs (sq_nonneg a)).trans hm

open MeasureTheory

omit [FiniteDimensional K V] [Finite K] in
theorem global_trunc_failure (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ L : ℝ≥0) (Q : Finset (ℙ K V)) (R J : ℕ) :
    (∑ x : Q,∫ ω,1-HighMoment.allTrunc R J ω
      ∂batchMeasure (fun p : Fin R×RadialLine x.val =>
        L*radialWeight x.val (outsideAt x.val S (O x.val)) δ p.2)) ≤
      ((R:ℝ)*(L:ℝ))^J*
        (∑ x : Q,∑ l : RadialLine x.val,(radialWeight x.val (outsideAt x.val S (O x.val)) δ l:ℝ)^J) := by
  calc
    _ ≤ ∑ x : Q,∑ l : RadialLine x.val,((R:ℝ)*
        ((L*radialWeight x.val (outsideAt x.val S (O x.val)) δ l:ℝ≥0):ℝ))^J :=
      Finset.sum_le_sum fun x _ => HighMoment.allTrunc_failure
        (fun l => L*radialWeight x.val (outsideAt x.val S (O x.val)) δ l) R J
    _ = _ := by
      simp only [NNReal.coe_mul,←mul_assoc,mul_pow,Finset.mul_sum]

end

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K I : Type} [Field K] [Finite K] [Fintype I]
  [∀ x : ℙ K (I→K),Fintype (RadialLine x)]

theorem residual_global_radial_moment {q : ℕ} [CharP K q]
    (hq : 2<q) (hcard : Nat.card K=q) (hI : Fintype.card I=4 ∨ Fintype.card I=5)
    (σ g n' θ : ℝ) (hσq : Real.exp σ=q) (hσ : 1000≤σ)
    (hg : 100000000≤g) (hghi : g≤2*σ) (hn' : Real.exp (3*σ/2+g)/4≤n')
    (X : Finset (ℙ K (I→K))) (hX : (X.card:ℝ)≤Real.exp (3*σ/2+g))
    (O : ℙ K (I→K)→Finset (ℙ K (I→K)))
    (δ : ℝ≥0) (hδ : 0<δ) (hδeq : (δ:ℝ)=(q:ℝ)/n')
    (hmax : (δ:ℝ)*((q:ℝ)+1)≤2) (hθ : 2*Real.exp (-g/20)≤θ)
    (Lines : Finset (Submodule K (I→K))) (hrank : ∀ l∈Lines,finrank K l=2)
    (Q : Finset (ℙ K (I→K))) (hLines : ∀ x∈Q,∀ l : RadialLine x,l.val∈Lines)
    (hcap : ∀ U : Submodule K (I→K),finrank K U=3 →
      ((X.filter fun y => y.submodule≤U).card:ℝ)≤
        (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5))
    (J : ℕ) (hJ : 2≤J) :
    (∑ x : Q,∑ l : RadialLine x.val,(radialWeight x.val (outsideAt x.val X (O x.val)) δ l:ℝ)^J) ≤
      (∑ x : Q,(Fintype.card (RadialLine x.val):ℝ))*θ^J+
        ((δ:ℝ)*((Nat.card K:ℝ)+1))^(J-2)*
          (4*(Nat.clog 2 X.card+1)*(333024*(q:ℝ)^2)) := by
  have hθ0 : 0≤θ := (by positivity : 0≤2*Real.exp (-g/20)).trans hθ
  apply global_radial_moment X O δ hδ θ _ hθ0 (by positivity) Lines Q hLines _ J hJ
  intro i hi hcut hamax
  have ha : Real.exp (-g/20)≤(δ:ℝ)*2^i := by linarith
  have ha2 : (δ:ℝ)*2^i≤2 := hamax.trans (by simpa only [hcard] using hmax)
  have ht := residual_rich_centers hq hcard hI σ g n' ((δ:ℝ)*2^i) hσq hσ hg hghi hn'
    ha ha2 X hX Lines hrank O hcap
  simpa only [←hδeq] using ht

end SharpRamseyFive.ScoreGeometry

end OAI
