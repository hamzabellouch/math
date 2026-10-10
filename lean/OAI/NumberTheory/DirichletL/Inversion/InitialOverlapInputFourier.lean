import OAI.NumberTheory.DirichletL.Inversion.InitialOverlapFourier
import OAI.NumberTheory.DirichletL.Inversion.InitialRayAttachment
import OAI.NumberTheory.DirichletL.Descent.SecondSeparatedColumns

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic
open FirstPassCubeLabels
namespace SevenEighths.InverseInitialOverlapInputFourier
open InverseMoment InverseInitialOverlapFourier InverseInitialArithmetic InverseInitialRayAttachment
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem input_integral (F : Finset ι) (Ψ : Eis→*ℂ) (j u : Eis)
    (H : Finset ι→ℝ→ℂ) (hH : ∀A∈F.powerset,Integrable (H A)) :
    inputConjugateRow p hg F Ψ j 1 1 (fun A=>∫t:ℝ,H A t) u =
      ∫t:ℝ,inputConjugateRow p hg F Ψ j 1 1 (fun A=>H A t) u := by
  rw [initial_input_row p hg]
  simp_rw [initial_input_row p hg]
  unfold supportConjugateSum
  have he (A:Finset ι) (t:ℝ) :
      supportMobius (fun i=>Ideal.span {p i}) A*
        (Ψ (∏i∈A,p i)*rowCoprimeMask (fun i=>Ideal.span {p i}) A j*H A t)*
        star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg A u)=
      (supportMobius (fun i=>Ideal.span {p i}) A*Ψ (∏i∈A,p i)*
        rowCoprimeMask (fun i=>Ideal.span {p i}) A j*
        star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg A u))*H A t := by ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun A hA=>(hH A hA).const_mul _)]
  simp only [integral_const_mul]
  apply Finset.sum_congr rfl
  intro A hA
  ring

theorem original_overlap_input
    (hp : ∀i,p i≠0) (F : Finset ι) (Ψ : Eis→*ℂ) (j u : Eis)
    (W : ℝ→ℂ) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (hs : Function.support W⊆Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (y : σ→ι→ℝ) (hy : ∀i∈slots,∀q∈lists i,0<y i q)
    (wFresh : ℝ→ℂ) (Z D yj : ℝ) (hZ : 0<Z) (hj : 0<yj) :
    ((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
      (fun A=>wFresh (primeProductNorm p A/Z^D)*
        ∑q∈slots.pi lists,
          (∏i∈slots.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
          W (yj*(primeProductNorm p A/Z^D)/(∏i∈slots.attach,y i.val (q i.val i.property)))) u =
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
          (initialTest p
            (primeMark slots lists (fun i q=>a i q*logPhase (-t) (Real.log (y i q))))
            (childLogTest wFresh t) Z D) u) := by
  let g := CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW
  let H : Finset ι→ℝ→ℂ := fun A t=>density g (Real.log yj) t*
    (primeMark slots lists (fun i q=>a i q*logPhase (-t) (Real.log (y i q))) A*
      childLogTest wFresh t (primeProductNorm p A/Z^D))
  have hH (A:Finset ι) : Integrable (H A) := by
    have hi := (overlap_mode_integrable g slots lists a (fun i q=>Real.log (y i q))
      A (Real.log yj) (Real.log (primeProductNorm p A/Z^D))).const_mul
      (wFresh (primeProductNorm p A/Z^D))
    convert hi using 1
    funext t
    dsimp [H,childLogTest]
    ring
  have he (A:Finset ι) :
      wFresh (primeProductNorm p A/Z^D)*
        (∑q∈slots.pi lists,
          (∏i∈slots.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
          W (yj*(primeProductNorm p A/Z^D)/(∏i∈slots.attach,y i.val (q i.val i.property)))) =
      ∫t:ℝ,H A t := by
    rw [actual_overlap_separation W a₀ b₀ ha₀ hs hW slots lists a y hy A yj
      (primeProductNorm p A/Z^D) hj
      (div_pos (primeProductNorm_pos p hp A) (Real.rpow_pos_of_pos hZ D)),←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [H,childLogTest,g]
    ring
  simp_rw [he]
  rw [input_integral p hg F Ψ j u H (fun A _=>hH A),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only [H]
  rw [initial_input_row p hg,initial_input_row p hg]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,initialTest]
  apply Finset.sum_congr rfl
  intro A hA
  ring

end SevenEighths.InverseInitialOverlapInputFourier

end

end OAI
