import OAI.NumberTheory.DirichletL.Inversion.InitialTotalEnergy

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialInputRadial
open ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic ConcreteTraceCRT
open InverseInitialConjugateEnergy
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem input_energy_summable (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(test:Finset ι→ℂ)
    (a:ℂ)(Φ:𝓢(ℝ,ℂ))(Y:ℝ)(hY:0<Y):
    Summable (fun u:O=>Φ (‖eisEmbedding u‖^2/Y)*
      (‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2:ℝ)):=by
  let c:Finset ι→ℂ:=fun S=>a*supportMobius (fun i=>Ideal.span {p i}) S*
    secondInputCoefficient p hg Ψ j 1 1 test S
  have he (u:O):a*inputConjugateRow p hg pool Ψ j 1 1 test u=
      star (∑S∈pool.powerset,star (c S)*finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S u):=by
    simp only [inputConjugateRow,supportConjugateSum,Finset.mul_sum,star_sum,star_mul,star_star,c]
    apply Finset.sum_congr rfl
    intro S hS
    ring
  simp_rw [he,norm_star]
  exact finiteSquarefreeRow_smoothed_mean_square_summable (fun i=>Ideal.span {p i}) hg
    pool.powerset id (fun S=>star (c S)) Φ Y hY

theorem finite_rows_le_input_norm (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(test:Finset ι→ℂ)
    (a:ℂ)(Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)
    (hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (Y:ℝ)(hY:0<Y)(rows:Finset O)(hrows:∀u∈rows,‖eisEmbedding u‖^2≤Y):
    (∑u∈rows,‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2)≤
      ‖∑'u:O,Φ (‖eisEmbedding u‖^2/Y)*
        (‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2:ℝ)‖:=by
  have hs:=input_energy_summable p hg pool Ψ j test a Φ Y hY
  have hr:=Complex.hasSum_re hs.hasSum
  have hfin:(∑u∈rows,‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2)=
      ∑u∈rows,(Φ (‖eisEmbedding u‖^2/Y)*
        (‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2:ℝ)).re:=by
    apply Finset.sum_congr rfl
    intro u hu
    rw [hone _ ⟨div_nonneg (sq_nonneg _) hY.le,(div_le_one hY).mpr (hrows u hu)⟩]
    simp only [one_mul,Complex.ofReal_re]
  rw [hfin]
  apply (hr.summable.sum_le_tsum rows (fun u _=>?_)).trans
  · rw [hr.tsum_eq]
    exact Complex.re_le_norm _
  · simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_nonneg (hΦ _) (sq_nonneg _)

end SevenEighths.InverseInitialInputRadial

end

end OAI
