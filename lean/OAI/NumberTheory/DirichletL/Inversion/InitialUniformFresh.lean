import OAI.NumberTheory.DirichletL.Inversion.InitialOverlapFresh

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialUniformFresh

theorem exists_uniform_fresh (K:ℕ)(a b:ℝ)(ha:0<a)(hab:a≤b):
    ∃(W:𝓢(ℝ,ℂ))(A B Bnorm:ℝ),0<A ∧ A≤B ∧ 0≤Bnorm ∧
      HasCompactSupport (W:ℝ→ℂ) ∧ tsupport (W:ℝ→ℂ)⊆Set.Icc A B ∧
      (∀x,‖W x‖≤Bnorm) ∧
      ∀{σ:Type*}[DecidableEq σ](I:Finset σ),I.card≤K→
      ∀(V:ℝ→ℂ),Function.support V⊆Set.Icc a b→
      ∀(y:σ→ℝ)(yj yc:ℝ),(∀i∈I,y i∈Set.Icc (1:ℝ) 2)→
        yj∈Set.Icc (1:ℝ) ((2:ℝ)^K)→0<yc→
        V (yj*yc/(∏i∈I,y i))≠0→W yc=1:=by
  let lo:=a/(2:ℝ)^K
  let hi:=lo+b*(2:ℝ)^K+1
  have hlo:0<lo:=by dsimp [lo];positivity
  have hb:0<b:=ha.trans_le hab
  obtain ⟨W,hWc,hWone,hWs⟩:=InverseSecondChildWindows.positive_cutoff lo hi hlo (by
    dsimp [hi]
    have hbp : 0<b*(2:ℝ)^K:=by positivity
    linarith)
  refine ⟨W,lo/2,hi+1,(SchwartzMap.seminorm ℝ 0 0) W,half_pos hlo,?_,by positivity,hWc,hWs,
    SchwartzMap.norm_le_seminorm ℝ W,?_⟩
  · dsimp [hi]
    have hbp : 0<b*(2:ℝ)^K:=by positivity
    linarith
  · intro σ dec I hI V hV y yj yc hy hj hc hn
    have hh:=InverseInitialOverlapFresh.overlap_column_interval I (fun _=>1) (fun _=>2) y
      a b 1 ((2:ℝ)^K) yj yc ha hab (by intros;norm_num) hy (by norm_num) hj hc (hV hn)
    simp only [Finset.prod_const,one_pow,mul_one,div_one] at hh
    apply hWone
    refine ⟨hh.1,?_⟩
    have hp:(2:ℝ)^I.card≤(2:ℝ)^K:=pow_le_pow_right₀ (by norm_num) hI
    have hup:yc≤b*(2:ℝ)^K:=hh.2.trans (mul_le_mul_of_nonneg_left hp hb.le)
    dsimp [hi]
    linarith

end SevenEighths.InverseInitialUniformFresh

end

end OAI
