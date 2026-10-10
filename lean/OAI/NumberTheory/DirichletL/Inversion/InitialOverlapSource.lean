import OAI.NumberTheory.DirichletL.Inversion.InitialOverlapInputFourier
import OAI.NumberTheory.DirichletL.Inversion.InitialOverlapFresh

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseInitialOverlapSource
open InverseInitialOverlapFresh InverseInitialOverlapInputFourier
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def tupleCoordinate (I : Finset σ) (y : σ→ι→ℝ) (q : ∀i∈I,ι) (i : σ) : ℝ :=
  if hi:i∈I then y i (q i hi) else 1

omit [DecidableEq ι] in
theorem tupleCoordinate_product (I : Finset σ) (y : σ→ι→ℝ) (q : ∀i∈I,ι) :
    (∏i∈I,tupleCoordinate I y q i)=∏i∈I.attach,y i.val (q i.val i.property) := by
  rw [←Finset.prod_attach]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [tupleCoordinate,dite_eq_left i.property]

theorem insert_original_fresh
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (lo hi : σ→ℝ) (W wFresh : ℝ→ℂ) (a₀ b₀ jlo jhi : ℝ)
    (_hW : Function.support W⊆Set.Icc a₀ b₀)
    (ha : ∀i∈I,∀q∈L i,a i q≠0→y i q∈Set.Icc (lo i) (hi i))
    (hFresh : ∀(v:σ→ℝ)(yj yc:ℝ),
      (∀i∈I,v i∈Set.Icc (lo i) (hi i))→yj∈Set.Icc jlo jhi→0<yc→
      W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (A : Finset ι) (yj yc : ℝ) (hj : yj∈Set.Icc jlo jhi) (hc : 0<yc) :
    wFresh yc*(∑q∈I.pi L,
      (∏i∈I.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
        W (yj*yc/(∏i∈I.attach,y i.val (q i.val i.property)))) =
      ∑q∈I.pi L,
        (∏i∈I.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
          W (yj*yc/(∏i∈I.attach,y i.val (q i.val i.property))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hz : (∏i∈I.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)=0
  · simp only [hz,zero_mul,mul_zero]
  by_cases hw : W (yj*yc/(∏i∈I.attach,y i.val (q i.val i.property)))=0
  · simp only [hw,mul_zero]
  have hcoord : ∀i∈I,tupleCoordinate I y q i∈Set.Icc (lo i) (hi i) := by
    intro i hi
    have hn := Finset.prod_ne_zero_iff.mp hz ⟨i,hi⟩ (Finset.mem_attach _ _)
    have hcoeff : a i (q i hi)≠0 := by
      intro he
      apply hn
      split_ifs
      · exact he
      · rfl
    simpa only [tupleCoordinate,dite_eq_left hi] using
      ha i hi (q i hi) ((Finset.mem_pi.mp hq) i hi) hcoeff
  have hf := hFresh (tupleCoordinate I y q) yj yc hcoord hj hc
    (by rwa [tupleCoordinate_product])
  rw [hf,one_mul]

theorem exists_original_overlap_input
    (I : Finset σ) (lo hi : σ→ℝ) (W : ℝ→ℂ)
    (a₀ b₀ jlo jhi : ℝ) (ha₀ : 0<a₀) (hab : a₀≤b₀)
    (hs : Function.support W⊆Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (hlo : ∀i∈I,0<lo i) (hhi : ∀i∈I,lo i≤hi i)
    (hjlo : 0<jlo) (hjhi : jlo≤jhi) :
    ∃(wFresh : 𝓢(ℝ,ℂ))(A B:ℝ),0<A ∧ A≤B ∧
      HasCompactSupport (wFresh:ℝ→ℂ) ∧ tsupport (wFresh:ℝ→ℂ)⊆Set.Icc A B ∧
      ∀(p:ι→ActualEisensteinCubic.O)(_hp:∀i,p i≠0)
        (hpmax:∀i,(Ideal.span {p i}).IsMaximal)
        (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
        (F:Finset ι)(Ψ:ActualEisensteinCubic.O→*ℂ)(j u:ActualEisensteinCubic.O)
        (lists:σ→Finset ι)(a:σ→ι→ℂ)(y:σ→ι→ℝ)
        (_hy:∀i∈I,∀q∈lists i,0<y i q)
        (_ha:∀i∈I,∀q∈lists i,a i q≠0→y i q∈Set.Icc (lo i) (hi i))
        (Z D yj:ℝ)(_hZ:0<Z)(_hj:yj∈Set.Icc jlo jhi),
      letI := hpmax
      ((Z^(-D/2):ℝ):ℂ)*SecondPassArithmetic.inputConjugateRow p hg F Ψ j 1 1
        (fun U=>∑q∈I.pi lists,
          (∏i∈I.attach,if q i.val i.property∈U then a i.val (q i.val i.property) else 0)*
            W (yj*(FirstPassCubeLabels.primeProductNorm p U/Z^D)/
              (∏i∈I.attach,y i.val (q i.val i.property)))) u =
        ∫t:ℝ,InverseInitialOverlapFourier.density
          (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
          (((Z^(-D/2):ℝ):ℂ)*SecondPassArithmetic.inputConjugateRow p hg F Ψ j 1 1
            (InverseInitialRayAttachment.initialTest p
              (InverseMoment.primeMark I lists
                (fun i q=>a i q*FourierBridge.logPhase (-t) (Real.log (y i q))))
              (InverseMoment.childLogTest wFresh t) Z D) u) := by
  obtain ⟨w,A,B,hA,hAB,hwc,hws,hfresh⟩ := exists_overlap_fresh I lo hi a₀ b₀ jlo jhi
    ha₀ hab hlo hhi hjlo hjhi
  refine ⟨w,A,B,hA,hAB,hwc,hws,?_⟩
  intro p hp hpmax hg F Ψ j u lists a y hy ha Z D yj hZ hj
  let := hpmax
  have he := original_overlap_input p hg hp F Ψ j u W a₀ b₀ ha₀ hs hW
    I lists a y hy w Z D yj hZ (hjlo.trans_le hj.1)
  convert he using 2
  apply congrArg (fun H:Finset ι→ℂ=>SecondPassArithmetic.inputConjugateRow p hg F Ψ j 1 1 H u)
  funext U
  exact (insert_original_fresh I lists a y lo hi W w a₀ b₀ jlo jhi hs ha
    (hfresh W hs) U yj (FirstPassCubeLabels.primeProductNorm p U/Z^D) hj
    (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp U)
      (Real.rpow_pos_of_pos hZ D))).symm

end SevenEighths.InverseInitialOverlapSource

end

end OAI
