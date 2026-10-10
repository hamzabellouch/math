import OAI.NumberTheory.DirichletL.Inversion.InitialCommonProfile
import OAI.NumberTheory.DirichletL.Inversion.InitialOverlapSource

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
namespace SevenEighths.InverseInitialCommonCutoff
open InverseMoment InverseInitialCommonProfile InverseInitialCommonRatios
open InverseInitialOverlapIdealFourier InverseInitialOverlapSource
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

def tupleProfile (I:Finset σ)(L:σ→Finset (Ideal Eis))(a:σ→Ideal Eis→ℂ)
    (Z:ℝ)(ell:σ→ℝ)(W:ℝ→ℂ)(yj yc:ℝ)(c:Ideal Eis) : ℂ :=
  ∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
    (if survivingProduct I q∣c then
      W (yj*yc/(∏i∈I.attach,slotRatio Z ell i.val (q i.val i.property))) else 0)

theorem tupleProfile_gates (I:Finset σ)(L:σ→Finset (Ideal Eis))(a:σ→Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (Z:ℝ)(ell:σ→ℝ)(W:ℝ→ℂ)(yj yc:ℝ)(c:Ideal Eis) :
    tupleProfile I L a Z ell W yj yc c=
      ∑q∈I.pi L,
        (∏i∈I.attach,if q i.val i.property∈activeIndices id I L c then a i.val (q i.val i.property) else 0)*
          W (yj*yc/(∏i∈I.attach,slotRatio Z ell i.val (q i.val i.property))) := by
  apply Finset.sum_congr rfl
  intro q hq
  have hg : (∏i∈I.attach,if q i.val i.property∈activeIndices id I L c then a i.val (q i.val i.property) else 0)=
      if survivingProduct I q∣c then ∏i∈I.attach,a i.val (q i.val i.property) else 0 := by
    calc
      _ = ∏i∈I.attach,if q i.val i.property∣c then a i.val (q i.val i.property) else 0 := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [activeIndices_mem id I L _ i.property ((Finset.mem_pi.mp hq) i.val i.property),id_eq]
      _ = _ := by
        convert! tuple_gate_product id I a q c (hcop q hq) using 1
  rw [hg]
  split_ifs <;> simp

theorem tupleProfile_insert_fresh
    (I:Finset σ)(L:σ→Finset (Ideal Eis))(a:σ→Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (Z:ℝ)(ell lo hi:σ→ℝ)(W wFresh:ℝ→ℂ)(a₀ b₀ jlo jhi:ℝ)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (yj yc:ℝ)(hj:yj∈Set.Icc jlo jhi)(hc:0<yc)(c:Ideal Eis) :
    wFresh yc*tupleProfile I L a Z ell W yj yc c=tupleProfile I L a Z ell W yj yc c := by
  rw [tupleProfile_gates I L a hcop]
  exact insert_original_fresh I L a (slotRatio Z ell) lo hi W wFresh a₀ b₀ jlo jhi
    hs ha hFresh (activeIndices id I L c) yj yc hj hc

end SevenEighths.InverseInitialCommonCutoff

end

end OAI
