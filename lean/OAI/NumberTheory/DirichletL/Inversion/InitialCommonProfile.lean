import OAI.NumberTheory.DirichletL.Inversion.InitialCommonLists
import OAI.NumberTheory.DirichletL.Inversion.InitialCommonRatios
import OAI.NumberTheory.DirichletL.Inversion.InitialOverlapIdealFourier

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
namespace SevenEighths.InverseInitialCommonProfile
open InverseMoment InverseInitialCommonLists InverseInitialCommonRatios
open InverseInitialOverlapFourier InverseInitialOverlapIdealFourier
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

def slotRatio (Z:ℝ)(ell:σ→ℝ)(i:σ)(P:Ideal Eis) : ℝ := (P.absNorm:ℝ)/Z^(ell i)

omit [DecidableEq σ] in
theorem slotRatio_pos (Z:ℝ)(hZ:0<Z)(ell:σ→ℝ)(i:σ){P:Ideal Eis}(hP:Prime P) :
    0<slotRatio Z ell i P := by
  apply div_pos _ (Real.rpow_pos_of_pos hZ _)
  exact_mod_cast Nat.pos_of_ne_zero (fun h=>hP.ne_zero (Ideal.absNorm_eq_zero_iff.mp h))

theorem common_profile_separation
    (W:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (F:Finset (Ideal Eis))(I:Finset σ)(L:σ→Finset (Ideal Eis))
    (hL:∀i∈I,∀P∈L i,Prime P)(a:σ→Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime
      (fun i:I=>q i.val i.property)))
    (Z:ℝ)(hZ:0<Z)(ell:σ→ℝ)(A:Finset (primePool F))
    (yj yc:ℝ)(hj:0<yj)(hc:0<yc) :
    (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      (if survivingProduct I q∣(∏i∈A,i.val) then
        W (yj*yc/(∏i∈I.attach,slotRatio Z ell i.val (q i.val i.property))) else 0)) =
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW)
        (Real.log yj) t*logPhase t (Real.log yc)*
        primeMark I (fun i=>poolList F (L i))
          (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A := by
  have hm (t:ℝ) : primeMark I (fun i=>poolList F (L i))
      (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A =
      primeMark I L (fun i P=>a i P*logPhase (-t) (Real.log (slotRatio Z ell i P)))
        (activeIndices id I L (∏i∈A,i.val)) :=
    (original_ideal_mark F I L hL
      (fun i P=>a i P*logPhase (-t) (Real.log (slotRatio Z ell i P))) A).symm.trans
      (indexed_mark_active id I L _ _)
  simp_rw [hm]
  have he := actual_overlap_separation W a₀ b₀ ha₀ hs hW I L a (slotRatio Z ell)
    (fun i hi P hP=>slotRatio_pos Z hZ ell i (hL i hi P hP))
    (activeIndices id I L (∏i∈A,i.val)) yj yc hj hc
  rw [←he]
  apply Finset.sum_congr rfl
  intro q hq
  have hprod : (∏i∈I.attach,if q i.val i.property∈activeIndices id I L (∏i∈A,i.val)
      then a i.val (q i.val i.property) else 0)=
      if survivingProduct I q∣(∏i∈A,i.val) then
        ∏i∈I.attach,a i.val (q i.val i.property) else 0 := by
    calc
      _ = ∏i∈I.attach,if q i.val i.property∣(∏i∈A,i.val) then a i.val (q i.val i.property) else 0 := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [activeIndices_mem id I L _ i.property ((Finset.mem_pi.mp hq) i.val i.property),id_eq]
      _ = _ := by
        convert! tuple_gate_product id I a q (∏i∈A,i.val) (hcop q hq) using 1
  rw [hprod]
  split_ifs <;> simp

theorem common_profile_integrable (g:𝓢(ℝ,ℂ))
    (F:Finset (Ideal Eis))(I:Finset σ)(L:σ→Finset (Ideal Eis))
    (a:σ→Ideal Eis→ℂ)(Z:ℝ)(ell:σ→ℝ)(A:Finset (primePool F))(yj yc:ℝ) :
    Integrable (fun t:ℝ=>density g (Real.log yj) t*logPhase t (Real.log yc)*
      primeMark I (fun i=>poolList F (L i))
        (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A) :=
  overlap_mode_integrable g I (fun i=>poolList F (L i)) (fun i q=>a i q.val)
    (fun i q=>Real.log (slotRatio Z ell i q.val)) A (Real.log yj) (Real.log yc)

end SevenEighths.InverseInitialCommonProfile

end

end OAI
