import Mathlib
import OAI.Probability.SKValue.Control.Regularity

namespace OAI

section
open MeasureTheory Set Filter Function
open scoped Topology NNReal Nat
namespace SKValue
structure VolterraData (T:ℝ) (hT:0≤T) where
  field:ℝ → ℝ → ℝ
  lip:ℝ≥0
  bound:∀t∈Icc (0:ℝ) T,∀x y,dist (field t x) (field t y)≤lip*dist x y
  integ:∀Y:C(Icc (0:ℝ) T,ℝ),IntervalIntegrable (fun s ↦ field s (Y (projIcc 0 T hT s))) volume 0 T
namespace VolterraData
variable {T:ℝ} {hT:0≤T} (D:VolterraData T hT)
noncomputable def next (Y:C(Icc (0:ℝ) T,ℝ)):C(Icc (0:ℝ) T,ℝ) where
  toFun t:=∫s in (0:ℝ)..(t:ℝ),D.field s (Y (projIcc 0 T hT s))
  continuous_toFun:=by
    have hc:=intervalIntegral.continuousOn_primitive_interval' (D.integ Y) left_mem_uIcc
    rw [uIcc_of_le hT] at hc
    exact hc.domRestrict
lemma next_apply (Y:C(Icc (0:ℝ) T,ℝ)) (t:Icc (0:ℝ) T):
    D.next Y t=∫s in (0:ℝ)..(t:ℝ),D.field s (Y (projIcc 0 T hT s)) :=rfl
lemma integ_to (Y:C(Icc (0:ℝ) T,ℝ)) (t:Icc (0:ℝ) T):
    IntervalIntegrable (fun s ↦ D.field s (Y (projIcc 0 T hT s))) volume 0 t := by
  apply (D.integ Y).mono_set
  rw [uIcc_of_le t.2.1,uIcc_of_le hT]
  exact Icc_subset_Icc le_rfl t.2.2
lemma iterate_bound (Y Z:C(Icc (0:ℝ) T,ℝ)) (n:ℕ) (t:Icc (0:ℝ) T):
    dist ((D.next)^[n] Y t) ((D.next)^[n] Z t)≤
      (D.lip*|((t:ℝ)-0)|)^n/n.factorial*dist Y Z := by
  induction n generalizing t with
  | zero=>simpa using ContinuousMap.dist_apply_le_dist (f:=Y) (g:=Z) t
  | succ n hn=>
    rw [iterate_succ_apply',iterate_succ_apply',dist_eq_norm,next_apply,next_apply,
      ←intervalIntegral.integral_sub (D.integ_to _ t) (D.integ_to _ t)]
    calc
      _≤∫s in uIoc (0:ℝ) (t:ℝ),(D.lip:ℝ)^(n+1)*|s-0|^n/n.factorial*dist Y Z := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply norm_integral_le_of_norm_le ((by fun_prop:Continuous (fun s:ℝ ↦
          (D.lip:ℝ)^(n+1)*|s-0|^n/n.factorial*dist Y Z)).integrableOn_uIoc)
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
        rw [uIoc_of_le t.2.1] at hs
        have hsT:s∈Icc (0:ℝ) T:=⟨hs.1.le,hs.2.trans t.2.2⟩
        rw [←dist_eq_norm]
        have hp:=D.bound s hsT ((D.next)^[n] Y (projIcc 0 T hT s)) ((D.next)^[n] Z (projIcc 0 T hT s))
        have hh:=hn (⟨s,hsT⟩:Icc (0:ℝ) T)
        have he:projIcc 0 T hT s=(⟨s,hsT⟩:Icc (0:ℝ) T):=projIcc_of_mem hT hsT
        rw [he] at hp ⊢
        apply hp.trans
        calc
          _≤(D.lip:ℝ)*((D.lip*|s-0|)^n/n.factorial*dist Y Z):=mul_le_mul_of_nonneg_left hh D.lip.coe_nonneg
          _=_:=by rw [mul_pow,pow_succ];ring
      _≤_:=by
        apply le_of_abs_le
        rw [←intervalIntegral.abs_intervalIntegral_eq,intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div,intervalIntegral.integral_const_mul,abs_mul,abs_div,
          abs_mul,intervalIntegral.abs_intervalIntegral_eq,integral_pow_abs_sub_uIoc,abs_div,
          abs_pow,abs_pow,abs_dist,NNReal.abs_eq,abs_abs,mul_div,div_div,←abs_mul,
          ←Nat.cast_succ,←Nat.cast_mul,←Nat.factorial_succ,Nat.abs_cast,←mul_pow]
lemma exists_fixedPoint:∃Y:C(Icc (0:ℝ) T,ℝ),D.next Y=Y := by
  obtain ⟨n,hn⟩:= (FloorSemiring.tendsto_pow_div_factorial_atTop ((D.lip:ℝ)*T)).eventually
    (gt_mem_nhds zero_lt_one) |>.exists
  have hn0:0≤((D.lip:ℝ)*T)^n/n.factorial:=by positivity
  have hc:ContractingWith ⟨((D.lip:ℝ)*T)^n/n.factorial,hn0⟩ (D.next)^[n] := by
    refine ⟨hn,LipschitzWith.of_dist_le_mul (fun Y Z ↦ ?_)⟩
    rw [ContinuousMap.dist_le]
    · intro t
      apply (D.iterate_bound Y Z n t).trans
      simp only [sub_zero,abs_of_nonneg t.2.1]
      change (D.lip*↑t)^n/n.factorial*dist Y Z ≤ ((D.lip:ℝ)*T)^n/n.factorial*dist Y Z
      gcongr
      · exact mul_nonneg D.lip.coe_nonneg t.2.1
      · exact t.2.2
    · positivity
  exact ⟨_,hc.isFixedPt_fixedPoint_iterate⟩
end VolterraData
end SKValue

end

section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology NNReal
namespace SKValue
lemma exists_local_diffusion_path (W:BrownianSpace) (γ:OrderParameter) {T:ℝ}
    (hT:T∈Ico (0:ℝ) 1) (b:ℝ → ℝ) (hb:ContinuousOn b (Icc (0:ℝ) T)):
    ∃X:ℝ → ℝ,ContinuousOn X (Icc (0:ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ.coeff s*gradient W γ s (X s)) volume 0 T ∧
      ∀t∈Icc (0:ℝ) T,X t=b t+∫s in (0:ℝ)..t,γ.coeff s*gradient W γ s (X s) := by
  obtain ⟨K,L,Lu,hLu,hG,hu⟩:=(sourceStripRegularity W γ).core T hT
  have hg0:0≤γ.coeff T:=γ.nonneg T hT
  have hi:IntervalIntegrable γ.coeff volume 0 T:=γ.intervalIntegrable.mono_set (by
    rw [uIcc_of_le hT.1,uIcc_of_le (by norm_num:(0:ℝ)≤1)];exact Icc_subset_Icc le_rfl hT.2.le)
  have hj:=derivative_joint_continuous hLu hu
  let D:VolterraData T hT.1:={
    field:=fun t y ↦ γ.coeff t*gradient W γ t (b t+y)
    lip:=⟨γ.coeff T*Lu,mul_nonneg hg0 hLu⟩
    bound:=by
      intro t ht x y
      have hg:0≤γ.coeff t:=γ.nonneg t ⟨ht.1,ht.2.trans_lt hT.2⟩
      have hgt:γ.coeff t≤γ.coeff T:=γ.monotone ⟨ht.1,ht.2.trans_lt hT.2⟩ hT ht.2
      simp only [Real.dist_eq,←mul_sub,abs_mul,abs_of_nonneg hg]
      have hh:=hu t ht t ht (b t+x) (b t+y)
      simp only [sub_self,abs_zero,zero_add,add_sub_add_left_eq_sub] at hh
      change _≤(γ.coeff T*Lu)*|x-y|
      calc
        _≤γ.coeff t*(Lu*|x-y|):=mul_le_mul_of_nonneg_left hh hg
        _≤γ.coeff T*(Lu*|x-y|):=mul_le_mul_of_nonneg_right hgt (by positivity)
        _=_:=by ring
    integ:=by
      intro Y
      apply hi.mul_continuousOn
      rw [uIcc_of_le hT.1]
      apply hj.comp (continuousOn_id.prodMk (hb.add ((Y.continuous.comp continuous_projIcc).continuousOn)))
      exact fun t ht ↦ ht }
  obtain ⟨Y,hY⟩:=D.exists_fixedPoint
  let X:=fun t ↦ b t+Y (projIcc 0 T hT.1 t)
  have hXcont:ContinuousOn X (Icc (0:ℝ) T):=hb.add ((Y.continuous.comp continuous_projIcc).continuousOn)
  refine ⟨X,hXcont,D.integ Y,?_⟩
  intro t ht
  have he:=congrArg (fun f:C(Icc (0:ℝ) T,ℝ) ↦ f ⟨t,ht⟩) hY
  change (∫s in (0:ℝ)..t,γ.coeff s*gradient W γ s (X s))=Y ⟨t,ht⟩ at he
  dsimp only [X]
  rw [projIcc_of_mem hT.1 ht,he]
end SKValue

end

end OAI
