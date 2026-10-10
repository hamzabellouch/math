import OAI.Dynamics.StandardMap.CurveOneStep

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology Classical
namespace StandardMapEntropy
def CurveTree (N : ℕ) : ℕ  →  Type
  | 0 => Unit
  | n+1 => CurveTree N n × CurveStepBranch N
instance curveTreeFintype (N n : ℕ) : Fintype (CurveTree N n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact @instFintypeProd _ _ ih inferInstance
lemma curveTree_card (N n : ℕ) : Fintype.card (CurveTree N n)=(196*N)^n := by
  induction n with
  | zero => change Fintype.card Unit=_; simp
  | succ n ih =>
      change Fintype.card (CurveTree N n × CurveStepBranch N)=_
      rw [Fintype.card_prod,ih,curveStepBranch_card,pow_succ]
noncomputable def fullCurveInterval : CurveInterval := ⟨0,1,le_rfl,by norm_num,le_rfl⟩
lemma fullCurveInterval_parameter : fullCurveInterval.parameter=id := by
  funext t; simp [fullCurveInterval,CurveInterval.parameter,affineParameter]
lemma curve_iterate_cover (k ε δ : ℝ) (hk : 0≤k) (hε : 0≤ε) (hδ0 : 0≤δ)
    (hδ1 : δ≤1) (hδ : 6*δ≤ε) (hε1 : 2*Real.pi*ε≤1) (hε2 : growthBase k*ε≤1)
    (N : ℕ) (hN : 0<N) (hN2 : 2*growthBase k≤(N:ℝ)^2)
    (g : ControlledCurve ε) (c : ℕ → CurvePlane) (n : ℕ) :
    ∃(I : CurveTree N n → CurveInterval) (C : CurveTree N n → ControlledCurve ε),
      (∀s∈Icc (0:ℝ) 1,(∀j<n,wrappedBox δ (c j) ((liftStep k)^[j+1] (g.map s)))  →
        ∃i,s∈Icc (I i).left (I i).right) ∧
      ∀i,(C i).map=(liftStep k)^[n] ∘ g.map ∘ (I i).parameter := by
  induction n with
  | zero =>
      refine ⟨fun _=>fullCurveInterval,fun _=>g,fun s hs _=>⟨(),hs⟩,?_⟩
      intro i; simp only [Function.iterate_zero,fullCurveInterval_parameter,Function.comp_id,Function.id_comp]
  | succ n ih =>
      obtain ⟨I,C,hcover,hmap⟩:=ih
      have hex:∀i:CurveTree N n,∃(J : CurveStepBranch N → CurveInterval)
          (D : CurveStepBranch N → ControlledCurve ε),
          (∀s∈Icc (0:ℝ) 1,wrappedBox δ (c n) (liftStep k ((C i).map s))  →
            ∃j,s∈Icc (J j).left (J j).right) ∧
          ∀j,(D j).map=(liftStep k) ∘ (C i).map ∘ (J j).parameter :=
        fun i=>curve_one_step_cover k ε δ hk hε hδ0 hδ1 hδ hε1 hε2 N hN hN2 (C i) (c n)
      choose J D hcover' hmap' using hex
      refine ⟨fun b=>(I b.1).comp (J b.1 b.2),fun b=>D b.1 b.2,?_,?_⟩
      · intro s hs hc
        obtain ⟨i,hi⟩:=hcover s hs (fun j hj=>hc j (by omega))
        obtain ⟨t,ht,hts⟩:=(I i).parameter_range.superset hi
        have hh:wrappedBox δ (c n) (liftStep k ((C i).map t)) := by
          rw [hmap]
          simpa only [Function.comp_apply,hts,Function.iterate_succ_apply'] using hc n (by omega)
        obtain ⟨j,hj⟩:=hcover' i t ht hh
        refine ⟨(i,j),?_⟩
        rw [← hts]
        exact (I i).comp_mem (J i j) hj
      · intro b
        rw [hmap',hmap]
        funext t
        simp only [Function.comp_apply,CurveInterval.comp_parameter,Function.iterate_succ_apply']
noncomputable def curveIterVelocity (k : ℝ) (g v : ℝ → CurvePlane) : ℕ  →  ℝ  →  CurvePlane
  | 0 => v
  | n+1 => liftCurveVelocity k ((liftStep k)^[n] ∘ g) (curveIterVelocity k g v n)
lemma curveIter_hasDeriv (k : ℝ) (g v : ℝ → CurvePlane)
    (hv : ∀t,HasDerivAt g (v t) t) (n : ℕ) (t : ℝ) :
    HasDerivAt ((liftStep k)^[n] ∘ g) (curveIterVelocity k g v n t) t := by
  induction n generalizing t with
  | zero => simpa only [Function.iterate_zero,Function.id_comp,curveIterVelocity] using hv t
  | succ n ih =>
      have h:=liftCurve_hasDeriv k ((liftStep k)^[n] ∘ g) (curveIterVelocity k g v n) ih t
      convert h using 1
      · funext x
        simp only [Function.comp_apply,Function.iterate_succ_apply']
      · rfl
lemma curveIter_velocity_continuous (k : ℝ) (g v : ℝ → CurvePlane)
    (hv : ∀t,HasDerivAt g (v t) t) (hc : Continuous v) (n : ℕ) :
    Continuous (curveIterVelocity k g v n) := by
  induction n with
  | zero => exact hc
  | succ n ih =>
      exact liftCurve_velocity_continuous k _ _
        (continuous_iff_continuousAt.mpr fun t=>(curveIter_hasDeriv k g v hv n t).continuousAt) ih
end StandardMapEntropy

end OAI
