import Mathlib
import OAI.Probability.LogConcave.TensorGraphs.IncidentMatrix
import OAI.Probability.LogConcave.JetEstimates.JetCongrList

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.AdjointRemoval
variable {d : ℕ} {P : Type*}

lemma hessian_congr_on_tokens (H : Point d → ℝ) (b c : P → Point d) (h : Hessian P)
    (he : ∀i∈h.tokens,b i=c i) : hessian H b h=hessian H c h := by
  have hf : b h.first=c h.first := he _ (by simp [Hessian.tokens])
  have hs : b h.second=c h.second := he _ (by simp [Hessian.tokens])
  unfold hessian
  rw [hf,hs]
  apply JetCalculus.jet_congr_on_list
  intro i hi
  exact he i (by simp [Hessian.tokens,hi])
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule
open scoped Classical

variable {n d : ℕ} {S : State (Fin (n+1))}

noncomputable def hessianIncidenceTensor
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (H : Point d → ℝ) (b : Fin d → Point d)
    (h : S.hessians) (x : Point d)
    (a : {t : Edge (U:=InternalEdge β) q //
      IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
        (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inr h) q t} → Fin d) : ℝ :=
  hessian H (fun i => if hi : destination hS i=Sum.inr h then
    b (a ⟨Sum.inl (Sum.inr i),Or.inr hi⟩) else 0) h x

lemma hessianIncidenceTensor_global
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (H : Point d → ℝ) (b : Fin d → Point d)
    (h : S.hessians) (x : Point d) (c : InternalEdge β ⊕ Fin q → Fin d) :
    hessianIncidenceTensor hS β q H b h x (fun t => duplicate c t.val)=
      hessian H (fun i => b (c (Sum.inl (Sum.inr i)))) h x := by
  unfold hessianIncidenceTensor
  refine congrFun (hessian_congr_on_tokens (P:=Fin (n+1)) H _ _
    (h : Hessian (Fin (n+1))) ?_) x
  intro i hi
  have hd : destination hS i=Sum.inr h :=
    (destination_iff_mem hS i (Sum.inr h)).mpr hi
  simp only [dite_eq_left hd]
  rfl
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule
open scoped Classical

variable {n d : ℕ} {S : State (Fin (n+1))}

abbrev TraceEdge (β : Fin n → ℕ) (q : ℕ) :=
  ((k : Fin n) × Fin (β k)) ⊕ (Fin q ⊕ Fin q)

def traceEmbed (β : Fin n → ℕ) (q : ℕ) : TraceEdge β q → Edge (U:=InternalEdge β) q
  | Sum.inl e => Sum.inl (Sum.inl e)
  | Sum.inr e => Sum.inr e

abbrev PrimaryTraceSlot
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) :=
  {t : TraceEdge β q //
    IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
      (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inl i) q (traceEmbed β q t)}

noncomputable def primaryIncidenceTensor
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (b : Fin d → Point d) (i : Fin (n+1))
    (F : (PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ) (x : Point d)
    (a : {t : Edge (U:=InternalEdge β) q //
      IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
        (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inl i) q t} → Fin d) : ℝ :=
  JetCalculus.jet (fun j => if hj : destination hS j=Sum.inl i then
    b (a ⟨Sum.inl (Sum.inr j),Or.inr hj⟩) else 0) (S.derivatives i)
      (F (fun t => a ⟨traceEmbed β q t.val,t.property⟩)
        (a ⟨Sum.inl (Sum.inr i),Or.inl rfl⟩)) x

lemma primaryIncidenceTensor_global
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (b : Fin d → Point d) (i : Fin (n+1))
    (F : (PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ)
    (x : Point d) (c : InternalEdge β ⊕ Fin q → Fin d) :
    primaryIncidenceTensor hS β q b i F x (fun t => duplicate c t.val)=
      JetCalculus.jet (fun j => b (c (Sum.inl (Sum.inr j)))) (S.derivatives i)
        (F (fun t => duplicate c (traceEmbed β q t.val)) (c (Sum.inl (Sum.inr i)))) x := by
  unfold primaryIncidenceTensor
  apply congrFun (JetCalculus.jet_congr_on_list _ _ _ _ ?_) x
  intro j hj
  have hd : destination hS j=Sum.inl i :=
    (destination_iff_mem hS j (Sum.inl i)).mpr hj
  simp only [dite_eq_left hd]
  rfl
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule TensorEnergy MeasureTheory
open scoped BigOperators Classical ENNReal

variable {n d : ℕ} {S : State (Fin (n+1))}
local instance edgeDecEqBT (β : Fin n → ℕ) (q : ℕ) :
    DecidableEq (Edge (U:=InternalEdge β) q) := Classical.decEq _
local instance cutDecEqBT (β : Fin n → ℕ) (q : ℕ) :
    DecidableEq (InternalEdge β ⊕ Fin q) :=
  @instDecidableEqSum _ _ (Classical.decEq _) (Classical.decEq _)

noncomputable def branchIncidenceTensor
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (H : Point d → ℝ) (b : Fin d → Point d)
    (F : ∀i,(PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ)
    (x : Point d) (v : TargetVertex S) :
    ({t : Edge (U:=InternalEdge β) q //
      IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
        (Sum.inl 0) (Sum.inl (Fin.last n)) v q t} → Fin d) → ℝ :=
  match v with
  | Sum.inl i => primaryIncidenceTensor hS β q b i (F i) x
  | Sum.inr h => hessianIncidenceTensor hS β q H b h x

lemma branchIncidenceTensor_global
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (H : Point d → ℝ) (b : Fin d → Point d)
    (F : ∀i,(PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ)
    (x : Point d) (c : InternalEdge β ⊕ Fin q → Fin d) :
    (∏v,branchIncidenceTensor hS β q H b F x v (fun t => duplicate c t.val))=
      (∏i,JetCalculus.jet (fun j => b (c (Sum.inl (Sum.inr j)))) (S.derivatives i)
        (F i (fun t => duplicate c (traceEmbed β q t.val)) (c (Sum.inl (Sum.inr i)))) x)*
      (S.hessians.map (fun h => hessian H (fun j => b (c (Sum.inl (Sum.inr j)))) h x)).prod := by
  rw [Fintype.prod_sum_type]
  simp only [branchIncidenceTensor,primaryIncidenceTensor_global,hessianIncidenceTensor_global]
  congr 1
  change (Finset.univ.val.map (fun h : S.hessians =>
    hessian H (fun j => b (c (Sum.inl (Sum.inr j)))) h x)).prod=_
  exact congrArg Multiset.prod (Multiset.map_univ S.hessians
    (fun h => hessian H (fun j => b (c (Sum.inl (Sum.inr j)))) h x))

theorem literal_branch_integral_bound
    (μ : Measure (Point d))
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (hβ : ∀k,0<β k) (q : ℕ) (hq : 0<q)
    (H : Point d → ℝ) (b : Fin d → Point d)
    (F : ∀i,(PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ)
    (M : TargetVertex S → Point d → ℝ) (hM : ∀v x,0≤M v x)
    (hT : ∀v x,AllSplitBound (branchIncidenceTensor hS β q H b F x v) (M v x))
    (B : Fin (n+1) → ℝ≥0∞) (C : S.hessians → ℝ≥0∞)
    (hMp : ∀i,AEMeasurable (fun x => ENNReal.ofReal (M (Sum.inl i) x)) μ)
    (hp : ∀i,(∫⁻x,ENNReal.ofReal (M (Sum.inl i) x)^(n+1) ∂μ)≤B i^(n+1))
    (hh : ∀h x,ENNReal.ofReal (M (Sum.inr h) x)≤C h) (hC : ∀h,C h≠⊤) :
    (∫⁻x,ENNReal.ofReal |∑c : InternalEdge β ⊕ Fin q → Fin d,
      (∏i,JetCalculus.jet (fun j => b (c (Sum.inl (Sum.inr j)))) (S.derivatives i)
        (F i (fun t => duplicate c (traceEmbed β q t.val)) (c (Sum.inl (Sum.inr i)))) x)*
      (S.hessians.map (fun h => hessian H (fun j => b (c (Sum.inl (Sum.inr j)))) h x)).prod| ∂μ)≤
      (d:ℝ≥0∞)^q*((∏i,B i)*(∏h,C h)) := by
  have hb := actual_tensor_integral_bound μ hS β hβ q d hq
    (branchIncidenceTensor hS β q H b F) M hM hT B C hMp hp hh hC
  convert hb using 1
  congr 1
  funext x
  congr 2
  apply Finset.sum_congr rfl
  intro c _
  exact (branchIncidenceTensor_global hS β q H b F x c).symm
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule
open scoped Classical

variable {n : ℕ} {S : State (Fin (n+1))}

noncomputable def primaryIncidentCases
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) :
    {t : Edge (U:=InternalEdge β) q //
      IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
        (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inl i) q t} ≃
      PrimaryTraceSlot hS β q i ⊕ (Unit ⊕ {j : Fin (n+1) // destination hS j=Sum.inl i}) where
  toFun t := by
    rcases t with ⟨(e|j)|e,ht⟩
    · exact Sum.inl ⟨Sum.inl e,ht⟩
    · by_cases hj : j=i
      · exact Sum.inr (Sum.inl ())
      · exact Sum.inr (Sum.inr ⟨j,ht.resolve_left (fun h => hj (Sum.inl.inj h))⟩)
    · exact Sum.inl ⟨Sum.inr e,ht⟩
  invFun t := by
    rcases t with t | (u | j)
    · exact ⟨traceEmbed β q t.val,t.property⟩
    · exact ⟨Sum.inl (Sum.inr i),Or.inl rfl⟩
    · exact ⟨Sum.inl (Sum.inr j.val),Or.inr j.property⟩
  left_inv t := by
    rcases t with ⟨(e|j)|e,ht⟩
    · rfl
    · dsimp only
      split_ifs with hj
      · subst j; rfl
      · rfl
    · rfl
  right_inv t := by
    rcases t with ⟨e|e,ht⟩ | (u | ⟨j,hj⟩)
    · rfl
    · rfl
    · cases u
      dsimp only
      simp only [dite_true]
    · dsimp only
      rw [dite_eq_right (destination_primary_ne hS hj)]

noncomputable def primarySlotEquiv
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) :
    (PrimaryTraceSlot hS β q i ⊕ (Unit ⊕ Fin (S.derivatives i).length)) ≃
      {t : Edge (U:=InternalEdge β) q //
        IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
          (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inl i) q t} :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) (derivativeEdgeEquiv hS i))).trans
    (primaryIncidentCases hS β q i).symm

lemma primarySlotEquiv_trace
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) (t : PrimaryTraceSlot hS β q i) :
    (primarySlotEquiv hS β q i (Sum.inl t)).val=traceEmbed β q t.val := rfl

lemma primarySlotEquiv_source
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) :
    (primarySlotEquiv hS β q i (Sum.inr (Sum.inl ()))).val=Sum.inl (Sum.inr i) := rfl

lemma primarySlotEquiv_derivative
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) (k : Fin (S.derivatives i).length) :
    (primarySlotEquiv hS β q i (Sum.inr (Sum.inr k))).val=
      Sum.inl (Sum.inr ((S.derivatives i).get k)) := rfl
end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
