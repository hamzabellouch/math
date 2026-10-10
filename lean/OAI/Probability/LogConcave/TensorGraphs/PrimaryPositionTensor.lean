import Mathlib
import OAI.Probability.LogConcave.TensorGraphs.HessianIncidentEquiv
import OAI.Probability.LogConcave.TensorGraphs.HessianIncidenceTensor
import OAI.Probability.LogConcave.JetEstimates.JetMapPositions
import OAI.Probability.LogConcave.JetEstimates.Reindex

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
open GraphSchedule TensorEnergy
open scoped Classical

variable {n d : ℕ} {S : State (Fin (n+1))}

noncomputable def primaryPositionTensor
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (b : Fin d → Point d) (i : Fin (n+1))
    (F : (PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ) (x : Point d)
    (a : PrimaryTraceSlot hS β q i ⊕ (Unit ⊕ Fin (S.derivatives i).length) → Fin d) : ℝ :=
  JetCalculus.jet (fun k => b (a (Sum.inr (Sum.inr k))))
    (List.finRange (S.derivatives i).length)
    (F (fun t => a (Sum.inl t)) (a (Sum.inr (Sum.inl ())))) x

lemma primaryIncidenceTensor_positions
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (b : Fin d → Point d) (i : Fin (n+1))
    (F : (PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ) (x : Point d)
    (a : {t : Edge (U:=InternalEdge β) q //
      IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
        (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inl i) q t} → Fin d) :
    primaryIncidenceTensor hS β q b i F x a=
      primaryPositionTensor hS β q b i F x (a ∘ primarySlotEquiv hS β q i) := by
  unfold primaryIncidenceTensor primaryPositionTensor
  rw [JetCalculus.jet_finRange]
  congr 2
  funext k
  have hk : (S.derivatives i).get k∈S.derivatives i := List.get_mem _ _
  have hd : destination hS ((S.derivatives i).get k)=Sum.inl i :=
    (destination_iff_mem hS _ (Sum.inl i)).mpr hk
  simp only [dite_eq_left hd]
  rfl

lemma primaryIncidenceTensor_allSplit
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (b : Fin d → Point d) (i : Fin (n+1))
    (F : (PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ) (x : Point d)
    (M : ℝ) (hM : AllSplitBound (primaryPositionTensor hS β q b i F x) M) :
    AllSplitBound (primaryIncidenceTensor hS β q b i F x) M := by
  have he : primaryIncidenceTensor hS β q b i F x=
    fun a => primaryPositionTensor hS β q b i F x (a ∘ primarySlotEquiv hS β q i) :=
      funext (primaryIncidenceTensor_positions hS β q b i F x)
  rw [he]
  exact hM.reindex (primarySlotEquiv hS β q i)
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule TensorEnergy
open scoped Classical

variable {n d : ℕ} {S : State (Fin (n+1))}

def hessianPositionList {P : Type*} (h : Hessian P) : List P :=
  h.first::h.second::h.extra

noncomputable def hessianPositionTensor
    (H : Point d → ℝ) (b : Fin d → Point d) (h : Hessian (Fin (n+1))) (x : Point d)
    (a : Fin (h.first::h.second::h.extra).length → Fin d) : ℝ :=
  JetCalculus.jet (fun k : Fin h.extra.length => b (a ⟨k.val+2,by simp only [List.length_cons]; omega⟩))
    (List.finRange h.extra.length)
    (directional (b (a ⟨0,by simp⟩)) (directional (b (a ⟨1,by simp⟩)) H)) x

lemma hessianIncidence_direction
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (b : Fin d → Point d) (h : S.hessians)
    (a : {t : Edge (U:=InternalEdge β) q //
      IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
        (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inr h) q t} → Fin d)
    (k : Fin (hessianPositionList (h : Hessian (Fin (n+1)))).length) :
    (if ht : destination hS ((hessianPositionList (h : Hessian (Fin (n+1)))).get k)=Sum.inr h then
      b (a ⟨Sum.inl (Sum.inr ((hessianPositionList (h : Hessian (Fin (n+1)))).get k)),Or.inr ht⟩) else 0)=
      b (a (hessianSlotEquiv hS β q h k)) := by
  have hk : (hessianPositionList (h : Hessian (Fin (n+1)))).get k∈ports S (Sum.inr h) := List.get_mem _ _
  have hd := (destination_iff_mem hS _ (Sum.inr h)).mpr hk
  simp only [dite_eq_left hd]
  rfl

lemma hessianIncidenceTensor_positions
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (H : Point d → ℝ) (b : Fin d → Point d)
    (h : S.hessians) (x : Point d)
    (a : {t : Edge (U:=InternalEdge β) q //
      IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
        (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inr h) q t} → Fin d) :
    hessianIncidenceTensor hS β q H b h x a=
      hessianPositionTensor H b (h : Hessian (Fin (n+1))) x (a ∘ hessianSlotEquiv hS β q h) := by
  have hf := hessianIncidence_direction hS β q b h a ⟨0,by simp [hessianPositionList]⟩
  have hs := hessianIncidence_direction hS β q b h a ⟨1,by simp [hessianPositionList]⟩
  simp only [hessianPositionList,List.get_eq_getElem,List.getElem_cons_zero,List.getElem_cons_succ] at hf hs
  unfold hessianIncidenceTensor hessianPositionTensor hessian
  rw [JetCalculus.jet_finRange]
  refine congrFun (congrArg₂
    (fun (v : Fin (h : Hessian (Fin (n+1))).extra.length → Point d) (f : Point d → ℝ) =>
      JetCalculus.jet v (List.finRange (h : Hessian (Fin (n+1))).extra.length) f) ?_ ?_) x
  · funext k
    have he := hessianIncidence_direction hS β q b h a ⟨k.val+2,by simp only [hessianPositionList,List.length_cons]; omega⟩
    simp only [hessianPositionList,List.get_eq_getElem,List.getElem_cons_succ] at he
    convert he using 1 <;> rfl
  · convert congrArg₂ directional hf (congrArg (fun v => directional v H) hs) using 1 <;> rfl

lemma hessianIncidenceTensor_allSplit
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (H : Point d → ℝ) (b : Fin d → Point d)
    (h : S.hessians) (x : Point d) (M : ℝ)
    (hM : AllSplitBound (hessianPositionTensor H b (h : Hessian (Fin (n+1))) x) M) :
    AllSplitBound (hessianIncidenceTensor hS β q H b h x) M := by
  have he : hessianIncidenceTensor hS β q H b h x=
    fun a => hessianPositionTensor H b (h : Hessian (Fin (n+1))) x (a ∘ hessianSlotEquiv hS β q h) :=
      funext (hessianIncidenceTensor_positions hS β q H b h x)
  rw [he]
  exact hM.reindex (hessianSlotEquiv hS β q h)
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule TensorEnergy MeasureTheory
open scoped BigOperators Classical ENNReal

variable {n d : ℕ} {S : State (Fin (n+1))}
local instance edgeDecEqPB (β : Fin n → ℕ) (q : ℕ) :
    DecidableEq (Edge (U:=InternalEdge β) q) := Classical.decEq _
local instance cutDecEqPB (β : Fin n → ℕ) (q : ℕ) :
    DecidableEq (InternalEdge β ⊕ Fin q) :=
  @instDecidableEqSum _ _ (Classical.decEq _) (Classical.decEq _)

theorem positional_branch_integral_bound
    (μ : Measure (Point d))
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (hβ : ∀k,0<β k) (q : ℕ) (hq : 0<q)
    (H : Point d → ℝ) (b : Fin d → Point d)
    (F : ∀i,(PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ)
    (Mp : Fin (n+1) → Point d → ℝ) (Mh : S.hessians → Point d → ℝ)
    (hMp0 : ∀i x,0≤Mp i x) (hMh0 : ∀h x,0≤Mh h x)
    (hTp : ∀i x,AllSplitBound (primaryPositionTensor hS β q b i (F i) x) (Mp i x))
    (hTh : ∀(h : S.hessians) x,AllSplitBound
      (hessianPositionTensor H b (h : Hessian (Fin (n+1))) x) (Mh h x))
    (B : Fin (n+1) → ℝ≥0∞) (C : S.hessians → ℝ≥0∞)
    (hMp : ∀i,AEMeasurable (fun x => ENNReal.ofReal (Mp i x)) μ)
    (hp : ∀i,(∫⁻x,ENNReal.ofReal (Mp i x)^(n+1) ∂μ)≤B i^(n+1))
    (hh : ∀h x,ENNReal.ofReal (Mh h x)≤C h) (hC : ∀h,C h≠⊤) :
    (∫⁻x,ENNReal.ofReal |∑c : InternalEdge β ⊕ Fin q → Fin d,
      (∏i,JetCalculus.jet (fun j => b (c (Sum.inl (Sum.inr j)))) (S.derivatives i)
        (F i (fun t => duplicate c (traceEmbed β q t.val)) (c (Sum.inl (Sum.inr i)))) x)*
      (S.hessians.map (fun h => hessian H (fun j => b (c (Sum.inl (Sum.inr j)))) h x)).prod| ∂μ)≤
      (d:ℝ≥0∞)^q*((∏i,B i)*(∏h,C h)) := by
  apply literal_branch_integral_bound μ hS β hβ q hq H b F (Sum.elim Mp Mh)
    (fun v => Sum.recOn v hMp0 hMh0) _ B C hMp hp hh hC
  intro v x
  cases v with
  | inl i => exact primaryIncidenceTensor_allSplit hS β q b i (F i) x (Mp i x) (hTp i x)
  | inr h => exact hessianIncidenceTensor_allSplit hS β q H b h x (Mh h x) (hTh h x)
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open scoped BigOperators ENNReal

variable {P : Type*} [Fintype P] [DecidableEq P]

omit [Fintype P] in
lemma hessian_sum_toType {S : State P} (f : Hessian P → ℕ) :
    (∑h : S.hessians,f h)=(S.hessians.map f).sum := by
  change (Finset.univ.val.map (fun h : S.hessians => f h)).sum=_
  exact congrArg Multiset.sum (Multiset.map_univ S.hessians f)

theorem terminal_product_budget {S : State P}
    (hS : S∈expand (Fintype.card P) initial) (j k : ℕ)
    (A R : ℝ≥0∞) (hA : 1≤A) (hR : 1≤R) :
    (∏i : P,A^(j+(S.derivatives i).length+1)*R^(k+j+(S.derivatives i).length))*
      (∏h : S.hessians,A^((h : Hessian P).extra.length+1)*R^((h : Hessian P).extra.length))≤
      A^(2*(Fintype.card P)*(j+1))*R^((Fintype.card P)*(k+j+1)) := by
  have hb := terminal_moment_budgets hS j k
  have hpa : (∑i : P,(j+(S.derivatives i).length+1))=
      (Fintype.card P)*(j+1)+∑i : P,(S.derivatives i).length := by
    simp only [show ∀i : P,j+(S.derivatives i).length+1=j+1+(S.derivatives i).length from
      fun i => by omega]
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul]
    ring
  have hpr : (∑i : P,(k+j+(S.derivatives i).length))=
      (Fintype.card P)*(k+j)+∑i : P,(S.derivatives i).length := by
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul]
    ring
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  simp only [Finset.prod_pow_eq_pow_sum,hpa,hpr]
  rw [hessian_sum_toType (S:=S) (fun h => h.extra.length+1),
    hessian_sum_toType (S:=S) (fun h => h.extra.length)]
  calc
    _ = A^((Fintype.card P)*(j+1)+(∑i,(S.derivatives i).length)+
        (S.hessians.map (fun h => h.extra.length+1)).sum)*
      R^((Fintype.card P)*(k+j)+(∑i,(S.derivatives i).length)+
        (S.hessians.map (fun h => h.extra.length)).sum) := by
          simp only [pow_add]
          ring
    _ ≤ _ := mul_le_mul' (pow_le_pow_right₀ hA hb.2.2.2.2)
      (pow_le_pow_right₀ hR hb.2.2.2.1)
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule TensorEnergy MeasureTheory
open scoped BigOperators Classical ENNReal

variable {n d : ℕ} {S : State (Fin (n+1))}
local instance edgeDecEqQB (β : Fin n → ℕ) (q : ℕ) :
    DecidableEq (Edge (U:=InternalEdge β) q) := Classical.decEq _
local instance cutDecEqQB (β : Fin n → ℕ) (q : ℕ) :
    DecidableEq (InternalEdge β ⊕ Fin q) :=
  @instDecidableEqSum _ _ (Classical.decEq _) (Classical.decEq _)

theorem quantitative_branch_integral_bound
    (μ : Measure (Point d))
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (hβ : ∀k,0<β k) (q : ℕ) (hq : 0<q)
    (H : Point d → ℝ) (b : Fin d → Point d)
    (F : ∀i,(PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ)
    (Mp : Fin (n+1) → Point d → ℝ) (Mh : S.hessians → Point d → ℝ)
    (hMp0 : ∀i x,0≤Mp i x) (hMh0 : ∀h x,0≤Mh h x)
    (hTp : ∀i x,AllSplitBound (primaryPositionTensor hS β q b i (F i) x) (Mp i x))
    (hTh : ∀(h : S.hessians) x,AllSplitBound
      (hessianPositionTensor H b (h : Hessian (Fin (n+1))) x) (Mh h x))
    (j k : ℕ) (A R : ℝ≥0∞) (hA : 1≤A) (hR : 1≤R) (hAf : A≠⊤) (hRf : R≠⊤)
    (hMp : ∀i,AEMeasurable (fun x => ENNReal.ofReal (Mp i x)) μ)
    (hp : ∀i,(∫⁻x,ENNReal.ofReal (Mp i x)^(n+1) ∂μ)≤
      (A^(j+(S.derivatives i).length+1)*R^(k+j+(S.derivatives i).length))^(n+1))
    (hh : ∀(h : S.hessians) x,ENNReal.ofReal (Mh h x)≤
      A^((h : Hessian (Fin (n+1))).extra.length+1)*R^((h : Hessian (Fin (n+1))).extra.length)) :
    (∫⁻x,ENNReal.ofReal |∑c : InternalEdge β ⊕ Fin q → Fin d,
      (∏i,JetCalculus.jet (fun a => b (c (Sum.inl (Sum.inr a)))) (S.derivatives i)
        (F i (fun t => duplicate c (traceEmbed β q t.val)) (c (Sum.inl (Sum.inr i)))) x)*
      (S.hessians.map (fun h => hessian H (fun a => b (c (Sum.inl (Sum.inr a)))) h x)).prod| ∂μ)≤
      (d:ℝ≥0∞)^q*(A^(2*(n+1)*(j+1))*R^((n+1)*(k+j+1))) := by
  have hC (h : S.hessians) :
      A^((h : Hessian (Fin (n+1))).extra.length+1)*R^((h : Hessian (Fin (n+1))).extra.length)≠⊤ := by
    finiteness
  have hb := positional_branch_integral_bound μ hS β hβ q hq H b F Mp Mh hMp0 hMh0 hTp hTh
    (fun i => A^(j+(S.derivatives i).length+1)*R^(k+j+(S.derivatives i).length))
    (fun h => A^((h : Hessian (Fin (n+1))).extra.length+1)*R^((h : Hessian (Fin (n+1))).extra.length))
    hMp hp hh hC
  apply hb.trans
  apply mul_le_mul' le_rfl
  simpa only [Fintype.card_fin] using terminal_product_budget hS j k A R hA hR
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory
open scoped ENNReal

variable {Ω α P : Type*} [MeasurableSpace Ω] [Fintype P] [DecidableEq P]

omit [Fintype P] [DecidableEq P] in

lemma lintegral_abs_list_sum_bound (μ : Measure Ω) (L : List α)
    (f : α → Ω → ℝ) (B : ℝ≥0∞)
    (hm : ∀a∈L,AEMeasurable (f a) μ)
    (hb : ∀a∈L,(∫⁻x,ENNReal.ofReal |f a x| ∂μ)≤B) :
    (∫⁻x,ENNReal.ofReal |(L.map (fun a => f a x)).sum| ∂μ)≤(L.length:ℝ≥0∞)*B := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hm' : ∀b∈L,AEMeasurable (f b) μ := fun b h => hm b (List.mem_cons_of_mem a h)
    have hb' : ∀b∈L,(∫⁻x,ENNReal.ofReal |f b x| ∂μ)≤B := fun b h => hb b (List.mem_cons_of_mem a h)
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    calc
      _ ≤ ∫⁻x,ENNReal.ofReal |f a x|+ENNReal.ofReal |(L.map (fun a => f a x)).sum| ∂μ := by
        apply lintegral_mono
        intro x
        dsimp only
        rw [←ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (abs_add_le _ _)
      _ = (∫⁻x,ENNReal.ofReal |f a x| ∂μ)+(∫⁻x,ENNReal.ofReal |(L.map (fun a => f a x)).sum| ∂μ) :=
        lintegral_add_left' ((hm a (List.mem_cons_self)).abs.ennreal_ofReal) _
      _ ≤ B+(L.length:ℝ≥0∞)*B := add_le_add (hb a List.mem_cons_self) (ih hm' hb')
      _ = ((L.length+1:ℕ):ℝ≥0∞)*B := by simp only [Nat.cast_add,Nat.cast_one,add_mul,one_mul]; rw [add_comm]

theorem removal_sum_bound (μ : Measure Ω) (f : State P → Ω → ℝ) (B : ℝ≥0∞)
    (hm : ∀S∈expand (Fintype.card P) initial,AEMeasurable (f S) μ)
    (hb : ∀S∈expand (Fintype.card P) initial,(∫⁻x,ENNReal.ofReal |f S x| ∂μ)≤B) :
    (∫⁻x,ENNReal.ofReal |((expand (Fintype.card P) initial).map (fun S => f S x)).sum| ∂μ)≤
      ((3*Fintype.card P+1:ℕ):ℝ≥0∞)^(Fintype.card P)*B := by
  apply (lintegral_abs_list_sum_bound μ _ f B hm hb).trans
  apply mul_le_mul' _ le_rfl
  exact_mod_cast (full_expansion_bookkeeping (P:=P)).1
end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
