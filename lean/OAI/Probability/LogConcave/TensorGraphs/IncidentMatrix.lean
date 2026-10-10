import Mathlib
import OAI.Probability.LogConcave.TensorGraphs.RankEquiv
import OAI.Probability.LogConcave.JetEstimates.AllSplitBound

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

namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V U : Type*} [Fintype V] [Fintype U]
    (key : V → ℕ) (src dst : U → V)
local instance edgeDecEqT (q : ℕ) : DecidableEq (Edge (U:=U) q) := Classical.decEq _
local instance finDecEqT (d : ℕ) : DecidableEq (Fin d) := Classical.decEq _

noncomputable def incidentMatrix (hkey : Function.Injective key) (hne : ∀u,src u≠dst u)
    (first last v : V) (q d : ℕ)
    (T : ({t : Edge (U:=U) q // IncidentAt src dst first last v q t} → Fin d) → ℝ) :
    (Frontier.Outgoing (emit key src dst first last q) (key v) → Fin d) →
      (Frontier.Incoming (absorb key src dst first last q) (key v) → Fin d) → ℝ :=
  fun o i => T (fun t => Sum.elim i o (incidentSplit key src dst hkey hne first last v q t))

omit [Fintype U] in
lemma incidentMatrix_global (hkey : Function.Injective key) (hne : ∀u,src u≠dst u)
    (first last v : V) (q d : ℕ)
    (T : ({t : Edge (U:=U) q // IncidentAt src dst first last v q t} → Fin d) → ℝ)
    (c : Edge (U:=U) q → Fin d) :
    incidentMatrix key src dst hkey hne first last v q d T
      (fun t => c t.val) (fun t => c t.val)=T (fun t => c t.val) := by
  unfold incidentMatrix
  congr 1
  funext t
  dsimp only [incidentSplit,Equiv.coe_fn_mk]
  split_ifs <;> rfl

lemma incidentMatrix_bound (hkey : Function.Injective key) (hne : ∀u,src u≠dst u)
    (first last v : V) (q d : ℕ)
    (T : ({t : Edge (U:=U) q // IncidentAt src dst first last v q t} → Fin d) → ℝ)
    (M : ℝ) (hT : TensorEnergy.AllSplitBound T M)
    [Nonempty (Frontier.Incoming (absorb key src dst first last q) (key v))]
    [Nonempty (Frontier.Outgoing (emit key src dst first last q) (key v))] :
    TensorEnergy.Bound (incidentMatrix key src dst hkey hne first last v q d T) (M^2) :=
  hT _ _ (incidentSplit key src dst hkey hne first last v q)
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical
open TensorEnergy

variable {V U : Type*} [Fintype V] [Fintype U] [Nonempty V]
local instance edgeDecEqTG (q : ℕ) : DecidableEq (Edge (U:=U) q) := Classical.decEq _
local instance finDecEqTG (d : ℕ) : DecidableEq (Fin d) := Classical.decEq _

theorem tensor_graph_bound (e : V ≃ Fin (Fintype.card V)) (src dst : U → V)
    (hne : ∀u,src u≠dst u) (first last : V) (q d : ℕ)
    (hsplit : ∀v,
      Nonempty (Frontier.Incoming (absorb (fun v => (e v).val) src dst first last q) (e v).val) ∧
      Nonempty (Frontier.Outgoing (emit (fun v => (e v).val) src dst first last q) (e v).val))
    (T : ∀v,({t : Edge (U:=U) q // IncidentAt src dst first last v q t} → Fin d) → ℝ)
    (M : V → ℝ) (hM : ∀v,0≤M v) (hT : ∀v,AllSplitBound (T v) (M v)) :
    |∑c : U ⊕ Fin q → Fin d, ∏v,T v (fun t => duplicate c t.val)|≤
      (d:ℝ)^q*(∏v,M v) := by
  let key : V → ℕ := fun v => (e v).val
  have hkey : Function.Injective key := Fin.val_injective.comp e.injective
  let D : ℕ → Type _ := fun k =>
    (Frontier.Outgoing (emit key src dst first last q) k → Fin d) →
      (Frontier.Incoming (absorb key src dst first last q) k → Fin d) → ℝ
  let a : ∀v,D (e v).val := fun v =>
    incidentMatrix key src dst hkey hne first last v q d (T v)
  let A : ∀k,D k := rankExtend e (fun _ _ _ => 0) a
  have hAt (v : V) : A (e v).val=a v := rankExtend_at e _ a v
  have hA (v : V) : Bound (A (e v).val) ((M v)^2) := by
    rw [hAt]
    let := (hsplit v).1
    let := (hsplit v).2
    exact incidentMatrix_bound key src dst hkey hne first last v q d (T v) (M v) (hT v)
  have hb := ranked_coordinate_bound e src dst hne first last q d A M hM hA
  have heq (v : V) (c : U ⊕ Fin q → Fin d) :
      A (e v).val (fun t => duplicate c t.val) (fun t => duplicate c t.val)=
        T v (fun t => duplicate c t.val) := by
    rw [hAt]
    exact incidentMatrix_global key src dst hkey hne first last v q d (T v) (duplicate c)
  convert hb using 1
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.prod_congr rfl
  intro v _
  exact (heq v c).symm
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open MeasureTheory TensorEnergy
open scoped BigOperators Classical ENNReal

variable {Ω P H U : Type*} [MeasurableSpace Ω] [Fintype P] [Fintype H] [Fintype U]
    [Nonempty P]
local instance edgeDecEqTGI (q : ℕ) : DecidableEq (Edge (U:=U) q) := Classical.decEq _
local instance finDecEqTGI (d : ℕ) : DecidableEq (Fin d) := Classical.decEq _

theorem tensor_graph_integral_bound (μ : Measure Ω)
    (e : P ⊕ H ≃ Fin (Fintype.card (P ⊕ H))) (src dst : U → P ⊕ H)
    (hne : ∀u,src u≠dst u) (first last : P ⊕ H) (q d : ℕ)
    (hsplit : ∀v,
      Nonempty (Frontier.Incoming (absorb (fun v => (e v).val) src dst first last q) (e v).val) ∧
      Nonempty (Frontier.Outgoing (emit (fun v => (e v).val) src dst first last q) (e v).val))
    (T : Ω → ∀v,({t : Edge (U:=U) q // IncidentAt src dst first last v q t} → Fin d) → ℝ)
    (M : P ⊕ H → Ω → ℝ) (hM : ∀v x,0≤M v x)
    (hT : ∀v x,AllSplitBound (T x v) (M v x))
    (B : P → ℝ≥0∞) (C : H → ℝ≥0∞)
    (hMp : ∀i,AEMeasurable (fun x => ENNReal.ofReal (M (Sum.inl i) x)) μ)
    (hp : ∀i,(∫⁻x,ENNReal.ofReal (M (Sum.inl i) x)^(Fintype.card P) ∂μ)≤B i^(Fintype.card P))
    (hh : ∀h x,ENNReal.ofReal (M (Sum.inr h) x)≤C h) (hC : ∀h,C h≠⊤) :
    (∫⁻x,ENNReal.ofReal |∑c : U ⊕ Fin q → Fin d,
      ∏v,T x v (fun t => duplicate c t.val)| ∂μ)≤
      (d:ℝ≥0∞)^q*((∏i,B i)*(∏h,C h)) := by
  have hpw (x : Ω) : ENNReal.ofReal |∑c : U ⊕ Fin q → Fin d,
        ∏v,T x v (fun t => duplicate c t.val)|≤
      (d:ℝ≥0∞)^q*((∏i,ENNReal.ofReal (M (Sum.inl i) x))*
        (∏h,ENNReal.ofReal (M (Sum.inr h) x))) := by
    have hb := ENNReal.ofReal_le_ofReal (tensor_graph_bound e src dst hne first last q d
      hsplit (T x) (fun v => M v x) (fun v => hM v x) (fun v => hT v x))
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_natCast,ENNReal.ofReal_prod_of_nonneg (fun v _ => hM v x),
      Fintype.prod_sum_type] at hb
    exact hb
  calc
    _ ≤ ∫⁻x,(d:ℝ≥0∞)^q*((∏i,ENNReal.ofReal (M (Sum.inl i) x))*
        (∏h,ENNReal.ofReal (M (Sum.inr h) x))) ∂μ := lintegral_mono hpw
    _ = (d:ℝ≥0∞)^q*(∫⁻x,(∏i,ENNReal.ofReal (M (Sum.inl i) x))*
        (∏h,ENNReal.ofReal (M (Sum.inr h) x)) ∂μ) :=
      lintegral_const_mul' _ _ (by finiteness)
    _ ≤ _ := mul_le_mul' le_rfl
      (NetworkMoments.lintegral_primary_auxiliary_le hMp hp hh hC)
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory GraphSchedule TensorEnergy
open scoped BigOperators Classical ENNReal

variable {n : ℕ} {S : State (Fin (n+1))}
local instance edgeDecEqAT (β : Fin n → ℕ) (q : ℕ) :
    DecidableEq (Edge (U:=InternalEdge β) q) := Classical.decEq _
local instance cutDecEqAT (β : Fin n → ℕ) (q : ℕ) :
    DecidableEq (InternalEdge β ⊕ Fin q) :=
  @instDecidableEqSum _ _ (Classical.decEq _) (Classical.decEq _)

theorem actual_tensor_contraction_bound
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (hβ : ∀k,0<β k) (q d : ℕ) (hq : 0<q)
    (T : ∀v : TargetVertex S,
      ({t : Edge (U:=InternalEdge β) q //
        IncidentAt (V:=TargetVertex S) (edgeSource (S:=S) β) (edgeTarget (S:=S) hS β)
          (Sum.inl 0) (Sum.inl (Fin.last n)) v q t} → Fin d) → ℝ)
    (M : TargetVertex S → ℝ) (hM : ∀v,0≤M v) (hT : ∀v,AllSplitBound (T v) (M v)) :
    |∑c : InternalEdge β ⊕ Fin q → Fin d, ∏v,T v (fun t => duplicate c t.val)|≤
      (d:ℝ)^q*(∏v,M v) := by
  obtain ⟨e,he⟩ := actual_ranked_schedule hS β hβ
  exact tensor_graph_bound e (edgeSource (S:=S) β) (edgeTarget (S:=S) hS β)
    (internal_source_ne hS β) (Sum.inl 0) (Sum.inl (Fin.last n)) q d (he q hq) T M hM hT

theorem actual_tensor_integral_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (hβ : ∀k,0<β k) (q d : ℕ) (hq : 0<q)
    (T : Ω → ∀v : TargetVertex S,
      ({t : Edge (U:=InternalEdge β) q //
        IncidentAt (V:=TargetVertex S) (edgeSource (S:=S) β) (edgeTarget (S:=S) hS β)
          (Sum.inl 0) (Sum.inl (Fin.last n)) v q t} → Fin d) → ℝ)
    (M : TargetVertex S → Ω → ℝ) (hM : ∀v x,0≤M v x)
    (hT : ∀v x,AllSplitBound (T x v) (M v x))
    (B : Fin (n+1) → ℝ≥0∞) (C : S.hessians → ℝ≥0∞)
    (hMp : ∀i,AEMeasurable (fun x => ENNReal.ofReal (M (Sum.inl i) x)) μ)
    (hp : ∀i,(∫⁻x,ENNReal.ofReal (M (Sum.inl i) x)^(n+1) ∂μ)≤B i^(n+1))
    (hh : ∀h x,ENNReal.ofReal (M (Sum.inr h) x)≤C h) (hC : ∀h,C h≠⊤) :
    (∫⁻x,ENNReal.ofReal |∑c : InternalEdge β ⊕ Fin q → Fin d,
      ∏v,T x v (fun t => duplicate c t.val)| ∂μ)≤
      (d:ℝ≥0∞)^q*((∏i,B i)*(∏h,C h)) := by
  obtain ⟨e,he⟩ := actual_ranked_schedule hS β hβ
  exact tensor_graph_integral_bound μ e (edgeSource (S:=S) β) (edgeTarget (S:=S) hS β)
    (internal_source_ne hS β) (Sum.inl 0) (Sum.inl (Fin.last n)) q d (he q hq) T M hM hT
    B C hMp (by simpa only [Fintype.card_fin] using hp) hh hC
end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
