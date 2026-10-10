import Mathlib
import OAI.Combinatorics.RamseyFive.Trees.HistoryPrivateStream
import OAI.Combinatorics.RamseyFive.Entropy.MarkedActualBudget
import OAI.Combinatorics.RamseyFive.Geometry.RectangleTransport

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {Ω κ α β I B A T : Type} [Fintype Ω] [Fintype κ] [Fintype α] [Fintype β]
  [Fintype I] [Fintype B] [Fintype A] [Fintype T] [Nonempty A]
local instance wpIDE : DecidableEq ((B×A)⊕T) := Classical.decEq _
omit [Nonempty A] in
@[simp] lemma blockActive_univ : blockActive (T:=T) (fun _ : B=>(Finset.univ : Finset A))=Finset.univ := by
  ext i
  cases i <;> simp [blockActive]
lemma fixedOutside_univ (p : Law (I→β)) : FixedOutside p Finset.univ := by
  intro i hi
  exact False.elim (hi (Finset.mem_univ i))
lemma mean_fiber_entropy_injective (p : Law Ω) (ctx : Ω→κ) (x : Ω→α) (f : α→β)
    (hf : Function.Injective f) (F : ℝ→ℝ) :
    mean (first (pair p ctx (fun z=>f (x z)))) (fun c=>F (entropy (fiber (pair p ctx (fun z=>f (x z))) c)))=
    mean (first (pair p ctx x)) (fun c=>F (entropy (fiber (pair p ctx x) c))) := by
  simp only [first_pair]
  apply mean_congr_pos
  intro c hc
  rw [fiber_pair_map p ctx x f c hc,entropy_map_injective _ _ hf]
end
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ] [Fintype α] {N w n : ℕ} [Nonempty (Fin n)]
  {admissible : (Fin N→α)→Prop}
local instance wpBDE : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance wpTDE : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
local instance wpSDE : DecidableEq (Slots w n) := Classical.decEq _
omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Nonempty (Fin n)] in
lemma windowTuple_injective : Function.Injective (fun x : Fin (w*(4*n))→FlagPair K V=>fun i : Slots w n=>x (slotEmbedding i)) := by
  intro x y h
  funext i
  obtain ⟨j,rfl⟩:=(slotEquiv w n).surjective i
  exact congrFun h j

omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin n)] in
lemma window_posterior_domains (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (D : κ→Fin (w*(4*n))→Finset (FlagPair K V))
    (hD : ∀z,0<S.law z→∀i,S.tuple z i∈D (ctx z) i) :
    ∀c,0<first (pair S.law ctx (windowTuple S)) c→
      InDomains (fiber (pair S.law ctx (windowTuple S)) c) (fun i=>D c (slotEmbedding i)) := by
  exact pair_fiber_domains S.law ctx (windowTuple S) _ (fun z hz i=>hD z hz (slotEmbedding i))

omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin n)] in
lemma window_posterior_consistent (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (hcons : ∀z,0<S.law z→TupleConsistent (S.tuple z)) :
    ∀c,0<first (pair S.law ctx (windowTuple S)) c→∀x,0<fiber (pair S.law ctx (windowTuple S)) c x→
      ∀i j,slotEmbedding i<slotEmbedding j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2 := by
  apply pair_fiber_pred
  intro z hz i j hij
  exact hcons z hz _ _ hij
omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin n)] in
lemma window_posterior_incident (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (hinc : ∀z,0<S.law z→TupleIncident (S.tuple z)) :
    ∀c,0<first (pair S.law ctx (windowTuple S)) c→∀x,0<fiber (pair S.law ctx (windowTuple S)) c x→
      ∀i,Incident (x i).1 (x i).2 := by
  apply pair_fiber_pred
  intro z hz i
  exact hinc z hz _
omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin n)] in
lemma window_posterior_occupancy (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (M : ℝ) (hocc : ∀z,0<S.law z→∀W : Submodule K (Dual K V),
      (∑i,if InRectangle W (S.tuple z i).1.rep (S.tuple z i).2.rep then (1:ℝ) else 0)≤M) :
    ∀c,0<first (pair S.law ctx (windowTuple S)) c→∀x,0<fiber (pair S.law ctx (windowTuple S)) c x→
      ∀W : Submodule K (Dual K V),
      (∑i,if InRectangle W (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M := by
  apply pair_fiber_pred
  intro z hz
  exact occupancy_reindex (S.tuple z) slotEmbedding slotEmbedding.injective M (hocc z hz)
omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin n)] in
lemma window_posterior_deficit (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (J : ℝ) :
    mean (first (pair S.law ctx (windowTuple S))) (fun c=>activeDeficit
      (fiber (pair S.law ctx (windowTuple S)) c) (blockActive (fun _=>Finset.univ)) J)=
    mean (first (pair S.law ctx S.tuple)) (fun c=>(w*(4*n):ℝ)*J-entropy (fiber (pair S.law ctx S.tuple) c)) := by
  simp only [blockActive_univ,activeDeficit,Finset.card_univ,card_slots,Nat.cast_mul,Nat.cast_ofNat]
  exact mean_fiber_entropy_injective S.law ctx S.tuple _ windowTuple_injective _
end
end SharpRamseyFive.SelectedTuple

end OAI
