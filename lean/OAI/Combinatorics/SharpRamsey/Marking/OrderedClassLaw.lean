import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.MarkingGeometricClass

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω Γ α β : Type*} [Fintype Ω] [Fintype Γ] [Fintype α] [Fintype β]

omit [Fintype Γ] in
lemma Law.map_congr_support (p : Law Ω) (f g : Ω→α)
    (h : ∀ x,p.mass x≠0→f x=g x) : p.map f=p.map g := by
  ext y
  change (∑ x with f x=y,p.mass x)=(∑ x with g x=y,p.mass x)
  simp only [sum_filter]
  apply sum_congr rfl
  intro x _
  by_cases hx : p.mass x=0
  · simp only [hx,ite_self]
  · rw [h x hx]

omit [Fintype Ω] [Fintype Γ] [Fintype α] [Fintype β] in

def chosenOrder {N m : ℕ} (S : Γ→Finset (Fin N)) (hm : m≤N) (z : Γ) : Fin m ↪o Fin N :=
  if hs : (S z).card=m then (S z).orderEmbOfFin hs else Fin.castLEOrderEmb hm

omit [Fintype Ω] [Fintype Γ] [Fintype α] [Fintype β] in
lemma chosenOrder_mem {N m : ℕ} (S : Γ→Finset (Fin N)) (hm : m≤N) (z : Γ)
    (hs : (S z).card=m) (i : Fin m) : chosenOrder S hm z i∈S z := by
  rw [chosenOrder,dite_eq_left hs]
  exact orderEmbOfFin_mem _ _ _

omit [Fintype Ω] [Fintype Γ] [Fintype α] [Fintype β] in
def orderedTuple {N m : ℕ} (S : Γ→Finset (Fin N)) (hm : m≤N)
    (θ : Ω→Γ) (F : Ω→Fin N→α) : Ω→Fin m→α :=
  fun x i=>F x (chosenOrder S hm (θ x) i)

omit [Fintype β] in

theorem ordered_cond_entropy {N m : ℕ} (p : Law Ω) (θ : Ω→Γ) (F : Ω→Fin N→α)
    (S : Γ→Finset (Fin N)) (hm : m≤N) (z : Γ)
    (hz : (p.map θ).mass z≠0) (hs : (S z).card=m) :
    entropy ((p.cond θ z).map (orderedTuple S hm θ F))=
      entropy (((p.cond θ z).map F).restrict (S z)) := by
  let e := (S z).orderIsoOfFin hs
  let relabel : (S z→α)→(Fin m→α) := fun f i=>f (e i)
  have hi : Function.Injective relabel := by
    intro f g h
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    exact congrFun h j
  have he : (p.cond θ z).map (orderedTuple S hm θ F)=
      (((p.cond θ z).map F).restrict (S z)).map relabel := by
    rw [Law.restrict,Law.map_map,Law.map_map]
    apply Law.map_congr_support
    intro x hx
    have hxθ := (p.cond_support θ z hz x hx).2
    funext i
    simp only [orderedTuple,hxθ,chosenOrder,dite_eq_left hs,Function.comp_apply,relabel,e]
    rfl
  rw [he]
  exact entropy_map_eq_of_injective _ relabel hi

omit [Fintype β] in

theorem ordered_deficit {N m : ℕ} (p : Law Ω) (θ : Ω→Γ) (F : Ω→Fin N→α)
    (S : Γ→Finset (Fin N)) (hm : m≤N)
    (hs : ∀ z,(p.map θ).mass z≠0→(S z).card=m) (J : ℝ) :
    (∑ z,(p.map θ).mass z*((m:ℝ)*J-
      entropy ((p.cond θ z).map (orderedTuple S hm θ F))))=
      selectedDeficit p θ F S J := by
  unfold selectedDeficit
  apply sum_congr rfl
  intro z _
  by_cases hz : (p.map θ).mass z=0
  · simp only [hz,zero_mul]
  · rw [ordered_cond_entropy p θ F S hm z hz (hs z hz),hs z hz]
    congr!

omit [Fintype α] [Fintype β] in

lemma ordered_support {N m : ℕ} (p : Law Ω) (θ : Ω→Γ) (F : Ω→Fin N→α)
    (S : Γ→Finset (Fin N)) (hm : m≤N) (D : Γ→Fin N→Finset α)
    (hs : ∀ z,(p.map θ).mass z≠0→(S z).card=m)
    (hD : ∀ x,p.mass x≠0→∀ i∈S (θ x),F x i∈D (θ x) i)
    (x : Ω) (hx : p.mass x≠0) (i : Fin m) :
    orderedTuple S hm θ F x i∈D (θ x) (chosenOrder S hm (θ x) i) := by
  apply hD x hx
  exact chosenOrder_mem S hm (θ x) (hs _ (ne_of_gt
    (lt_of_lt_of_le (lt_of_le_of_ne (p.nonneg x) (Ne.symm hx)) (p.le_map θ x)))) i

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Marking
open Finset
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]

omit [FiniteDimensional K V] in

lemma scanConsistent_ordered {N m : ℕ}
    (F : Fin N→ProjectivePair (K:=K) (V:=V))
    (hF : ScanConsistent ((List.ofFn F).map toScan)) (e : Fin m ↪o Fin N) :
    ScanConsistent ((List.ofFn (fun i=>F (e i))).map toScan) := by
  unfold ScanConsistent at hF ⊢
  rw [List.map_ofFn] at hF ⊢
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact List.pairwise_ofFn.mp hF (e.strictMono hij)

end
end SharpLogRamsey.Marking

end

end OAI
