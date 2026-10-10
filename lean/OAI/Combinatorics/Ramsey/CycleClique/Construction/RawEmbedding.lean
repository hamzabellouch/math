import OAI.Combinatorics.Ramsey.CycleClique.Construction.AssignedDeletion
import OAI.Combinatorics.Ramsey.CycleClique.Construction.NormalizedIncident

namespace OAI

/-! Transport a finite chain certificate through an injective graph embedding. -/

namespace CycleClique.Construction
variable {W V : Type*} {H : SimpleGraph W} {G : SimpleGraph V}
variable {Q₀ : Finset W} {Q : Finset V} {f : W → V}

theorem chainCliqueCount_map (hQ : ∀ v, f v ∈ Q ↔ v ∈ Q₀) (l : List W) :
    chainCliqueCount Q (l.map f) = chainCliqueCount Q₀ l := by
  classical
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, chainCliqueCount_cons, hQ, ih]

theorem chainOutsideCount_map (hQ : ∀ v, f v ∈ Q ↔ v ∈ Q₀) (l : List W) :
    chainOutsideCount Q (l.map f) = chainOutsideCount Q₀ l := by
  classical
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [chainOutsideCount, List.map_cons, List.filter_cons] at ih ⊢
    by_cases hx : x ∈ Q₀ <;> simp [hQ, hx] at ih ⊢ <;> omega

namespace RawPathSystem

def embed (S : RawPathSystem H Q₀) (f : W → V) (hf : Function.Injective f)
    (hQ : ∀ v, f v ∈ Q ↔ v ∈ Q₀)
    (hG : ∀ {x y}, H.Adj x y → G.Adj (f x) (f y)) : RawPathSystem G Q where
  chains := S.chains.map (List.map f)
  paths := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    exact ⟨(S.paths r hr).1.map hf, List.isChain_map_of_isChain f (fun _ _ h => hG h) (S.paths r hr).2⟩
  disjoint := by
    apply (List.nodup_flatten.mp ?_).2
    simpa only [← List.map_flatten] using S.flatten_nodup.map hf
  endpoints := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    constructor
    · intro v hv
      rw [List.head?_map] at hv
      obtain ⟨w, hw, rfl⟩ := Option.mem_map.mp hv
      exact (hQ w).mpr ((S.endpoints r hr).1 w hw)
    · intro v hv
      rw [List.getLast?_map] at hv
      obtain ⟨w, hw, rfl⟩ := Option.mem_map.mp hv
      exact (hQ w).mpr ((S.endpoints r hr).2 w hw)
  no_clique_steps := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    exact List.isChain_map_of_isChain f (fun _ _ hn hh =>
      hn ⟨(hQ _).mp hh.1, (hQ _).mp hh.2⟩) (S.no_clique_steps r hr)

@[simp] theorem embed_amount (S : RawPathSystem H Q₀) (hf : Function.Injective f)
    (hQ : ∀ v, f v ∈ Q ↔ v ∈ Q₀)
    (hG : ∀ {x y}, H.Adj x y → G.Adj (f x) (f y)) :
    (S.embed f hf hQ hG).amount = S.amount := by
  rw [amount_eq_outside_count, amount_eq_outside_count]
  change chainOutsideCount Q ((S.chains.map (List.map f)).flatten) = _
  rw [← List.map_flatten]
  exact chainOutsideCount_map hQ _

@[simp] theorem embed_assignedCount (S : RawPathSystem H Q₀) (hf : Function.Injective f)
    (hQ : ∀ v, f v ∈ Q ↔ v ∈ Q₀)
    (hG : ∀ {x y}, H.Adj x y → G.Adj (f x) (f y)) :
    (S.embed f hf hQ hG).assignedCount = S.assignedCount := by
  change rawAssignedCount Q (S.chains.map (List.map f)) = rawAssignedCount Q₀ S.chains
  simp only [rawAssignedCount, List.map_map, Function.comp_def, chainCliqueCount_map hQ]

@[simp] theorem embed_normalize_incident (S : RawPathSystem H Q₀)
    (hf : Function.Injective f) (hQ : ∀ v, f v ∈ Q ↔ v ∈ Q₀)
    (hG : ∀ {x y}, H.Adj x y → G.Adj (f x) (f y)) :
    (S.embed f hf hQ hG).normalize.incident = S.normalize.incident := by
  rw [normalize_incident, normalize_incident]
  change ((S.chains.map (List.map f)).map (activeCliqueCount Q)).sum = _
  simp only [List.map_map, Function.comp_def, activeCliqueCount, List.length_map,
    chainCliqueCount_map hQ]
  rfl

theorem normalize_incident_le (S : RawPathSystem G Q) :
    S.normalize.incident ≤ chainCliqueCount Q S.chains.flatten := by
  rw [normalize_incident, chainCliqueCount_flatten]
  induction S.chains with
  | nil => simp
  | cons l C ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (by unfold activeCliqueCount; split_ifs <;> omega) ih

end RawPathSystem
end CycleClique.Construction

end OAI
