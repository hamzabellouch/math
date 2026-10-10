import OAI.MeasureTheory.DyadicAvoidance.FiniteTableModel
import OAI.MeasureTheory.DyadicAvoidance.OrderedRouting
import OAI.MeasureTheory.DyadicAvoidance.RoutingPath

namespace OAI

universe u_ι u_X u_Y

noncomputable section

namespace Problem310.CenterRouteExposure
open Problem310.RoutingPath

/-- Equality of all node decisions at two samples identifies their entire routes,
even when the two decision functions have different parameter spaces. -/
theorem routeFrom_congr_at {ι : Type u_ι} {X : Type u_X} {Y : Type u_Y}
    (chooseX : List ι → X → ι) (chooseY : List ι → Y → ι)
    (x : X) (y : Y) (h : ∀ P, chooseX P x = chooseY P y)
    (n : ℕ) (P : List ι) :
    routeFrom chooseX n P x = routeFrom chooseY n P y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [routeFrom_succ, ih, h]

/-- The decision at every stage is also fixed by the node-decision data. -/
theorem route_decision_congr_at {ι : Type u_ι} {X : Type u_X} {Y : Type u_Y}
    (chooseX : List ι → X → ι) (chooseY : List ι → Y → ι)
    (x : X) (y : Y) (h : ∀ P, chooseX P x = chooseY P y)
    (n : ℕ) (P : List ι) :
    chooseX (routeFrom chooseX n P x) x =
      chooseY (routeFrom chooseY n P y) y := by
  rw [routeFrom_congr_at chooseX chooseY x y h]
  exact h _

/-- The event that the first default occurs at a specified stage. -/
def FirstDefaultAt {ι : Type u_ι} {X : Type u_X} (choose : List ι → X → ι)
    (default : ι) (d k : ℕ) (P : List ι) (x : X) : Prop :=
  k < d ∧ choose (routeFrom choose k P x) x = default ∧
    ∀ l < k, choose (routeFrom choose l P x) x ≠ default

/-- Full center exposure fixes whether a given stage is the first default. -/
theorem firstDefaultAt_congr {ι : Type u_ι} {X : Type u_X} {Y : Type u_Y}
    (chooseX : List ι → X → ι) (chooseY : List ι → Y → ι)
    (x : X) (y : Y) (h : ∀ P, chooseX P x = chooseY P y)
    (default : ι) (d k : ℕ) (P : List ι) :
    FirstDefaultAt chooseX default d k P x ↔
      FirstDefaultAt chooseY default d k P y := by
  simp only [FirstDefaultAt, route_decision_congr_at chooseX chooseY x y h]

open Problem310.FiniteTableModel Problem310.OrderedRouting

/-- The full deterministic center exposure: one bit for every selector table. -/
def centerExposure {M d : ℕ} (b : Node M d → Fin M → ℕ) (x : ℝ)
    (ω : SelectorTable b) : Node M d × Fin M → Bool :=
  fun e => ω (selectorAddress b e.1 e.2 x)

/-- Complete any exposure assignment by setting all unexposed bits to false.
This is only a deterministic representative of an atom, not a probability law. -/
def centerCompletion {M d : ℕ} (b : Node M d → Fin M → ℕ) (x : ℝ)
    (ξ : Node M d × Fin M → Bool) : SelectorTable b :=
  Function.extend (fun e : Node M d × Fin M => selectorAddress b e.1 e.2 x)
    ξ (fun _ => false)

@[simp] theorem centerExposure_completion {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ξ : Node M d × Fin M → Bool) :
    centerExposure b x (centerCompletion b x ξ) = ξ := by
  funext e
  exact (center_selectorAddress_injective b x).extend_apply ξ (fun _ => false) e

/-- Every exposure assignment has a representative selector table. -/
theorem centerExposure_surjective {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) :
    Function.Surjective (centerExposure b x) :=
  fun ξ => ⟨centerCompletion b x ξ, centerExposure_completion b x ξ⟩

/-- Even the extended selector function is fixed by center exposure: invalid
nodes use the same constant false value in both outcomes. -/
theorem selectorValue_eq_of_centerExposure_eq {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) {ω ω' : SelectorTable b}
    (h : centerExposure b x ω = centerExposure b x ω')
    (P : List (Child M)) (i : Fin M) :
    selectorValue b ω P i x = selectorValue b ω' P i x := by
  by_cases hP : P.length < d
  · have he := congrFun h (⟨P, hP⟩, i)
    simpa only [centerExposure, selectorValue, dite_eq_left hP] using he
  · simp only [selectorValue, dite_eq_right hP]

/-- The actual first-success choice made by a selector table at a fixed center. -/
def centerChoice {M d : ℕ} (b : Node M d → Fin M → ℕ) (x : ℝ)
    (P : List (Child M)) (ω : SelectorTable b) : Child M :=
  chooseChild (fun i => selectorValue b ω P i x)

theorem centerChoice_eq_of_centerExposure_eq {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) {ω ω' : SelectorTable b}
    (h : centerExposure b x ω = centerExposure b x ω') (P : List (Child M)) :
    centerChoice b x P ω = centerChoice b x P ω' := by
  exact chooseChild_congr _ _ (selectorValue_eq_of_centerExposure_eq b x h P)

/-- Every center route is constant on each full exposure atom. -/
theorem centerRoute_eq_of_centerExposure_eq {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) {ω ω' : SelectorTable b}
    (h : centerExposure b x ω = centerExposure b x ω')
    (n : ℕ) (P : List (Child M)) :
    routeFrom (centerChoice b x) n P ω = routeFrom (centerChoice b x) n P ω' :=
  routeFrom_congr_at _ _ ω ω' (centerChoice_eq_of_centerExposure_eq b x h) n P

/-- The decision made at every center-route stage is constant on the atom. -/
theorem centerRoute_decision_eq_of_centerExposure_eq {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) {ω ω' : SelectorTable b}
    (h : centerExposure b x ω = centerExposure b x ω')
    (n : ℕ) (P : List (Child M)) :
    centerChoice b x (routeFrom (centerChoice b x) n P ω) ω =
      centerChoice b x (routeFrom (centerChoice b x) n P ω') ω' :=
  route_decision_congr_at _ _ ω ω' (centerChoice_eq_of_centerExposure_eq b x h) n P

/-- First-default events can be defined entirely on the finite exposure space. -/
theorem firstDefaultAt_centerCompletion {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ω : SelectorTable b)
    (k : ℕ) (P : List (Child M)) :
    FirstDefaultAt (centerChoice b x) (Fin.last M) d k P ω ↔
      FirstDefaultAt (centerChoice b x) (Fin.last M) d k P
        (centerCompletion b x (centerExposure b x ω)) := by
  apply firstDefaultAt_congr
  apply centerChoice_eq_of_centerExposure_eq
  simp

/-- A good exposure atom has one fixed first-default stage and node, uniformly
for every completion of all unexposed selector coordinates. -/
theorem firstDefaultData_on_atom {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ξ : Node M d × Fin M → Bool)
    (hgood : ∃ k < d, centerChoice b x
      (routeFrom (centerChoice b x) k [] (centerCompletion b x ξ))
        (centerCompletion b x ξ) = Fin.last M) :
    ∃ k : ℕ, ∃ U : List (Child M), k < d ∧
      ∀ ω : SelectorTable b, centerExposure b x ω = ξ →
        routeFrom (centerChoice b x) k [] ω = U ∧
        FirstDefaultAt (centerChoice b x) (Fin.last M) d k [] ω := by
  obtain ⟨k, hk, hdefault, hprior⟩ :=
    exists_first_default (centerChoice b x) d [] (centerCompletion b x ξ) (Fin.last M) hgood
  refine ⟨k, routeFrom (centerChoice b x) k [] (centerCompletion b x ξ), hk, ?_⟩
  intro ω hω
  have he : centerExposure b x ω = centerExposure b x (centerCompletion b x ξ) := by
    simpa only [centerExposure_completion] using hω
  refine ⟨centerRoute_eq_of_centerExposure_eq b x he k [], ?_⟩
  apply (firstDefaultAt_congr _ _ ω (centerCompletion b x ξ)
    (centerChoice_eq_of_centerExposure_eq b x he) (Fin.last M) d k []).mpr
  exact ⟨hk, hdefault, hprior⟩

/-- Version of the atomwise first-default witness with the actual bounded node
and stage types required to index the finite selector tables and window data. -/
theorem firstDefaultNode_on_atom {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ξ : Node M d × Fin M → Bool)
    (hgood : ∃ k < d, centerChoice b x
      (routeFrom (centerChoice b x) k [] (centerCompletion b x ξ))
        (centerCompletion b x ξ) = Fin.last M) :
    ∃ k : Fin d, ∃ U : Node M d, U.val.length = k.val ∧
      ∀ ω : SelectorTable b, centerExposure b x ω = ξ →
        routeFrom (centerChoice b x) k.val [] ω = U.val ∧
        FirstDefaultAt (centerChoice b x) (Fin.last M) d k.val [] ω := by
  obtain ⟨k, U, hk, hU⟩ := firstDefaultData_on_atom b x ξ hgood
  have hroute := (hU (centerCompletion b x ξ) (centerExposure_completion b x ξ)).1
  have hlen : U.length = k := by
    rw [← hroute, length_routeFrom]
    simp
  exact ⟨⟨k, hk⟩, ⟨U, by simpa only [hlen] using hk⟩, hlen, hU⟩

/-- The good atoms are those whose (equivalently, every) center route has a default. -/
def GoodExposure {M d : ℕ} (b : Node M d → Fin M → ℕ) (x : ℝ)
    (ξ : Node M d × Fin M → Bool) : Prop :=
  ∃ k < d, centerChoice b x
    (routeFrom (centerChoice b x) k [] (centerCompletion b x ξ))
      (centerCompletion b x ξ) = Fin.last M

/-- The finite-atom good predicate is exactly the actual center-path default event. -/
theorem goodExposure_centerExposure_iff {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ω : SelectorTable b) :
    GoodExposure b x (centerExposure b x ω) ↔
      ∃ k < d, centerChoice b x (routeFrom (centerChoice b x) k [] ω) ω = Fin.last M := by
  have he : centerExposure b x ω = centerExposure b x
      (centerCompletion b x (centerExposure b x ω)) := by simp
  constructor
  · rintro ⟨k, hk, hd⟩
    exact ⟨k, hk, (centerRoute_decision_eq_of_centerExposure_eq b x he k []).trans hd⟩
  · rintro ⟨k, hk, hd⟩
    exact ⟨k, hk, (centerRoute_decision_eq_of_centerExposure_eq b x he k []).symm.trans hd⟩

/-- This is the event identity used to transport the no-default probability
estimate to the bad atoms of the full center-exposure partition. -/
theorem badExposure_centerExposure_iff {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ω : SelectorTable b) :
    ¬ GoodExposure b x (centerExposure b x ω) ↔
      ∀ k < d, centerChoice b x (routeFrom (centerChoice b x) k [] ω) ω ≠ Fin.last M := by
  rw [goodExposure_centerExposure_iff]
  simp only [not_exists, not_and, ne_eq]

end Problem310.CenterRouteExposure

end

end OAI
