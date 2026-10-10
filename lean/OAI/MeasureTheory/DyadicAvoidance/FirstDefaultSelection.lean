import OAI.MeasureTheory.DyadicAvoidance.FirstDefault
import OAI.MeasureTheory.DyadicAvoidance.OrderedRouting
import OAI.MeasureTheory.DyadicAvoidance.RoutingPath

namespace OAI

universe u_Ω u_ι u_X u_Y

noncomputable section

namespace Problem310.FirstDefault

/-- A path cylinder is exactly the event that first-success routing selects
its prescribed child at each of its prescribed nodes. -/
theorem cylinder_iff_chooseChild {M d : ℕ} {Ω : Type u_Ω}
    (S : Address M → Ω → Bool) (f : Path M d) (ω : Ω) :
    ω ∈ cylinder S f ↔ ∀ k : Fin d,
      OrderedRouting.chooseChild (fun j => S (pathPrefix f k, j) ω) = (f k).castSucc := by
  constructor
  · intro h k
    apply (OrderedRouting.chooseChild_eq_nondefault_iff _ _).mpr
    constructor
    · have hi := h ⟨k, ⟨(f k).val, Nat.lt_succ_self _⟩⟩
      simpa only [address, requiredBit, decide_true] using hi
    · intro j hj
      have hi := h ⟨k, ⟨j.val, lt_trans hj (Nat.lt_succ_self _)⟩⟩
      have hne : j.val ≠ (f k).val := Nat.ne_of_lt hj
      simpa only [address, requiredBit, hne, decide_false] using hi
  · intro h i
    obtain ⟨k, j⟩ := i
    obtain ⟨hsuccess, hprev⟩ :=
      (OrderedRouting.chooseChild_eq_nondefault_iff _ _).mp (h k)
    by_cases heq : j.val = (f k).val
    · have ha : address f ⟨k, j⟩ = (pathPrefix f k, f k) := by
        apply Prod.ext
        · rfl
        · exact Fin.ext heq
      change S (address f ⟨k, j⟩) ω = requiredBit f ⟨k, j⟩
      simpa only [ha, requiredBit, heq, decide_true] using hsuccess
    · have hlt : j.val < (f k).val := by omega
      have hj := hprev ⟨j.val, lt_trans hlt (f k).isLt⟩ hlt
      change S (address f ⟨k, j⟩) ω = requiredBit f ⟨k, j⟩
      simpa only [address, requiredBit, heq, decide_false] using hj

/-- Canonical child choice from a family of selector bits at tree addresses. -/
def centerChoice {M : ℕ} {Ω : Type u_Ω} (S : Address M → Ω → Bool)
    (P : List (Fin (M + 1))) (ω : Ω) : Fin (M + 1) :=
  OrderedRouting.chooseChild (fun j => S (P, j) ω)

/-- The actual routed center avoids the default exactly on the finite union
of the path cylinders used by the exact first-default probability law. -/
theorem noDefault_iff_mem_cylinders {M d : ℕ} {Ω : Type u_Ω}
    (S : Address M → Ω → Bool) (ω : Ω) :
    (∀ k < d, centerChoice S (RoutingPath.routeFrom (centerChoice S) k [] ω) ω ≠
      Fin.last M) ↔ ω ∈ ⋃ f : Path M d, cylinder S f := by
  rw [RoutingPath.noDefault_iff_exists_choices]
  simp only [Set.mem_iUnion, cylinder_iff_chooseChild]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, fun k => ?_⟩
    simpa only [centerChoice, pathPrefix_eq_take_ofFn] using hf k.val k.isLt
  · rintro ⟨f, hf⟩
    refine ⟨f, fun k hk => ?_⟩
    simpa only [centerChoice, pathPrefix_eq_take_ofFn] using hf ⟨k, hk⟩

/-- The equality is also available as a set rewrite for probability measures. -/
theorem noDefault_event_eq_cylinders {M d : ℕ} {Ω : Type u_Ω}
    (S : Address M → Ω → Bool) :
    {ω | ∀ k < d, centerChoice S (RoutingPath.routeFrom (centerChoice S) k [] ω) ω ≠
      Fin.last M} = ⋃ f : Path M d, cylinder S f := by
  ext ω
  exact noDefault_iff_mem_cylinders S ω

/-- Change the auxiliary parameter space without changing any node choices. -/
theorem routeFrom_change_parameter {ι : Type u_ι} {X : Type u_X} {Y : Type u_Y}
    (f : List ι → X → ι) (g : List ι → Y → ι) (x : X) (y : Y)
    (h : ∀ P, f P x = g P y) (n : ℕ) (P : List ι) :
    RoutingPath.routeFrom f n P x = RoutingPath.routeFrom g n P y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [RoutingPath.routeFrom_succ, ih, h]

/-- Equivalent leaf-membership formulation, convenient for concrete routers. -/
theorem default_not_mem_iff_mem_cylinders {M d : ℕ} {Ω : Type u_Ω}
    (S : Address M → Ω → Bool) (ω : Ω) :
    Fin.last M ∉ RoutingPath.routeFrom (centerChoice S) d [] ω ↔
      ω ∈ ⋃ f : Path M d, cylinder S f := by
  rw [← RoutingPath.noDefault_iff_not_mem]
  exact noDefault_iff_mem_cylinders S ω

/-- Spatially parametrized selectors have the same no-default event as the
cylinders at a fixed center. This is directly usable with `selectorValue`. -/
theorem spatial_default_not_mem_iff {M d : ℕ} {Ω : Type u_Ω} {X : Type u_X}
    (S : Ω → List (Fin (M + 1)) → Fin M → X → Bool) (ω : Ω) (x : X) :
    Fin.last M ∉ RoutingPath.routeFrom
      (fun P y => OrderedRouting.chooseChild (fun j => S ω P j y)) d [] x ↔
      ω ∈ ⋃ f : Path M d,
        cylinder (fun a ω' => S ω' a.1 a.2 x) f := by
  have hr := routeFrom_change_parameter
    (centerChoice (fun a ω' => S ω' a.1 a.2 x))
    (fun P y => OrderedRouting.chooseChild (fun j => S ω P j y)) ω x
    (fun _ => rfl) d []
  rw [← hr]
  exact default_not_mem_iff_mem_cylinders _ ω

end Problem310.FirstDefault

end

end OAI
