import OAI.MeasureTheory.DyadicAvoidance.RoutingPath
import OAI.MeasureTheory.DyadicAvoidance.GridSeparation

namespace OAI

universe u_ι u_X u_K u_V u_J

noncomputable section

namespace Problem310.LocalPredicateFactor

open RoutingPath GridSeparation

variable {ι : Type u_ι} {X : Type u_X} {K : Type u_K} {V : Type u_V}

/-- Routing through a subtree only uses its strict-descendant choices.
If those choices factor through one key, the terminal leaf does too. -/
theorem route_eq_of_key_eq (choose : List ι → X → ι)
    (key : X → K) (r : ℕ) (P : List ι)
    (hchoice : ∀ Q : List ι, P.IsPrefix Q → Q.length < P.length + r →
      ∀ x y : X, key x = key y → choose Q x = choose Q y)
    {x y : X} (hxy : key x = key y) :
    routeFrom choose r P x = routeFrom choose r P y := by
  apply routeFrom_eq_of_choices_eq choose r P y x
  intro k hk
  apply hchoice (routeFrom choose k P y) (prefix_routeFrom choose k P y)
  · rw [length_routeFrom]
    omega
  · exact hxy

/-- A terminal output on a routed subtree factors through a common key
provided every choice and every possible terminal output does. -/
theorem terminal_eq_of_key_eq (choose : List ι → X → ι)
    (terminal : List ι → X → V) (key : X → K) (r : ℕ) (P : List ι)
    (hchoice : ∀ Q : List ι, P.IsPrefix Q → Q.length < P.length + r →
      ∀ x y : X, key x = key y → choose Q x = choose Q y)
    (hterminal : ∀ Q : List ι, P.IsPrefix Q → Q.length = P.length + r →
      ∀ x y : X, key x = key y → terminal Q x = terminal Q y)
    {x y : X} (hxy : key x = key y) :
    terminal (routeFrom choose r P x) x = terminal (routeFrom choose r P y) y := by
  have hroute := route_eq_of_key_eq choose key r P hchoice hxy
  rw [hroute]
  exact hterminal _ (prefix_routeFrom choose r P y)
    (length_routeFrom choose r P y) x y hxy

/-- An incoming selector multiplied by a local terminal predicate also
factors through that key. This includes a child which is already a leaf. -/
theorem local_predicate_eq_of_key_eq (choose : List ι → X → ι)
    (terminal : List ι → X → Bool) (incoming : X → Bool)
    (key : X → K) (r : ℕ) (P : List ι)
    (hchoice : ∀ Q : List ι, P.IsPrefix Q → Q.length < P.length + r →
      ∀ x y : X, key x = key y → choose Q x = choose Q y)
    (hterminal : ∀ Q : List ι, P.IsPrefix Q → Q.length = P.length + r →
      ∀ x y : X, key x = key y → terminal Q x = terminal Q y)
    (hincoming : ∀ x y : X, key x = key y → incoming x = incoming y)
    {x y : X} (hxy : key x = key y) :
    (incoming x && terminal (routeFrom choose r P x) x) =
      (incoming y && terminal (routeFrom choose r P y) y) := by
  rw [hincoming x y hxy,
    terminal_eq_of_key_eq choose terminal key r P hchoice hterminal hxy]

/-- A single table evaluated at any coarser grid is a function of the finest key. -/
theorem table_eq_of_finest_key {b B : ℕ} (hb : b ≤ B)
    (table : Fin (2 ^ (b + 2)) → V) {x y : ℝ}
    (hxy : ⌊(2 : ℝ) ^ (B + 2) * Int.fract x⌋ =
      ⌊(2 : ℝ) ^ (B + 2) * Int.fract y⌋) :
    table (dyadicKey b x) = table (dyadicKey b y) := by
  apply congrArg table
  apply (dyadicKey_eq_iff b x y).mpr
  exact periodicKey_dyadic_eq_of_refine hb hxy

variable {J : Type u_J}

/-- An arbitrary deterministic rule applied to selector-table lookups depends
only on a common finer key. In particular this applies to first-success routing. -/
theorem choice_eq_of_finest_key (b : J → ℕ) (B : ℕ)
    (tables : ∀ j, Fin (2 ^ (b j + 2)) → Bool)
    (rule : (J → Bool) → ι) (hb : ∀ j, b j ≤ B) {x y : ℝ}
    (hxy : ⌊(2 : ℝ) ^ (B + 2) * Int.fract x⌋ =
      ⌊(2 : ℝ) ^ (B + 2) * Int.fract y⌋) :
    rule (fun j => tables j (dyadicKey (b j) x)) =
      rule (fun j => tables j (dyadicKey (b j) y)) := by
  apply congrArg rule
  funext j
  exact table_eq_of_finest_key (hb j) (tables j) hxy

/-- A table-based node rule, with no restriction on which deterministic
first-success/default convention the rule uses. -/
def gridChoice (b : List ι → J → ℕ)
    (tables : ∀ Q j, Fin (2 ^ (b Q j + 2)) → Bool)
    (rule : List ι → (J → Bool) → ι) (Q : List ι) (x : ℝ) : ι :=
  rule Q (fun j => tables Q j (dyadicKey (b Q j) x))

def gridTerminal (c : List ι → ℕ)
    (tables : ∀ Q, Fin (2 ^ (c Q + 2)) → Bool) (Q : List ι) (x : ℝ) : Bool :=
  tables Q (dyadicKey (c Q) x)

/-- The incoming selector and every table in a child subtree may have different
resolutions. A bound on all those resolutions gives exactly the common-key
factorization needed for deterministic scale representatives. -/
theorem grid_local_predicate_factors
    (b : List ι → J → ℕ) (c : List ι → ℕ) (bIn B : ℕ)
    (selectors : ∀ Q j, Fin (2 ^ (b Q j + 2)) → Bool)
    (terminals : ∀ Q, Fin (2 ^ (c Q + 2)) → Bool)
    (incoming : Fin (2 ^ (bIn + 2)) → Bool)
    (rule : List ι → (J → Bool) → ι) (r : ℕ) (P : List ι)
    (hb : ∀ Q : List ι, P.IsPrefix Q → Q.length < P.length + r →
      ∀ j, b Q j ≤ B)
    (hc : ∀ Q : List ι, P.IsPrefix Q → Q.length = P.length + r → c Q ≤ B)
    (hIn : bIn ≤ B) {x y : ℝ}
    (hxy : ⌊(2 : ℝ) ^ (B + 2) * Int.fract x⌋ =
      ⌊(2 : ℝ) ^ (B + 2) * Int.fract y⌋) :
    (incoming (dyadicKey bIn x) &&
      gridTerminal c terminals (routeFrom (gridChoice b selectors rule) r P x) x) =
    (incoming (dyadicKey bIn y) &&
      gridTerminal c terminals (routeFrom (gridChoice b selectors rule) r P y) y) := by
  apply local_predicate_eq_of_key_eq
    (gridChoice b selectors rule) (gridTerminal c terminals)
    (fun z => incoming (dyadicKey bIn z))
    (fun z => ⌊(2 : ℝ) ^ (B + 2) * Int.fract z⌋) r P
  · intro Q hPQ hlen u v huv
    exact choice_eq_of_finest_key (b Q) B (selectors Q) (rule Q)
      (hb Q hPQ hlen) huv
  · intro Q hPQ hlen u v huv
    exact table_eq_of_finest_key (hc Q hPQ hlen) (terminals Q) huv
  · intro u v huv
    exact table_eq_of_finest_key hIn incoming huv
  · exact hxy

end Problem310.LocalPredicateFactor

end

end OAI
