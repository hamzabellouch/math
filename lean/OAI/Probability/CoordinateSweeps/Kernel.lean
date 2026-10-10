import Mathlib
import OAI.Probability.CoordinateSweeps.Conditioning
import OAI.Combinatorics.Graphs.Coverage

namespace OAI

/-!
All definitions are finite and use the source's ordinary probability and trace
normalizations.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

/-! The alternating placement kernel from 04-sparse:eq7.
Endpoints below need not be injections; invalid specifications have probability
zero automatically. On valid endpoint placements this is exactly the source Q. -/
namespace CoordinateSweeps
namespace Grid

variable (G : Grid)

/- The unique auxiliary trajectory joining two slots. -/
def pathBetween (x y : G.Slot) (t : Fin (G.b+1)) : G.Slot :=
  fun j => if j.val < t.val then y j else x j

@[simp] theorem pathBetween_zero (x y : G.Slot) : G.pathBetween x y 0 = x := by
  ext j
  simp [pathBetween]

@[simp] theorem pathBetween_last (x y : G.Slot) :
    G.pathBetween x y (Fin.last G.b) = y := by
  ext j
  simp [pathBetween, j.isLt]

@[simp] theorem pathBetween_input (x y : G.Slot) (j : Fin G.b) :
    G.pathBetween x y j.castSucc j = x j := by
  simp [pathBetween]

@[simp] theorem pathBetween_output (x y : G.Slot) (j : Fin G.b) :
    G.pathBetween x y j.succ j = y j := by
  simp [pathBetween]

theorem pathBetween_step (x y : G.Slot) (j k : Fin G.b) (hne : k ≠ j) :
    G.pathBetween x y j.succ k = G.pathBetween x y j.castSucc k := by
  have hne' : k.val ≠ j.val := fun he => hne (Fin.ext he)
  simp only [pathBetween, Fin.val_succ, Fin.val_castSucc]
  have hi : k.val < j.val+1 ↔ k.val < j.val := by omega
  simp only [hi]

/- The stage-decorated line used by the auxiliary trajectory. -/
def pathLine (x y : G.Slot) (j : Fin G.b) : G.Line j :=
  fun k => G.pathBetween x y j.castSucc k

/- Endpoint events are equivalent to the unique additional trajectory's
line assignments. No feasibility or injectivity is postulated. -/
def endpointEvent {k : ℕ} (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (ω : G.Choices) : Prop := ∀ i ∈ A, G.sweep ω (x i) = y i

/- A direct finite constraint event on one line for the extra particles. -/
def extraLineEvent {k : ℕ} (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (j : Fin G.b) (L : G.Line j) (σ : Equiv.Perm (Cube (G.bits j))) : Prop :=
  ∀ i ∈ A, G.pathLine (x i) (y i) j = L → σ (x i j) = y i j

namespace Holes
variable {G} {h k : ℕ}

/- Exact one-line probability after the hole assignments are prescribed. -/
def localExtraProbability (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (j : Fin G.b) (L : G.Line j)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j)))) : ℝ :=
  (∑ σ, if H.LineCompatible j L σ ∧ G.extraLineEvent x y A j L σ then μ σ else 0) /
    (∑ σ, if H.LineCompatible j L σ then μ σ else 0)

/- Product form of the exact conditional endpoint probability. The bridge to
the original conditioned sweep event is proved below, not assumed. -/
def extraProbability (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (μ : ∀ j : Fin G.b, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) : ℝ :=
  ∏ j, ∏ L : G.Line j, H.localExtraProbability x y A j L (μ j)

/- The path-weight alternating placement matrix Q, with counting measure and
s, not s-h, in its normalization, exactly as 04-sparse:eq7. -/
def placementKernel (H : G.Holes h) (x y : Fin k → G.Slot)
    (μ : ∀ j : Fin G.b, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) : ℝ :=
  (G.size : ℝ)⁻¹ ^ k * ∑ A ∈ (Finset.univ : Finset (Fin k)).powerset,
    (-1 : ℝ) ^ (k-A.card) * (G.size : ℝ)^A.card * H.extraProbability x y A μ

/- A line-isolated additional trajectory, relative to all other additional
paths AND the prescribed holes. Stage indices are never conflated. -/
def LineIsolated (H : G.Holes h) (x y : Fin k → G.Slot) (i : Fin k) : Prop :=
  (∀ j (a : Fin h), ¬ H.OnLine j (G.pathLine (x i) (y i) j) a) ∧
  (∀ j (a : Fin k), a ≠ i →
    G.pathLine (x a) (y a) j ≠ G.pathLine (x i) (y i) j)

theorem lineCompatible_of_empty (H : G.Holes h) (j : Fin G.b) (L : G.Line j)
    (he : ∀ i, ¬ H.OnLine j L i) (σ : Equiv.Perm (Cube (G.bits j))) :
    H.LineCompatible j L σ := by
  intro i
  exact (he i.val i.property).elim

theorem localExtraProbability_no_paths (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (j : Fin G.b) (L : G.Line j)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j))))
    (he : ∀ i, ¬ H.OnLine j L i)
    (ha : ∀ i ∈ A, G.pathLine (x i) (y i) j ≠ L) :
    H.localExtraProbability x y A j L μ = 1 := by
  have hr : ∀ σ, G.extraLineEvent x y A j L σ := by
    intro σ i hi hL
    exact (ha i hi hL).elim
  simp [localExtraProbability, H.lineCompatible_of_empty j L he, hr, μ.sum_mass]

theorem extraLineEvent_insert {G : Grid} {k : ℕ} (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (i : Fin k) (j : Fin G.b) (L : G.Line j)
    (σ : Equiv.Perm (Cube (G.bits j))) :
    G.extraLineEvent x y (insert i A) j L σ ↔
      ((G.pathLine (x i) (y i) j = L → σ (x i j) = y i j) ∧
        G.extraLineEvent x y A j L σ) := by
  simp [extraLineEvent]

/- The source's one-card marginal property, stated for a line law. This is
proved for both U and the actual binary law below, not a main-proof assumption. -/
def OneCardUniform {d : ℕ} (μ : FiniteLaw (Equiv.Perm (Cube d))) : Prop :=
  ∀ u v : Cube d, (∑ σ, if σ u = v then μ σ else 0) = (2^d : ℝ)⁻¹

theorem extraLineEvent_insert_off {G : Grid} {k : ℕ} (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (i : Fin k) (j : Fin G.b) (L : G.Line j)
    (hne : G.pathLine (x i) (y i) j ≠ L)
    (σ : Equiv.Perm (Cube (G.bits j))) :
    G.extraLineEvent x y (insert i A) j L σ ↔ G.extraLineEvent x y A j L σ := by
  rw [extraLineEvent_insert]
  simp [hne]

theorem localExtraProbability_insert_off (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (i : Fin k) (j : Fin G.b) (L : G.Line j)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j))))
    (hne : G.pathLine (x i) (y i) j ≠ L) :
    H.localExtraProbability x y (insert i A) j L μ =
      H.localExtraProbability x y A j L μ := by
  simp only [localExtraProbability, extraLineEvent_insert_off x y A i j L hne]

theorem localExtraProbability_isolated_insert (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (i : Fin k) (hi : i ∉ A)
    (his : H.LineIsolated x y i) (j : Fin G.b)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j)))) (hμ : OneCardUniform μ) :
    H.localExtraProbability x y (insert i A) j (G.pathLine (x i) (y i) j) μ =
      (2^G.bits j : ℝ)⁻¹ := by
  have he : ∀ σ, H.LineCompatible j (G.pathLine (x i) (y i) j) σ :=
    H.lineCompatible_of_empty j _ (his.1 j)
  have ha : ∀ σ, G.extraLineEvent x y A j (G.pathLine (x i) (y i) j) σ := by
    intro σ a ha hL
    exact (his.2 j a (by intro he; subst a; exact hi ha) hL).elim
  simp only [localExtraProbability, he, true_and, extraLineEvent_insert, ha,
    and_true, true_implies, ite_true, μ.sum_mass, div_one]
  exact hμ (x i j) (y i j)

theorem stageExtraProbability_isolated_insert (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (i : Fin k) (hi : i ∉ A)
    (his : H.LineIsolated x y i) (j : Fin G.b)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j)))) (hμ : OneCardUniform μ) :
    (∏ L : G.Line j, H.localExtraProbability x y (insert i A) j L μ) =
      (2^G.bits j : ℝ)⁻¹ * ∏ L : G.Line j, H.localExtraProbability x y A j L μ := by
  let L₀ := G.pathLine (x i) (y i) j
  have hs := H.localExtraProbability_isolated_insert x y A i hi his j μ hμ
  have he : H.localExtraProbability x y A j L₀ μ = 1 := by
    apply H.localExtraProbability_no_paths x y A j L₀ μ (his.1 j)
    intro a ha
    exact his.2 j a (by intro he; subst a; exact hi ha)
  have hprod : (∏ L ∈ Finset.univ.erase L₀, H.localExtraProbability x y (insert i A) j L μ) =
      ∏ L ∈ Finset.univ.erase L₀, H.localExtraProbability x y A j L μ := by
    apply Finset.prod_congr rfl
    intro L hL
    exact H.localExtraProbability_insert_off x y A i j L μ
      (Ne.symm (Finset.mem_erase.mp hL).1)
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ L₀),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ L₀), hs, he, one_mul, hprod]

theorem extraProbability_isolated_insert (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (i : Fin k) (hi : i ∉ A)
    (his : H.LineIsolated x y i)
    (μ : ∀ j : Fin G.b, FiniteLaw (Equiv.Perm (Cube (G.bits j))))
    (hμ : ∀ j, OneCardUniform (μ j)) :
    H.extraProbability x y (insert i A) μ =
      (G.size : ℝ)⁻¹ * H.extraProbability x y A μ := by
  unfold extraProbability
  simp_rw [H.stageExtraProbability_isolated_insert x y A i hi his _ _ (hμ _)]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  congr 1
  simp [size, Nat.cast_prod, Nat.cast_pow]

/- Elementary pairing identity for the alternating sum. -/
lemma alternating_cancel {ι : Type*} [DecidableEq ι] (s : Finset ι) (i : ι) (hi : i ∈ s)
    (P : Finset ι → ℝ)
    (hP : ∀ A ⊆ s.erase i, P (insert i A) = P A) :
    ∑ A ∈ s.powerset, (-1 : ℝ) ^ A.card * P A = 0 := by
  have hs : s = insert i (s.erase i) := (Finset.insert_erase hi).symm
  rw [hs, Finset.sum_powerset_insert (Finset.notMem_erase i s)]
  have hh : (∑ A ∈ (s.erase i).powerset, (-1 : ℝ) ^ (insert i A).card * P (insert i A)) =
      -(∑ A ∈ (s.erase i).powerset, (-1 : ℝ) ^ A.card * P A) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro A hA
    have hsub : A ⊆ s.erase i := Finset.mem_powerset.mp hA
    have hni : i ∉ A := fun hh => Finset.notMem_erase i s (hsub hh)
    rw [Finset.card_insert_of_notMem hni, hP A hsub, pow_succ]
    ring
  rw [hh]
  ring

/- Isolated-path cancellation for the actual product conditional kernel.
There is no independence assumption between auxiliary particle factors. -/
theorem placementKernel_eq_zero_of_isolated (H : G.Holes h) (x y : Fin k → G.Slot)
    (i : Fin k) (his : H.LineIsolated x y i)
    (μ : ∀ j : Fin G.b, FiniteLaw (Equiv.Perm (Cube (G.bits j))))
    (hμ : ∀ j, OneCardUniform (μ j)) : H.placementKernel x y μ = 0 := by
  have hsize : (G.size : ℝ) ≠ 0 := by
    apply ne_of_gt
    exact_mod_cast (Finset.prod_pos (fun j _ => pow_pos (by decide : 0 < (2:ℕ)) _))
  have hc := alternating_cancel (Finset.univ : Finset (Fin k)) i (Finset.mem_univ _)
    (fun A => (G.size : ℝ)^A.card * H.extraProbability x y A μ) (by
      intro A hA
      have hi : i ∉ A := fun hi => Finset.notMem_erase i _ (hA hi)
      rw [Finset.card_insert_of_notMem hi, pow_succ,
        H.extraProbability_isolated_insert x y A i hi his μ hμ]
      field_simp)
  have he : (∑ A ∈ (Finset.univ : Finset (Fin k)).powerset,
      (-1 : ℝ)^(k-A.card) * (G.size : ℝ)^A.card * H.extraProbability x y A μ) =
      (-1 : ℝ)^k * ∑ A ∈ (Finset.univ : Finset (Fin k)).powerset,
        (-1 : ℝ)^A.card * ((G.size : ℝ)^A.card * H.extraProbability x y A μ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A hA
    have hAk : A.card ≤ k := by simpa using Finset.card_le_univ A
    have hp : (-1 : ℝ)^(k-A.card) = (-1 : ℝ)^k * (-1 : ℝ)^A.card := by
      have h := pow_add (-1 : ℝ) (k-A.card) A.card
      rw [Nat.sub_add_cancel hAk] at h
      have hsq : (-1 : ℝ)^A.card * (-1 : ℝ)^A.card = 1 := by
        rw [← mul_pow]
        norm_num
      rw [h, mul_assoc, hsq, mul_one]
    rw [hp]
    ring
  rw [placementKernel, he, hc, mul_zero, mul_zero]

end Holes
end Grid
end CoordinateSweeps

namespace CoordinateSweeps.Grid
variable (G : Grid)

theorem boundary_coordinate_before (ω : G.Choices) (x : G.Slot) (k : Fin G.b)
    (t : ℕ) (ht : t ≤ k.val) : G.boundary ω t x k = x k := by
  induction t with
  | zero => simp
  | succ t ih =>
    have htb : t < G.b := by omega
    rw [G.boundary_succ ω htb]
    change G.stage ω ⟨t,htb⟩ (G.boundary ω t x) k = _
    rw [G.stage_apply_ne ω _ k (by intro he; have := congrArg Fin.val he; dsimp at this; omega)]
    exact ih (by omega)

theorem boundary_coordinate_stable (ω : G.Choices) (x : G.Slot) (k : Fin G.b)
    (u v : ℕ) (hku : k.val < u) (huv : u ≤ v) (hvb : v ≤ G.b) :
    G.boundary ω v x k = G.boundary ω u x k := by
  induction v, huv using Nat.le_induction with
  | base => rfl
  | succ v huv ih =>
    have hvb' : v < G.b := by omega
    rw [G.boundary_succ ω hvb']
    change G.stage ω ⟨v,hvb'⟩ (G.boundary ω v x) k = _
    rw [G.stage_apply_ne ω _ k (by intro he; have := congrArg Fin.val he; dsimp at this; omega)]
    exact ih (by omega)

theorem boundary_eq_pathBetween (ω : G.Choices) (x : G.Slot) (t : Fin (G.b+1)) :
    G.boundary ω t x = G.pathBetween x (G.sweep ω x) t := by
  funext k
  unfold pathBetween
  split_ifs with hkt
  · exact (G.boundary_coordinate_stable ω x k t G.b hkt (by omega) le_rfl).symm
  · exact G.boundary_coordinate_before ω x k t (by omega)

/- Actual endpoint events are exactly the auxiliary path constraints. -/
theorem sweep_eq_iff_line_assignments (ω : G.Choices) (x y : G.Slot) :
    G.sweep ω x = y ↔
      ∀ j, ω j (G.pathLine x y j) (x j) = y j := by
  constructor
  · intro hxy j
    have hs := congrArg (fun p : Equiv.Perm G.Slot => p x j)
      (G.boundary_succ ω j.isLt)
    change G.boundary ω (j.val+1) x j = G.stage ω j (G.boundary ω j x) j at hs
    rw [show G.boundary ω (j.val+1) x = G.pathBetween x y j.succ by
      simpa [hxy] using G.boundary_eq_pathBetween ω x j.succ,
      show G.boundary ω j.val x = G.pathBetween x y j.castSucc by
      simpa [hxy] using G.boundary_eq_pathBetween ω x j.castSucc] at hs
    change (ω j (fun k => G.pathBetween x y j.castSucc k)) (x j) = y j
    simpa only [G.stage_apply_same, G.pathBetween_input, G.pathBetween_output] using hs.symm
  · intro hxy
    have hb : ∀ t (ht : t ≤ G.b),
        G.boundary ω t x = G.pathBetween x y ⟨t,by omega⟩ := by
      intro t
      induction t with
      | zero => intro ht; simp
      | succ t ih =>
        intro ht
        have htb : t < G.b := by omega
        rw [G.boundary_succ ω htb]
        change G.stage ω ⟨t,htb⟩ (G.boundary ω t x) = _
        rw [ih (by omega)]
        funext k
        by_cases hkt : k = ⟨t,htb⟩
        · subst k
          have hi := hxy ⟨t,htb⟩
          change ω ⟨t,htb⟩ (fun k => G.pathBetween x y ⟨t,by omega⟩ k) (x ⟨t,htb⟩) = y ⟨t,htb⟩ at hi
          simpa only [stage_apply_same, pathBetween, Fin.val_mk, lt_self_iff_false,
            ite_false, Nat.lt_succ_self, ite_true] using hi
        · rw [G.stage_apply_ne ω _ k hkt]
          exact (G.pathBetween_step x y ⟨t,htb⟩ k hkt).symm
    have hh := hb G.b le_rfl
    change G.sweep ω x = G.pathBetween x y (Fin.last G.b) at hh
    rw [G.pathBetween_last] at hh
    exact hh

theorem endpointEvent_iff_lines {k : ℕ} (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (ω : G.Choices) :
    G.endpointEvent x y A ω ↔ ∀ j L, G.extraLineEvent x y A j L (ω j L) := by
  constructor
  · intro he j L i hi hL
    have h := (G.sweep_eq_iff_line_assignments ω (x i) (y i)).mp (he i hi) j
    simpa [hL] using h
  · intro he i hi
    apply (G.sweep_eq_iff_line_assignments ω (x i) (y i)).mpr
    intro j
    exact he j (G.pathLine (x i) (y i) j) i hi rfl

end CoordinateSweeps.Grid

namespace CoordinateSweeps

/- Finite independence, keeping an arbitrary local constraint at every factor. -/
theorem sum_prod_ite_all {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)]
    (w : ∀ i, X i → ℝ) (P : ∀ i, X i → Prop) :
    (∑ x : ∀ i, X i, if ∀ i, P i (x i) then ∏ i, w i (x i) else 0) =
      ∏ i, ∑ y, if P i y then w i y else 0 := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ∀ i, P i (x i)
  · simp [hx]
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    rw [ite_eq_right hx]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

namespace Grid
variable (G : Grid)

def productLineMass
    (μ : ∀ j : Fin G.b, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) (ω : G.Choices) : ℝ :=
  ∏ j, ∏ L, μ j (ω j L)

theorem sum_productLineMass_event
    (μ : ∀ j : Fin G.b, FiniteLaw (Equiv.Perm (Cube (G.bits j))))
    (P : ∀ j : Fin G.b, G.Line j → Equiv.Perm (Cube (G.bits j)) → Prop) :
    (∑ ω, if ∀ j L, P j L (ω j L) then G.productLineMass μ ω else 0) =
      ∏ j, ∏ L, ∑ σ, if P j L σ then μ j σ else 0 := by
  unfold productLineMass
  calc
    _ = ∏ j, ∑ ω : G.Line j → Equiv.Perm (Cube (G.bits j)),
        if ∀ L, P j L (ω L) then ∏ L, μ j (ω L) else 0 := by
      convert sum_prod_ite_all
        (fun j (ω : G.Line j → Equiv.Perm (Cube (G.bits j))) => ∏ L, μ j (ω L))
        (fun j (ω : G.Line j → Equiv.Perm (Cube (G.bits j))) => ∀ L, P j L (ω L)) using 1 <;>
        congr!
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      convert sum_prod_ite_all (fun _ σ => μ j σ) (P j) using 1

namespace Holes
variable {G} {h k : ℕ}

/- Conditional probability of an endpoint specification, from the original
independent line sample space; the full trajectories of the holes are retained. -/
def conditionalEndpointProbability (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k))
    (μ : ∀ j : Fin G.b, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) : ℝ :=
  (∑ ω, if H.Compatible ω ∧ G.endpointEvent x y A ω then G.productLineMass μ ω else 0) /
    (∑ ω, if H.Compatible ω then G.productLineMass μ ω else 0)

/- The kernel's product formula really is the conditioned sweep probability;
no independence of different layers of the auxiliary paths is used. -/
theorem extraProbability_eq_conditionalEndpoint (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k))
    (μ : ∀ j : Fin G.b, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) :
    H.extraProbability x y A μ = H.conditionalEndpointProbability x y A μ := by
  have he : ∀ ω : G.Choices,
      H.Compatible ω ∧ G.endpointEvent x y A ω ↔
        ∀ j L, H.LineCompatible j L (ω j L) ∧ G.extraLineEvent x y A j L (ω j L) := by
    intro ω
    rw [H.compatible_iff_lines, G.endpointEvent_iff_lines]
    constructor
    · intro h j L
      exact ⟨h.1 j L, h.2 j L⟩
    · intro h
      exact ⟨fun j L => (h j L).1, fun j L => (h j L).2⟩
  unfold conditionalEndpointProbability
  simp only [he]
  simp only [H.compatible_iff_lines]
  have hn : (∑ ω : G.Choices,
      if ∀ j L, H.LineCompatible j L (ω j L) ∧ G.extraLineEvent x y A j L (ω j L)
      then G.productLineMass μ ω else 0) =
      ∏ j, ∏ L, ∑ σ, if H.LineCompatible j L σ ∧ G.extraLineEvent x y A j L σ
        then μ j σ else 0 := by
    convert G.sum_productLineMass_event μ (fun j L σ =>
      H.LineCompatible j L σ ∧ G.extraLineEvent x y A j L σ) using 1 <;>
      congr!
  have hd : (∑ ω : G.Choices, if ∀ j L, H.LineCompatible j L (ω j L)
      then G.productLineMass μ ω else 0) =
      ∏ j, ∏ L, ∑ σ, if H.LineCompatible j L σ then μ j σ else 0 := by
    convert G.sum_productLineMass_event μ H.LineCompatible using 1
  rw [hn, hd]
  simp only [extraProbability, localExtraProbability, Finset.prod_div_distrib]

/- At the source law, the denominator in the direct event formula is exactly
the source normalizer (with all prescribed paths, not just endpoints). -/
theorem lineMass_hole_normalizer (H : G.Holes h) {z : ℝ}
    (hz : 0 ≤ z) (hz' : z ≤ 1) :
    (∑ ω, if H.Compatible ω then
      G.productLineMass (fun j => lineLaw (G.bits j) z hz hz') ω else 0) =
      H.probability z := by
  symm
  exact sum_subtype_eq_sum_ite_of_iff (fun _ => Iff.rfl) (G.choiceWeight z)

end Holes
end Grid
end CoordinateSweeps

namespace CoordinateSweeps

def binaryBoundary {d : ℕ} (bits : BinaryChoices d) (t : ℕ) : Equiv.Perm (Cube d) :=
  ((List.ofFn (fun j => binaryLayer j (bits j))).take t).reverse.prod

@[simp] theorem binaryBoundary_zero {d : ℕ} (bits : BinaryChoices d) :
    binaryBoundary bits 0 = 1 := by simp [binaryBoundary]

@[simp] theorem binaryBoundary_last {d : ℕ} (bits : BinaryChoices d) :
    binaryBoundary bits d = binarySweep d bits := by
  simp only [binaryBoundary, binarySweep, orderedProduct]
  rw [List.take_of_length_le (by simp)]

theorem binaryBoundary_succ {d : ℕ} (bits : BinaryChoices d) {t : ℕ} (ht : t < d) :
    binaryBoundary bits (t+1) = binaryLayer ⟨t,ht⟩ (bits ⟨t,ht⟩) * binaryBoundary bits t := by
  unfold binaryBoundary
  rw [List.take_succ_eq_append_getElem (by simpa using ht)]
  simp [List.reverse_append]

@[simp] theorem binaryLayer_apply_same {d : ℕ} (j : Fin d)
    (bits : ({k : Fin d // k ≠ j} → Bool) → Bool) (x : Cube d) :
    binaryLayer j bits x j = Bool.xor (x j) (bits (fun k => x k)) := by
  simp [binaryLayer, pairSwitch, Equiv.funSplitAt_apply, Equiv.funSplitAt_symm_apply]

theorem binaryLayer_apply_ne {d : ℕ} (j k : Fin d) (hne : k ≠ j)
    (bits : ({k : Fin d // k ≠ j} → Bool) → Bool) (x : Cube d) :
    binaryLayer j bits x k = x k := by
  simp [binaryLayer, pairSwitch, Equiv.funSplitAt_apply, Equiv.funSplitAt_symm_apply, hne]

def binaryPath {d : ℕ} (x y : Cube d) (t : ℕ) : Cube d :=
  fun k => if k.val < t then y k else x k

def binaryPathLine {d : ℕ} (x y : Cube d) (j : Fin d) : {k : Fin d // k ≠ j} → Bool :=
  fun k => binaryPath x y j.val k

@[simp] theorem binaryPath_zero {d : ℕ} (x y : Cube d) : binaryPath x y 0 = x := by
  funext k; simp [binaryPath]

@[simp] theorem binaryPath_last {d : ℕ} (x y : Cube d) : binaryPath x y d = y := by
  funext k; simp [binaryPath, k.isLt]

theorem binaryBoundary_before {d : ℕ} (bits : BinaryChoices d) (x : Cube d) (k : Fin d)
    (t : ℕ) (ht : t ≤ k.val) : binaryBoundary bits t x k = x k := by
  induction t with
  | zero => simp
  | succ t ih =>
    have htb : t < d := by omega
    rw [binaryBoundary_succ bits htb]
    change binaryLayer ⟨t,htb⟩ (bits ⟨t,htb⟩) (binaryBoundary bits t x) k = _
    rw [binaryLayer_apply_ne _ k (by intro he; have := congrArg Fin.val he; dsimp at this; omega)]
    exact ih (by omega)

theorem binaryBoundary_stable {d : ℕ} (bits : BinaryChoices d) (x : Cube d) (k : Fin d)
    (u v : ℕ) (hku : k.val < u) (huv : u ≤ v) (hvd : v ≤ d) :
    binaryBoundary bits v x k = binaryBoundary bits u x k := by
  induction v, huv using Nat.le_induction with
  | base => rfl
  | succ v huv ih =>
    have hvd' : v < d := by omega
    rw [binaryBoundary_succ bits hvd']
    change binaryLayer ⟨v,hvd'⟩ (bits ⟨v,hvd'⟩) (binaryBoundary bits v x) k = _
    rw [binaryLayer_apply_ne _ k (by intro he; have := congrArg Fin.val he; dsimp at this; omega)]
    exact ih (by omega)

theorem binaryBoundary_eq_path {d : ℕ} (bits : BinaryChoices d) (x : Cube d)
    (t : ℕ) (ht : t ≤ d) :
    binaryBoundary bits t x = binaryPath x (binarySweep d bits x) t := by
  funext k
  unfold binaryPath
  split_ifs with hkt
  · simpa using (binaryBoundary_stable bits x k t d hkt ht le_rfl).symm
  · exact binaryBoundary_before bits x k t (by omega)

theorem binarySweep_eq_iff_coins {d : ℕ} (bits : BinaryChoices d) (x y : Cube d) :
    binarySweep d bits x = y ↔
      ∀ j, bits j (binaryPathLine x y j) = Bool.xor (x j) (y j) := by
  have hxor : ∀ a b c : Bool, Bool.xor a b = c ↔ b = Bool.xor a c := by decide
  constructor
  · intro hxy j
    have hs := congrArg (fun p : Equiv.Perm (Cube d) => p x j)
      (binaryBoundary_succ bits j.isLt)
    change binaryBoundary bits (j.val+1) x j =
      binaryLayer j (bits j) (binaryBoundary bits j.val x) j at hs
    rw [binaryBoundary_eq_path bits x (j.val+1) (by omega),
      binaryBoundary_eq_path bits x j.val (by omega), hxy,
      binaryLayer_apply_same] at hs
    have hh : Bool.xor (x j) (bits j (binaryPathLine x y j)) = y j := by
      change Bool.xor (x j) (bits j (fun k => if k.val.val < j.val then y k else x k)) = y j
      simpa only [binaryPath, Nat.lt_succ_self, ite_true, lt_self_iff_false, ite_false] using hs.symm
    exact (hxor _ _ _).mp hh
  · intro hxy
    have hb : ∀ t (ht : t ≤ d), binaryBoundary bits t x = binaryPath x y t := by
      intro t
      induction t with
      | zero => intro ht; simp
      | succ t ih =>
        intro ht
        have htd : t < d := by omega
        rw [binaryBoundary_succ bits htd]
        change binaryLayer ⟨t,htd⟩ (bits ⟨t,htd⟩) (binaryBoundary bits t x) = _
        rw [ih (by omega)]
        funext k
        by_cases hkt : k = ⟨t,htd⟩
        · subst k
          rw [binaryLayer_apply_same]
          have hi := (hxor _ _ _).mpr (hxy ⟨t,htd⟩)
          change Bool.xor (x ⟨t,htd⟩) (bits ⟨t,htd⟩ (fun k => if k.val.val < t then y k else x k)) = y ⟨t,htd⟩ at hi
          simpa only [binaryPath, Nat.lt_succ_self, ite_true, lt_self_iff_false, ite_false] using hi
        · rw [binaryLayer_apply_ne _ k hkt]
          have hne : k.val ≠ t := fun he => hkt (Fin.ext he)
          simp only [binaryPath]
          have he : k.val < t+1 ↔ k.val < t := by omega
          simp [he]
    simpa using hb d le_rfl

end CoordinateSweeps

namespace CoordinateSweeps
namespace FiniteLaw

/- Independent uniform choices coincide with the uniform law on a finite
product, including dependent factors. -/
theorem uniform_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)] :
    uniform (∀ i, X i) = independent (fun i => uniform (X i)) := by
  ext x
  change (Fintype.card (∀ i, X i) : ℝ)⁻¹ = ∏ i, (Fintype.card (X i) : ℝ)⁻¹
  simp [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]

/- One specified coordinate of a uniform random function is uniform. -/
theorem uniform_eval {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [Nonempty B] (a : A) (b : B) :
    (∑ f : A → B, if f a = b then uniform (A → B) f else 0) =
      (Fintype.card B : ℝ)⁻¹ := by
  let e := Equiv.funSplitAt a B
  rw [← Equiv.sum_comp e.symm]
  have hc : Fintype.card (A → B) = Fintype.card B * Fintype.card ({j : A // j ≠ a} → B) := by
    simpa using Fintype.card_congr e
  simp only [uniform_apply, Fintype.sum_prod_type, e, Equiv.funSplitAt_symm_apply]
  rw [hc, Nat.cast_mul]
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hA : (Fintype.card ({j : A // j ≠ a} → B) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp
  simp

/- Exact pushforward probability identity. -/
theorem map_event {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteLaw A) (f : A → B) (P : B → Prop) :
    (∑ b, if P b then μ.map f b else 0) = ∑ a, if P (f a) then μ a else 0 := by
  simp only [map_apply]
  have hi : ∀ b, (if P b then ∑ a, if f a = b then μ a else 0 else 0) =
      ∑ a, if P b then (if f a = b then μ a else 0) else 0 := by
    intro b; by_cases hb : P b <;> simp [hb]
  simp only [hi]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have h : ∀ b, (if P b then (if f a = b then μ a else 0) else 0) =
      if f a = b then (if P (f a) then μ a else 0) else 0 := by
    intro b
    by_cases hb : f a = b
    · subst b; simp
    · simp [hb]
  simp only [h, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end FiniteLaw

/- The actual fair-switch binary sweep sends every given slot uniformly.
In particular this is not imported as a hypothesis on the line law. -/
theorem binaryLaw_one_card (d : ℕ) (x y : Cube d) :
    (∑ σ, if σ x = y then binaryLaw d σ else 0) = (2^d : ℝ)⁻¹ := by
  unfold binaryLaw
  have hm := FiniteLaw.map_event (FiniteLaw.uniform (BinaryChoices d)) (binarySweep d) (fun σ => σ x = y)
  have he : (∑ σ, if σ x = y then
      (FiniteLaw.uniform (BinaryChoices d)).map (binarySweep d) σ else 0) =
      ∑ bits : BinaryChoices d, if binarySweep d bits x = y then
        FiniteLaw.uniform (BinaryChoices d) bits else 0 := by
    convert hm using 1 <;> congr!
  rw [he, FiniteLaw.uniform_pi]
  simp only [binarySweep_eq_iff_coins]
  change (∑ bits : BinaryChoices d,
    if ∀ j, bits j (binaryPathLine x y j) = Bool.xor (x j) (y j) then
      ∏ j, FiniteLaw.uniform (({k : Fin d // k ≠ j} → Bool) → Bool) (bits j) else 0) = _
  have hs := sum_prod_ite_all
    (fun j (b : ({k : Fin d // k ≠ j} → Bool) → Bool) => FiniteLaw.uniform _ b)
    (fun j (b : ({k : Fin d // k ≠ j} → Bool) → Bool) =>
      b (binaryPathLine x y j) = Bool.xor (x j) (y j))
  calc
    _ = ∏ j : Fin d, ∑ b : ({k : Fin d // k ≠ j} → Bool) → Bool,
        if b (binaryPathLine x y j) = Bool.xor (x j) (y j) then FiniteLaw.uniform _ b else 0 := by
      convert hs using 1 <;> congr!
    _ = ∏ _j : Fin d, (2 : ℝ)⁻¹ := by
      apply Finset.prod_congr rfl
      intro j _
      have hu := FiniteLaw.uniform_eval (binaryPathLine x y j) (Bool.xor (x j) (y j))
      convert hu using 1 <;> congr!
    _ = _ := by simp [← inv_pow]

end CoordinateSweeps

namespace CoordinateSweeps

/- The uniform permutation law has the same exact one-card marginal. -/
theorem uniformLaw_one_card (d : ℕ) (x y : Cube d) :
    (∑ σ : Equiv.Perm (Cube d), if σ x = y then FiniteLaw.uniform _ σ else 0) =
      (2^d : ℝ)⁻¹ := by
  let ex : Fin 1 ↪ Cube d := ⟨fun _ => x, fun _ _ _ => Subsingleton.elim _ _⟩
  let ey : Fin 1 ↪ Cube d := ⟨fun _ => y, fun _ _ _ => Subsingleton.elim _ _⟩
  have hu := FiniteLaw.uniform_assignments ex ey
  have hp : ∀ σ : Equiv.Perm (Cube d), ex.trans σ.toEmbedding = ey ↔ σ x = y := by
    intro σ
    constructor
    · intro he
      have hh := congrArg (fun e : Fin 1 ↪ Cube d => e 0) he
      exact hh
    · intro he
      apply Function.Embedding.ext
      intro i
      exact he
  simp only [FiniteLaw.assignments, hp] at hu
  have hc : Fintype.card (Cube d) = 2^d := by simp [Cube]
  simp only [hc, Nat.descFactorial_one, Nat.cast_pow, Nat.cast_ofNat] at hu
  convert hu using 1

/- No auxiliary marginal hypothesis remains: this is the manuscript's real
line law, including either endpoint value of the mixture parameter. -/
theorem lineLaw_one_card (d : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1) :
    Grid.Holes.OneCardUniform (lineLaw d z hz hz') := by
  intro x y
  change (∑ σ, if σ x = y then
    (1-z) * FiniteLaw.uniform _ σ + z * binaryLaw d σ else 0) = _
  have hi : ∀ σ : Equiv.Perm (Cube d),
      (if σ x = y then (1-z) * FiniteLaw.uniform _ σ + z * binaryLaw d σ else 0) =
      (1-z) * (if σ x = y then FiniteLaw.uniform _ σ else 0) +
        z * (if σ x = y then binaryLaw d σ else 0) := by
    intro σ; by_cases h : σ x = y <;> simp [h]
  simp only [hi, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hu : (∑ σ : Equiv.Perm (Cube d), if σ x = y then FiniteLaw.uniform _ σ else 0) =
      (2^d : ℝ)⁻¹ := uniformLaw_one_card d x y
  have hb : (∑ σ : Equiv.Perm (Cube d), if σ x = y then binaryLaw d σ else 0) =
      (2^d : ℝ)⁻¹ := binaryLaw_one_card d x y
  rw [hu, hb]
  ring

/- Isolated-path cancellation, now for the literal conditioned sweep law. -/
theorem Grid.Holes.placementKernel_lineLaw_eq_zero_of_isolated
    {G : Grid} {h k : ℕ} (H : G.Holes h) (x y : Fin k → G.Slot)
    (i : Fin k) (his : H.LineIsolated x y i)
    (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1) :
    H.placementKernel x y (fun j => lineLaw (G.bits j) z hz hz') = 0 := by
  exact H.placementKernel_eq_zero_of_isolated x y i his _
    (fun j => lineLaw_one_card (G.bits j) z hz hz')

end CoordinateSweeps

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.Grid
variable (G : Grid)

def spliceEquiv (t : Fin (G.b+1)) : (G.Slot × G.Slot) ≃ (G.Slot × G.Slot) where
  toFun p := (G.pathBetween p.1 p.2 t, G.pathBetween p.2 p.1 t)
  invFun p := (G.pathBetween p.1 p.2 t, G.pathBetween p.2 p.1 t)
  left_inv p := by
    apply Prod.ext <;> funext j <;> simp only [pathBetween] <;> split_ifs <;> rfl
  right_inv p := by
    apply Prod.ext <;> funext j <;> simp only [pathBetween] <;> split_ifs <;> rfl

/- Exact counting identity for one layer of an independent endpoint pair. -/
theorem sum_pathBetween (t : Fin (G.b+1)) (f : G.Slot → ℝ) :
    (∑ p : G.Slot × G.Slot, f (G.pathBetween p.1 p.2 t)) =
      (G.size : ℝ) * ∑ x : G.Slot, f x := by
  calc
    _ = ∑ p : G.Slot × G.Slot, f p.1 := by
      exact Equiv.sum_comp (G.spliceEquiv t) (fun p => f p.1)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, G.card_slot, nsmul_eq_mul]
      rw [Finset.mul_sum]

/- A uniform slot chooses each stage-line with probability m_j/s. -/
theorem sum_slot_line (j : Fin G.b) (L : G.Line j) (c : ℝ) :
    (∑ x : G.Slot, if (fun k : {k : Fin G.b // k ≠ j} => x k) = L then c else 0) =
      (2^G.bits j : ℝ) * c := by
  let e := Equiv.piSplitAt j (fun k => Cube (G.bits k))
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  have he : ∀ u : Cube (G.bits j), ∀ v : G.Line j,
      (fun k : {k : Fin G.b // k ≠ j} => e.symm (u,v) k) = v := by
    intro u v
    funext k
    simp [e, Equiv.piSplitAt_symm_apply, k.property]
  simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [Cube]

/- Uniform product weight on the full pair of endpoints, with replacement. -/
def endpointWeight (p : G.Slot × G.Slot) : ℝ := FiniteLaw.uniform _ p

theorem endpointWeight_nonneg (p : G.Slot × G.Slot) : 0 ≤ G.endpointWeight p :=
  (FiniteLaw.uniform _).nonneg p

theorem endpointWeight_total : ∑ p, G.endpointWeight p = 1 := FiniteLaw.sum_mass _

/- A single fixed vertex-sharing event has exact probability 1/s. -/
theorem probability_path_vertex (t : Fin (G.b+1)) (v : G.Slot) :
    (∑ p : G.Slot × G.Slot, if G.pathBetween p.1 p.2 t = v then G.endpointWeight p else 0) =
      (G.size : ℝ)⁻¹ := by
  have hs := G.sum_pathBetween t (fun x => if x = v then
    (Fintype.card (G.Slot × G.Slot) : ℝ)⁻¹ else 0)
  have hn : (G.size : ℝ) ≠ 0 := by
    exact_mod_cast (show G.size ≠ 0 by rw [← G.card_slot]; exact Fintype.card_ne_zero)
  calc
    _ = (G.size : ℝ) * ∑ x : G.Slot, if x = v then
        (Fintype.card (G.Slot × G.Slot) : ℝ)⁻¹ else 0 := by
      convert hs using 1
      congr!
    _ = _ := by
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Fintype.card_prod, G.card_slot,
        Nat.cast_mul]
      field_simp

/- A single stage-line-sharing event has exact probability m_j/s. -/
theorem probability_path_line (j : Fin G.b) (L : G.Line j) :
    (∑ p : G.Slot × G.Slot, if G.pathLine p.1 p.2 j = L then G.endpointWeight p else 0) =
      (2^G.bits j : ℝ) / G.size := by
  have hs := G.sum_pathBetween j.castSucc (fun x =>
    if (fun k : {k : Fin G.b // k ≠ j} => x k) = L then
      (Fintype.card (G.Slot × G.Slot) : ℝ)⁻¹ else 0)
  have hn : (G.size : ℝ) ≠ 0 := by
    exact_mod_cast (show G.size ≠ 0 by rw [← G.card_slot]; exact Fintype.card_ne_zero)
  calc
    _ = (G.size : ℝ) * ∑ x : G.Slot,
        if (fun k : {k : Fin G.b // k ≠ j} => x k) = L then
          (Fintype.card (G.Slot × G.Slot) : ℝ)⁻¹ else 0 := by
      convert hs using 1
      congr!
    _ = _ := by
      rw [G.sum_slot_line]
      simp only [Fintype.card_prod, G.card_slot, Nat.cast_mul]
      field_simp

end CoordinateSweeps.Grid

namespace CoordinateSweeps.Coverage

/- The union bound on a single finite random datum. -/
theorem sum_ite_exists_le {X J : Type*} [Fintype X] [Fintype J]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (P : J → X → Prop) :
    (∑ x, if ∃ j, P j x then w x else 0) ≤ ∑ j, ∑ x, if P j x then w x else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  have hpj : ∀ j, 0 ≤ (if P j x then w x else 0) := by
    intro j; split_ifs; exact hw x; exact le_rfl
  by_cases he : ∃ j, P j x
  · obtain ⟨j,hj⟩ := he
    rw [ite_eq_left ⟨j,hj⟩]
    have hh := Finset.single_le_sum (fun j _ => hpj j) (Finset.mem_univ j)
    simpa only [ite_eq_left hj] using hh
  · rw [ite_eq_right he]
    exact Finset.sum_nonneg (fun j _ => hpj j)

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Grid
variable (G : Grid)

/- Sharing means using the same decorated line at the same stage. -/
def lineShares (p q : G.Slot × G.Slot) : Prop :=
  ∃ j : Fin G.b, G.pathLine p.1 p.2 j = G.pathLine q.1 q.2 j

/- Vertex sharing means the same slot at one fixed stage boundary. -/
def vertexShares (p q : G.Slot × G.Slot) : Prop :=
  ∃ t : Fin (G.b+1), G.pathBetween p.1 p.2 t = G.pathBetween q.1 q.2 t

theorem lineShares_symm : ∀ ⦃left right⦄, G.lineShares left right → G.lineShares right left := by
  rintro p q ⟨j,hj⟩
  exact ⟨j,hj.symm⟩

theorem vertexShares_symm : ∀ ⦃left right⦄, G.vertexShares left right → G.vertexShares right left := by
  rintro p q ⟨j,hj⟩
  exact ⟨j,hj.symm⟩

def lineSharingRate : ℝ := ∑ j : Fin G.b, (2^G.bits j : ℝ) / G.size

def vertexSharingRate : ℝ := (G.b+1 : ℕ) / (G.size : ℝ)

theorem lineSharingRate_nonneg : 0 ≤ G.lineSharingRate := by
  apply Finset.sum_nonneg
  intro j _
  positivity

theorem vertexSharingRate_nonneg : 0 ≤ G.vertexSharingRate := by
  unfold vertexSharingRate
  positivity

theorem probability_lineShares_le (q : G.Slot × G.Slot) :
    (∑ p, if G.lineShares p q then G.endpointWeight p else 0) ≤ G.lineSharingRate := by
  have hu := Coverage.sum_ite_exists_le G.endpointWeight G.endpointWeight_nonneg
    (fun j : Fin G.b => fun p : G.Slot × G.Slot =>
      G.pathLine p.1 p.2 j = G.pathLine q.1 q.2 j)
  calc
    _ ≤ ∑ j : Fin G.b, ∑ p : G.Slot × G.Slot,
        if G.pathLine p.1 p.2 j = G.pathLine q.1 q.2 j then G.endpointWeight p else 0 := by
      convert hu using 1 <;> congr!
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact G.probability_path_line j (G.pathLine q.1 q.2 j)

theorem probability_vertexShares_le (q : G.Slot × G.Slot) :
    (∑ p, if G.vertexShares p q then G.endpointWeight p else 0) ≤ G.vertexSharingRate := by
  have hu := Coverage.sum_ite_exists_le G.endpointWeight G.endpointWeight_nonneg
    (fun j : Fin (G.b+1) => fun p : G.Slot × G.Slot =>
      G.pathBetween p.1 p.2 j = G.pathBetween q.1 q.2 j)
  calc
    _ ≤ ∑ j : Fin (G.b+1), ∑ p : G.Slot × G.Slot,
        if G.pathBetween p.1 p.2 j = G.pathBetween q.1 q.2 j then G.endpointWeight p else 0 := by
      convert hu using 1 <;> congr!
    _ = ∑ _j : Fin (G.b+1), (G.size : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro j _
      exact G.probability_path_vertex j (G.pathBetween q.1 q.2 j)
    _ = _ := by simp [vertexSharingRate, div_eq_mul_inv]

namespace Holes
variable {G} {h k : ℕ}

/- Keep the actual prescribed hole paths, recording their endpoints. -/
def endpointData (H : G.Holes h) (i : Fin h) : G.Slot × G.Slot :=
  (H.path i 0, H.path i (Fin.last G.b))

/- The source's feasibility ensures these endpoints reconstruct the entire
prescribed trajectory, not merely an unrelated bridge between its endpoints. -/
theorem path_eq_pathBetween (H : G.Holes h) (hH : H.Feasible)
    (i : Fin h) (t : Fin (G.b+1)) :
    H.path i t = G.pathBetween (H.endpointData i).1 (H.endpointData i).2 t := by
  obtain ⟨ω,hω⟩ := hH
  have hb := G.boundary_eq_pathBetween ω (H.path i 0) t
  have hl := hω i (Fin.last G.b)
  change G.sweep ω (H.path i 0) = H.path i (Fin.last G.b) at hl
  rw [hω i t, hl] at hb
  exact hb

/- A card not covered by any line-sharing has exactly the isolation property
needed for the alternating probability kernel. -/
theorem lineIsolated_of_not_covered (H : G.Holes h) (hH : H.Feasible)
    (x : Fin k → G.Slot × G.Slot) (i : Fin k)
    (hi : i ∉ Coverage.sharingCoverage G.lineShares H.endpointData x) :
    H.LineIsolated (fun a => (x a).1) (fun a => (x a).2) i := by
  have h0 : ¬ ((∃ a : Fin k, i ≠ a ∧ G.lineShares (x i) (x a)) ∨
      ∃ a : Fin h, G.lineShares (x i) (H.endpointData a)) := by
    simpa only [Coverage.sharingCoverage, Coverage.mem_covered] using hi
  constructor
  · intro j a ha
    apply h0
    right
    refine ⟨a,j,?_⟩
    change (fun k : {k : Fin G.b // k ≠ j} => H.path a j.castSucc k) = G.pathLine (x i).1 (x i).2 j at ha
    rw [H.path_eq_pathBetween hH a j.castSucc] at ha
    exact ha.symm
  · intro j a hai ha
    apply h0
    left
    exact ⟨a,hai.symm,j,ha.symm⟩

/- Nonzero Q entries require coverage of every auxiliary particle, for the
literal real line mixture and full feasible path conditioning. -/
theorem placementKernel_ne_zero_coverage (H : G.Holes h) (hH : H.Feasible)
    (x : Fin k → G.Slot × G.Slot) (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hQ : H.placementKernel (fun a => (x a).1) (fun a => (x a).2)
      (fun j => lineLaw (G.bits j) z hz hz') ≠ 0) :
    (Coverage.sharingCoverage G.lineShares H.endpointData x).card = k := by
  have hall : Coverage.sharingCoverage G.lineShares H.endpointData x = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    by_contra hi
    exact hQ (H.placementKernel_lineLaw_eq_zero_of_isolated _ _ i
      (H.lineIsolated_of_not_covered hH x i hi) z hz hz')
  simp [hall]

/- The exact full-array probability bound needed to estimate the counting
Hilbert--Schmidt norm in the many-coordinate sparse case. -/
theorem probability_nonzero_placementKernel_le (H : G.Holes h) (hH : H.Feasible)
    (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hsmall : ((k+h : ℕ) : ℝ) * G.lineSharingRate ≤ 1) :
    Coverage.probability G.endpointWeight (fun x : Fin k → G.Slot × G.Slot =>
      H.placementKernel (fun a => (x a).1) (fun a => (x a).2)
        (fun j => lineLaw (G.bits j) z hz hz') ≠ 0) ≤
      (2 : ℝ)^k * (((k+h : ℕ) : ℝ) * G.lineSharingRate)^((k : ℝ)/2) := by
  have ht := Coverage.probability_coverage_le (I := Fin k) G.lineShares G.lineShares_symm H.endpointData
    G.endpointWeight G.endpointWeight_nonneg G.endpointWeight_total
    G.lineSharingRate G.lineSharingRate_nonneg G.probability_lineShares_le
    (by simpa using hsmall) k
  calc
    _ ≤ Coverage.probability G.endpointWeight (fun x : Fin k → G.Slot × G.Slot =>
        k ≤ (Coverage.sharingCoverage G.lineShares H.endpointData x).card) :=
      Coverage.probability_mono G.endpointWeight G.endpointWeight_nonneg
        (fun x hx => (H.placementKernel_ne_zero_coverage hH x z hz hz' hx).ge)
    _ ≤ _ := by simpa using ht

end Holes
end CoordinateSweeps.Grid

end
end
open scoped Matrix.Norms.L2Operator

end OAI
