import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.State2
import OAI.Combinatorics.KMedianRecovery.Recovery.Ball
import OAI.Combinatorics.KMedianRecovery.Machines.FirstSize
import OAI.Combinatorics.KMedianRecovery.Sampling.Kernel

namespace OAI

namespace MetricKMedianRecovery.Sampling
open RadiusMenus
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable def leafDistances (s : State V) (w : V) : Finset ℝ :=
  s.leaves.toFinset.image (fun z => dist w z.1+z.2)

noncomputable def nearestLeaf (s : State V) (w : V) : Option ℝ :=
  if h : (leafDistances s w).Nonempty then some ((leafDistances s w).inf' h id) else none

lemma nearestLeaf_of_mem (s : State V) (w : V) (z : V × ℝ) (hz : z ∈ s.leaves) :
    ∃ r, nearestLeaf s w = some r ∧ r ≤ dist w z.1+z.2 := by
  classical
  have hm : dist w z.1+z.2 ∈ leafDistances s w :=
    Finset.mem_image.mpr ⟨z,List.mem_toFinset.mpr hz,rfl⟩
  have hn : (leafDistances s w).Nonempty := ⟨_,hm⟩
  refine ⟨_,?_,Finset.inf'_le id hm⟩
  simp only [nearestLeaf, dite_eq_left hn]

lemma nearestLeaf_lower (s : State V) (w : V) (r a : ℝ)
    (hr : nearestLeaf s w = some r) (ha : ∀ z ∈ s.leaves, a ≤ dist w z.1+z.2) : a ≤ r := by
  classical
  unfold nearestLeaf at hr
  split_ifs at hr with hn
  · cases Option.some.inj hr
    apply Finset.le_inf'
    intro d hd
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hd
    exact ha z (List.mem_toFinset.mp hz)

abbrev Entry (M E J : ℕ) := Fin M ⊕ (Fin (E+1) ⊕ Fin J)
abbrev Action (D : Finset V) (M E J : ℕ) := Unit ⊕ (D ⊕ (D × Entry M E J))

noncomputable def clientWeight (S : Finset V) (Δ : ℝ) (s : State V) (w : V) : ℝ :=
  max 0 (reference S Δ s w)

noncomputable def totalWeight (D S : Finset V) (Δ : ℝ) (s : State V) : ℝ :=
  ∑ w ∈ D, clientWeight S Δ s w

lemma clientWeight_nonneg (S : Finset V) (Δ : ℝ) (s : State V) (w : V) :
    0 ≤ clientWeight S Δ s w := le_max_left _ _

lemma clientWeight_eq (S : Finset V) (Δ : ℝ) (s : State V) (w : V)
    (hΔ : 0 ≤ Δ) (hr : ∀ z ∈ s.leaves, 0 ≤ z.2) :
    clientWeight S Δ s w = reference S Δ s w :=
  max_eq_right (reference_nonneg S Δ s w hΔ hr)

lemma menuWeight_nonneg (M E J : ℕ) (a : Entry M E J) : 0 ≤ menuWeight M E J a := by
  rcases a with i | (i | i)
  · simp only [menuWeight]; positivity
  · simp only [menuWeight]; positivity
  · simp only [menuWeight]
    apply mul_nonneg (by norm_num)
    apply div_nonneg (by positivity)
    exact Finset.sum_nonneg (fun _ _ => by positivity)

noncomputable def transitionWeight (D S : Finset V) (Δ : ℝ) (M E J : ℕ)
    (s : Option (State V)) (a : Action D M E J) : ℝ :=
  match s with
  | none => if a = Sum.inl () then 1 else 0
  | some s => if 0 < totalWeight D S Δ s then
      match a with
      | .inl _ => 0
      | .inr (.inl w) => clientWeight S Δ s w/(2*totalWeight D S Δ s)
      | .inr (.inr (w,e)) => clientWeight S Δ s w/(2*totalWeight D S Δ s)*menuWeight M E J e
    else if a = Sum.inl () then 1 else 0

lemma transitionWeight_nonneg (D S : Finset V) (Δ : ℝ) (M E J : ℕ)
    (s : Option (State V)) (a : Action D M E J) : 0 ≤ transitionWeight D S Δ M E J s a := by
  classical
  cases s with
  | none => simp only [transitionWeight]; split_ifs <;> norm_num
  | some s =>
    simp only [transitionWeight]
    split_ifs with h
    · rcases a with u | (w | ⟨w,e⟩)
      · exact le_rfl
      · exact div_nonneg (clientWeight_nonneg S Δ s w) (by positivity)
      · exact mul_nonneg (div_nonneg (clientWeight_nonneg S Δ s w) (by positivity))
          (menuWeight_nonneg M E J e)
    · norm_num
    · norm_num

lemma transitionWeight_total (D S : Finset V) (Δ : ℝ) (M E J : ℕ)
    (hM : 0 < M) (hJ : 0 < J) (s : Option (State V)) :
    ∑ a : Action D M E J, transitionWeight D S Δ M E J s a = 1 := by
  classical
  cases s with
  | none => simp [transitionWeight]
  | some s =>
    by_cases h : 0 < totalWeight D S Δ s
    · simp only [transitionWeight, ite_eq_left h, Fintype.sum_sum_type, Fintype.sum_prod_type,
        Finset.sum_const_zero, zero_add, ← Finset.mul_sum, menuWeight_total M E J hM hJ, mul_one]
      rw [← Finset.sum_div, Finset.sum_coe_sort]
      change totalWeight D S Δ s/(2*totalWeight D S Δ s) +
        totalWeight D S Δ s/(2*totalWeight D S Δ s) = 1
      field_simp
      ring
    · simp [transitionWeight, h]

noncomputable def actualKernel (D S : Finset V) (Δ : ℝ) (M E J : ℕ)
    (hM : 0 < M) (hJ : 0 < J) : Guided.Kernel (Option (State V)) (Action D M E J) :=
  ⟨transitionWeight D S Δ M E J, transitionWeight_nonneg D S Δ M E J,
    transitionWeight_total D S Δ M E J hM hJ⟩

noncomputable def menuRadius (D : Finset V) (hD : D.Nonempty) (P kappa : ℝ)
    (m M E J : ℕ) (s : State V) (w : V) : Entry M E J → Option ℝ
  | .inl j => some ((j.val+1)*kappa*Population.radius D hD P m w)
  | .inr (.inl e) => (nearestLeaf s w).map (fun r => r/(1+kappa)^e.val)
  | .inr (.inr j) => some ((j.val+1)*kappa*Population.radius D hD P m w)

noncomputable def retain (m : ℕ) (s : State V) : Option (State V) :=
  if s.leaves.length ≤ m ∧ s.deleted.card ≤ m then some s else none

noncomputable def update (D F S : Finset V) (hD : D.Nonempty) (Δ P kappa : ℝ)
    (m M E J : ℕ) (s : Option (State V)) (a : Action D M E J) : Option (State V) :=
  match s with
  | none => none
  | some s => if 0 < totalWeight D S Δ s then
      match a with
      | .inl _ => none
      | .inr (.inl w) =>
        match ofLex (chosen S Δ s w) with
        | .inl v => retain m (s.remove v)
        | .inr _ => none
      | .inr (.inr (w,e)) =>
        match menuRadius D hD P kappa m M E J s w e with
        | none => none
        | some R => if (F.filter (fun v => dist w.val v ≤ R)).Nonempty then
            retain m (s.add w R) else none
    else none

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma retained_limits (m : ℕ) (s t : State V) (h : retain m s = some t) :
    t.leaves.length ≤ m ∧ t.deleted.card ≤ m := by
  unfold retain at h
  split_ifs at h with hc
  · cases Option.some.inj h
    exact hc

lemma update_limits (D F S : Finset V) (hD : D.Nonempty) (Δ P kappa : ℝ)
    (m M E J : ℕ) (s : Option (State V)) (a : Action D M E J) (t : State V)
    (h : update D F S hD Δ P kappa m M E J s a = some t) :
    t.leaves.length ≤ m ∧ t.deleted.card ≤ m := by
  cases s with
  | none => contradiction
  | some s =>
    simp only [update] at h
    split_ifs at h with hw
    · rcases a with u | (w | ⟨w,e⟩)
      · contradiction
      · cases he : ofLex (chosen S Δ s w) with
        | inl v => exact retained_limits m _ t (by simpa only [he] using h)
        | inr j => simp only [he] at h; contradiction
      · cases hr : menuRadius D hD P kappa m M E J s w e with
        | none => simp only [hr] at h; contradiction
        | some R =>
          simp only [hr] at h
          split_ifs at h with hb
          · exact retained_limits m _ t h

end MetricKMedianRecovery.Sampling

end OAI
