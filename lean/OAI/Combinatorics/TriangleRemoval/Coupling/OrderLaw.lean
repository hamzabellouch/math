import Mathlib

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave
section RandomOrder
variable {K : Type*} [Fintype K] [DecidableEq K]

noncomputable def orderLaw : ℕ → Finset K → PMF (List K)
  | 0, _ => PMF.pure []
  | d + 1, C =>
      if h : C.Nonempty then
        (PMF.uniformOfFinset C h).bind
          (fun a => (orderLaw d (C.erase a)).map (List.cons a))
      else PMF.pure []

omit [Fintype K] in
@[simp] theorem pmf_map_cons_apply (p : PMF (List K)) (a b : K) (bs : List K) :
    (p.map (List.cons a)) (b :: bs) = if a = b then p bs else 0 := by
  by_cases hab : a = b
  · subst b
    simp [PMF.map_apply]
  · simp [PMF.map_apply, hab, Ne.symm hab]

omit [Fintype K] [DecidableEq K] in
@[simp] theorem pmf_map_cons_nil (p : PMF (List K)) (a : K) :
    (p.map (List.cons a)) [] = 0 := by simp [PMF.map_apply]

theorem orderLaw_apply_cons (d : ℕ) (C : Finset K) (hC : C.Nonempty)
    (a : K) (as : List K) :
    orderLaw (d + 1) C (a :: as) =
      (PMF.uniformOfFinset C hC a) * orderLaw d (C.erase a) as := by
  simp only [orderLaw, dite_eq_left hC, PMF.bind_apply, tsum_fintype, pmf_map_cons_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem orderLaw_apply_nil (d : ℕ) (C : Finset K) (hC : C.Nonempty) :
    orderLaw (d + 1) C [] = 0 := by
  simp [orderLaw, hC, PMF.bind_apply]

def Enumerates (C : Finset K) (as : List K) : Prop := as.Nodup ∧ as.toFinset = C

omit [Fintype K] in
@[simp] theorem enumerates_nil (C : Finset K) : Enumerates C [] ↔ C = ∅ := by
  simp [Enumerates, eq_comm]

omit [Fintype K] in
@[simp] theorem enumerates_cons (C : Finset K) (a : K) (as : List K) :
    Enumerates C (a :: as) ↔ a ∈ C ∧ Enumerates (C.erase a) as := by
  constructor
  · rintro ⟨hn, hc⟩
    have ha : a ∉ as.toFinset := by simpa using (List.nodup_cons.mp hn).1
    simp only [List.toFinset_cons] at hc
    refine ⟨hc ▸ Finset.mem_insert_self _ _, (List.nodup_cons.mp hn).2, ?_⟩
    rw [← hc, Finset.erase_insert ha]
  · rintro ⟨ha, hn, hc⟩
    have han : a ∉ as := by
      simpa only [← List.mem_toFinset] using (hc ▸ Finset.notMem_erase a C)
    refine ⟨List.nodup_cons.mpr ⟨han, hn⟩, ?_⟩
    simp only [List.toFinset_cons, hc, Finset.insert_erase ha]

theorem orderLaw_apply (d : ℕ) (C : Finset K) (hd : C.card ≤ d) (as : List K) :
    orderLaw d C as = if Enumerates C as then ((C.card.factorial : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  induction d generalizing C as with
  | zero =>
    have hC : C = ∅ := Finset.card_eq_zero.mp (by omega)
    subst C
    cases as with
    | nil => simp [orderLaw, Enumerates]
    | cons a as => simp [orderLaw, enumerates_cons]
  | succ d ih =>
    by_cases hC : C.Nonempty
    · cases as with
      | nil => simp [orderLaw_apply_nil d C hC, hC.ne_empty]
      | cons a as =>
        rw [orderLaw_apply_cons d C hC]
        by_cases ha : a ∈ C
        · have hcard : C.card = (C.erase a).card + 1 := (Finset.card_erase_add_one ha).symm
          have hde : (C.erase a).card ≤ d := by omega
          rw [ih (C.erase a) hde as, PMF.uniformOfFinset_apply_of_mem hC ha, enumerates_cons]
          simp only [ha, true_and]
          split_ifs with he
          · rw [hcard, Nat.factorial_succ, Nat.cast_mul]
            rw [ENNReal.mul_inv (Or.inr (by finiteness)) (Or.inl (by finiteness))]
          · simp
        · rw [PMF.uniformOfFinset_apply_of_notMem hC ha]
          simp only [zero_mul, enumerates_cons, ha, false_and, ↓reduceIte]
    · have hE : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
      subst C
      cases as with
      | nil => simp [orderLaw, Enumerates]
      | cons a as => simp [orderLaw, enumerates_cons]

omit [Fintype K] in
theorem enumerates_mem {C : Finset K} {as : List K} (h : Enumerates C as) (a : K) :
    a ∈ as ↔ a ∈ C := by rw [← List.mem_toFinset, h.2]

omit [Fintype K] in
theorem enumerates_length {C : Finset K} {as : List K} (h : Enumerates C as) :
    as.length = C.card := by rw [← h.2, List.toFinset_card_of_nodup h.1]

theorem enumerates_map_perm {as : List K} (h : Enumerates Finset.univ as)
    (σ : Equiv.Perm K) : Enumerates Finset.univ (as.map σ) := by
  refine ⟨h.1.map σ.injective, ?_⟩
  apply Finset.eq_univ_of_forall
  intro x
  simp only [List.mem_toFinset, List.mem_map]
  exact ⟨σ.symm x, (enumerates_mem h _).mpr (Finset.mem_univ _), σ.apply_symm_apply x⟩

theorem relabel_injective {as : List K} (h : Enumerates Finset.univ as) :
    Function.Injective (fun σ : Equiv.Perm K => as.map σ) := by
  intro σ ρ he
  apply Equiv.ext
  intro a
  exact List.map_inj_left.mp he a ((enumerates_mem h _).mpr (Finset.mem_univ _))

theorem exists_relabel {as bs : List K} (ha : Enumerates Finset.univ as)
    (hb : Enumerates Finset.univ bs) : ∃ σ : Equiv.Perm K, as.map σ = bs := by
  let ea := ha.1.getEquivOfForallMemList as (fun x =>
    (enumerates_mem ha x).mpr (Finset.mem_univ x))
  let eb := hb.1.getEquivOfForallMemList bs (fun x =>
    (enumerates_mem hb x).mpr (Finset.mem_univ x))
  have hel : as.length = bs.length := (enumerates_length ha).trans (enumerates_length hb).symm
  let σ := ea.symm.trans ((finCongr hel).trans eb)
  refine ⟨σ, ?_⟩
  apply List.ext_get (by simpa using hel)
  intro i hi hj
  simp only [List.get_eq_getElem, List.getElem_map]
  change σ (as.get ⟨i, by simpa using hi⟩) = bs.get ⟨i, hj⟩
  change eb (finCongr hel (ea.symm (ea ⟨i, by simpa using hi⟩))) = _
  simp only [Equiv.symm_apply_apply]
  rfl

theorem uniform_relabel_eq_orderLaw (d : ℕ) (hd : Fintype.card K ≤ d)
    (as : List K) (ha : Enumerates Finset.univ as) :
    (PMF.uniformOfFintype (Equiv.Perm K)).map (fun σ : Equiv.Perm K => as.map σ) =
      orderLaw d Finset.univ := by
  classical
  apply PMF.ext
  intro bs
  rw [orderLaw_apply d Finset.univ (by simpa using hd) bs, PMF.map_apply, tsum_fintype]
  by_cases hb : Enumerates Finset.univ bs
  · obtain ⟨σ, rfl⟩ := exists_relabel ha hb
    have he : ∀ ρ : Equiv.Perm K, as.map σ = as.map ρ ↔ ρ = σ := by
      intro ρ
      exact ⟨fun h => (relabel_injective ha h).symm, fun h => h ▸ rfl⟩
    simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      PMF.uniformOfFintype_apply, Fintype.card_perm, hb, Finset.card_univ]
  · have he : ∀ ρ : Equiv.Perm K, bs ≠ as.map ρ := by
      intro ρ hρ
      apply hb
      rw [hρ]
      exact enumerates_map_perm ha ρ
    simp only [he, ↓reduceIte, Finset.sum_const_zero, hb]

end RandomOrder
end SharpTerminalLeave

end

end OAI
