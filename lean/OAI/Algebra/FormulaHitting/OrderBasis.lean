import OAI.Algebra.FormulaHitting.Wronskian
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

namespace OAI

noncomputable section

namespace NCHitting

open PowerSeries Submodule

variable {F : Type*} [Field F] [CharZero F]

def HasOrderBasis (V : Submodule F (PowerSeries F)) : Prop :=
  ∃ (k : ℕ) (b : Fin k → PowerSeries F) (a : Fin k → ℕ),
    LinearIndependent F b ∧ Submodule.span F (Set.range b) = V ∧
      Function.Injective a ∧
      (∀ i, PowerSeries.coeff (a i) (b i) ≠ 0) ∧
      (∀ i r, r < a i → PowerSeries.coeff r (b i) = 0)

omit [CharZero F] in
theorem hasOrderBasis_bot : HasOrderBasis (⊥ : Submodule F (PowerSeries F)) := by
  refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_, ?_⟩
  · exact linearIndependent_empty_type
  · simp
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i

omit [CharZero F] in
theorem hasOrderBasis_of_finrank_le (N : ℕ) :
    ∀ (V : Submodule F (PowerSeries F)) [FiniteDimensional F V],
      Module.finrank F V ≤ N → HasOrderBasis V := by
  classical
  induction N with
  | zero =>
    intro V _ hV
    have he : V = ⊥ := Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hV)
    rw [he]
    exact hasOrderBasis_bot
  | succ N ih =>
    intro V _ hV
    by_cases he : V = ⊥
    · rw [he]; exact hasOrderBasis_bot
    have hex : ∃ a : ℕ, ∃ v : PowerSeries F, v ∈ V ∧ PowerSeries.coeff a v ≠ 0 := by
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot he
      have hc : ∃ a, PowerSeries.coeff a v ≠ 0 := by
        by_contra h
        push Not at h
        apply hv0
        ext a
        simpa using h a
      obtain ⟨a, ha⟩ := hc
      exact ⟨a, v, hv, ha⟩
    let a := Nat.find hex
    obtain ⟨v, hv, hva⟩ := Nat.find_spec hex
    have hlow : ∀ x ∈ V, ∀ r < a, PowerSeries.coeff r x = 0 := by
      intro x hx r hr
      by_contra hc
      have hh := Nat.find_min' hex ⟨x, hx, hc⟩
      omega
    let W : Submodule F (PowerSeries F) := V ⊓ LinearMap.ker (PowerSeries.coeff a)
    have hWlt : W < V := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro h
      have hvW : v ∈ W := h.symm ▸ hv
      exact hva ((LinearMap.mem_ker.mp hvW.2))
    have hdim : Module.finrank F W ≤ N := by
      have hlt := Submodule.finrank_lt_finrank_of_lt hWlt
      omega
    obtain ⟨k, b, aa, hli, hspan, hinj, hlead, hzero⟩ := ih W hdim
    have hbW : ∀ i, b i ∈ W := by
      intro i
      rw [← hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hvnot : v ∉ Submodule.span F (Set.range b) := by
      rw [hspan]
      intro h
      exact hva (LinearMap.mem_ker.mp h.2)
    have hneq : ∀ i, a ≠ aa i := by
      intro i hi
      exact hlead i (hi ▸ LinearMap.mem_ker.mp (hbW i).2)
    refine ⟨k+1, Fin.cons v b, Fin.cons a aa, hli.finCons hvnot, ?_, ?_, ?_, ?_⟩
    · apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro x ⟨i, rfl⟩
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hv
        · simpa using (hbW j).1
      · intro x hx
        let c : F := PowerSeries.coeff a x / PowerSeries.coeff a v
        have hy : x - c • v ∈ W := by
          constructor
          · exact V.sub_mem hx (V.smul_mem c hv)
          · apply LinearMap.mem_ker.mpr
            simp only [map_sub, map_smul, smul_eq_mul, c]
            rw [div_mul_cancel₀ _ hva, sub_self]
        have hvm : v ∈ Submodule.span F (Set.range (Fin.cons v b)) :=
          Submodule.subset_span ⟨0, rfl⟩
        have hym : x - c • v ∈ Submodule.span F (Set.range (Fin.cons v b)) := by
          apply (Submodule.span_mono (s := Set.range b) ?_)
          · rwa [hspan]
          · rintro y ⟨j, rfl⟩
            exact ⟨j.succ, rfl⟩
        have := Submodule.add_mem (Submodule.span F (Set.range (Fin.cons v b)))
          hym (Submodule.smul_mem _ c hvm)
        simpa using this
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro _; rfl
        · intro hij; exact (hneq j' (by simpa using hij)).elim
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro hij; exact (hneq i' (by simpa using hij.symm)).elim
        · intro hij
          have hij' : aa i' = aa j' := by simpa using hij
          exact congrArg Fin.succ (hinj hij')
    · intro i
      exact Fin.cases hva hlead i
    · intro i
      exact Fin.cases (hlow v hv) hzero i

omit [CharZero F] in
theorem hasOrderBasis (V : Submodule F (PowerSeries F)) [FiniteDimensional F V] :
    HasOrderBasis V := hasOrderBasis_of_finrank_le (Module.finrank F V) V le_rfl

theorem wronskian_ne_zero_of_linearIndependent {k : ℕ}
    (f : Fin k → PowerSeries F) (hf : LinearIndependent F f) : wronskian f ≠ 0 := by
  classical
  let := FiniteDimensional.span_of_finite F (Set.finite_range f)
  obtain ⟨l, b, a, hb, hspan, ha, hlead, hzero⟩ := hasOrderBasis (Submodule.span F (Set.range f))
  have hdimf : Module.finrank F (Submodule.span F (Set.range f)) = k := by
    simpa using finrank_span_eq_card hf
  have hdimb : Module.finrank F (Submodule.span F (Set.range b)) = l := by
    simpa using finrank_span_eq_card hb
  rw [hspan, hdimf] at hdimb
  subst l
  have hm : ∀ j, ∃ c : Fin k → F, ∑ i : Fin k, c i • f i = b j := by
    intro j
    apply (Submodule.mem_span_range_iff_exists_fun F).mp
    rw [← hspan]
    exact Submodule.subset_span ⟨j, rfl⟩
  choose c hc using hm
  have hfn : (fun j => ∑ i : Fin k, c j i • f i) = b := funext hc
  have he := wronskian_linearCombination f (fun i j => c j i)
  rw [hfn] at he
  have hbn := (wronskian_order_sum b a ha hlead hzero).1
  intro h
  rw [h, zero_mul] at he
  exact hbn he

end NCHitting

end

end OAI
