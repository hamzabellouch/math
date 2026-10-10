import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.StripCoefficient

namespace OAI

noncomputable section

namespace Foulkes.Strips
open Matrix Finset Submodule

lemma matching_of_det_ne_zero {n i : ℕ} (l m : Fin n → ℕ)
    (hd : (incidence (assignments i l m)).det ≠ 0) :
    ∃ σ : Equiv.Perm (Fin n), ∀ c, m c ≤ l (σ c) ∧ m c % i = l (σ c) % i := by
  classical
  rw [Matrix.det_apply] at hd
  obtain ⟨σ, hσ, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  have hp : (∏ c, incidence (assignments i l m) (σ c) c) ≠ 0 := by
    intro hh
    exact ht (by rw [hh, smul_zero])
  refine ⟨σ, fun c => ?_⟩
  have hc := (Finset.prod_ne_zero_iff.mp hp) c (mem_univ c)
  simpa only [incidence, assignments, mem_filter, mem_univ, true_and,
    ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] using hc

lemma containment_of_det_ne_zero {n i : ℕ} (l m : Fin n → ℕ)
    (hl : Antitone l) (hm : Antitone m)
    (hd : (incidence (assignments i l m)).det ≠ 0) (j : Fin n) : m j ≤ l j := by
  classical
  obtain ⟨σ,hσ⟩ := matching_of_det_ne_zero l m hd
  by_contra h
  let e : Fin (j.val+1) → Fin n := fun c => ⟨c.val, by omega⟩
  have hrow (c : Fin (j.val+1)) : (σ (e c)).val < j.val := by
    by_contra hh
    have hm' : m j ≤ m (e c) := hm (by change c.val ≤ j.val; omega)
    have hl' : l (σ (e c)) ≤ l j := hl (by change j.val ≤ (σ (e c)).val; omega)
    have hc := (hσ (e c)).1
    omega
  let f : Fin (j.val+1) → Fin j.val := fun c => ⟨(σ (e c)).val, hrow c⟩
  have hf : Function.Injective f := by
    intro c d hcd
    have hv : (σ (e c)).val = (σ (e d)).val := congrArg (fun z : Fin j.val => z.val) hcd
    have hh : σ (e c) = σ (e d) := Fin.ext hv
    have hc : c.val = d.val := congrArg (fun z : Fin n => z.val) (σ.injective hh)
    exact Fin.ext hc
  have hn := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hn
  omega

lemma le_of_residue_eq_of_lt_add {i x y : ℕ} (_hi : 0 < i)
    (hres : x % i = y % i) (hxy : x < y+i) : x ≤ y := by
  by_contra h
  have hyx : y < x := Nat.lt_of_not_ge h
  have hd : i ∣ x-y := (Nat.modEq_iff_dvd' (Nat.le_of_lt hyx)).mp hres.symm
  have hh := Nat.le_of_dvd (Nat.sub_pos_of_lt hyx) hd
  omega

lemma shifted_containment_of_det_ne_zero {n i : ℕ} (hi : 0 < i) (l m : Fin n → ℕ)
    (hl : Antitone l) (hm : Antitone m)
    (hd : (incidence (assignments i l m)).det ≠ 0)
    (j : Fin n) (hji : j.val+i < n) : l ⟨j.val+i,hji⟩ + i ≤ m j := by
  classical
  by_contra h
  have hjm : m j < l ⟨j.val+i,hji⟩ + i := Nat.lt_of_not_ge h
  let A : Matrix (Fin n) (Fin n) ℚ := (incidence (assignments i l m)).map Int.cast
  have hA : A.det ≠ 0 := by
    rw [show A = (incidence (assignments i l m)).map Int.cast from rfl, ← Int.cast_det]
    exact_mod_cast hd
  have hind := Matrix.linearIndependent_rows_of_det_ne_zero hA
  let embed : Fin (j.val+i+1) → Fin n := fun r => ⟨r.val, by omega⟩
  have hembed : Function.Injective embed := by
    intro r s hrs
    exact Fin.ext (congrArg (fun z : Fin n => z.val) hrs)
  have hlin : LinearIndependent ℚ (fun r : Fin (j.val+i+1) => A (embed r)) :=
    hind.comp embed hembed
  let gen : Fin j.val ⊕ Fin i → Fin n → ℚ := Sum.elim
    (fun c => Pi.single (⟨c.val, by omega⟩ : Fin n) 1)
    (fun u c => if j.val ≤ c.val ∧ m c % i = u.val then 1 else 0)
  let U : Submodule ℚ (Fin n → ℚ) := Submodule.span ℚ (Set.range gen)
  have hgen (q : Fin j.val ⊕ Fin i) : gen q ∈ U :=
    Submodule.subset_span ⟨q,rfl⟩
  have hrow (r : Fin (j.val+i+1)) : A (embed r) ∈ U := by
    let u : Fin i := ⟨l (embed r) % i, Nat.mod_lt _ hi⟩
    have he : A (embed r) =
        (∑ c : Fin j.val, A (embed r) ⟨c.val, by omega⟩ • gen (Sum.inl c)) + gen (Sum.inr u) := by
      funext c
      have hlr : l ⟨j.val+i,hji⟩ ≤ l (embed r) := hl (show embed r ≤ ⟨j.val+i,hji⟩ by
        exact Nat.le_of_lt_succ r.isLt)
      by_cases hc : c.val < j.val
      · have hcc : (⟨c.val,hc⟩ : Fin j.val).val = c.val := rfl
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        have hsum : (∑ d : Fin j.val, A (embed r) ⟨d.val, by omega⟩ * gen (Sum.inl d) c) =
            A (embed r) c := by
          rw [Finset.sum_eq_single ⟨c.val,hc⟩]
          · simp [gen]
          · intro d hd hne
            have hdc : (⟨d.val, by omega⟩ : Fin n) ≠ c := by
              intro he
              apply hne
              exact Fin.ext (congrArg (fun z : Fin n => z.val) he)
            simp [gen, Ne.symm hdc]
          · simp
        rw [hsum]
        have hnc : ¬j ≤ c := by change ¬j.val ≤ c.val; omega
        simp [gen, u, hnc]
      · have hsum : (∑ d : Fin j.val, A (embed r) ⟨d.val, by omega⟩ • gen (Sum.inl d)) c = 0 := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          apply Finset.sum_eq_zero
          intro d hd
          have hdc : (⟨d.val, by omega⟩ : Fin n) ≠ c := by
            intro he
            have hv : d.val = c.val := congrArg (fun z : Fin n => z.val) he
            have hdlt := d.isLt
            omega
          simp [gen, Ne.symm hdc]
        rw [Pi.add_apply, hsum, zero_add]
        have hmj : m c ≤ m j := hm (show j ≤ c by exact Nat.le_of_not_gt hc)
        have hlt : m c < l (embed r)+i := by omega
        have iffcond : (m c ≤ l (embed r) ∧ m c % i = l (embed r) % i) ↔
            m c % i = l (embed r) % i :=
          ⟨And.right, fun hr => ⟨le_of_residue_eq_of_lt_add hi hr hlt, hr⟩⟩
        simp only [A, Matrix.map_apply, incidence, assignments, mem_filter, mem_univ, true_and,
          gen, Sum.elim_inr, u, Nat.le_of_not_gt hc, true_and]
        simp only [iffcond, Int.cast_ite, Int.cast_one, Int.cast_zero]
    rw [he]
    exact U.add_mem (U.sum_mem (fun c hc => U.smul_mem _ (hgen (Sum.inl c)))) (hgen (Sum.inr u))
  have hsub : Submodule.span ℚ (Set.range (fun r : Fin (j.val+i+1) => A (embed r))) ≤ U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨r,rfl⟩
    exact hrow r
  have hdim := Submodule.finrank_mono hsub
  have heq := finrank_span_eq_card hlin
  have hbound : Module.finrank ℚ U ≤ j.val+i := by
    simpa [U, Set.finrank] using (finrank_range_le_card (R := ℚ) gen)
  rw [heq, Fintype.card_fin] at hdim
  omega

end Foulkes.Strips

end

end OAI
