import OAI.Probability.ThorpShuffle.Polytabloids

namespace OAI

universe uI uX uK

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

variable {n : ℕ} {D : YoungDiagram}

def Standard (t : Fin n ≃ Cells D) : Prop := StrictMono t.symm

lemma standard_row_lt_iff (t : Fin n ≃ Cells D) (ht : Standard t) (x y : Fin n)
    (hr : (t x).val.1 = (t y).val.1) : x < y ↔ (t x).val.2 < (t y).val.2 := by
  constructor
  · intro hxy
    by_contra hn
    have hc : (t y).val.2 ≤ (t x).val.2 := Nat.le_of_not_gt hn
    have hyx : t y ≤ t x := ⟨by omega, hc⟩
    have hh : y ≤ x := by simpa only [Equiv.symm_apply_apply] using ht.monotone hyx
    exact not_le_of_gt hxy hh
  · intro hc
    have hxy : t x < t y := by
      refine lt_iff_le_not_ge.mpr ⟨⟨by omega, hc.le⟩, ?_⟩
      intro hh
      exact not_le_of_gt hc hh.2
    simpa only [Equiv.symm_apply_apply] using ht hxy

lemma standard_col_lt_iff (t : Fin n ≃ Cells D) (ht : Standard t) (x y : Fin n)
    (hc : (t x).val.2 = (t y).val.2) : x < y ↔ (t x).val.1 < (t y).val.1 := by
  constructor
  · intro hxy
    by_contra hn
    have hr : (t y).val.1 ≤ (t x).val.1 := Nat.le_of_not_gt hn
    have hyx : t y ≤ t x := ⟨hr, by omega⟩
    have hh : y ≤ x := by simpa only [Equiv.symm_apply_apply] using ht.monotone hyx
    exact not_le_of_gt hxy hh
  · intro hr
    have hxy : t x < t y := by
      refine lt_iff_le_not_ge.mpr ⟨⟨hr.le, by omega⟩, ?_⟩
      intro hh
      exact not_le_of_gt hr hh.1
    simpa only [Equiv.symm_apply_apply] using ht hxy

lemma column_eq_rowRank (t : Fin n ≃ Cells D) (ht : Standard t) (x : Fin n) :
    Fintype.card {y : Fin n // y < x ∧ (t y).val.1 = (t x).val.1} = (t x).val.2 := by
  let e : {y : Fin n // y < x ∧ (t y).val.1 = (t x).val.1} ≃ Fin ((t x).val.2) := {
    toFun := fun y => ⟨(t y.val).val.2, (standard_row_lt_iff t ht y.val x y.property.2).mp y.property.1⟩
    invFun := fun j => ⟨t.symm ⟨((t x).val.1, j), D.up_left_mem le_rfl j.isLt.le (t x).property⟩, by
      constructor
      · apply (standard_row_lt_iff t ht _ x (by simp)).mpr
        simpa only [Equiv.apply_symm_apply] using j.isLt
      · simp⟩
    left_inv := by
      intro y
      apply Subtype.ext
      apply t.injective
      simp only [Equiv.apply_symm_apply]
      apply Subtype.ext
      exact Prod.ext y.property.2.symm rfl
    right_inv := by intro j; apply Fin.ext; simp }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

lemma standard_eq_of_rows (t u : Fin n ≃ Cells D) (ht : Standard t) (hu : Standard u)
    (hr : ∀ x, (t x).val.1 = (u x).val.1) : t = u := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  apply Prod.ext (hr x)
  rw [← column_eq_rowRank t ht x, ← column_eq_rowRank u hu x]
  exact Fintype.card_congr ((Equiv.refl (Fin n)).subtypeEquiv (fun y => by simp only [Equiv.refl_apply, hr]))

end Thorp.Young

namespace Thorp.Specht
open scoped Classical

theorem independent_of_leading {I : Type uI} {X : Type uX} {K : Type uK} [Fintype I] [Fintype X] [LinearOrder K]
    (e : I → EuclideanSpace ℂ X) (b : I → X) (key : X → K)
    (hinj : Function.Injective (key ∘ b)) (hdiag : ∀ i, e i (b i) ≠ 0)
    (htri : ∀ i x, e i x ≠ 0 → key (b i) ≤ key x) : LinearIndependent ℂ e := by
  let : LinearOrder I := LinearOrder.lift' (key ∘ b) hinj
  rw [linearIndependent_iff']
  intro s a ha i hi
  by_contra hai
  let S := s.filter fun j => a j ≠ 0
  have hs : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hai⟩⟩
  let j := S.min' hs
  have hj : j ∈ S := S.min'_mem hs
  have hj' : j ∈ s := (Finset.mem_filter.mp hj).1
  have haz : a j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hval := congrArg (fun v : EuclideanSpace ℂ X => v (b j)) ha
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at hval
  rw [Finset.sum_eq_single_of_mem j hj'] at hval
  · exact (mul_ne_zero haz (hdiag j)) hval
  · intro k hk hkj
    by_cases hak : a k = 0
    · simp [hak]
    have hks : k ∈ S := Finset.mem_filter.mpr ⟨hk, hak⟩
    have hjk : j ≤ k := S.min'_le k hks
    have hjk' : j < k := lt_of_le_of_ne hjk (Ne.symm hkj)
    have hzero : e k (b j) = 0 := by
      by_contra hn
      have hh := htri k (b j) hn
      exact not_le_of_gt hjk' hh
    simp [hzero]

end Thorp.Specht

namespace Thorp.Specht
open scoped Classical

variable {n : ℕ} (D : YoungDiagram) (t : Fin n ≃ Thorp.Young.Cells D)

lemma column_word_le (ht : Thorp.Young.Standard t) (c : fiberGroup (tableauCol D t)) :
    toLex (tableauRow D t) ≤ toLex (fun x => tableauRow D t (c.val⁻¹ x)) := by
  by_cases hc : c.val = 1
  · simp [hc]
  let S := Finset.univ.filter fun x : Fin n => c.val⁻¹ x ≠ x
  have hs : S.Nonempty := by
    by_contra hn
    apply hc
    have he : c.val⁻¹ = 1 := by
      apply Equiv.ext
      intro x
      by_contra hx
      exact hn ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
    exact inv_eq_one.mp he
  let x := S.min' hs
  have hx : c.val⁻¹ x ≠ x := (Finset.mem_filter.mp (S.min'_mem hs)).2
  have hbefore (y : Fin n) (hy : y < x) : c.val⁻¹ y = y := by
    by_contra hn
    have hm : y ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ y, hn⟩
    exact not_le_of_gt hy (S.min'_le y hm)
  have hlt : x < c.val⁻¹ x := by
    apply lt_of_le_of_ne
    · by_contra hn
      have hh := hbefore (c.val⁻¹ x) (lt_of_not_ge hn)
      exact hx (c.val.symm.injective hh)
    · exact Ne.symm hx
  have hcol : (t x).val.2 = (t (c.val⁻¹ x)).val.2 := by
    have hh := c.property (c.val⁻¹ x)
    simpa only [tableauCol, perm_apply_inv] using hh
  have hrow := (Thorp.Young.standard_col_lt_iff t ht x (c.val⁻¹ x) hcol).mp hlt
  apply le_of_lt
  change Pi.Lex (· < ·) (· < ·) (tableauRow D t) (fun y => tableauRow D t (c.val⁻¹ y))
  exact ⟨x, fun y hy => congrArg (tableauRow D t) (hbefore y hy).symm, hrow⟩

def movedTableau (g : Equiv.Perm (Fin n)) : Fin n ≃ Thorp.Young.Cells D := (g⁻¹).trans t

def StandardPerm := {g : Equiv.Perm (Fin n) // Thorp.Young.Standard (movedTableau D t g)}

instance : Fintype (StandardPerm D t) := inferInstanceAs (Fintype {g : Equiv.Perm (Fin n) // Thorp.Young.Standard (movedTableau D t g)})

def movedWord (g : Equiv.Perm (Fin n)) : Tabloid (tableauRow D t) := g • baseTabloid (tableauRow D t)

lemma movedWord_apply (g : Equiv.Perm (Fin n)) (x : Fin n) :
    (movedWord D t g).val x = tableauRow D (movedTableau D t g) x := rfl

lemma moved_diag (g : Equiv.Perm (Fin n)) :
    tabloidRep D t g (polytabloid D t) (movedWord D t g) = 1 := by
  change polytabloid D t (g⁻¹ • (g • baseTabloid (tableauRow D t))) = 1
  rw [inv_smul_smul]
  exact polytabloid_diag D t

lemma moved_leading (g : Equiv.Perm (Fin n)) (hg : Thorp.Young.Standard (movedTableau D t g))
    (f : Tabloid (tableauRow D t)) (hf : tabloidRep D t g (polytabloid D t) f ≠ 0) :
    toLex (movedWord D t g).val ≤ toLex f.val := by
  obtain ⟨h, hh⟩ := polytabloid_support D t (g⁻¹ • f) hf
  have he : f = (g * h.val) • baseTabloid (tableauRow D t) := by
    rw [mul_smul]
    exact inv_smul_eq_iff.mp hh
  let c : Equiv.Perm (Fin n) := g * h.val * g⁻¹
  have hc : c ∈ fiberGroup (tableauCol D (movedTableau D t g)) := by
    intro x
    change (t (g⁻¹ (g (h.val (g⁻¹ x))))).val.2 = (t (g⁻¹ x)).val.2
    rw [perm_inv_apply]
    exact h.property (g⁻¹ x)
  have hcword : c • movedWord D t g = f := by
    rw [he]
    change (g * h.val * g⁻¹) • (g • baseTabloid _) = (g * h.val) • baseTabloid _
    simp only [← mul_smul, inv_mul_cancel_right]
  have hw := column_word_le D (movedTableau D t g) hg ⟨c, hc⟩
  change toLex (movedWord D t g).val ≤ toLex (c • movedWord D t g).val at hw
  rw [hcword] at hw
  exact hw

lemma standardWord_injective : Function.Injective (fun g : StandardPerm D t => toLex (movedWord D t g.val).val) := by
  intro g h he
  have hr : ∀ x, (movedTableau D t g.val x).val.1 = (movedTableau D t h.val x).val.1 :=
    fun x => congrFun he x
  have ht := Thorp.Young.standard_eq_of_rows _ _ g.property h.property hr
  apply Subtype.ext
  apply inv_injective
  apply Equiv.ext
  intro x
  apply t.injective
  exact congrArg (fun z : Fin n ≃ Thorp.Young.Cells D => z x) ht

theorem standard_polytabloids_independent :
    LinearIndependent ℂ (fun g : StandardPerm D t => tabloidRep D t g.val (polytabloid D t)) := by
  apply independent_of_leading _ (fun g => movedWord D t g.val) (fun f => toLex f.val)
    (standardWord_injective D t)
  · intro i
    rw [moved_diag]
    exact one_ne_zero
  · intro i f hf
    exact moved_leading D t i.val i.property f hf

def orbitVector (g : Equiv.Perm (Fin n)) : (module D t).toSubmodule :=
  ⟨tabloidRep D t g (polytabloid D t),
    (module D t).apply_mem_toSubmodule g (self_mem_cyclic _ _)⟩

theorem standardPerm_card_le_degree :
    Fintype.card (StandardPerm D t) ≤ Module.finrank ℂ (module D t).toSubmodule := by
  have hi : LinearIndependent ℂ (fun g : StandardPerm D t => orbitVector D t g.val) :=
    LinearIndependent.of_comp (module D t).toSubmodule.subtype (standard_polytabloids_independent D t)
  exact hi.fintype_card_le_finrank

end Thorp.Specht

end

end OAI
