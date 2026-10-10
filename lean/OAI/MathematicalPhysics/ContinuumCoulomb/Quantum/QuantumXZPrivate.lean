import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZModel

namespace OAI

/-! Private subdivision mediators prevent distinct two-body terms from sharing a pair. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem qmaSinglePauliWord_support_eq (i : ι) (a : Fin 4) (ha : a ≠ 0) :
    qmaPauliSupport (qmaSinglePauliWord i a) = {i} := by
  ext k
  by_cases hk : k = i <;> simp [qmaPauliSupport,qmaSinglePauliWord,hk,ha]

omit [DecidableEq ι] in
theorem qmaXZSubdivision_inr_mem (a b : ι → Fin 4) (e t : κ) (k : Fin 4) :
    Sum.inr t ∈ qmaPauliSupport (qmaXZSubdivisionWord a b e k) ↔ k ≠ 0 ∧ t = e := by
  fin_cases k <;> simp [qmaXZSubdivisionWord,qmaPauliSupport,qmaSinglePauliWord]

theorem qmaXZSubdivision_pair_index (a b : ι → Fin 4) (e : κ) (k : Fin 4)
    (h : (qmaPauliSupport (qmaXZSubdivisionWord a b e k)).card = 2) : k = 2 ∨ k = 3 := by
  fin_cases k
  · change (qmaPauliSupport (fun _ : ι ⊕ κ => 0)).card = 2 at h
    simp [qmaPauliSupport] at h
  · change (qmaPauliSupport (Sum.elim (fun _ : ι => 0) (qmaSinglePauliWord e 3))).card = 2 at h
    rw [qmaPauliSupport_join_card,qmaSinglePauliWord_support_eq e 3 (by decide)] at h
    simp [qmaPauliSupport] at h
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem qmaXZSubdivision_private_pair (a b : κ → ι → Fin 4)
    (hd : ∀ e, Disjoint (qmaPauliSupport (a e)) (qmaPauliSupport (b e)))
    (e f : κ) (k l : Fin 4)
    (hk : (qmaPauliSupport (qmaXZSubdivisionWord (a e) (b e) e k)).card = 2)
    (heq : qmaPauliSupport (qmaXZSubdivisionWord (a e) (b e) e k) =
      qmaPauliSupport (qmaXZSubdivisionWord (a f) (b f) f l)) : e = f ∧ k = l := by
  have hl := heq ▸ hk
  have hk' := qmaXZSubdivision_pair_index (a e) (b e) e k hk
  have hl' := qmaXZSubdivision_pair_index (a f) (b f) f l hl
  have hk0 : k ≠ 0 := by rcases hk' with rfl | rfl <;> decide
  have hin : Sum.inr e ∈ qmaPauliSupport (qmaXZSubdivisionWord (a e) (b e) e k) :=
    (qmaXZSubdivision_inr_mem _ _ _ _ _).mpr ⟨hk0,rfl⟩
  rw [heq] at hin
  have hef := ((qmaXZSubdivision_inr_mem _ _ _ _ _).mp hin).2
  subst f
  refine ⟨rfl,?_⟩
  rcases hk' with rfl | rfl <;> rcases hl' with rfl | rfl
  · rfl
  · change qmaPauliSupport (Sum.elim (a e) (qmaSinglePauliWord e 1)) =
      qmaPauliSupport (Sum.elim (b e) (qmaSinglePauliWord e 1)) at heq
    have hab : qmaPauliSupport (a e) = qmaPauliSupport (b e) := by
      ext i
      have h := Finset.ext_iff.mp heq (Sum.inl i)
      simpa [qmaPauliSupport] using h
    have hz : qmaPauliSupport (a e) = ∅ :=
      (Finset.disjoint_self_iff_empty _).mp (by simpa only [← hab] using hd e)
    change (qmaPauliSupport (Sum.elim (a e) (qmaSinglePauliWord e 1))).card = 2 at hk
    rw [qmaPauliSupport_join_card,hz,qmaSinglePauliWord_support_eq e 1 (by decide)] at hk
    norm_num at hk
  · change qmaPauliSupport (Sum.elim (b e) (qmaSinglePauliWord e 1)) =
      qmaPauliSupport (Sum.elim (a e) (qmaSinglePauliWord e 1)) at heq
    have hab : qmaPauliSupport (b e) = qmaPauliSupport (a e) := by
      ext i
      have h := Finset.ext_iff.mp heq (Sum.inl i)
      simpa [qmaPauliSupport] using h
    have hz : qmaPauliSupport (b e) = ∅ :=
      (Finset.disjoint_self_iff_empty _).mp (by simpa only [← hab] using (hd e).symm)
    change (qmaPauliSupport (Sum.elim (b e) (qmaSinglePauliWord e 1))).card = 2 at hk
    rw [qmaPauliSupport_join_card,hz,qmaSinglePauliWord_support_eq e 1 (by decide)] at hk
    norm_num at hk
  · rfl

theorem qmaXZPrivate_exists (w : κ → ι → Fin 4) (J : κ → ℝ)
    (hw : ∀ e, (qmaPauliSupport (w e)).card ≤ 2)
    (hy : ∀ e i, w e i ≠ 2) {N : ℝ} (hN : 1 ≤ N) :
    ∃ (v : (κ × Fin 4) → (ι ⊕ κ → Fin 4)) (K : (κ × Fin 4) → ℝ),
      (∀ p i, v p i ≠ 2) ∧ (∀ p, (qmaPauliSupport (v p)).card ≤ 2) ∧
      (∀ p q, (qmaPauliSupport (v p)).card = 2 →
        qmaPauliSupport (v p) = qmaPauliSupport (v q) → p = q) ∧
      |MediatorGraph.normalizedBottom (∑ p, (K p:ℂ) • qmaPauliWord (v p)) -
        MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • qmaPauliWord (w e))| ≤ 1/N := by
  choose L T hL hT hdis hcover using fun e =>
    qmaBalancedSupport (qmaPauliSupport (w e)) 1 (hw e)
  let a := fun e => qmaPauliRestrict (L e) (w e)
  let b := fun e => qmaPauliRestrict (T e) (w e)
  have ha (e : κ) : (qmaPauliSupport (a e)).card ≤ 1 :=
    (Finset.card_le_card (qmaPauliRestrict_support _ _)).trans (hL e)
  have hb (e : κ) : (qmaPauliSupport (b e)).card ≤ 1 :=
    (Finset.card_le_card (qmaPauliRestrict_support _ _)).trans (hT e)
  have hab (e : κ) : qmaPauliWord (a e)*qmaPauliWord (b e) = qmaPauliWord (w e) :=
    qmaPauliRestrict_factor _ _ _ (hdis e) (by rw [hcover e])
  have hcomm (e : κ) : qmaPauliWord (a e)*qmaPauliWord (b e) =
      qmaPauliWord (b e)*qmaPauliWord (a e) := qmaPauliRestrict_commute _ _ _ (hdis e)
  have hd (e : κ) : Disjoint (qmaPauliSupport (a e)) (qmaPauliSupport (b e)) :=
    (hdis e).mono (qmaPauliRestrict_support _ _) (qmaPauliRestrict_support _ _)
  let R := 8*(qmaThirdBudget 0 J)^4*N
  refine ⟨fun p => qmaXZSubdivisionWord (a p.1) (b p.1) p.1 p.2,
    fun p => qmaXZSubdivisionWeight R (J p.1) p.2,?_,?_,?_,?_⟩
  · intro p i
    exact qmaXZSubdivision_noY _ _ _ (qmaPauliRestrict_noY _ _ (hy p.1))
      (qmaPauliRestrict_noY _ _ (hy p.1)) _ _
  · intro p
    exact qmaXZSubdivision_support _ _ _ (ha p.1) (hb p.1) _
  · intro p q hp hpq
    obtain ⟨he,hk⟩ := qmaXZSubdivision_private_pair a b hd p.1 q.1 p.2 q.2 hp hpq
    exact Prod.ext he hk
  · have h := qmaXZSubdivision_accuracy a b J hcomm hN
    simpa only [hab] using h

end ContinuumCoulomb

end

end OAI
