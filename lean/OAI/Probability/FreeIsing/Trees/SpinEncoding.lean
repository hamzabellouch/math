import OAI.Probability.FreeIsing.Trees.Parents

namespace OAI

noncomputable section

namespace Problem367

def spinAgreementCode (a b : IsingSpin) : IsingSpin :=
  if a = b then .pos else .neg

lemma spinAgreementCode_injective_right (a : IsingSpin) :
    Function.Injective (spinAgreementCode a) := by
  intro b c h
  cases a <;> cases b <;> cases c <;> simp_all [spinAgreementCode]

@[simp] lemma spinAgreementCode_eq_pos_iff (a b : IsingSpin) :
    spinAgreementCode a b = .pos ↔ a = b := by
  cases a <;> cases b <;> simp [spinAgreementCode]

@[simp] lemma spinAgreementCode_eq_neg_iff (a b : IsingSpin) :
    spinAgreementCode a b = .neg ↔ a ≠ b := by
  cases a <;> cases b <;> simp [spinAgreementCode]

def connectedSpinEncode {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length)
    (σ : D → IsingSpin) (v : D) : IsingSpin := by
  classical
  exact if hv : (v : TreeVertex d) = r then σ v else
    spinAgreementCode
      (σ ⟨parentVertex v, hD.parent_mem_of_ne_min hr hmin v.2 hv⟩) (σ v)

@[simp] lemma connectedSpinEncode_apply_root {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) (σ : D → IsingSpin) :
    connectedSpinEncode hD r hr hmin σ ⟨r, hr⟩ = σ ⟨r, hr⟩ := by
  simp [connectedSpinEncode]

lemma connectedSpinEncode_apply_ne_root {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) (σ : D → IsingSpin)
    (v : D) (hv : (v : TreeVertex d) ≠ r) :
    connectedSpinEncode hD r hr hmin σ v =
      spinAgreementCode
        (σ ⟨parentVertex v, hD.parent_mem_of_ne_min hr hmin v.2 hv⟩) (σ v) := by
  simp [connectedSpinEncode, hv]

lemma connectedSpinEncode_injective {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) :
    Function.Injective (connectedSpinEncode hD r hr hmin) := by
  classical
  intro σ τ hστ
  have aux : ∀ n : ℕ, ∀ v : D, v.1.1.length = n → σ v = τ v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hn
      by_cases hv : (v : TreeVertex d) = r
      · have hh := congrFun hστ v
        simpa [connectedSpinEncode, hv] using hh
      · let p : D := ⟨parentVertex v, hD.parent_mem_of_ne_min hr hmin v.2 hv⟩
        have hnil := ConnectedFinset.ne_nil_of_ne_min hmin v.2 hv
        have hpos : 0 < v.1.1.length := List.length_pos_iff.mpr hnil
        have hplen : p.1.1.length < n := by
          change (parentVertex v.1).1.length < n
          rw [parentVertex_length]
          omega
        have hpeq : σ p = τ p := ih p.1.1.length hplen p rfl
        have hh : spinAgreementCode (σ p) (σ v) =
            spinAgreementCode (τ p) (τ v) := by
          simpa [connectedSpinEncode, hv, p] using congrFun hστ v
        rw [hpeq] at hh
        exact spinAgreementCode_injective_right (τ p) hh
  funext v
  exact aux v.1.1.length v rfl

lemma connectedSpinEncode_bijective {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) :
    Function.Bijective (connectedSpinEncode hD r hr hmin) := by
  have hi := connectedSpinEncode_injective hD r hr hmin
  exact ⟨hi, Finite.surjective_of_injective hi⟩

def connectedSpinEquiv {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) :
    (D → IsingSpin) ≃ (D → IsingSpin) :=
  Equiv.ofBijective _ (connectedSpinEncode_bijective hD r hr hmin)

@[simp] lemma connectedSpinEquiv_apply {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) (σ : D → IsingSpin) :
    connectedSpinEquiv hD r hr hmin σ = connectedSpinEncode hD r hr hmin σ := rfl

lemma spinAgreementCode_comm (a b : IsingSpin) :
    spinAgreementCode a b = spinAgreementCode b a := by
  cases a <;> cases b <;> rfl

lemma ConnectedFinset.spin_eq_on_iff_root_agreements {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r : TreeVertex d} (hr : r ∈ D)
    (σ τ : TreeVertex d → IsingSpin) :
    (∀ v ∈ D, σ v = τ v) ↔
      σ r = τ r ∧ ∀ e ∈ inducedEdges D,
        spinAgreementCode (σ e.1) (σ e.2) =
          spinAgreementCode (τ e.1) (τ e.2) := by
  classical
  constructor
  · intro h
    refine ⟨h r hr, ?_⟩
    intro e he
    have heD := Finset.mem_product.mp (Finset.mem_filter.mp he).1
    rw [h e.1 heD.1, h e.2 heD.2]
  · rintro ⟨hroot, hedges⟩
    have step {u v : TreeVertex d} (hu : u ∈ D) (hv : v ∈ D)
        (hadj : treeAdj u v) (heq : σ u = τ u) : σ v = τ v := by
      have hcode : spinAgreementCode (σ u) (σ v) =
          spinAgreementCode (τ u) (τ v) := by
        rcases treeAdj_length hadj with hlen | hlen
        · apply hedges (u, v)
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hadj, by change u.1.length < v.1.length; omega⟩
        · have his : (v, u) ∈ inducedEdges D := by
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_product.mpr ⟨hv, hu⟩, Or.symm hadj, by change v.1.length < u.1.length; omega⟩
          simpa only [spinAgreementCode_comm (σ v) (σ u),
            spinAgreementCode_comm (τ v) (τ u)] using hedges (v, u) his
      rw [heq] at hcode
      exact spinAgreementCode_injective_right (τ u) hcode
    intro v hv
    have hpath := hD.2 r hr v hv
    induction hpath with
    | refl => exact hroot
    | tail hpath hadj ih => exact step hadj.1 hadj.2.1 hadj.2.2 (ih hadj.1)

end Problem367

end

end OAI
