import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section

namespace Problem336

@[simp] theorem relabelGraph_refl (G : GraphCode) :
    relabelGraph (Equiv.refl ℕ) G = G := by
  apply Subtype.ext
  rfl

@[simp] theorem relabelLabels_refl (U : ℕ → ℝ) :
    relabelLabels (Equiv.refl ℕ) U = U := rfl

@[simp] theorem relabelGraph_trans (σ τ : Equiv ℕ ℕ) (G : GraphCode) :
    relabelGraph (σ.trans τ) G = relabelGraph τ (relabelGraph σ G) := by
  apply Subtype.ext
  rfl

@[simp] theorem relabelLabels_trans (σ τ : Equiv ℕ ℕ) (U : ℕ → ℝ) :
    relabelLabels (σ.trans τ) U = relabelLabels τ (relabelLabels σ U) := rfl

@[simp] theorem relabelGraph_symm (σ : Equiv ℕ ℕ) (G : GraphCode) :
    relabelGraph σ.symm (relabelGraph σ G) = G := by
  apply Subtype.ext
  funext u v
  simp [relabelGraph]

@[simp] theorem relabelLabels_symm (σ : Equiv ℕ ℕ) (U : ℕ → ℝ) :
    relabelLabels σ.symm (relabelLabels σ U) = U := by
  funext u
  simp [relabelLabels]

@[simp] theorem adj_relabelGraph (σ : Equiv ℕ ℕ) (G : GraphCode) (u v : ℕ) :
    Adj (relabelGraph σ G) u v ↔ Adj G (σ.symm u) (σ.symm v) := Iff.rfl

@[simp] theorem adj_relabelGraph_apply (σ : Equiv ℕ ℕ) (G : GraphCode) (u v : ℕ) :
    Adj (relabelGraph σ G) (σ u) (σ v) ↔ Adj G u v := by
  simp

theorem relabelGraph_reachable (σ : Equiv ℕ ℕ) (G : GraphCode)
    {u v : ℕ} (h : Relation.ReflTransGen (Adj G) u v) :
    Relation.ReflTransGen (Adj (relabelGraph σ G)) (σ u) (σ v) := by
  exact Relation.ReflTransGen.lift σ
    (fun a b hab => (adj_relabelGraph_apply σ G a b).2 hab) u v h

theorem GraphConnected.relabel (σ : Equiv ℕ ℕ) {G : GraphCode}
    (h : GraphConnected G) : GraphConnected (relabelGraph σ G) := by
  intro u v
  simpa only [Equiv.apply_symm_apply] using relabelGraph_reachable σ G (h (σ.symm u) (σ.symm v))

@[simp] theorem graphConnected_relabelGraph_iff (σ : Equiv ℕ ℕ) (G : GraphCode) :
    GraphConnected (relabelGraph σ G) ↔ GraphConnected G := by
  constructor
  · intro h
    simpa using h.relabel σ.symm
  · exact GraphConnected.relabel σ

theorem GraphLocallyFinite.relabel (σ : Equiv ℕ ℕ) {G : GraphCode}
    (h : GraphLocallyFinite G) : GraphLocallyFinite (relabelGraph σ G) := by
  intro u
  exact (h (σ.symm u)).preimage σ.symm.injective.injOn

@[simp] theorem graphLocallyFinite_relabelGraph_iff (σ : Equiv ℕ ℕ) (G : GraphCode) :
    GraphLocallyFinite (relabelGraph σ G) ↔ GraphLocallyFinite G := by
  constructor
  · intro h
    simpa using h.relabel σ.symm
  · exact GraphLocallyFinite.relabel σ

theorem measurable_relabelGraph (σ : Equiv ℕ ℕ) : Measurable (relabelGraph σ) := by
  apply Measurable.subtype_mk
  apply Measurable.of_eval
  intro u
  apply Measurable.of_eval
  intro v
  exact (measurable_pi_apply (σ.symm v)).comp
    ((measurable_pi_apply (σ.symm u)).comp measurable_subtype_coe)

theorem measurable_relabelLabels (σ : Equiv ℕ ℕ) : Measurable (relabelLabels σ) := by
  apply Measurable.of_eval
  intro u
  exact measurable_pi_apply (σ.symm u)

end Problem336

end

end OAI
