import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelOutput
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedRawBlock
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialReindex

namespace OAI

/-! Conversion of the actual ordered sparse labels into the literal raw
X/Z instructions, including the explicit finite relabeling of their energy. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelTable
open scoped BigOperators Classical

variable {ι κ : Type} {n m : ℕ}

def numberedSites (q : Fin n ≃ ι) (e : Fin m ≃ κ) (xs : κ → List ι) :
    Fin m → List (Fin n) := fun a => (xs (e a)).map q.symm

def numberedWord (q : Fin n ≃ ι) (e : Fin m ≃ κ) (w : κ → ι → Fin 4) :
    Fin m → Fin n → Fin 4 := fun a i => w (e a) (q i)

private theorem tag_numbered (q : Fin n ≃ ι) (xs : List ι) (w : ι → Fin 4) :
    QuantumOrderedLabelData.tag (index q) xs w =
      ((xs.map q.symm).map (fun i => (i.val,(w (q i)).val))) := by
  simp only [QuantumOrderedLabelData.tag,List.map_map,Function.comp_def,
    Equiv.apply_symm_apply,index]

theorem packed_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ) :
    (table e (index q) xs w J).map QuantumOrderedRawPacking.value =
      QuantumRawExchange.packed (QuantumOrderedRawBlock.terms
        (numberedSites q e xs) (numberedWord q e w)) (fun i => J (e i)) := by
  simp only [table,List.map_ofFn,Function.comp_def,QuantumRawExchange.packed]
  apply congrArg List.ofFn
  funext i
  rw [tag_numbered]
  exact QuantumOrderedRawPacking.value_pack _ _ _

variable [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem numbered_sites_length (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (i : Fin m) :
    (numberedSites q e xs i).length=(xs (e i)).length := List.length_map _

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem numbered_sites_nodup (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (hx : ∀ a, (xs a).Nodup) (i : Fin m) :
    (numberedSites q e xs i).Nodup := (hx (e i)).map q.symm.injective

omit [DecidableEq ι] [Fintype κ] in
theorem numbered_support (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (w : κ → ι → Fin 4) (i : Fin m) :
    qmaPauliSupport (numberedWord q e w i)=
      (qmaPauliSupport (w (e i))).map q.symm.toEmbedding :=
  qmaPauliSupport_relabel q.symm (w (e i))

omit [Fintype κ] in
theorem numbered_cover (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hs : ∀ a, qmaPauliSupport (w a) ⊆ (xs a).toFinset) (i : Fin m) :
    qmaPauliSupport (numberedWord q e w i) ⊆ (numberedSites q e xs i).toFinset := by
  rw [numbered_support]
  intro j hj
  obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hj
  exact List.mem_toFinset.mpr (List.mem_map.mpr
    ⟨a,List.mem_toFinset.mp (hs (e i) ha),rfl⟩)

omit [DecidableEq ι] [Fintype κ] in
theorem numbered_private (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (w : κ → ι → Fin 4)
    (hp : ∀ a b, (qmaPauliSupport (w a)).card=2 →
      qmaPauliSupport (w a)=qmaPauliSupport (w b) → a=b)
    (i j : Fin m) (hi : (qmaPauliSupport (numberedWord q e w i)).card=2)
    (hij : qmaPauliSupport (numberedWord q e w i)=
      qmaPauliSupport (numberedWord q e w j)) : i=j := by
  apply e.injective
  apply hp (e i) (e j)
  · simpa only [numbered_support,Finset.card_map] using hi
  · rw [numbered_support,numbered_support] at hij
    exact (Finset.map_injective q.symm.toEmbedding) hij

theorem numbered_energy (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (w : κ → ι → Fin 4) (J : κ → ℝ) :
    MediatorGraph.normalizedBottom (qmaPauliFamily (numberedWord q e w) (fun i => J (e i))) =
      MediatorGraph.normalizedBottom (qmaPauliFamily w J) := by
  have hw (i : Fin m) : qmaPauliWord (numberedWord q e w i) =
      (qmaPauliWord (w (e i))).submatrix
        (qmaQubitBasisEquiv q.symm) (qmaQubitBasisEquiv q.symm) :=
    qmaPauliWord_relabel q.symm (w (e i))
  have hm : qmaPauliFamily (numberedWord q e w) (fun i => J (e i)) =
      (qmaPauliFamily w J).submatrix
        (qmaQubitBasisEquiv q.symm) (qmaQubitBasisEquiv q.symm) := by
    ext s t
    simp only [qmaPauliFamily,Matrix.sum_apply,Matrix.smul_apply,
      Matrix.submatrix_apply,hw,smul_eq_mul]
    exact e.sum_comp (fun a => (J a:ℂ)*
      qmaPauliWord (w a) (qmaQubitBasisEquiv q.symm s) (qmaQubitBasisEquiv q.symm t))
  rw [hm]
  exact MediatorGraph.normalizedBottom_reindex (qmaQubitBasisEquiv q.symm) _

end ContinuumCoulomb.QuantumOrderedLabelTable

end

end OAI
