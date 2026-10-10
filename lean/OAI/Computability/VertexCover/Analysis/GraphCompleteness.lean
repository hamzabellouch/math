import Mathlib
import OAI.Computability.VertexCover.Analysis.MidpointGridTail

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover
noncomputable section

 theorem finiteMean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : finiteMean (fun x => f (e x)) = finiteMean f := by
  unfold finiteMean
  rw [e.sum_comp f, Fintype.card_congr e]

 theorem finiteMean_product {α β : Type*} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    finiteMean f = finiteMean (fun x => finiteMean (fun y => f (x,y))) := by
  simp only [finiteMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

 theorem finiteMean_product_fst {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (f : α → ℝ) : finiteMean (fun x : α × β => f x.1) = finiteMean f := by
  rw [finiteMean_product]
  simp only [finiteMean_const]

def splitSelected {ι κ α : Type*} [DecidableEq κ] (slot : ι → κ) :
    (ι → κ → α) ≃ (ι → α) × ((i : ι) → {k : κ // k ≠ slot i} → α) where
  toFun w := (fun i => w i (slot i), fun i k => w i k.1)
  invFun v i k := if h : k = slot i then v.1 i else v.2 i ⟨k,h⟩
  left_inv w := by funext i k; dsimp; split_ifs with h <;> simp_all
  right_inv v := by
    apply Prod.ext
    · funext i; simp
    · funext i k; simp [k.2]

 theorem finiteMean_selected {ι κ α : Type*} [Fintype ι] [Fintype κ] [Fintype α]
    [DecidableEq ι] [DecidableEq κ] [Nonempty α] (slot : ι → κ) (f : (ι → α) → ℝ) :
    finiteMean (fun w : ι → κ → α => f (fun i => w i (slot i))) = finiteMean f := by
  classical
  calc
    _ = finiteMean (fun v : (ι → α) × ((i : ι) → {k : κ // k ≠ slot i} → α) => f v.1) :=
      finiteMean_equiv (splitSelected slot) (fun v => f v.1)
    _ = _ := finiteMean_product_fst f

 theorem finiteMean_truthValue {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    finiteMean (fun x => truthValue (P x)) =
      ((Finset.univ.filter P).card : ℝ) / Fintype.card α := by
  classical
  unfold finiteMean truthValue
  congr 1
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hp : P x <;> simp [hp]

end
end VertexCover

namespace VertexCover.LabelCover
noncomputable section

 theorem gridRational_real (d : ℕ) (u : Fin (2*d+1)) :
    (gridRational d u : ℝ) = FiniteAntiConcentration.grid d u := by
  unfold gridRational FiniteAntiConcentration.grid
  push_cast
  rfl

 theorem honestSum_density (Φ : LabelCover) (d t : ℕ) (A : Φ.Labeling)
    (hA : ∀ e, Φ.Satisfies A e) :
    finiteMean (fun v : Φ.Vertex d => truthValue ((t:ℝ) < Φ.honestSum A hA v)) =
      FiniteAntiConcentration.gridTailDensity d d t := by
  classical
  let : Nonempty (Φ.Seeds d) := ⟨fun _ => ⟨0, Φ.M_pos⟩⟩
  rw [finiteMean_product]
  have hf (seed : Φ.Seeds d) :
      finiteMean (fun w : Fin d → Fin (Φ.WeightDimension d) → Fin (2*d+1) =>
        truthValue ((t:ℝ) < Φ.honestSum A hA (seed,w))) =
      FiniteAntiConcentration.gridTailDensity d d t := by
    unfold honestSum
    simp only [gridRational_real]
    rw [finiteMean_selected
      (fun j => (Φ.query seed j).slot (Φ.localOfSatisfying A hA (Φ.query seed j)))
      (fun x : Fin d → Fin (2*d+1) => truthValue ((t:ℝ) < ∑ i, FiniteAntiConcentration.grid d (x i)))]
    rw [finiteMean_truthValue]
    simp only [FiniteAntiConcentration.gridTailDensity, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  simp only [hf, finiteMean_const]

 theorem graph_completeness (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (A : Φ.Labeling) (hA : ∀ e, Φ.Satisfies A e) :
    ∃ I : Finset (Φ.Vertex (Parameters.d m)),
      (Φ.graph (Parameters.d m) (Parameters.t m)).IsIndepSet (I : Set (Φ.Vertex (Parameters.d m))) ∧
      ((1:ℝ)/2-1/(m:ℝ)) * Fintype.card (Φ.Vertex (Parameters.d m)) < I.card := by
  classical
  let I : Finset (Φ.Vertex (Parameters.d m)) :=
    Finset.univ.filter (fun v => (Parameters.t m : ℝ) < Φ.honestSum A hA v)
  refine ⟨I, ?_, ?_⟩
  · have he : (I : Set (Φ.Vertex (Parameters.d m))) = {v | (Parameters.t m : ℝ) < Φ.honestSum A hA v} := by
      ext v
      simp [I]
    rw [he]
    exact Φ.honest_large_sum_independent _ A hA
  · have htail := Parameters.midpoint_grid_tail m hm
    have hdense := Φ.honestSum_density (Parameters.d m) (Parameters.t m) A hA
    rw [finiteMean_truthValue] at hdense
    have hfinal : (1:ℝ)/2-1/(m:ℝ) <
        (I.card : ℝ) / Fintype.card (Φ.Vertex (Parameters.d m)) := by
      rw [hdense]
      exact htail.2.trans htail.1
    have hn : 0 < Fintype.card (Φ.Vertex (Parameters.d m)) := by
      rw [Φ.vertex_card]
      exact Nat.mul_pos (Nat.pow_pos Φ.M_pos) (Nat.pow_pos (by omega))
    exact (lt_div_iff₀ (Nat.cast_pos.mpr hn)).mp hfinal

 theorem graph_completeness_cover (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (A : Φ.Labeling) (hA : ∀ e, Φ.Satisfies A e) :
    ∃ C : Finset (Φ.Vertex (Parameters.d m)),
      (Φ.graph (Parameters.d m) (Parameters.t m)).IsVertexCover (C : Set (Φ.Vertex (Parameters.d m))) ∧
      (C.card : ℝ) < ((1:ℝ)/2+1/(m:ℝ)) * Fintype.card (Φ.Vertex (Parameters.d m)) := by
  classical
  obtain ⟨I, hI, hcard⟩ := Φ.graph_completeness m hm A hA
  refine ⟨Iᶜ, ?_, ?_⟩
  · simpa only [Finset.coe_compl] using SimpleGraph.isVertexCover_compl.mpr hI
  · have hn := Finset.card_le_univ I
    rw [Finset.card_compl, Nat.cast_sub hn]
    nlinarith

end
end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
