import OAI.NumberTheory.Ostmann.Arithmetic.HistoryHeightBudgetCost
import OAI.NumberTheory.Ostmann.Construction.HistoryGiantGuard

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryHeightBudgetFixed
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicState HistorySymbolicSlots HistorySymbolicEncoding HistorySymbolicLinearity
variable {ι : Type*}

theorem product_fixedBound {F : ℝ} (hF : 1 ≤ F) (es : List (Expr ι))
    (he : ∀ e ∈ es, e.FixedBound F) : (HistorySymbolicStep.product es).FixedBound F := by
  induction es with
  | nil => simpa [HistorySymbolicStep.product] using hF
  | cons e es ih =>
      exact (Expr.fixedBound_mul F _ _).mpr
        ⟨he e (by simp), ih (fun z hz => he z (by simp [hz]))⟩

theorem product_ofFn_fixedBound {F : ℝ} (hF : 1 ≤ F) {n : ℕ} (f : Fin n → Expr ι)
    (he : ∀ i, (f i).FixedBound F) : (HistorySymbolicStep.product (List.ofFn f)).FixedBound F := by
  apply product_fixedBound hF
  intro e he'
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he'
  exact he i

theorem pivot_fixedBound {F : ℝ} (hF : 1 ≤ F) (s v w : ℤ)
    (plus minus : Expr ι) (u hp hm : List (Expr ι))
    (hs : |(s : ℝ)| ≤ F) (hv : |(v : ℝ)| ≤ F) (hw : |(w : ℝ)| ≤ F)
    (hplus : plus.FixedBound F) (hminus : minus.FixedBound F)
    (hu : ∀ e ∈ u, e.FixedBound F) (hhp : ∀ e ∈ hp, e.FixedBound F)
    (hhm : ∀ e ∈ hm, e.FixedBound F) :
    (HistorySymbolicStep.pivot s v w plus minus u hp hm).FixedBound F := by
  simpa only [HistorySymbolicStep.pivot, Expr.fixedBound_divide, Expr.fixedBound_sub,
    Expr.fixedBound_mul, Expr.fixedBound_fixed] using
    And.intro (And.intro (And.intro hv (And.intro hminus (product_fixedBound hF hm hhm)))
      (And.intro hw (And.intro hplus (product_fixedBound hF hp hhp))))
      (And.intro hs (product_fixedBound hF u hu))

def StateFixedBound (F : ℝ) {a : State} (e : StateExpr a ι) : Prop :=
  e.plus.FixedBound F ∧ e.minus.FixedBound F ∧ ∀ i, (e.small i).FixedBound F

theorem append_fixedBound {F : ℝ} {xs ys : List SmallSlot}
    (f : Fin xs.length → Expr ι) (g : Fin ys.length → Expr ι)
    (hf : ∀ i, (f i).FixedBound F) (hg : ∀ i, (g i).FixedBound F) :
    ∀ i, (append f g i).FixedBound F := by
  intro i
  change (Fin.append f g _).FixedBound F
  refine Fin.addCases (motive := fun j : Fin (xs.length+ys.length) =>
    (Fin.append f g j).FixedBound F) ?_ ?_ _
  · intro j
    simpa only [Fin.append_left] using hf j
  · intro j
    simpa only [Fin.append_right] using hg j

theorem child_fixedBound {F : ℝ} (hF : 1 ≤ F)
    {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ} {a : State}
    {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι)
    (he : StateFixedBound F e) (hc : ∀ i, (comp i).FixedBound F)
    (hf : |(a.frequency : ℝ)| ≤ F)
    (hl : |(left.root.frequency : ℝ)| ≤ F) (hr : |(right.root.frequency : ℝ)| ≤ F) :
    StateFixedBound F (leftState hs e comp) ∧ StateFixedBound F (rightState hs e comp) := by
  have hP := product_ofFn_fixedBound hF (leftPart (splitSlots hs e)) (fun _ => he.2.2 _)
  have hM := product_ofFn_fixedBound hF (rightPart (splitSlots hs e)) (fun _ => he.2.2 _)
  have hU := product_ofFn_fixedBound hF comp hc
  have hPivot : (pivotExpr hs e comp).FixedBound F := by
    simpa only [pivotExpr, HistorySymbolicStep.pivot, Expr.fixedBound_divide,
      Expr.fixedBound_sub, Expr.fixedBound_mul, Expr.fixedBound_fixed] using
      And.intro (And.intro (And.intro hl (And.intro he.2.1 hM))
        (And.intro hr (And.intro he.1 hP))) (And.intro hf hU)
  exact ⟨⟨hPivot,he.1,fun _ => append_fixedBound comp (leftPart (splitSlots hs e)) hc (fun _ => he.2.2 _) _⟩,
    ⟨hPivot,he.2.1,fun _ => append_fixedBound comp (rightPart (splitSlots hs e)) hc (fun _ => he.2.2 _) _⟩⟩

def TreeFixedBound (F : ℝ) : {l : ℕ} → (h : History l) → TreeExpr ι h → Prop
  | _, .leaf _, e => StateFixedBound F e
  | _, .node _ _ _ _ _ left right, e =>
      StateFixedBound F e.1 ∧ TreeFixedBound F left e.2.1 ∧ TreeFixedBound F right e.2.2

theorem root_frequency_mem {l : ℕ} (h : History l) : h.root.frequency ∈ h.frequencies := by
  cases h <;> simp [History.root, History.frequencies]

theorem encode_fixedBound {F : ℝ} (hF : 1 ≤ F) {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι) (he : StateFixedBound F e)
    (hc : ∀ i, (comp i).FixedBound F) (hf : ∀ s ∈ h.frequencies, |(s : ℝ)| ≤ F) :
    TreeFixedBound F h (encode V outside h hs e comp) := by
  induction h with
  | leaf a => exact he
  | @node l a p u hp hm left right ihl ihr =>
      have hchildren := child_fixedBound hF hs e (fun i => comp (Sum.inl i)) he
        (fun i => hc (Sum.inl i)) (hf _ (by simp [History.frequencies]))
        (hf _ (by simp [History.frequencies, root_frequency_mem left]))
        (hf _ (by simp [History.frequencies, root_frequency_mem right]))
      refine ⟨he,?_,?_⟩
      · exact ihl (History.supported_left hs) _ _ hchildren.1
          (fun i => hc (Sum.inr (Sum.inl i)))
          (fun s hmem => hf s (by simp [History.frequencies,hmem]))
      · exact ihr (History.supported_right hs) _ _ hchildren.2
          (fun i => hc (Sum.inr (Sum.inr i)))
          (fun s hmem => hf s (by simp [History.frequencies,hmem]))

def frequencyBound (V : ℕ → ℕ) (l : ℕ) : ℝ :=
  max 1 (((Finset.range (l+1)).sup V : ℕ) : ℝ)

theorem one_le_frequencyBound (V : ℕ → ℕ) (l : ℕ) : 1 ≤ frequencyBound V l := le_max_left _ _

theorem supported_frequencyBound {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) :
    ∀ s ∈ h.frequencies, |(s : ℝ)| ≤ frequencyBound V l := by
  intro s hmem
  obtain ⟨_,j,hjl,hj⟩ := History.supported_frequency_bounds hs s hmem
  have hmax : V j ≤ (Finset.range (l+1)).sup V :=
    Finset.le_sup (f := V) (Finset.mem_range.mpr (by omega))
  have hcast : (s.natAbs : ℝ) ≤ (((Finset.range (l+1)).sup V : ℕ) : ℝ) := by exact_mod_cast hj.trans hmax
  have hsabs : (s.natAbs : ℝ) = |(s : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hsabs] at hcast
  exact hcast.trans (le_max_right (1 : ℝ) _)

theorem symbolicHistory_fixedBound {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) :
    TreeFixedBound (frequencyBound V l) h (symbolicHistory h hs) := by
  apply encode_fixedBound (one_le_frequencyBound V l)
  · exact ⟨Expr.fixedBound_atom _ _,Expr.fixedBound_atom _ _,fun _ => Expr.fixedBound_atom _ _⟩
  · exact fun _ => Expr.fixedBound_atom _ _
  · exact supported_frequencyBound h hs

theorem coefficientHistory_fixedBound {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (second : Bool) :
    TreeFixedBound (frequencyBound V l) h (coefficientHistory h hs second) := by
  apply encode_fixedBound (one_le_frequencyBound V l)
  · have hF := one_le_frequencyBound V l
    have hF0 : (0 : ℝ) ≤ frequencyBound V l := by linarith
    cases second <;> simp [StateFixedBound,coefficientRoot,rootExpr,hF,hF0]
  · exact fun _ => Expr.fixedBound_atom _ _
  · exact supported_frequencyBound h hs

end Ostmann.Arithmetic.HistoryHeightBudgetFixed

end

end OAI
