import Mathlib
import OAI.Geometry.HyperbolicGroups.GenericTable

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B A : Type*} [DecidableEq F]

/-- Actual amalgamated fields: one copy in U, one copy per branch outside U. -/
abbrev Var (U : Finset F) := U ⊕ (B × {f : F // f ∉ U})

/-- Actual amalgamated row positions; all positions still refer to the original
arrays, not to newly independent copies of an array. -/
abbrev Pos (support : R → Finset F) (U : Finset F) :=
  {r : R // support r ⊆ U} ⊕ (B × {r : R // ¬support r ⊆ U})

def coord (U : Finset F) (j : B) (f : F) : Var (B := B) U :=
  if h : f ∈ U then Sum.inl ⟨f,h⟩ else Sum.inr (j,⟨f,h⟩)

def field (U : Finset F) : Var (B := B) U → F
  | .inl f => f.val
  | .inr jf => jf.2.val

@[simp] lemma field_coord (U : Finset F) (j : B) (f : F) : field U (coord U j f) = f := by
  unfold coord
  split_ifs <;> rfl

lemma coord_injective (U : Finset F) (j : B) : Function.Injective (coord U j) := by
  intro f g h
  simpa using congrArg (field U) h

@[simp] lemma coord_in (U : Finset F) (j : B) (f : U) :
    coord U j f.val = Sum.inl f := by simp [coord, f.property]

@[simp] lemma coord_out (U : Finset F) (j : B) (f : {f : F // f ∉ U}) :
    coord U j f.val = Sum.inr (j,f) := by simp [coord, f.property]

def array (support : R → Finset F) (U : Finset F) : Pos (B := B) support U → R
  | .inl r => r.val
  | .inr jr => jr.2.val

def branch [Nonempty B] (support : R → Finset F) (U : Finset F) : Pos (B := B) support U → B
  | .inl _ => Classical.choice inferInstance
  | .inr jr => jr.1

def row [Nonempty B] (support : R → Finset F) (U : Finset F)
    (σ : Var (B := B) U → A) (s : Pos (B := B) support U) : TableModel.Entry (A := A) support :=
  ⟨array support U s, fun f => σ (coord U (branch support U s) f.val)⟩

def rowSupport [Nonempty B] [DecidableEq B] (support : R → Finset F) (U : Finset F)
    (s : Pos (B := B) support U) : Finset (Var (B := B) U) :=
  (support (array support U s)).image (coord U (branch support U s))

lemma read_row [Nonempty B] [DecidableEq B] (support : R → Finset F) (U : Finset F)
    (σ τ : Var (B := B) U → A) (s : Pos (B := B) support U)
    (h : row support U σ s = row support U τ s) :
    ∀ v ∈ rowSupport support U s, σ v = τ v := by
  intro v hv
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hv
  have he : (fun f : support (array support U s) => σ (coord U (branch support U s) f.val)) =
      (fun f : support (array support U s) => τ (coord U (branch support U s) f.val)) := by
    exact eq_of_heq (Sigma.mk.inj h).2
  exact congrFun he ⟨f,hf⟩

/-- The only injectivity imposed is within one field across branches. -/
def InjectiveFields (U : Finset F) (σ : Var (B := B) U → A) : Prop :=
  ∀ f : {f : F // f ∉ U}, Function.Injective (fun j => σ (Sum.inr (j,f)))

instance [Fintype F] [Fintype B] [DecidableEq B] [DecidableEq A]
    (U : Finset F) (σ : Var (B := B) U → A) : Decidable (InjectiveFields U σ) :=
  inferInstanceAs (Decidable (∀ field : {f : F // f ∉ U}, ∀ branch other,
    σ (Sum.inr (branch, field)) = σ (Sum.inr (other, field)) → branch = other))

lemma row_injective [Nonempty B] (support : R → Finset F) (U : Finset F)
    (σ : Var (B := B) U → A) (hσ : InjectiveFields U σ) :
    Function.Injective (row support U σ) := by
  intro s t he
  have ha : array support U s = array support U t := congrArg Sigma.fst he
  cases s with
  | inl r =>
    cases t with
    | inl q => exact congrArg Sum.inl (Subtype.ext ha)
    | inr jq => exact False.elim (jq.2.property ((show r.val = jq.2.val from ha) ▸ r.property))
  | inr jr =>
    cases t with
    | inl q => exact False.elim (jr.2.property ((show q.val = jr.2.val from ha.symm) ▸ q.property))
    | inr kq =>
      obtain ⟨j,r⟩ := jr
      obtain ⟨k,q⟩ := kq
      have hrq : r = q := Subtype.ext ha
      subst q
      have hf : ∃ f ∈ support r.val, f ∉ U := by simpa [Finset.subset_iff] using r.property
      obtain ⟨f,hf,hfu⟩ := hf
      have he' : (fun f : support r.val => σ (coord U j f.val)) =
          (fun f : support r.val => σ (coord U k f.val)) := eq_of_heq (Sigma.mk.inj he).2
      have hk := congrFun he' ⟨f,hf⟩
      have hjk : j = k := hσ ⟨f,hfu⟩ (by simpa [coord,hfu] using hk)
      subst k
      rfl

/-- Every actual branch is a master match exactly when every amalgamated row
trial is present. This identity permits the later coupling on actual matches. -/
lemma present_iff [Nonempty B] (support : R → Finset F) (U : Finset F)
    (σ : Var (B := B) U → A) (w : TableModel.Entry (A := A) support → Bool) :
    BernoulliCandidates.Present (row support U) w σ ↔
      ∀ j : B, TableModel.IsMatch support w (fun f => σ (coord U j f)) := by
  constructor
  · intro h j r
    by_cases hr : support r ⊆ U
    · have he : row support U σ (Sum.inl ⟨r,hr⟩) =
          TableModel.row support (fun f => σ (coord U j f)) r := by
        dsimp [row,TableModel.row,array,branch]
        congr 1
        funext f
        simp [coord,hr f.property]
      rw [← he]
      exact h _
    · exact h (Sum.inr (j,⟨r,hr⟩))
  · intro h s
    exact h (branch support U s) (array support U s)

end StarModel
end HyperbolicObstruction
end
end

section

end
end

end OAI
