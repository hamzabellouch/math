import OAI.Analysis.InterpolatedFactors.Rotations

namespace OAI

noncomputable section
namespace FreeGroupFactorMain.WeightedCornerIndex
open CircularRotation
abbrev SelfIndex := ℕ ⊕ (Bool ⊕ Bool)
abbrev PairIndex := ℕ ⊕ Fin 3
abbrev Index := PairedIndex SelfIndex PairIndex

inductive Kind where
  | fresh : ℕ → Bool → Bool → Kind
  | residual : Option Bool → Option Bool → Kind
  | diagonal : Bool → Kind
  deriving DecidableEq

namespace Kind

def valid : Kind → Prop
  | .fresh _ r s => ¬(r=false ∧ s=false)
  | .residual r s => ¬(r=none ∧ s=none)
  | .diagonal _ => True

instance (k : Kind) : Decidable k.valid := by cases k <;> unfold valid <;> infer_instance

def transpose : Kind → Kind
  | .fresh n r s => .fresh n s r
  | .residual r s => .residual s r
  | .diagonal r => .diagonal r
end Kind

def endpoints : Fin 3 → Option Bool × Option Bool :=
  Fin.cases (none,some false) (Fin.cases (none,some true) (fun _ => (some false,some true)))

def description : Index → Kind
  | .inl (.inl n) => .fresh n true true
  | .inl (.inr (.inl b)) => .residual (some b) (some b)
  | .inl (.inr (.inr b)) => .diagonal b
  | .inr (.inl n,b) => .fresh n b (!b)
  | .inr (.inr k,false) => .residual (endpoints k).1 (endpoints k).2
  | .inr (.inr k,true) => .residual (endpoints k).2 (endpoints k).1

def indexOf : Kind → Index
  | .fresh n false false => .inl (.inl n)
  | .fresh n false true => .inr (.inl n,false)
  | .fresh n true false => .inr (.inl n,true)
  | .fresh n true true => .inl (.inl n)
  | .residual none none => .inl (.inl 0)
  | .residual none (some false) => .inr (.inr 0,false)
  | .residual (some false) none => .inr (.inr 0,true)
  | .residual none (some true) => .inr (.inr 1,false)
  | .residual (some true) none => .inr (.inr 1,true)
  | .residual (some false) (some true) => .inr (.inr 2,false)
  | .residual (some true) (some false) => .inr (.inr 2,true)
  | .residual (some false) (some false) => .inl (.inr (.inl false))
  | .residual (some true) (some true) => .inl (.inr (.inl true))
  | .diagonal b => .inl (.inr (.inr b))

theorem indexOf_description (i : Index) : indexOf (description i)=i := by
  rcases i with (n | (b | b)) | ⟨(n | k),b⟩
  · rfl
  · cases b <;> rfl
  · rfl
  · cases b <;> rfl
  · fin_cases k <;> cases b <;> rfl

theorem description_injective : Function.Injective description :=
  Function.LeftInverse.injective indexOf_description

theorem description_valid (i : Index) : (description i).valid := by
  rcases i with (n | (b | b)) | ⟨(n | k),b⟩
  · simp [description,Kind.valid]
  · simp [description,Kind.valid]
  · trivial
  · cases b <;> simp [description,Kind.valid]
  · fin_cases k <;> cases b <;> decide

theorem description_indexOf (k : Kind) (hk : k.valid) : description (indexOf k)=k := by
  cases k with
  | fresh n r s =>
      cases r <;> cases s
      all_goals first | exact False.elim (hk ⟨rfl,rfl⟩) | rfl
  | residual r s =>
      rcases r with _|(_|_) <;> rcases s with _|(_|_)
      all_goals first | exact False.elim (hk ⟨rfl,rfl⟩) | rfl
  | diagonal b => rfl

theorem description_flip (i : Index) :
    description (CircularRotation.flip i)=(description i).transpose := by
  rcases i with (n | (b | b)) | ⟨(n | k),b⟩
  · rfl
  · rfl
  · rfl
  · cases b <;> rfl
  · cases b <;> rfl

def reservoirCode : Index × ℕ ≃ ℕ :=
  @Denumerable.eqv _ (Classical.choice (nonempty_denumerable (Index × ℕ)))
end FreeGroupFactorMain.WeightedCornerIndex

end

end OAI
