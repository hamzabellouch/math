import OAI.NumberTheory.Ostmann.Characters.BinaryExposureTree
import OAI.NumberTheory.Ostmann.Characters.PairedFrequencyProbability

namespace OAI

noncomputable section
namespace Ostmann.Characters.FrequencyExposure
open Arithmetic.FrequencyMultiplicity
open BinaryExposure

structure Data (Q:ℕ) where
  s : ℤ
  s' : ℤ
  v : ℤ
  w : ℤ
  v' : ℤ
  w' : ℤ
  divides : s.natAbs∣Q
  divides' : s'.natAbs∣Q

structure Coefficients {Q:ℕ} (H:Type*) (d:Data Q) where
  A : H→(ZMod Q)ˣ→(ZMod d.s.natAbs)ˣ
  B : H→(ZMod Q)ˣ→(ZMod d.s.natAbs)ˣ
  A' : H→(ZMod Q)ˣ→(ZMod d.s'.natAbs)ˣ
  B' : H→(ZMod Q)ˣ→(ZMod d.s'.natAbs)ˣ

variable {Q:ℕ} {H:Type*}

def constraint (d:List Bool→Data Q) (a:∀p,Coefficients H (d p))
    (_k:ℕ) (h:List Bool×H) (t x:(ZMod Q)ˣ) : Prop :=
  rawSplitConstraint (d h.1).s.natAbs (d h.1).v (d h.1).w
    ((a h.1).A h.2 t) ((a h.1).B h.2 t)
    (ZMod.unitsMap (d h.1).divides t) (ZMod.unitsMap (d h.1).divides x) ∧
  rawSplitConstraint (d h.1).s'.natAbs (d h.1).v' (d h.1).w'
    ((a h.1).A' h.2 t) ((a h.1).B' h.2 t)
    (ZMod.unitsMap (d h.1).divides' t) (ZMod.unitsMap (d h.1).divides' x)

def update (b:Bool) (f:List Bool→H→(ZMod Q)ˣ→(ZMod Q)ˣ→H)
    (_k:ℕ) (h:List Bool×H) (t x:(ZMod Q)ˣ) : List Bool×H :=
  (b::h.1,f h.1 h.2 t x)

def reducedPair (d:Data Q) : ℕ :=
  (reducedModulus d.v d.w d.s).lcm (reducedModulus d.v' d.w' d.s')

def budget (C:NNReal) (ε:ℝ) (d:List Bool→Data Q) :
    (k:ℕ)→List Bool→Budget k
  | 0,_ => PUnit.unit
  | k+1,p => (⟨(C:ℝ)*(reducedPair (d p):ℝ)^(ε-1),by positivity⟩,
      budget C ε d k (false::p), budget C ε d k (true::p))

theorem paired_frequency_tree_count (ε:ℝ) (hε:0<ε) :
    ∃ C:NNReal, 0<C ∧ ∀ Q:ℕ, ∀ [NeZero Q], ∀ H:Type*,
      ∀ d:List Bool→Data Q, ∀ a:∀p,Coefficients H (d p),
      ∀ left right:List Bool→H→(ZMod Q)ˣ→(ZMod Q)ˣ→H,
      ∀ k p h t,
      (Nat.card {z:BinaryHaar.Splits (ZMod Q)ˣ k //
        admissible (constraint d a) (update false left) (update true right) k (p,h) t z}:ℝ)/
        Nat.card (BinaryHaar.Splits (ZMod Q)ˣ k) ≤
      ((budget C ε d k p).value:ℝ) := by
  obtain ⟨C,hC,hlocal⟩ := paired_frequency_split_probability_le_rpow ε hε
  let C' : NNReal := ⟨C,hC.le⟩
  refine ⟨C',hC,?_⟩
  intro Q _ H d a left right k p h t
  apply count_le_tree
  have hc : ∀ k p h t,
      Controlled (constraint d a) (update false left) (update true right)
        k (p,h) t (budget C' ε d k p) := by
    intro k
    induction k with
    | zero => intros; trivial
    | succ k ih =>
      intro p h t
      constructor
      · exact hlocal Q (d p).s (d p).s' (d p).v (d p).w (d p).v' (d p).w'
          (d p).divides (d p).divides'
          ((a p).A h t) ((a p).B h t) ((a p).A' h t) ((a p).B' h t) t
      · intro x
        exact ⟨ih _ _ _,ih _ _ _⟩
  exact hc k p h t

end Ostmann.Characters.FrequencyExposure

end

end OAI
