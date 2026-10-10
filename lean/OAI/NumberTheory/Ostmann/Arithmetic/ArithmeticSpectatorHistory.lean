import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticSpectatorNode
import OAI.NumberTheory.Ostmann.Construction.TransferConjugations
import OAI.NumberTheory.Ostmann.Tree.RationalTreeLeaves

namespace OAI

/-! # From reconstructed integer histories to the spectator tree

The realization conditions record the two child products and the terminal
modulus. They allow composite inserted pivots: division by the compensation
unit gives the giant used by the rational tree. No prime law is assigned to
that composite integer.
-/

namespace Ostmann
open scoped Classical ComplexConjugate

noncomputable def spectatorHistoryLeaf {State : Type*} {q : ℕ} [Fact q.Prime]
    (modulus : State → ℕ) (g : ZMod q → ℂ) (D : (ZMod q)ˣ) (σ : State) (s : ℤ) : ℂ :=
  g ((s : ZMod q) / ((D : ZMod q) * (modulus σ : ZMod q)))

noncomputable def spectatorHistoryCutoff {State : Type*} {q : ℕ} [Fact q.Prime]
    (sys : TransferHistorySystem State) (σ : State) (s v w : ℤ) : ℝ :=
  if (historyPivot sys σ s v w : ZMod q) = 0 then 0 else 1

noncomputable def spectatorHistoryWeight {State : Type*} {q : ℕ} [Fact q.Prime]
    (sys : TransferHistorySystem State) (modulus : State → ℕ)
    (g : ZMod q → ℂ) (D : (ZMod q)ˣ) (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) : ℂ :=
  recursiveTransferWeight sys (spectatorHistoryLeaf modulus g D)
    (spectatorHistoryCutoff (q := q) sys) n σ t

def SpectatorHistoryRealizes {State : Type*} {q : ℕ} [Fact q.Prime]
    (sys : TransferHistorySystem State) (modulus : State → ℕ) :
    {n : ℕ} → {C : (ZMod q)ˣ} → RationalTreeData (ZMod q)ˣ n C →
      State → FrequencyTree ℤ n → (ZMod q)ˣ → (ZMod q)ˣ → TreeLeafTuple (ZMod q)ˣ n → Prop
  | _, _, .leaf s C, σ, t, XL, XR, x =>
      ((frequencyRoot (A := ℤ) 0 t : ℤ) : ZMod q) = s ∧
        (modulus σ : ZMod q) = (XL * XR * C * treeLeafProduct 0 x : (ZMod q)ˣ)
  | n + 1, _, .node s CL CR u left right, σ, t, XL, XR, x =>
      let v := frequencyRoot n t.2.1
      let w := frequencyRoot n t.2.2
      let P := historyPivot sys σ t.1 v w
      ValidTransferNode sys σ t.1 v w P ∧
      (t.1 : ZMod q) = s ∧ (v : ZMod q) = left.frequency ∧ (w : ZMod q) = right.frequency ∧
      (sys.leftProduct σ : ZMod q) = (XL * CL * treeLeafProduct n x.1 : (ZMod q)ˣ) ∧
      (sys.rightProduct σ : ZMod q) = (XR * CR * treeLeafProduct n x.2 : (ZMod q)ˣ) ∧
      ∀ h : (P : ZMod q) ≠ 0,
        SpectatorHistoryRealizes sys modulus left (sys.leftState σ P) t.2.1
          (Units.mk0 (P : ZMod q) h / u) XL x.1 ∧
        SpectatorHistoryRealizes sys modulus right (sys.rightState σ P) t.2.2
          (Units.mk0 (P : ZMod q) h / u) XR x.2

theorem spectatorHistoryWeight_eq_tree {State : Type*} {q : ℕ} [Fact q.Prime]
    (sys : TransferHistorySystem State) (modulus : State → ℕ)
    (g : ZMod q → ℂ) (D : (ZMod q)ˣ)
    {n : ℕ} {C : (ZMod q)ˣ} (T : RationalTreeData (ZMod q)ˣ n C)
    (σ : State) (t : FrequencyTree ℤ n) (XL XR : (ZMod q)ˣ)
    (x : TreeLeafTuple (ZMod q)ˣ n)
    (h : SpectatorHistoryRealizes sys modulus T σ t XL XR x) (b : Bool) :
    (if b then conj (spectatorHistoryWeight sys modulus g D n σ t)
      else spectatorHistoryWeight sys modulus g D n σ t) =
      rationalTreeAmplitude g D T XL XR (transferConjugations n b) x := by
  induction T generalizing σ XL XR b with
  | leaf s C =>
    rcases h with ⟨hs, hM⟩
    have ha : ((frequencyRoot (A := ℤ) 0 t : ℤ) : ZMod q) / ((D : ZMod q) * (modulus σ : ZMod q)) =
        (rationalTreeArgument s C D XL XR x : ZMod q) := by
      rw [hs, hM]
      simp only [rationalTreeArgument, Units.val_div_eq_div_val, Units.val_mul]
      apply congrArg (fun z : ZMod q => (s : ZMod q) / z)
      dsimp only [treeLeafProduct]
      ring
    cases b with
    | false => exact congrArg g ha
    | true => exact congrArg star (congrArg g ha)
  | @node n s CL CR u left right ihL ihR =>
    rcases h with ⟨hvalid, hs, hv, hw, hL, hR, hchild⟩
    let P := historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    let V := reconstructedEntry (s : ZMod q) left.frequency right.frequency u
      ((XL * CL * treeLeafProduct n x.1 : (ZMod q)ˣ) : ZMod q)
      ((XR * CR * treeLeafProduct n x.2 : (ZMod q)ˣ) : ZMod q)
    have hs0 : (t.1 : ZMod q) ≠ 0 := by rw [hs]; exact Units.ne_zero s
    have hV : V = (P : ZMod q) / u := by
      dsimp only [V]
      rw [← hs, ← hv, ← hw, ← hL, ← hR]
      exact hvalid.spectator_composite_reconstruction u hs0
    have hW := recursiveTransferWeight_node sys (spectatorHistoryLeaf modulus g D)
      (spectatorHistoryCutoff (q := q) sys) n σ t P hvalid
    change (if b then conj _ else _) = _
    by_cases hp : (P : ZMod q) = 0
    · have hV0 : V = 0 := by rw [hV, hp, zero_div]
      have hweight : spectatorHistoryWeight sys modulus g D (n + 1) σ t = 0 := by
        unfold spectatorHistoryWeight
        rw [hW]
        simp only [spectatorHistoryCutoff, show (historyPivot sys σ t.1
          (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) : ZMod q) = 0 from hp,
          ↓reduceIte, Complex.ofReal_zero, zero_mul]
      simp only [hweight, map_zero, ite_self, rationalTreeAmplitude, transferConjugations]
      change 0 = if hv : V = 0 then 0 else _
      rw [dite_eq_left hV0]
    · have hV0 : V ≠ 0 := by rw [hV]; exact div_ne_zero hp (Units.ne_zero u)
      have hunit : Units.mk0 V hV0 = Units.mk0 (P : ZMod q) hp / u := by
        apply Units.ext
        simpa only [Units.val_mk0, Units.val_div_eq_div_val] using hV
      have hweight : spectatorHistoryWeight sys modulus g D (n + 1) σ t =
          spectatorHistoryWeight sys modulus g D n (sys.leftState σ P) t.2.1 *
            conj (spectatorHistoryWeight sys modulus g D n (sys.rightState σ P) t.2.2) := by
        unfold spectatorHistoryWeight
        rw [hW]
        simp only [spectatorHistoryCutoff, show (historyPivot sys σ t.1
          (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) : ZMod q) ≠ 0 from hp,
          ↓reduceIte, Complex.ofReal_one, one_mul, Complex.star_def]
      have hl := ihL (sys.leftState σ P) t.2.1
        (Units.mk0 (P : ZMod q) hp / u) XL x.1 (hchild hp).1 b
      have hr := ihR (sys.rightState σ P) t.2.2
        (Units.mk0 (P : ZMod q) hp / u) XR x.2 (hchild hp).2 (!b)
      rw [hweight]
      simp only [rationalTreeAmplitude, transferConjugations]
      change _ = if hv : V = 0 then 0 else _
      rw [dite_eq_right hV0, hunit, ← hl, ← hr]
      cases b <;> simp

end Ostmann

end OAI
