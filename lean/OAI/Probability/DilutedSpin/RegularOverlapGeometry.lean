import OAI.Probability.DilutedSpin.OverlapDepthAverage

namespace OAI

section
namespace DilutedSpinGlass.ReducedTopology
open DepthAverage
noncomputable local instance regularOverlapGeometryDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type
noncomputable local instance regularOverlapGeometryPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {L : ℕ} [NeZero L]

def regularOverlapDomain (S : ReducedTopology) (L : ℕ) [NeZero L] (η : ℝ)
    (q : S.Vertex → Fin L) : Prop :=
  Regular η q ∧ Admissible S (fun v => (q v).val) 0 L

lemma admissible_of_all_lower (S : ReducedTopology) (q : S.Vertex → ℕ) {lo lo' hi : ℕ}
    (h : Admissible S q lo hi) (hl : ∀ v, lo'≤q v) : Admissible S q lo' hi := by
  cases S with
  | leaf => trivial
  | node k hk C => exact ⟨hl none,h.2⟩

omit [NeZero L] in
lemma regular_prepend {α : Type} {η : ℝ} (hη : 0<η) (hη1 : η≤1)
    (q : α → Fin L) (hq : Regular η q) (d : Fin L)
    (hlo : η/4<normalized d) (hhi : normalized d≤η/2) :
    Regular (η/8) (fun i : Option α => i.elim d q) := by
  constructor
  · intro i
    cases i with
    | none => simp only [Option.elim_none]; constructor <;> linarith
    | some i => simpa only [Option.elim_some] using
        (show η/8<normalized (q i) ∧ normalized (q i)<1-η/8 by have := hq.1 i; constructor <;> linarith)
  · intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j =>
        simp only [Option.elim_none,Option.elim_some]
        have hj := (hq.1 j).1
        rw [abs_of_neg (by linarith : normalized d-normalized (q j)<0)]
        linarith
    | some i =>
      cases j with
      | none =>
        simp only [Option.elim_none,Option.elim_some]
        have hi := (hq.1 i).1
        rw [abs_of_pos (by linarith : 0<normalized (q i)-normalized d)]
        linarith
      | some j =>
        have hh := hq.2 i j (by intro e; exact hij (congrArg some e))
        simp only [Option.elim_some]
        linarith

lemma regularOverlap_prepend {η : ℝ} (hη : 0<η) (hη1 : η≤1)
    (S : ReducedTopology) (q : S.Vertex → Fin L) (hq : regularOverlapDomain S L η q)
    (d : Fin L) (hlo : η/4<normalized d) (hhi : normalized d≤η/2) :
    regularShapeDomain S L (η/8) (fun i => i.elim d q) := by
  refine ⟨regular_prepend hη hη1 q hq.1 d hlo hhi,?_⟩
  apply admissible_of_all_lower S _ hq.2
  intro v
  have hh : normalized d<normalized (q v) := by have := (hq.1.1 v).1; linarith
  have he : d.val<(q v).val := by
    unfold normalized at hh
    exact_mod_cast ((div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr (NeZero.pos L))).mp hh)
  simpa only [Option.elim_some,Option.elim_none] using (Nat.succ_le_of_lt he)

lemma overlap_interval_geometry {η : ℝ} (hη : 0<η) (hη1 : η≤1) (hlarge : 8<η*(L:ℝ)) :
    let r := ⌊η*(L:ℝ)/4⌋₊
    2*r<L ∧ η/8≤(r:ℝ)/(L:ℝ) ∧
      ∀ d : Fin L, r<d.val ∧ d.val≤2*r → η/4<normalized d ∧ normalized d≤η/2 := by
  let r := ⌊η*(L:ℝ)/4⌋₊
  have hL : (0:ℝ)<L := Nat.cast_pos.mpr (NeZero.pos L)
  have hr : (r:ℝ)≤η*(L:ℝ)/4 := Nat.floor_le (by positivity)
  have hrs : η*(L:ℝ)/4<(r:ℝ)+1 := Nat.lt_floor_add_one _
  have h2r : (2*r:ℕ)<L := by
    have hh : (2:ℝ)*(r:ℝ)<(L:ℝ) := by nlinarith
    exact_mod_cast hh
  refine ⟨h2r,(le_div_iff₀ hL).mpr (by nlinarith),?_⟩
  intro d hd
  have hd0 : (r:ℝ)+1≤(d.val:ℝ) := by exact_mod_cast hd.1
  have hd1 : (d.val:ℝ)≤2*(r:ℝ) := by exact_mod_cast hd.2
  constructor
  · exact (lt_div_iff₀ hL).mpr (by nlinarith)
  · exact (div_le_iff₀ hL).mpr (by nlinarith)

end DilutedSpinGlass.ReducedTopology

end

end OAI
