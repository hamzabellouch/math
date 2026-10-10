import OAI.Probability.DilutedSpin.RegularPhysicalShift

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open DepthAverage
noncomputable local instance regularFrameExtractionDecidableEq (β : Type) :
    DecidableEq β := Classical.decEq β

lemma admissible_replace_upper (S : ReducedTopology) (q : S.Vertex → ℕ)
    {lo hi hi' : ℕ} (ha : Admissible S q lo hi) (hr : ∀ v, q v<hi') :
    Admissible S q lo hi' := by
  induction S generalizing lo with
  | leaf => trivial
  | node k hk C ih =>
    exact ⟨ha.1,hr none,fun j => ih j _ (ha.2.2 j) (fun v => hr (some ⟨j,v⟩))⟩

/-- Every assignment in the actual regular/admissible parent domain is one
of the literal frames of physical_grid_scheduled_step. The extraction keeps
the complete terminal horizon, evaluation level and first branching level;
it loses neither endpoint cases nor further child branching coordinates. -/
theorem regular_node_frame {L : ℕ} [NeZero L] {η : ℝ} (hη : 0<η)
    (hlarge : 1<η*(L:ℝ)) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (Q : Option (ReducedTopology.node k hk C).Vertex → Fin L)
    (hQ : regularShapeDomain (.node k hk C) L η Q) :
    ∃ H r d : ℕ, L=H+1+1+r+1+(d+1) ∧ (Q none).val=d+1 ∧
      (Q (some none)).val=r+1+(d+1) ∧
      ∀ j, Admissible (C j) (fun v => (Q (some (some ⟨j,v⟩))).val)
        (r+1+(d+1)+1) (r+1+(d+1)+1+H) := by
  have hL : (0:ℝ)<L := Nat.cast_pos.mpr (NeZero.pos L)
  have hdpos : 0<(Q none).val := by
    have hh := (lt_div_iff₀ hL).mp (hQ.1.1 none).1
    have hh' : (0:ℝ)<((Q none).val:ℝ) := (mul_pos hη hL).trans hh
    exact_mod_cast hh'
  have heval : (Q none).val+1≤(Q (some none)).val := hQ.2.1
  have hroom := regular_room hlarge hQ.1
  let d := (Q none).val-1
  let r := (Q (some none)).val-(Q none).val-1
  let H := L-(Q (some none)).val-2
  have hd : (Q none).val=d+1 := by dsimp [d]; omega
  have hr : (Q (some none)).val=r+1+(d+1) := by dsimp [r,d]; omega
  have hH : L=H+1+1+r+1+(d+1) := by
    have hh := hroom (some none)
    dsimp [H,r,d]
    omega
  refine ⟨H,r,d,hH,hd,hr,?_⟩
  intro j
  have ha := admissible_replace_upper (C j) _ (hQ.2.2.2 j)
    (hi' := r+1+(d+1)+1+H) (by
      intro v
      have hh := hroom (some (some ⟨j,v⟩))
      change (Q (some (some ⟨j,v⟩))).val < r+1+(d+1)+1+H
      omega)
  simpa only [hr] using ha

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
