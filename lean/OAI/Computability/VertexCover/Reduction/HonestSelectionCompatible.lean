import Mathlib
import OAI.Computability.VertexCover.PCP.AlphabetTableQueries
import OAI.Computability.VertexCover.Reduction.CompatibleSingleton

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
namespace VertexCover.LabelCover

abbrev PositionPair (d : ℕ) := {jk : Fin d × Fin d // jk.1 < jk.2}
abbrev Seeds (Φ : LabelCover) (d : ℕ) := PositionPair d → Fin Φ.M

def query (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d) (j : Fin d) : Φ.Query d :=
  ⟨j, (fun k => Φ.left (seed ⟨(j, k.1), k.2⟩)),
    (fun k => Φ.right (seed ⟨(k.1, j), k.2⟩))⟩

theorem query_left_mem (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (j k : Fin d) (hjk : j < k) :
    Φ.left (seed ⟨(j, k), hjk⟩) ∈ (Φ.query seed j).scopeU := by
  exact Finset.mem_image.mpr ⟨⟨k, hjk⟩, Finset.mem_univ _, rfl⟩

theorem query_right_mem (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (j k : Fin d) (hjk : j < k) :
    Φ.right (seed ⟨(j, k), hjk⟩) ∈ (Φ.query seed k).scopeV := by
  exact Finset.mem_image.mpr ⟨⟨j, hjk⟩, Finset.mem_univ _, rfl⟩

theorem query_injective (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d) :
    Function.Injective (Φ.query seed) := by
  intro j k h
  exact congrArg Sigma.fst h

namespace Query

theorem scope_card_le {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) :
    i.scopeU.card + i.scopeV.card ≤ d - 1 := by
  have hU : i.scopeU.card ≤ d - 1 - i.1.val := by
    calc
      i.scopeU.card ≤ Fintype.card {k : Fin d // i.1 < k} := Finset.card_image_le
      _ = (Finset.Ioi i.1).card := by simp [Fintype.card_subtype, Finset.filter_lt_eq_Ioi]
      _ = d - 1 - i.1.val := Fin.card_Ioi i.1
  have hV : i.scopeV.card ≤ i.1.val := by
    calc
      i.scopeV.card ≤ Fintype.card {k : Fin d // k < i.1} := Finset.card_image_le
      _ = (Finset.Iio i.1).card := by simp [Fintype.card_subtype, Finset.filter_gt_eq_Iio]
      _ = i.1.val := Fin.card_Iio i.1
  have := i.1.isLt
  omega

theorem localLabel_card_le {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) :
    Fintype.card i.LocalLabel ≤ (max Φ.qU Φ.qV)^(d - 1) := by
  let q := max Φ.qU Φ.qV
  have hq : 0 < q := lt_of_lt_of_le Φ.qU_pos (le_max_left _ _)
  calc
    Fintype.card i.LocalLabel ≤ Fintype.card i.Assignment := Fintype.card_subtype_le _
    _ = Φ.qU^i.scopeU.card * Φ.qV^i.scopeV.card := by
      simp [Assignment, Fintype.card_prod, ]
    _ ≤ q^i.scopeU.card * q^i.scopeV.card :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (le_max_left _ _) _)
        (Nat.pow_le_pow_left (le_max_right _ _) _)
    _ = q^(i.scopeU.card + i.scopeV.card) := (pow_add _ _ _).symm
    _ ≤ q^(d - 1) := Nat.pow_le_pow_right hq i.scope_card_le

end Query

def localOfSatisfying (Φ : LabelCover) (A : Φ.Labeling)
    (hA : ∀ c, Φ.Satisfies A c) {d : ℕ} (i : Φ.Query d) : i.LocalLabel :=
  ⟨(fun x => A.1 x.1, fun y => A.2 y.1), fun c _ _ => hA c⟩

def honestSelection (Φ : LabelCover) (A : Φ.Labeling)
    (hA : ∀ c, Φ.Satisfies A c) (d : ℕ) : Finset (Φ.Coordinate d) :=
  Finset.univ.image (fun i => ⟨i, Φ.localOfSatisfying A hA i⟩)

theorem honestSelection_compatible (Φ : LabelCover) (A : Φ.Labeling)
    (hA : ∀ c, Φ.Satisfies A c) (d : ℕ) :
    Φ.Compatible (Φ.honestSelection A hA d) := by
  classical
  have shape : ∀ p ∈ Φ.honestSelection A hA d,
      p = ⟨p.1, Φ.localOfSatisfying A hA p.1⟩ := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp q hq heq
    calc
      p = ⟨p.1, Φ.localOfSatisfying A hA p.1⟩ := shape p hp
      _ = ⟨q.1, Φ.localOfSatisfying A hA q.1⟩ :=
        congrArg (fun i => (⟨i, Φ.localOfSatisfying A hA i⟩ : Φ.Coordinate d)) heq
      _ = q := (shape q hq).symm
  · intro p hp q hq x hx hy
    have ep := shape p hp
    have eq := shape q hq
    cases p with | mk i a =>
      cases q with | mk j b =>
        simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at ep eq
        subst a; subst b; rfl
  · intro p hp q hq y hx hy
    have ep := shape p hp
    have eq := shape q hq
    cases p with | mk i a =>
      cases q with | mk j b =>
        simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at ep eq
        subst a; subst b; rfl
  · intro p hp q hq c hx hy
    have ep := shape p hp
    have eq := shape q hq
    cases p with | mk i a =>
      cases q with | mk j b =>
        simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at ep eq
        subst a; subst b
        exact hA c

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
