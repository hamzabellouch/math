import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.Popular

namespace OAI

section
namespace SharpLogRamsey

section LinearAlgebra
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem flag_vectors_independent {m : ℕ} (a : Fin m → V)
    (b : Fin m → Module.Dual K V)
    (ha : ∀ i, a i ≠ 0)
    (hz : ∀ i j, i ≤ j → b j (a i) = 0)
    (hn : ∀ i j, i < j → b i (a j) ≠ 0) :
    LinearIndependent K a := by
  induction m with
  | zero => exact linearIndependent_empty_type
  | succ m ih =>
    apply linearIndependent_finSucc'.mpr
    refine ⟨ih (Fin.init a) (Fin.init b) (fun i => ha i.castSucc)
      (fun i j h => hz i.castSucc j.castSucc h)
      (fun i j h => hn i.castSucc j.castSucc h), ?_⟩
    cases m with
    | zero => simpa using ha (Fin.last 0)
    | succ n =>
      intro hmem
      let j : Fin (n + 1 + 1) := (Fin.last n).castSucc
      have hspan : Submodule.span K (Set.range (Fin.init a)) ≤
          LinearMap.ker (b j) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        exact hz i.castSucc j (by simpa [j] using Fin.le_last i)
      have hzero : b j (a (Fin.last (n + 1))) = 0 := hspan hmem
      exact hn j (Fin.last (n + 1)) (by simp [j]) hzero

theorem flag_length_lt_finrank [FiniteDimensional K V] {m : ℕ}
    (a : Fin (m+1) → V) (b : Fin (m+1) → Module.Dual K V)
    (ha : ∀ i, a i ≠ 0) (hb : b (Fin.last m) ≠ 0)
    (hz : ∀ i j, i ≤ j → b j (a i) = 0)
    (hn : ∀ i j, i < j → b i (a j) ≠ 0) :
    m + 1 < Module.finrank K V := by
  let W := LinearMap.ker (b (Fin.last m))
  let a' : Fin (m+1) → W := fun i => ⟨a i, hz i (Fin.last m) (Fin.le_last i)⟩
  have hli : LinearIndependent K a' :=
    LinearIndependent.of_comp W.subtype (flag_vectors_independent a b ha hz hn)
  have hle : m + 1 ≤ Module.finrank K W := by
    simpa using hli.fintype_card_le_finrank
  have hproper : W ≠ ⊤ := by
    exact fun h => hb (LinearMap.ker_eq_top.mp h)
  exact hle.trans_lt (Submodule.finrank_lt hproper)

end LinearAlgebra

section Flags
variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]

theorem incident_iff_submodule (a : Projectivization K V)
    (b : Projectivization K (Module.Dual K V)) :
    Incident K V a b ↔ a.submodule ≤ LinearMap.ker b.rep := by
  rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]
  rfl

def flagGraph {N : ℕ} (F : Fin N → Flag K V) : SimpleGraph (Fin N) where
  Adj i j :=
    (i < j ∧ Incident K V (F i).point (F j).dualPoint ∧
      ¬ Incident K V (F j).point (F i).dualPoint) ∨
    (j < i ∧ Incident K V (F j).point (F i).dualPoint ∧
      ¬ Incident K V (F i).point (F j).dualPoint)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun i => by simp⟩

variable {K V}

theorem flagGraph_adj_of_lt {N : ℕ} (F : Fin N → Flag K V)
    {i j : Fin N} (hij : i < j) :
    (flagGraph K V F).Adj i j ↔
      Incident K V (F i).point (F j).dualPoint ∧
      ¬ Incident K V (F j).point (F i).dualPoint := by
  simp only [flagGraph, hij, true_and, not_lt_of_ge hij.le, false_and, or_false]

theorem flagGraph_cliqueFree [FiniteDimensional K V] {d N : ℕ}
    (hdim : Module.finrank K V = d+1) (F : Fin N → Flag K V) :
    (flagGraph K V F).CliqueFree (d+1) := by
  intro S hS
  let e := S.orderEmbOfFin hS.card_eq
  let a : Fin (d+1) → V := fun i => (F (e i)).point.rep
  let b : Fin (d+1) → Module.Dual K V := fun i => (F (e i)).dualPoint.rep
  have hedge (i j : Fin (d+1)) (h : i < j) :
      Incident K V (F (e i)).point (F (e j)).dualPoint ∧
      ¬ Incident K V (F (e j)).point (F (e i)).dualPoint := by
    apply (flagGraph_adj_of_lt F (e.strictMono h)).mp
    exact hS.isClique (S.orderEmbOfFin_mem hS.card_eq i)
      (S.orderEmbOfFin_mem hS.card_eq j) (ne_of_lt (e.strictMono h))
  have hz : ∀ i j, i ≤ j → b j (a i) = 0 := by
    intro i j h
    rcases lt_or_eq_of_le h with hlt | rfl
    · exact (hedge i j hlt).1
    · exact (F (e i)).incident
  have hn : ∀ i j, i < j → b i (a j) ≠ 0 := by
    intro i j h
    exact (hedge i j h).2
  have hlt := flag_length_lt_finrank a b (fun i => (F (e i)).point.rep_nonzero)
    (F (e (Fin.last d))).dualPoint.rep_nonzero hz hn
  omega

theorem consistent_iff_no_edges {N : ℕ} (F : Fin N → Flag K V) :
    Consistent F ↔ ∀ i j, ¬ (flagGraph K V F).Adj i j := by
  constructor
  · intro h i j hadj
    rcases hadj with ⟨hij, hinc, hnot⟩ | ⟨hji, hinc, hnot⟩
    · exact hnot (h i j hij hinc)
    · exact hnot (h j i hji hinc)
  · intro h i j hij hinc
    by_contra hnot
    exact h i j ((flagGraph_adj_of_lt F hij).mpr ⟨hinc, hnot⟩)

def ConsistentOn {N : ℕ} (F : Fin N → Flag K V) (S : Finset (Fin N)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i < j → Incident K V (F i).point (F j).dualPoint →
    Incident K V (F j).point (F i).dualPoint

theorem consistentOn_iff_compl_isClique {N : ℕ} (F : Fin N → Flag K V)
    (S : Finset (Fin N)) :
    ConsistentOn F S ↔ (flagGraph K V F)ᶜ.IsClique S := by
  constructor
  · intro h i hi j hj hne
    rw [SimpleGraph.compl_adj]
    refine ⟨hne, ?_⟩
    rintro (⟨hij, hinc, hnot⟩ | ⟨hji, hinc, hnot⟩)
    · exact hnot (h i hi j hj hij hinc)
    · exact hnot (h j hj i hi hji hinc)
  · intro h i hi j hj hij hinc
    have hnot := ((flagGraph K V F).compl_adj i j).mp (h hi hj (ne_of_lt hij))
    by_contra hrev
    exact hnot.2 ((flagGraph_adj_of_lt F hij).mpr ⟨hinc, hrev⟩)

noncomputable def projectiveSubmoduleEquiv (W : Submodule K V) :
    Projectivization K W ≃ {a : Projectivization K V // a.submodule ≤ W} := by
  let f : Projectivization K W → {a : Projectivization K V // a.submodule ≤ W} :=
    fun a => ⟨Projectivization.map W.subtype W.injective_subtype a, by
      induction a using Projectivization.ind with
      | h v hv =>
        rw [Projectivization.map_mk, Projectivization.submodule_mk,
          Submodule.span_singleton_le_iff_mem]
        exact v.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    exact Projectivization.map_injective W.subtype W.injective_subtype
      (congrArg Subtype.val h)
  · rintro ⟨a, ha⟩
    have hmem : a.rep ∈ W := ha (by
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _)
    let v : W := ⟨a.rep, hmem⟩
    have hv : v ≠ 0 := fun h => a.rep_nonzero (congrArg Subtype.val h)
    refine ⟨Projectivization.mk K v hv, ?_⟩
    apply Subtype.ext
    exact a.mk_rep

theorem card_incident_points [Finite K] [FiniteDimensional K V] {d : ℕ}
    (hdim : Module.finrank K V = d+1)
    (b : Projectivization K (Module.Dual K V)) :
    Nat.card {a : Projectivization K V // Incident K V a b} =
      ∑ i ∈ Finset.range d, Nat.card K ^ i := by
  let e : {a : Projectivization K V // Incident K V a b} ≃
      {a : Projectivization K V // a.submodule ≤ LinearMap.ker b.rep} :=
    Equiv.subtypeEquivRight (fun a => incident_iff_submodule K V a b)
  rw [Nat.card_congr e, ← Nat.card_congr (projectiveSubmoduleEquiv (LinearMap.ker b.rep))]
  apply Projectivization.card_of_finrank
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
  omega

theorem card_flags [Finite K] [FiniteDimensional K V] {d : ℕ}
    (hdim : Module.finrank K V = d+1) :
    Nat.card (Flag K V) =
      (∑ i ∈ Finset.range (d+1), Nat.card K ^ i) *
      (∑ i ∈ Finset.range d, Nat.card K ^ i) := by
  classical
  let : Finite V := Finite.of_injective (Module.finBasis K V).equivFun
    (Module.finBasis K V).equivFun.injective
  let : Finite (Module.Dual K V) :=
    Finite.of_injective (Module.finBasis K (Module.Dual K V)).equivFun
      (Module.finBasis K (Module.Dual K V)).equivFun.injective
  let : Finite (Projectivization K V) :=
    Finite.of_injective Projectivization.rep (fun a b h => by
      rw [← a.mk_rep, ← b.mk_rep]; congr 1)
  let : Finite (Projectivization K (Module.Dual K V)) :=
    Finite.of_injective Projectivization.rep (fun a b h => by
      rw [← a.mk_rep, ← b.mk_rep]; congr 1)
  let := Fintype.ofFinite (Projectivization K (Module.Dual K V))
  let e : Flag K V ≃ Σ b : Projectivization K (Module.Dual K V),
      {a : Projectivization K V // Incident K V a b} :=
    { toFun := fun f => ⟨f.dualPoint, f.point, f.incident⟩
      invFun := fun f => ⟨f.2.1, f.1, f.2.2⟩
      left_inv := fun f => by cases f; rfl
      right_inv := fun f => by cases f; rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [card_incident_points hdim]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card]
  rw [Projectivization.card_of_finrank K (Module.Dual K V)
    (Subspace.dual_finrank_eq.trans hdim)]

theorem prime_flagGraph_cliqueFree (q d N : ℕ) [Fact q.Prime]
    (F : Fin N → Flag (ZMod q) (Fin (d+1) → ZMod q)) :
    (flagGraph (ZMod q) (Fin (d+1) → ZMod q) F).CliqueFree (d+1) := by
  apply flagGraph_cliqueFree
  simp

end Flags
end SharpLogRamsey

end

end OAI
