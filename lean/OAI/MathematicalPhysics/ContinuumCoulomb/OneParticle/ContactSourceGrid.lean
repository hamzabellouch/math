import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactGrid
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceHamiltonian

namespace OAI

/-! Every edge of the actual signed square-lattice source has a canonical
geometric strip, and the source's simple-edge promise makes these strips
pairwise distinct. -/

noncomputable section
namespace ContinuumCoulomb

private theorem natAbs_one_cases {a : ℤ} (h : a.natAbs = 1) : a = 1 ∨ a = -1 := by
  exact Int.natAbs_eq_natAbs_iff.mp (by simpa using h)

theorem exists_contactGridEdge (p q : ℤ × ℤ)
    (h : (p.1 - q.1).natAbs + (p.2 - q.2).natAbs = 1) :
    ∃ e : ContactGridEdge, e.left = p ∧ e.right = q := by
  have hx : (p.1 - q.1).natAbs = 0 ∨ (p.1 - q.1).natAbs = 1 := by omega
  rcases hx with hx | hx
  · have hxeq : p.1 = q.1 := sub_eq_zero.mp (Int.natAbs_eq_zero.mp hx)
    have hy : (p.2 - q.2).natAbs = 1 := by omega
    rcases natAbs_one_cases hy with hy | hy
    · refine ⟨⟨true, q, true⟩, ?_, ?_⟩
      · apply Prod.ext <;> simp [ContactGridEdge.left, ContactGridEdge.upper] <;> omega
      · simp [ContactGridEdge.right]
    · refine ⟨⟨true, p, false⟩, ?_, ?_⟩
      · simp [ContactGridEdge.left]
      · apply Prod.ext <;> simp [ContactGridEdge.right, ContactGridEdge.upper] <;> omega
  · have hy : (p.2 - q.2).natAbs = 0 := by omega
    have hyeq : p.2 = q.2 := sub_eq_zero.mp (Int.natAbs_eq_zero.mp hy)
    rcases natAbs_one_cases hx with hx | hx
    · refine ⟨⟨false, q, true⟩, ?_, ?_⟩
      · apply Prod.ext <;> simp [ContactGridEdge.left, ContactGridEdge.upper] <;> omega
      · simp [ContactGridEdge.right]
    · refine ⟨⟨false, p, false⟩, ?_, ?_⟩
      · simp [ContactGridEdge.left]
      · apply Prod.ext <;> simp [ContactGridEdge.right, ContactGridEdge.upper] <;> omega

theorem ContactGridEdge.same_key_endpoints {e f : ContactGridEdge} (h : e.key = f.key) :
    (e.left = f.left ∧ e.right = f.right) ∨
      (e.left = f.right ∧ e.right = f.left) := by
  have hv : e.vertical = f.vertical := congrArg Prod.fst h
  have ha : e.anchor = f.anchor := congrArg Prod.snd h
  have hu : e.upper = f.upper := by simp only [ContactGridEdge.upper, hv, ha]
  cases he : e.reversed <;> cases hf : f.reversed <;>
    simp [ContactGridEdge.left, ContactGridEdge.right, he, hf, ha, hu]

def SquareLatticeHeisenberg.contactEdge (F : SquareLatticeHeisenberg) (e : Fin F.edges) :
    ContactGridEdge :=
  (exists_contactGridEdge (F.coordinate (F.left e)) (F.coordinate (F.right e)) (F.adjacent e)).choose

@[simp] theorem SquareLatticeHeisenberg.contactEdge_left (F : SquareLatticeHeisenberg)
    (e : Fin F.edges) : (F.contactEdge e).left = F.coordinate (F.left e) :=
  (exists_contactGridEdge _ _ (F.adjacent e)).choose_spec.1

@[simp] theorem SquareLatticeHeisenberg.contactEdge_right (F : SquareLatticeHeisenberg)
    (e : Fin F.edges) : (F.contactEdge e).right = F.coordinate (F.right e) :=
  (exists_contactGridEdge _ _ (F.adjacent e)).choose_spec.2

/-- Distinct source edges cannot share a canonical strip, even when their
listed orientations are opposite. -/
theorem SquareLatticeHeisenberg.contactEdge_key_injective (F : SquareLatticeHeisenberg) :
    Function.Injective (fun e => (F.contactEdge e).key) := by
  intro e f h
  by_contra hne
  have hs := F.edge_simple e f hne
  rcases ContactGridEdge.same_key_endpoints h with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · apply hs.1
    exact ⟨F.coordinate_injective (by simpa using hl),
      F.coordinate_injective (by simpa using hr)⟩
  · apply hs.2
    exact ⟨F.coordinate_injective (by simpa using hl),
      F.coordinate_injective (by simpa using hr)⟩

end ContinuumCoulomb

end

end OAI
