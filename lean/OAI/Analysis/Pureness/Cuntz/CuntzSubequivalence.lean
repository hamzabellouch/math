import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Algebra.Star.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.Algebra.Monoid

namespace OAI
open Filter Topology
namespace CuntzPureness

variable {B : Type*} [NonUnitalNormedRing B] [StarRing B]

def CuntzSubequiv (a b : B) : Prop :=
  a ∈ closure (Set.range fun v : B => star v * b * v)

theorem cuntzSubequiv_iff_sequence (a b : B) :
    CuntzSubequiv a b ↔
      ∃ v : ℕ → B, Tendsto (fun j => star (v j) * b * v j) atTop (𝓝 a) := by
  rw [CuntzSubequiv, mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨u, hu, hlim⟩
    choose v hv using hu
    exact ⟨v, by simpa only [hv] using hlim⟩
  · rintro ⟨v, hv⟩
    exact ⟨_, fun j => ⟨v j, rfl⟩, hv⟩

theorem cuntzSubequiv_iff_norm (a b : B) :
    CuntzSubequiv a b ↔ ∀ ε : ℝ, 0 < ε →
      ∃ v : B, ‖a - star v * b * v‖ < ε := by
  simp only [CuntzSubequiv, Metric.mem_closure_iff, Set.mem_range, dist_eq_norm]
  constructor
  · intro h ε hε
    obtain ⟨_, ⟨v, rfl⟩, hv⟩ := h ε hε
    exact ⟨v, hv⟩
  · intro h ε hε
    obtain ⟨v, hv⟩ := h ε hε
    exact ⟨_, ⟨v, rfl⟩, hv⟩

theorem cuntzSubequiv_conjugate (b v : B) : CuntzSubequiv (star v * b * v) b :=
  subset_closure ⟨v, rfl⟩

theorem zero_cuntzSubequiv (b : B) : CuntzSubequiv 0 b := by
  simpa using cuntzSubequiv_conjugate b 0

theorem cuntzSubequiv_of_tendsto {a : ℕ → B} {b c : B}
    (h : ∀ j, CuntzSubequiv (a j) b) (ha : Tendsto a atTop (𝓝 c)) :
    CuntzSubequiv c b :=
  isClosed_closure.mem_of_tendsto ha (Filter.Eventually.of_forall h)

theorem CuntzSubequiv.conjugate_left {a b : B} (h : CuntzSubequiv a b) (v : B) :
    CuntzSubequiv (star v * a * v) b := by
  obtain ⟨w, hw⟩ := (cuntzSubequiv_iff_sequence a b).mp h
  apply (cuntzSubequiv_iff_sequence _ _).mpr
  refine ⟨fun j => w j * v, ?_⟩
  have hlim : Tendsto (fun j => star v * (star (w j) * b * w j) * v)
      atTop (𝓝 (star v * a * v)) :=
    (tendsto_const_nhds.mul hw).mul tendsto_const_nhds
  simpa only [star_mul, mul_assoc] using hlim

theorem CuntzSubequiv.trans {a b c : B}
    (hab : CuntzSubequiv a b) (hbc : CuntzSubequiv b c) : CuntzSubequiv a c := by
  obtain ⟨v, hv⟩ := (cuntzSubequiv_iff_sequence a b).mp hab
  exact cuntzSubequiv_of_tendsto (fun j => hbc.conjugate_left (v j)) hv

theorem cuntzSubequiv_zero_iff (a : B) : CuntzSubequiv a 0 ↔ a = 0 := by
  simp [CuntzSubequiv, Set.range_const]

variable {A : Type*} [NormedRing A] [StarRing A]

theorem cuntzSubequiv_refl (a : A) : CuntzSubequiv a a := by
  simpa using cuntzSubequiv_conjugate a 1

def cuntzSetoid : Setoid A where
  r a b := CuntzSubequiv a b ∧ CuntzSubequiv b a
  iseqv := {
    refl := fun a => ⟨cuntzSubequiv_refl a, cuntzSubequiv_refl a⟩
    symm := fun h => h.symm
    trans := fun h₁ h₂ => ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩ }
end CuntzPureness

end OAI
