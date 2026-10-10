import OAI.Analysis.Pureness.Projections.OrthogonalPartialIsometry

namespace OAI
noncomputable section
namespace CuntzPureness
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

structure ProjectionMatch (p q : D) where
  val : D
  initial : IsStarProjection (star val*val)
  range : IsStarProjection (val*star val)
  initial_le : star val*val ≤ q
  range_le : val*star val ≤ p

namespace ProjectionMatch
variable {p q : D}

omit [StarOrderedRing D] in
@[ext] theorem ext {u v : ProjectionMatch p q} (h : u.val=v.val) : u=v := by
  cases u; cases v; cases h; rfl

instance projectionMatchPartialOrder : PartialOrder (ProjectionMatch p q) where
  le u v := star u.val*u.val ≤ star v.val*v.val ∧ v.val*(star u.val*u.val)=u.val
  le_refl u := ⟨le_rfl,partial_isometry_mul_initial u.val u.initial⟩
  le_trans u v w huv hvw := by
    refine ⟨huv.1.trans hvw.1,?_⟩
    calc
      w.val*(star u.val*u.val) = w.val*((star v.val*v.val)*(star u.val*u.val)) := by
        rw [(u.initial.le_iff_mul_eq_right v.initial).mp huv.1]
      _ = v.val*(star u.val*u.val) := by rw [← mul_assoc,hvw.2]
      _ = u.val := huv.2
  le_antisymm u v huv hvu := by
    apply ext
    have he := le_antisymm huv.1 hvu.1
    rw [he,partial_isometry_mul_initial v.val v.initial] at huv
    exact huv.2.symm

lemma le_def (u v : ProjectionMatch p q) :
    u ≤ v ↔ star u.val*u.val ≤ star v.val*v.val ∧ v.val*(star u.val*u.val)=u.val := Iff.rfl

def zero (hp : IsStarProjection p) (hq : IsStarProjection q) : ProjectionMatch p q where
  val := 0
  initial := by simp only [star_zero,zero_mul]; exact IsStarProjection.zero D
  range := by simp only [star_zero,zero_mul]; exact IsStarProjection.zero D
  initial_le := by simpa using hq.nonneg
  range_le := by simpa using hp.nonneg

lemma zero_le (hp : IsStarProjection p) (hq : IsStarProjection q) (v : ProjectionMatch p q) :
    zero hp hq ≤ v := by
  change star (0:D)*0 ≤ star v.val*v.val ∧ v.val*(star (0:D)*0)=0
  simp

theorem exists_extension (hp : IsStarProjection p) (hq : IsStarProjection q)
    (u : ProjectionMatch p q) (w : ProjectionMatch (p-u.val*star u.val) (q-star u.val*u.val)) :
    ∃ v : ProjectionMatch p q, u ≤ v ∧ v.val=u.val+w.val ∧
      star v.val*v.val=star u.val*u.val+star w.val*w.val := by
  obtain ⟨hi,hr,he,hg,heq,hgp,hext⟩ := partial_isometry_orthogonal_extension p q u.val w.val
    hp hq u.initial u.range w.initial w.range u.initial_le u.range_le w.initial_le w.range_le
  let v : ProjectionMatch p q := ⟨u.val+w.val,he,hg,heq,hgp⟩
  refine ⟨v,⟨?_,hext⟩,rfl,hi⟩
  change star u.val*u.val ≤ star (u.val+w.val)*(u.val+w.val)
  rw [hi]
  exact le_add_of_nonneg_right w.initial.nonneg
end ProjectionMatch
end CuntzPureness

end

end OAI
