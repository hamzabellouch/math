import OAI.Geometry.Convex.GeneralMahler.Laplace
import OAI.Geometry.Convex.GeneralMahler.Segment.All
import OAI.Geometry.Convex.GeneralMahler.Scalar.AllNodes
import OAI.Geometry.Convex.GeneralMahler.Middle.Good

namespace OAI

/-! The general Mahler inequality, equality characterization, and Santaló minimum. -/

namespace GeneralMahler

open SCal SCal.Grid SCal.Mid Set MeasureTheory

lemma Complete_profile_input : Input091 :=
  let h : NG := Nodes.covered
  ⟨hSeg01 h, upd_ok h, Eq04full h Tab.Cn Tab.checkedP ⟨Tab.gtrue, Tab.gfalse⟩⟩

/-- The sharp volume-product bound and its simplex equality case. -/
theorem mahal {n : ℕ} (K : Body n) :
    ((n : ℝ) + 1) ^ (n + 1) / (n.factorial : ℝ) ^ 2 ≤ K.P ∧
      (K.P = ((n : ℝ) + 1) ^ (n + 1) / (n.factorial : ℝ) ^ 2 ↔
        IsSimplex (K : Set (Rn n))) :=
  Body.main_with_profiles Complete_profile_input K

/-- The sharp lower bound also holds at every interior center. -/
theorem all_centers {n : ℕ} (K : Body n) {x : Rn n}
    (hx : x ∈ interior (K : Set (Rn n))) :
    ((n : ℝ) + 1) ^ (n + 1) / (n.factorial : ℝ) ^ 2 ≤ K.productAt x :=
  (mahal K).1.trans (Body.product_min hx)

def ofSet {n : ℕ} (K : Set (Rn n)) (hK : IsCompact K) (hc : Convex ℝ K)
    (hi : (interior K).Nonempty) : Body n where
  carrier := K
  convex' := hc
  isCompact' := hK
  nonempty' := hi.mono interior_subset
  solid := hi

/-- The Santaló minimum is attained uniquely and satisfies the sharp Mahler inequality. -/
theorem general_geometric {n : ℕ} (_hn : 1 ≤ n) (K : Set (Rn n))
    (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    let D := ofSet K hK hc hi
    (∃! x, x ∈ interior K ∧ IsMinOn D.polarVol (interior K) x) ∧
    (D.santalo ∈ interior K ∧ IsMinOn D.polarVol (interior K) D.santalo) ∧
    (D.P = (volume K).toReal * (volume (polarAt K D.santalo)).toReal) ∧
    D.P = sInf (D.productAt '' interior K) ∧
    ((n : ℝ) + 1) ^ (n + 1) / (n.factorial : ℝ) ^ 2 ≤ D.P ∧
      (D.P = ((n : ℝ) + 1) ^ (n + 1) / (n.factorial : ℝ) ^ 2 ↔ IsSimplex K) := by
  intro D
  exact ⟨D.santalo_exists, D.santalo_spec, rfl, D.product_inf, (mahal D).1, (mahal D).2⟩

end GeneralMahler

end OAI
