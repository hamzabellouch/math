import OAI.Geometry.SurfaceImmersion.Whitney.SmoothCrosscapConnectingArc

namespace OAI

/-! Singleton fibers over crosscaps prevent the source projection of an
ordered connecting arc from revisiting either singular endpoint. -/
noncomputable section
open Set unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} {Y : Type*} {f : M → Y} {p q : M} {Γ : I → M × M}

lemma ordered_arc_endpoints_distinct (hi : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q)) : p ≠ q := by
  intro hpq
  have hpair : Γ 0 = Γ 1 := by rw [hzero,hone,hpq]
  have h := congrArg (fun t : I => (t:ℝ)) (hi hpair)
  norm_num at h

lemma ordered_arc_source_start_unique (hi : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ u, f (Γ u).1 = f (Γ u).2)
    (hne : ∀ u : I, 0 < (u:ℝ) → (u:ℝ) < 1 → (Γ u).1 ≠ (Γ u).2)
    (hsing : ∀ x, f x = f p → x = p) :
    ∀ u : I, (Γ u).1 = p → u = 0 := by
  intro u hu
  by_contra hu0
  have hu1 : u ≠ 1 := by
    intro he
    rw [he,hone] at hu
    exact ordered_arc_endpoints_distinct hi hzero hone hu.symm
  have h0 : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (by
    intro he
    exact hu0 (Subtype.ext he.symm))
  have h1 : (u:ℝ) < 1 := lt_of_le_of_ne u.property.2 (by
    intro he
    exact hu1 (Subtype.ext he))
  have hsecond : (Γ u).2 = p := hsing _ ((heq u).symm.trans (congrArg f hu))
  exact hne u h0 h1 (hu.trans hsecond.symm)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
