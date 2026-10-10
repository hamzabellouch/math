import OAI.Geometry.SurfaceImmersion.Whitney.RulingHomotopy
import OAI.Geometry.SurfaceImmersion.Geometry.CompactFamilyRegularLocus
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapCoordinateRegularity

namespace OAI

/-! One rectangular neighborhood works throughout the actual ruled
homotopy: its singular set is exactly the original two endpoints. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

theorem CrosscapCoordinateStrip.ruled_neighborhood (S : CrosscapCoordinateStrip A) :
    ∃ U : Set Base, IsOpen U ∧ U ⊆ S.domain ∧
      (∀ t ∈ Icc A.arc.start A.arc.finish, (![0,t] : Base) ∈ U) ∧
      ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ U,
        Function.Injective (fderiv ℝ (rulingHomotopy S.model s) x) ↔
          x ≠ ![0,A.arc.start] ∧ x ≠ ![0,A.arc.finish] := by
  let a : Base := ![0,A.arc.start]
  let b : Base := ![0,A.arc.finish]
  have hab : a ≠ b := by
    intro he
    apply A.arc.start_lt_finish.ne
    exact congrFun he 1
  have haT := S.transverse A.arc.start (left_mem_Icc.mpr A.arc.start_lt_finish.le)
  have hbT := S.transverse A.arc.finish (right_mem_Icc.mpr A.arc.start_lt_finish.le)
  obtain ⟨ra,hra,hIa⟩ := rulingHomotopy_crosscap_isolation S.model_smooth A.arc.start
    (by simpa only [crosscapAxis_apply] using S.left_vertical)
    (by simpa only [crosscapAxis_apply] using haT)
    (by simpa only [crosscapAxis_apply] using S.endpoint_direction_regular.1)
  obtain ⟨rb,hrb,hIb⟩ := rulingHomotopy_crosscap_isolation S.model_smooth A.arc.finish
    (by simpa only [crosscapAxis_apply] using S.right_vertical)
    (by simpa only [crosscapAxis_apply] using hbT)
    (by simpa only [crosscapAxis_apply] using S.endpoint_direction_regular.2)
  simp only [crosscapAxis_apply] at hIa hIb
  let R := {x | ∀ s ∈ Icc (0:ℝ) 1, Function.Injective (fderiv ℝ (rulingHomotopy S.model s) x)}
  have hR : IsOpen R := compact_family_regular_locus_open isCompact_Icc _
    (rulingHomotopy_derivative_continuous S.model_smooth)
  let O := (ball a ra \ {b}) ∪ (ball b rb \ {a}) ∪ (R \ ({a} ∪ {b}))
  have hO : IsOpen O := ((isOpen_ball.sdiff isClosed_singleton).union
    (isOpen_ball.sdiff isClosed_singleton)).union
      (hR.sdiff (isClosed_singleton.union isClosed_singleton))
  let U := S.domain ∩ O
  have hU : IsOpen U := S.domain_open.inter hO
  have haxis : ∀ t ∈ Icc A.arc.start A.arc.finish, (![0,t] : Base) ∈ U := by
    intro t ht
    have hdom : (![0,t] : Base) ∈ S.domain := by
      apply S.rectangle 0 ⟨by linarith [S.width_pos],by linarith [S.width_pos]⟩ t
      constructor <;> linarith [S.width_pos,ht.1,ht.2]
    refine ⟨hdom,?_⟩
    change (![0,t] : Base) ∈ (ball a ra \ {b}) ∪ (ball b rb \ {a}) ∪ (R \ ({a} ∪ {b}))
    by_cases hta : t = A.arc.start
    · subst t
      exact Or.inl (Or.inl ⟨mem_ball_self hra,hab⟩)
    · by_cases htb : t = A.arc.finish
      · subst t
        exact Or.inl (Or.inr ⟨mem_ball_self hrb,Ne.symm hab⟩)
      · apply Or.inr
        constructor
        · intro s hs
          have he := rulingHomotopy_first_jet S.model_smooth s t
          rw [crosscapAxis_apply] at he
          rw [he]
          exact S.interior_regular t ⟨lt_of_le_of_ne ht.1 (Ne.symm hta),lt_of_le_of_ne ht.2 htb⟩
        · rintro (he | he)
          · exact hta (congrFun he 1)
          · exact htb (congrFun he 1)
  refine ⟨U,hU,inter_subset_left,haxis,?_⟩
  intro s hs x hx
  change x ∈ S.domain ∩ O at hx
  rcases hx.2 with (hxa | hxb) | hxr
  · have hneqb : x ≠ b := hxa.2
    constructor
    · intro hi
      exact ⟨fun he => (hIa s hs x hxa.1).mpr he hi,hneqb⟩
    · rintro ⟨hn,_⟩
      by_contra hi
      exact hn ((hIa s hs x hxa.1).mp hi)
  · have hneqa : x ≠ a := hxb.2
    constructor
    · intro hi
      exact ⟨hneqa,fun he => (hIb s hs x hxb.1).mpr he hi⟩
    · rintro ⟨_,hn⟩
      by_contra hi
      exact hn ((hIb s hs x hxb.1).mp hi)
  · constructor
    · intro _
      exact ⟨fun he => hxr.2 (Or.inl he),fun he => hxr.2 (Or.inr he)⟩
    · intro _
      exact hxr.1 s hs

theorem CrosscapCoordinateStrip.ruled_rectangle (S : CrosscapCoordinateStrip A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc (0:ℝ) 1,
      ∀ x ∈ Icc (-δ) δ, ∀ t ∈ Icc (A.arc.start-δ) (A.arc.finish+δ),
        (![x,t] : Base) ∈ S.domain ∧
        (Function.Injective (fderiv ℝ (rulingHomotopy S.model s) (![x,t] : Base)) ↔
          (![x,t] : Base) ≠ ![0,A.arc.start] ∧ (![x,t] : Base) ≠ ![0,A.arc.finish]) := by
  obtain ⟨U,hU,hUD,haxis,hI⟩ := S.ruled_neighborhood
  obtain ⟨δ,hδ,hrect⟩ := compact_axis_rectangle A.arc.start_lt_finish.le hU haxis
  exact ⟨δ,hδ,fun s hs x hx t ht => ⟨hUD (hrect x hx t ht),hI s hs _ (hrect x hx t ht)⟩⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
