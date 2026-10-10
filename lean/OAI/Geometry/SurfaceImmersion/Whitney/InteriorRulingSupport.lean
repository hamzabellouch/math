import OAI.Geometry.SurfaceImmersion.Whitney.RuledCrosscapStrip
import OAI.Geometry.SurfaceImmersion.Geometry.TransverseSupport

namespace OAI

/-! A compact longitudinal cutoff in the regular interior has a fixed
compact regular rectangle containing all sufficiently narrow corrections. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

theorem CrosscapCoordinateStrip.interior_ruling_support (S : CrosscapCoordinateStrip A)
    {η : ℝ → ℝ} (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo A.arc.start A.arc.finish) :
    ∃ (δ : ℝ) (K : Set Base), 0 < δ ∧ IsCompact K ∧ K ⊆ S.domain ∧
      (∀ x ∈ K, Function.Injective (fderiv ℝ S.model x)) ∧
      ∀ r : ℝ, 0 < r → r ≤ δ → tsupport (narrowedRuling S.model η r) ⊆ K := by
  obtain ⟨δ,hδ,hrect⟩ := S.ruled_rectangle
  let T : ℝ × ℝ → Base := fun z => ![z.1,z.2]
  let K := T '' (Icc (-δ) δ ×ˢ tsupport η)
  have hT : Continuous T := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd
  have hK : IsCompact K := (isCompact_Icc.prod hc).image hT
  have hpoints : ∀ x ∈ K, x ∈ S.domain ∧ Function.Injective (fderiv ℝ S.model x) := by
    rintro x ⟨⟨u,t⟩,⟨hu,ht⟩,rfl⟩
    have hti := hs ht
    have htb : t ∈ Icc (A.arc.start-δ) (A.arc.finish+δ) :=
      ⟨by linarith [hti.1],by linarith [hti.2]⟩
    obtain ⟨hdom,hI⟩ := hrect 0 (by norm_num) u hu t htb
    have hneq : (![u,t] : Base) ≠ ![0,A.arc.start] ∧ (![u,t] : Base) ≠ ![0,A.arc.finish] := by
      constructor <;> intro he
      · have hh := congrFun he 1
        exact hti.1.ne' hh
      · have hh := congrFun he 1
        exact hti.2.ne hh
    have hnew := hI.mpr hneq
    have he : rulingHomotopy S.model 0 = S.model := by
      funext y
      simp [rulingHomotopy,linearMapHomotopy]
    rw [he] at hnew
    exact ⟨hdom,hnew⟩
  refine ⟨δ,K,hδ,hK,fun x hx => (hpoints x hx).1,fun x hx => (hpoints x hx).2,?_⟩
  intro r hr hrδ x hx
  obtain ⟨h0,h1⟩ := narrowedRuling_support S.model η hr hx
  refine ⟨(x 0,x 1),⟨?_,h1⟩,?_⟩
  · exact abs_le.mp (h0.trans hrδ)
  · ext i; fin_cases i <;> rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
