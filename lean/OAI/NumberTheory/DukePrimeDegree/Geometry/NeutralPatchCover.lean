import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralSmallRectangles

namespace OAI

/-! # A countable cover by actual small neutral rectangles -/

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

structure SmallNeutralPatch (n : ℕ) (ε : ℝ) where
  center : G n
  box : RootPrefixBox (neutralEmptyPrefix n) (completeRootChain n)
    (emptyRootPattern n) (completeRootChain_final n) center
  bound : ℝ
  base : Set (NeutralCoordinateBase n)
  neutral : Set (transverseNeutralSpace n)
  base_open : IsOpen base
  neutral_open : IsOpen neutral
  neutral_nonempty : neutral.Nonempty
  time_bound : box.time ⊆ (completeRootChain n).remainingWindow bound 0
  in_box : ∀ z ∈ base ×ˢ neutral, neutralToPrefix n z ∈ box.domain
  small : ∀ z ∈ base ×ˢ neutral, ∀ w ∈ base ×ˢ neutral,
    (neutralProductParam n z)⁻¹*neutralProductParam n w ∈ matrixBall n ε

def SmallNeutralPatch.raw {n : ℕ} {ε : ℝ} (P : SmallNeutralPatch n ε) : Set (X n) :=
  neutralQuotientParam n P.center '' (P.base ×ˢ P.neutral)

lemma neutralQuotientParam_localHomeomorph (n : ℕ) (g : G n) :
    IsLocalHomeomorph (neutralQuotientParam n g) :=
  (quotient_covering n).isLocalHomeomorph.comp
    ((Homeomorph.mulLeft g).isLocalHomeomorph.comp
      (neutralProductParam_isOpenEmbedding n).isLocalHomeomorph)

lemma SmallNeutralPatch.raw_open {n : ℕ} {ε : ℝ} (P : SmallNeutralPatch n ε) :
    IsOpen P.raw :=
  (neutralQuotientParam_localHomeomorph n P.center).isOpenMap _
    (P.base_open.prod P.neutral_open)

theorem exists_countable_small_neutral_patches (n : ℕ)
    (z₀ : NeutralCoordinateBase n × transverseNeutralSpace n) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℕ → SmallNeutralPatch n ε, (⋃ i, (P i).raw)=univ := by
  classical
  have hx (x : X n) : ∃ P : SmallNeutralPatch n ε, x ∈ P.raw := by
    induction x using Quotient.inductionOn with
    | h g =>
      let g₀ := g*(neutralProductParam n z₀)⁻¹
      obtain ⟨B,R,A,K,hA,hK,hz,hBR,hAB,hsmall⟩ :=
        exists_small_neutral_rectangle n g₀ z₀ hε
      let P : SmallNeutralPatch n ε :=
        ⟨g₀,B,R,A,K,hA,hK,⟨z₀.2,hz.2⟩,hBR,hAB,hsmall⟩
      refine ⟨P,z₀,hz,?_⟩
      change Quotient.mk _ ((g*(neutralProductParam n z₀)⁻¹)*neutralProductParam n z₀)=
        Quotient.mk _ g
      rw [inv_mul_cancel_right]
  obtain ⟨S,_,hS,hcover⟩ := isOpen_biUnion_countable
    (univ : Set (SmallNeutralPatch n ε)) SmallNeutralPatch.raw
    (fun P _ => P.raw_open)
  have hfull : (⋃ P ∈ S, P.raw)=univ := by
    rw [hcover]
    apply eq_univ_of_forall
    intro x
    obtain ⟨P,hP⟩ := hx x
    exact mem_iUnion₂.mpr ⟨P,mem_univ _,hP⟩
  have hSne : S.Nonempty := by
    have hz : (Quotient.mk _ (1 : G n)) ∈ ⋃ P ∈ S, P.raw := by rw [hfull]; trivial
    obtain ⟨P,hP,_⟩ := mem_iUnion₂.mp hz
    exact ⟨P,hP⟩
  obtain ⟨P,hP⟩ := hS.exists_eq_range hSne
  refine ⟨P,?_⟩
  rw [hP] at hfull
  simpa only [biUnion_range] using hfull

end DukePrimeDegree

end

end OAI
