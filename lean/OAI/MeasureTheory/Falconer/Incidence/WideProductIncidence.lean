import OAI.MeasureTheory.Falconer.Incidence.NormalizedProductPencils
import OAI.MeasureTheory.Falconer.Incidence.RegularProductIncidence

namespace OAI

/-! Product incidence for the actual width-three packet geometry. The
rounding and bounded-chart normalization are performed inside the proof;
separation of the original union is not required. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem wide_product_incidence {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let α := (1/2:ℝ)^N
      let δ := 4*α
      let W := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ (Y : Finset ℝ) (P : ℝ → Finset (Space 2)) (T : Space 2 → Finset (Space 2))
        (s KP KT KY n m M R : ℝ) (NP : ℕ),
      δ ≤ 1/8 → Y.Nonempty → κ ≤ s → s ≤ 1 → 1 ≤ KP → 1 ≤ KT → 0 ≤ KY →
      0 < n → 0 < m → 0 ≤ M → 0 < R → 0 < NP →
      (∀ y ∈ Y, |y| ≤ 1 ∧ FiniteSeparatedAt δ (P y) ∧
        NormalizedFiniteBallBound δ s KP (P y) ∧ n ≤ ((P y).card:ℝ) ∧
        (P y).card ≤ NP ∧ ∀ x ∈ P y, x 0 = y) →
      (∀ y ∈ Y, ∀ x ∈ P y, InBoundedLineChart (T x) ∧ FiniteSeparatedAt δ (T x) ∧
        NormalizedFiniteBallBound δ s KT (T x) ∧ m ≤ ((T x).card:ℝ) ∧
        ((T x).card:ℝ) ≤ M ∧ ∀ l ∈ T x, TubeIncident (3*δ) x l) →
      (∀ u r : ℝ, α ≤ r → r ≤ 1 → scalarBallMass Y u r ≤ KY*r^(2*κ)*(Y.card:ℝ)) →
      4*(361^2*R) ≤ W → 4*(361^2*R)*KY ≤ W →
      4*(361^2*R)^2*((4:ℝ)^(2*s)+25*(KP*(4:ℝ)^s)*
        ((361*KT*(10:ℝ)^s)*(4:ℝ)^s)*(M/(m/361))*(4:ℝ)^s) ≤ W →
      ((7*NP:ℕ):ℝ)^2 ≤ W*(n*(m/361)/50) →
      Real.log ((7*NP:ℕ):ℝ) ≤ (1-4*κ)*(N:ℝ)*Real.log 2 →
      R*(n*m/25) < ((Y.biUnion fun y => (P y).biUnion T).card:ℝ) := by
  obtain ⟨ε,N0,hε,hN0,hmain⟩ := regular_product_incidence hκ hκ1
  refine ⟨ε,N0,hε,hN0,?_⟩
  intro N hN
  dsimp only
  intro Y P T s KP KT KY n m M R NP hsmall hY hs hs1 hKP hKT hKY hn hm hM hR hNP
    hrows hpencils hYball hRc hYc hGc hPc hlog
  let α := (1/2:ℝ)^N
  let δ := 4*α
  let Q := fun y => (P y).image verticalQuarter
  let U := normalizedRowPencils δ T
  let F := Y.biUnion P
  have hδ : 0 < δ := by dsimp [δ,α]; positivity
  have hscale : δ/4 = α := by dsimp [δ]; ring
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hQrows : ∀ y ∈ Y, |y| ≤ 1 ∧ FiniteSeparatedAt α (Q y) ∧
      NormalizedFiniteBallBound α s (KP*(4:ℝ)^s) (Q y) ∧ n ≤ ((Q y).card:ℝ) ∧
      (Q y).card ≤ NP ∧ ∀ x ∈ Q y, x 0 = y := by
    intro y hy
    obtain ⟨hy1,hsep,hreg,hlo,hup,hrow⟩ := hrows y hy
    refine ⟨hy1,?_,?_,?_,?_,?_⟩
    · simpa only [hscale,Q] using verticalQuarter_row_separated (δ := δ) (P y) hrow hsep
    · simpa only [hscale,Q] using verticalQuarter_row_regular hδ hs0 hKP (P y) hrow hreg
    · simpa only [Q,Finset.card_image_of_injective _ verticalQuarter_injective] using hlo
    · simpa only [Q,Finset.card_image_of_injective _ verticalQuarter_injective] using hup
    · intro x hx
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      exact hrow p hp
  have hUpencils : ∀ y ∈ Y, ∀ x ∈ Q y, InBoundedLineChart (U x) ∧
      NormalizedFiniteBallBound α s ((361*KT*(10:ℝ)^s)*(4:ℝ)^s) (U x) ∧
      m/361 ≤ ((U x).card:ℝ) ∧ ((U x).card:ℝ) ≤ M ∧
      ∀ l ∈ U x, TubeIncident α x l := by
    intro y hy x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    have hp0 : |p 0| ≤ 1 := by rw [(hrows y hy).2.2.2.2.2 p hp]; exact (hrows y hy).1
    obtain ⟨hchart,hsep,hreg,hlo,hup,hinc⟩ := hpencils y hy p hp
    simp only [U,normalizedRowPencils,verticalFour_verticalQuarter]
    refine ⟨normalizedPencil_chart hδ hsmall p (T p) hp0 hchart hinc,?_,?_,?_,?_⟩
    · simpa only [hscale] using normalizedPencil_regular hδ hs0 hKT p (T p) hp0 hsep hchart hinc hreg
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 361)).2
      have hh := hlo.trans (normalizedPencil_card_lower hδ p (T p) hp0 hsep
        (fun l hl => ⟨(hchart l hl).1,hinc l hl⟩))
      simpa only [mul_comm] using hh
    · exact (Nat.cast_le.mpr (normalizedPencil_card_upper δ p (T p))).trans hup
    · simpa only [hscale] using normalizedPencil_incident hδ p (T p)
  have hF0 : ∀ p ∈ F, |p 0| ≤ 1 := by
    intro p hp
    obtain ⟨y,hy,hp⟩ := Finset.mem_biUnion.mp hp
    rw [(hrows y hy).2.2.2.2.2 p hp]
    exact (hrows y hy).1
  have hFT : ∀ p ∈ F, ∀ l ∈ T p, |l 0| ≤ 1 ∧ TubeIncident (3*δ) p l := by
    intro p hp l hl
    obtain ⟨y,hy,hp⟩ := Finset.mem_biUnion.mp hp
    exact ⟨((hpencils y hy p hp).1 l hl).1,(hpencils y hy p hp).2.2.2.2.2 l hl⟩
  have he : Y.biUnion (fun y => (Q y).biUnion U) =
      (F.image verticalQuarter).biUnion U := by
    simp only [F,Q,Finset.biUnion_image,Finset.biUnion_biUnion]
  have hsep : FiniteSeparatedAt α (Y.biUnion fun y => (Q y).biUnion U) := by
    rw [he]
    simpa only [hscale,U] using normalizedRowPencils_union_separated hδ F T
  have hupper : ((Y.biUnion fun y => (Q y).biUnion U).card:ℝ) ≤
      361*((Y.biUnion fun y => (P y).biUnion T).card:ℝ) := by
    rw [he]
    simpa only [U,F,Finset.biUnion_biUnion] using normalizedRowPencils_union_card hδ F T hF0 hFT
  have hgrowth := hmain N hN Y Q U s (KP*(4:ℝ)^s) ((361*KT*(10:ℝ)^s)*(4:ℝ)^s)
    KY n (m/361) M (361^2*R) NP hY hs hs1 (by positivity) (by positivity) hKY
    hn (by positivity) hM (by positivity) hNP hQrows hUpencils hsep hYball hRc hYc hGc hPc hlog
  nlinarith only [hgrowth,hupper]

end Falconer

end OAI
