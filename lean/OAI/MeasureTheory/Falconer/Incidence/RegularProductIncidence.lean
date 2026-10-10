import OAI.MeasureTheory.Falconer.Geometry.RegularSmallProjections
import OAI.MeasureTheory.Falconer.Measures.ProductProjectionReduction
import OAI.MeasureTheory.Falconer.Measures.ScalarSubsetMass

namespace OAI

/-! Strict incidence gain on the actual regular product configuration.
The sole analytic ingredient is the proved small-projection obstruction. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem regular_product_incidence {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let W := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ (Y : Finset ℝ) (P : ℝ → Finset (Space 2)) (T : Space 2 → Finset (Space 2))
        (s KP KT KY n m M R : ℝ) (NP : ℕ),
      Y.Nonempty → κ ≤ s → s ≤ 1 → 0 ≤ KP → 0 ≤ KT → 0 ≤ KY →
      0 < n → 0 < m → 0 ≤ M → 0 < R → 0 < NP →
      (∀ y ∈ Y, |y| ≤ 1 ∧ FiniteSeparatedAt δ (P y) ∧
        NormalizedFiniteBallBound δ s KP (P y) ∧ n ≤ ((P y).card:ℝ) ∧
        (P y).card ≤ NP ∧ ∀ x ∈ P y, x 0 = y) →
      (∀ y ∈ Y, ∀ x ∈ P y, InBoundedLineChart (T x) ∧
        NormalizedFiniteBallBound δ s KT (T x) ∧ m ≤ ((T x).card:ℝ) ∧
        ((T x).card:ℝ) ≤ M ∧ ∀ l ∈ T x, TubeIncident δ x l) →
      FiniteSeparatedAt δ (Y.biUnion fun y => (P y).biUnion T) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass Y u r ≤ KY*r^(2*κ)*(Y.card:ℝ)) →
      4*R ≤ W → 4*R*KY ≤ W →
      4*R^2*((4:ℝ)^(2*s)+25*KP*KT*(M/m)*(4:ℝ)^s) ≤ W →
      ((7*NP:ℕ):ℝ)^2 ≤ W*(n*m/50) →
      Real.log ((7*NP:ℕ):ℝ) ≤ (1-4*κ)*(N:ℝ)*Real.log 2 →
      R*(n*m/25) < ((Y.biUnion fun y => (P y).biUnion T).card:ℝ) := by
  obtain ⟨ε,N0,hε,hN0,hmain⟩ := regular_small_projection_obstruction hκ hκ1
  refine ⟨ε,N0,hε,hN0,?_⟩
  intro N hN
  dsimp only
  intro Y P T s KP KT KY n m M R NP hY hs hs1 hKP hKT hKY hn hm hM hR hNP
    hrows hpencils hsep hYball hRcost hYcost hGcost hPcost hlog
  let δ := (1/2:ℝ)^N
  let W := Real.exp (ε*(N:ℝ)*Real.log 2)
  let A := fun y => (P y).biUnion T
  let U := Y.biUnion A
  have hδ : 0 < δ := by positivity
  have hW : 0 < W := Real.exp_pos _
  have hs0 : 0 ≤ s := hκ.le.trans hs
  by_contra hnot
  have hunion : (U.card:ℝ) ≤ R*(n*m/25) := le_of_not_gt hnot
  obtain ⟨G,hGU,hG,hGcard,hGreg,Z,hZY,hZ,hYZ,hcommon⟩ :=
    product_projection_reduction Y hY P T hδ hs0 hKP hKT hn hm hM hR NP hrows hpencils hunion
  have hGupper : (G.card:ℝ) ≤ W*(n*m/100) := by
    calc
      _ ≤ (U.card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hGU)
      _ ≤ R*(n*m/25) := hunion
      _ = (4*R)*(n*m/100) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hRcost (by positivity)
  have hmass : W⁻¹*(G.card:ℝ) ≤ n*m/100 := by
    have hh := mul_le_mul_of_nonneg_left hGupper (inv_nonneg.mpr hW.le)
    have he : W⁻¹*(W*(n*m/100)) = n*m/100 := by field_simp
    rwa [he] at hh
  have hGregular : NormalizedFiniteBallBound δ (2*s) W G := by
    intro z r hr hr1
    have hh := mul_le_mul_of_nonneg_right hGcost
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) (2*s)) (Nat.cast_nonneg G.card))
    exact (hGreg z r hr hr1).trans (by simpa only [mul_assoc,W] using hh)
  have hZball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass Z u r ≤ W*r^(2*κ)*(Z.card:ℝ) := by
    intro u r hr hr1
    have hrpow : 0 ≤ r^(2*κ) := Real.rpow_nonneg (hδ.le.trans hr) _
    calc
      _ ≤ scalarBallMass Y u r := scalarBallMass_mono hZY u r
      _ ≤ KY*r^(2*κ)*(Y.card:ℝ) := hYball u r hr hr1
      _ ≤ KY*r^(2*κ)*(4*R*(Z.card:ℝ)) := mul_le_mul_of_nonneg_left hYZ (mul_nonneg hKY hrpow)
      _ = (4*R*KY)*(r^(2*κ)*(Z.card:ℝ)) := by ring
      _ ≤ W*(r^(2*κ)*(Z.card:ℝ)) :=
        mul_le_mul_of_nonneg_right hYcost (mul_nonneg hrpow (Nat.cast_nonneg Z.card))
      _ = _ := by ring
  have hGbounded : ∀ p ∈ G, ∀ i, |p i| ≤ 1 := by
    intro p hp i
    obtain ⟨y,hy,hp⟩ := Finset.mem_biUnion.mp (hGU hp)
    obtain ⟨x,hx,hp⟩ := Finset.mem_biUnion.mp hp
    have hbound := (hpencils y hy x hx).1 p hp
    fin_cases i
    · exact hbound.1
    · exact hbound.2
  apply hmain N hN (2*s) Z G (fun y => G ∩ A y) (7*NP)
    (by linarith only [hs]) (by linarith only [hs1]) hZ hG (by omega)
    (fun z hz => (hrows z (hZY hz)).1) hGbounded (finiteSeparatedAt_subset hGU hsep)
    hGregular
  · have hGc : n*m/50 ≤ (G.card:ℝ) := by convert hGcard using 1; ring
    exact hPcost.trans (mul_le_mul_of_nonneg_left hGc hW.le)
  · exact hZball
  · intro y hy
    refine ⟨Finset.inter_subset_left,?_,(hcommon y hy).2⟩
    exact hmass.trans (by convert (hcommon y hy).1 using 1; ring)
  · exact hlog

end Falconer

end OAI
