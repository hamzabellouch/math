import OAI.MeasureTheory.Falconer.Incidence.CenteredPacketPencils
import OAI.MeasureTheory.Falconer.Measures.WideProductPower

namespace OAI

/-! The product gain applies to the original fine pencils of a coarse
packet. The proof constructs their row pencils by dilation and retains
control of the actual original union. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem centered_packet_product_power {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < η ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let Δ := 4*(1/2:ℝ)^N
      let D := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ (s c b : ℝ) (Y : Finset ℝ) (P : ℝ → Finset (Space 2))
        (S : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (NP : ℕ),
      let L := Real.exp ((s-ε)*(N:ℝ)*Real.log 2)
      let U := Real.exp ((s+ε)*(N:ℝ)*Real.log 2)
      κ ≤ s → s ≤ 1-8*κ → Y.Nonempty → 0 < NP → (NP:ℝ) ≤ U →
      (∀ y ∈ Y, |y| ≤ 1 ∧ FiniteSeparatedAt Δ (P y) ∧
        NormalizedFiniteBallBound Δ s D (P y) ∧ L ≤ ((P y).card:ℝ) ∧
        (P y).card ≤ NP ∧ ∀ x ∈ P y, x 0 = y) →
      (∀ y ∈ Y, ∀ x ∈ P y, ∃ p ∈ S, p 1+c*p 0-b = Δ*x 1 ∧ |p 0-y| ≤ Δ) →
      (∀ p ∈ S, FiniteSeparatedAt (Δ^2) (T p) ∧
        NormalizedFiniteBallBound (Δ^2) s (D/Δ^s) (T p) ∧
        L ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ U ∧
        ∀ l ∈ T p, |l 0| ≤ 1 ∧ |l 0+c| ≤ Δ ∧ |l 1-b| ≤ Δ ∧ TubeIncident (Δ^2) p l) →
      (∀ u r : ℝ, (1/2:ℝ)^N ≤ r → r ≤ 1 →
        scalarBallMass Y u r ≤ D*r^(2*κ)*(Y.card:ℝ)) →
      Real.exp ((2*s+η)*(N:ℝ)*Real.log 2) ≤ ((S.biUnion T).card:ℝ) := by
  obtain ⟨ε,η,Nmin,hε,hη,hNmin,hmain⟩ := wide_product_power hκ hκ1
  refine ⟨ε,η,max Nmin 5,hε,hη,lt_of_lt_of_le hNmin (le_max_left _ _),?_⟩
  intro N hN
  dsimp only
  intro s c b Y P S T NP hs hs1 hY hNP hNPup hrows hrep hT hYball
  let Δ := 4*(1/2:ℝ)^N
  let D := Real.exp (ε*(N:ℝ)*Real.log 2)
  let L := Real.exp ((s-ε)*(N:ℝ)*Real.log 2)
  let U := Real.exp ((s+ε)*(N:ℝ)*Real.log 2)
  let Z := Y.biUnion P
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hN5 : 5 ≤ N := (le_max_right _ _).trans hN
  have hΔ1 : Δ ≤ 1 := by
    have hh := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) ≤ 1) hN5
    norm_num at hh
    dsimp [Δ]
    linarith only [hh]
  have hrepZ : ∀ x ∈ Z, ∃ p ∈ S, p 1+c*p 0-b = Δ*x 1 ∧ |p 0-x 0| ≤ Δ := by
    intro x hx
    obtain ⟨y,hy,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨p,hp,h1,h0⟩ := hrep y hy x hx
    refine ⟨p,hp,h1,?_⟩
    rwa [(hrows y hy).2.2.2.2.2 x hx]
  obtain ⟨V,hcard,hV⟩ := centered_packet_pencil_lift hΔ hΔ1 Z S T hrepZ hT
  have hVp : ∀ y ∈ Y, ∀ x ∈ P y, InBoundedLineChart (V x) ∧
      FiniteSeparatedAt Δ (V x) ∧ NormalizedFiniteBallBound Δ s D (V x) ∧
      L ≤ ((V x).card:ℝ) ∧ ((V x).card:ℝ) ≤ U ∧
      ∀ l ∈ V x, TubeIncident (3*Δ) x l := by
    intro y hy x hx
    obtain ⟨hc,hs,hr,hl,hu,hi⟩ := hV x (Finset.mem_biUnion.mpr ⟨y,hy,hx⟩)
    have he : (D/Δ^s)*Δ^s = D := div_mul_cancel₀ D (Real.rpow_pos_of_pos hΔ s).ne'
    rw [he] at hr
    exact ⟨hc,hs,hr,hl,hu,hi⟩
  have hgain := hmain N ((le_max_left _ _).trans hN) s Y P V NP hs hs1 hY hNP hNPup
    hrows hVp hYball
  have hunion : Y.biUnion (fun y => (P y).biUnion V) = Z.biUnion V := by
    simp only [Z,Finset.biUnion_biUnion]
  rw [hunion] at hgain
  exact hgain.trans hcard

end Falconer

end OAI
