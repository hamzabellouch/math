import OAI.MeasureTheory.Falconer.Angular.LocalDirectionPackets
import OAI.MeasureTheory.Falconer.Estimates.LocalLineResolution

namespace OAI

/-! Local packet thinning after the actual cell similarity, with preserved
point mass, point regularity, and the original global tube count. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem rescaled_cell_packet_refinement {δ Δ s t K KP y a m M : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hρ1 : δ/Δ ≤ 1/2)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (hKP : 0 ≤ KP) (hy : |y| ≤ 1)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hcell : ∀ p ∈ P, |p 0-y| ≤ Δ/4 ∧ |p 1-a| ≤ Δ/4)
    (hPsep : FiniteSeparatedAt δ P)
    (hPball : NormalizedFiniteBallBound (δ/Δ) t KP
      (P.image (localPacketPoint Δ y a)))
    (hT : ∀ p ∈ P, (T p).Nonempty ∧ m ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ M ∧
      NormalizedFiniteBallBound δ s K (T p) ∧
      ∀ l ∈ T p, |l 0| ≤ 1/2 ∧ TubeIncident δ p l)
    (D : ℕ) (hD : ∀ p ∈ P, (T p).card ≤ D) :
    let J := Nat.log 2 D+1
    ∃ k : ℕ, ∃ Q ⊆ P.image (localPacketPoint Δ y a), Q.Nonempty ∧
      (P.card:ℝ) ≤ (J:ℝ)*(Q.card:ℝ) ∧
      (∀ p ∈ Q, |p 0| ≤ 1/4 ∧ |p 1| ≤ 1/4) ∧
      FiniteSeparatedAt (δ/Δ) Q ∧ NormalizedFiniteBallBound (δ/Δ) t (KP*(J:ℝ)) Q ∧
      ∃ U : Space 2 → Finset (Space 2),
        (∀ p ∈ Q, (U p).Nonempty ∧ InBoundedLineChart (U p) ∧
          FiniteSeparatedAt (δ/Δ) (U p) ∧
          NormalizedFiniteBallBound (δ/Δ) s (2*((K*3^s)*7^s)*(J:ℝ)) (U p) ∧
          (∀ l ∈ U p, TubeIncident (δ/Δ) p l) ∧
          m/(2*(J:ℝ)*(2:ℝ)^k) ≤ ((U p).card:ℝ) ∧
          ((U p).card:ℝ) ≤ M/(2:ℝ)^k) ∧
        (2:ℝ)^k*((Q.biUnion U).card:ℝ) ≤ 13*((P.biUnion T).card:ℝ) ∧
        ((∀ a : ℝ, |a| ≤ 1/2 → |lineGridRound (δ/Δ) a| ≤ 1/2) →
          ∀ p ∈ Q, ∀ l ∈ U p, |l 0| ≤ 1/2) := by
  let ρ := δ/Δ
  let F := localPacketPoint Δ y a
  let L := localCellLine Δ y a
  let G := fun z : Space 2 => Δ • z+rowPoint y a
  let P' := P.image F
  let V := fun z => (T (G z)).image L
  let J := Nat.log 2 D+1
  have hρ : 0 < ρ := div_pos hδ hΔ
  have hδρ : δ ≤ ρ := by
    apply (le_div_iff₀ hΔ).2
    nlinarith only [hΔ1,hδ]
  have hG (p : Space 2) : G (F p) = p := by
    apply localPacketPoint_injective hΔ y a
    exact localPacketPoint_inverse hΔ y a (F p)
  have hV (p : Space 2) : V (F p) = (T p).image L := by
    dsimp only [V]
    rw [hG]
  have hVc (p : Space 2) : (V (F p)).card = (T p).card := by
    rw [hV,Finset.card_image_of_injective _ (localCellLine_injective hΔ y a)]
  have hP' : P'.Nonempty := hP.image F
  have hsmall : ∀ p ∈ P', |p 0| ≤ 1/4 ∧ |p 1| ≤ 1/4 := by
    intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    constructor
    · change |(p 0-y)/Δ| ≤ 1/4
      rw [abs_div,abs_of_pos hΔ]
      exact (div_le_iff₀ hΔ).2 (by linarith only [(hcell p hp).1])
    · change |(p 1-a)/Δ| ≤ 1/4
      rw [abs_div,abs_of_pos hΔ]
      exact (div_le_iff₀ hΔ).2 (by linarith only [(hcell p hp).2])
  have hK' : 1 ≤ K*3^s := by
    have hh := Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 3) hs
    nlinarith only [hK,hh,mul_le_mul hK hh (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hK)]
  have hVdata : ∀ z ∈ P', (V z).Nonempty ∧ NormalizedFiniteBallBound δ s (K*3^s) (V z) ∧
      ∀ l ∈ V z, |l 0| ≤ 1/2 ∧ TubeIncident ρ z l := by
    intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    rw [hV]
    refine ⟨(hT p hp).1.image L,?_,?_⟩
    · exact localCellLine_regular_at hΔ hΔ1 hy hδ le_rfl hs hK (T p) (hT p hp).2.2.2.1
    · intro l hl
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hl
      exact ⟨((hT p hp).2.2.2.2 b hb).1,
        localCellLine_incident hΔ y a p b ((hT p hp).2.2.2.2 b hb).2⟩
  have hVD : ∀ z ∈ P', (V z).card ≤ D := by
    intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    rw [hVc]
    exact hD p hp
  obtain ⟨k,Q,hQP',hQ,hmass,U,hU,hunion⟩ := local_direction_packet_refinement
    hρ hρ1 hδρ hs hK' P' V hP' hsmall hVdata D hVD
  have hPcard : P'.card = P.card := Finset.card_image_of_injective _ (localPacketPoint_injective hΔ y a)
  have hP'sep : FiniteSeparatedAt ρ P' := by
    intro z hz w hw hzw
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hw
    rw [localPacketPoint_dist hΔ]
    exact div_le_div_of_nonneg_right (hPsep p hp q hq (fun he => hzw (congrArg F he))) hΔ.le
  have hVU : P'.biUnion V ⊆ (P.biUnion T).image L := by
    intro l hl
    obtain ⟨z,hz,hl⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    rw [hV] at hl
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_image_of_mem L (Finset.mem_biUnion.mpr ⟨p,hp,hb⟩)
  have hVUcard : ((P'.biUnion V).card:ℝ) ≤ ((P.biUnion T).card:ℝ) :=
    Nat.cast_le.mpr ((Finset.card_le_card hVU).trans Finset.card_image_le)
  refine ⟨k,Q,hQP',hQ,by simpa only [hPcard] using hmass,
    fun p hp => hsmall p (hQP' hp),finiteSeparatedAt_subset hQP' hP'sep,
    normalized_finite_ball_bound_subset hρ.le hKP hQP' hmass hPball,U,?_,
    hunion.trans (mul_le_mul_of_nonneg_left hVUcard (by norm_num)),?_⟩
  · intro z hz
    obtain ⟨p,hp,hpEq⟩ := Finset.mem_image.mp (hQP' hz)
    have hsize : m ≤ ((V z).card:ℝ) ∧ ((V z).card:ℝ) ≤ M := by
      rw [← hpEq,hVc]
      exact ⟨(hT p hp).2.1,(hT p hp).2.2.1⟩
    obtain ⟨_,hne,hchart,hsep,hball,hinc,_,hlo,hhi,_⟩ := hU z hz
    refine ⟨hne,hchart,hsep,hball,hinc,?_,?_⟩
    · apply (div_le_iff₀ (by positivity : 0 < 2*(J:ℝ)*(2:ℝ)^k)).2
      have hh : ((V z).card:ℝ) ≤ (J:ℝ)*(2*(2:ℝ)^k)*((U z).card:ℝ) := by exact_mod_cast hlo
      nlinarith only [hsize.1,hh]
    · apply (le_div_iff₀ (by positivity : 0 < (2:ℝ)^k)).2
      have hh : (2:ℝ)^k*((U z).card:ℝ) ≤ ((V z).card:ℝ) := by exact_mod_cast hhi
      nlinarith only [hh,hsize.2]
  · intro hround z hz l hl
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ((hU z hz).1 hl)
    exact hround (b 0) (((hVdata z (hQP' hz)).2.2 b hb).1)

end Falconer

end OAI
