import OAI.MeasureTheory.Falconer.Estimates.PacketCentering

namespace OAI

/-! Use an arbitrary good local direction to construct rows for the
centered packet. The witnesses remain points of the original cell subset. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem directed_local_packet_row (N : ℕ) {s t KI KP ρ y a c b : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hKI : 0 ≤ KI) (hKP : 0 ≤ KP) (hρ : 0 < ρ)
    (hc : |c| ≤ 1) (P A : Finset (Space 2)) (hP : P.Nonempty) (hAP : A ⊆ P)
    (hsize : ρ*(P.card:ℝ) ≤ (A.card:ℝ))
    (hcell : ∀ p ∈ P, |p 0-y| ≤ 1/(2:ℝ)^N ∧ |p 1-a| ≤ 1/(2:ℝ)^N)
    (henergy : planarProjectionEnergy N s c
      (P.image (localPacketPoint (1/(2:ℝ)^N) y a)) ≤
      2*projectionEnergyBudget N s t KI KP*(P.card:ℝ)^2) :
    let Δ := 1/(2:ℝ)^N
    let K := projectedSubsetSampleConstant N s t KI KP ρ/(4:ℝ)^s
    ∃ R : Finset (Space 2), R.Nonempty ∧
      R.card ≤ Nat.ceil ((Δ/4)^(-s)) ∧ FiniteSeparatedAt Δ R ∧
      NormalizedFiniteBallBound Δ s K R ∧ 1 ≤ K*Δ^s*(R.card:ℝ) ∧
      ∀ x ∈ R, x 0 = y ∧ ∃ p ∈ A,
        p 1+c*p 0-b = Δ*x 1 ∧ |p 0-x 0| ≤ Δ := by
  dsimp only
  let Δ := 1/(2:ℝ)^N
  let F := localPacketPoint Δ y a
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ1 : Δ ≤ 1 := (div_le_one (by positivity : (0:ℝ) < (2:ℝ)^N)).2
    (one_le_pow₀ (by norm_num))
  have hcardP : (P.image F).card = P.card :=
    Finset.card_image_of_injective _ (localPacketPoint_injective hΔ y a)
  have hcardA : (A.image F).card = A.card :=
    Finset.card_image_of_injective _ (localPacketPoint_injective hΔ y a)
  have hsize' : ρ*((P.image F).card:ℝ) ≤ ((A.image F).card:ℝ) := by
    rwa [hcardP,hcardA]
  have henergy' : planarProjectionEnergy N s c (P.image F) ≤
      2*projectionEnergyBudget N s t KI KP*((P.image F).card:ℝ)^2 := by
    rwa [hcardP]
  obtain ⟨Q,hQ,hQA,hsep,hreg,_,hcardQ,_⟩ := robust_projection_subset N hs hst hKI hKP hc hρ
    (P.image F) (A.image F) (hP.image _)
    (localPacketPoint_chart hΔ P hcell) (Finset.image_subset_image hAP) hsize' henergy'
  let S := A.image (packetCenterPoint c b)
  let a' := a+c*y-b
  have hQS : Q ⊆ S.image (fun p => rowPoint 0 ((p 1-a')/(4*Δ))) := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp (hQA hq)
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_image.mpr ⟨packetCenterPoint c b p,Finset.mem_image.mpr ⟨p,hp,rfl⟩,?_⟩
    have he : lineParameterProjection c (F p)/4 =
        (packetCenterPoint c b p 1-a')/(4*Δ) := by
      dsimp [F,localPacketPoint,lineParameterProjection,packetCenterPoint,a']
      field_simp
      ring
    rw [he]
  have hnear : ∀ p ∈ S, |p 0-y| ≤ Δ := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact (hcell q (hAP hq)).1
  obtain ⟨R,hR,hRQ,hRsep,hRreg,hrep⟩ := projected_packet_row hΔ S Q hQ hQS hnear hsep hreg
  refine ⟨R,hR,?_,hRsep,hRreg,finite_ball_bound_card_lower hΔ hΔ1 hR hRreg,?_⟩
  · rwa [hRQ]
  · intro x hx
    obtain ⟨hx0,p,hp,hp1,hp0⟩ := hrep x hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hx0,q,hq,hp1,hp0⟩

end Falconer

end OAI
