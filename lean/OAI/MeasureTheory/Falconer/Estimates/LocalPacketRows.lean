import OAI.MeasureTheory.Falconer.Estimates.ProjectedPacketRows

namespace OAI

/-! The robust projection theorem in the original coordinates of one
coarse cell. No projected point or fine-scale witness is replaced. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def localPacketPoint (Δ y a : ℝ) (p : Space 2) : Space 2 :=
  rowPoint ((p 0-y)/Δ) ((p 1-a)/Δ)

theorem localPacketPoint_injective {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ) :
    Function.Injective (localPacketPoint Δ y a) := by
  intro p q he
  have h0 := congrArg (fun z : Space 2 => z 0) he
  have h1 := congrArg (fun z : Space 2 => z 1) he
  change (p 0-y)/Δ = (q 0-y)/Δ at h0
  change (p 1-a)/Δ = (q 1-a)/Δ at h1
  have he0 := (div_left_inj' hΔ.ne').1 h0
  have he1 := (div_left_inj' hΔ.ne').1 h1
  ext i
  fin_cases i
  · change p 0 = q 0
    linarith only [he0]
  · change p 1 = q 1
    linarith only [he1]

theorem localPacketPoint_chart {Δ y a : ℝ} (hΔ : 0 < Δ)
    (P : Finset (Space 2))
    (hP : ∀ p ∈ P, |p 0-y| ≤ Δ ∧ |p 1-a| ≤ Δ) :
    InBoundedLineChart (P.image (localPacketPoint Δ y a)) := by
  intro q hq
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
  constructor
  · change |(p 0-y)/Δ| ≤ 1
    rw [abs_div,abs_of_pos hΔ]
    exact (div_le_one hΔ).2 (hP p hp).1
  · change |(p 1-a)/Δ| ≤ 1
    rw [abs_div,abs_of_pos hΔ]
    exact (div_le_one hΔ).2 (hP p hp).2

theorem local_packet_row (N : ℕ) {s t KI KP ρ y a : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hKI : 0 ≤ KI) (hKP : 0 ≤ KP) (hρ : 0 < ρ)
    (P A : Finset (Space 2)) (hP : P.Nonempty) (hAP : A ⊆ P)
    (hsize : ρ*(P.card:ℝ) ≤ (A.card:ℝ))
    (hcell : ∀ p ∈ P, |p 0-y| ≤ 1/(2:ℝ)^N ∧ |p 1-a| ≤ 1/(2:ℝ)^N)
    (henergy : planarProjectionEnergy N s 0
      (P.image (localPacketPoint (1/(2:ℝ)^N) y a)) ≤
      2*projectionEnergyBudget N s t KI KP*(P.card:ℝ)^2) :
    let Δ := 1/(2:ℝ)^N
    let K := projectedSubsetSampleConstant N s t KI KP ρ/(4:ℝ)^s
    ∃ R : Finset (Space 2), R.Nonempty ∧
      R.card ≤ Nat.ceil ((Δ/4)^(-s)) ∧ FiniteSeparatedAt Δ R ∧
      NormalizedFiniteBallBound Δ s K R ∧ 1 ≤ K*Δ^s*(R.card:ℝ) ∧
      ∀ x ∈ R, x 0 = y ∧ ∃ p ∈ A, p 1 = Δ*x 1 ∧ |p 0-x 0| ≤ Δ := by
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
  have henergy' : planarProjectionEnergy N s 0 (P.image F) ≤
      2*projectionEnergyBudget N s t KI KP*((P.image F).card:ℝ)^2 := by
    rwa [hcardP]
  obtain ⟨Q,hQ,hQA,hsep,hreg,_,hcardQ,_⟩ := robust_projection_subset N hs hst hKI hKP
    (by norm_num : |(0:ℝ)| ≤ 1) hρ (P.image F) (A.image F) (hP.image _)
    (localPacketPoint_chart hΔ P hcell) (Finset.image_subset_image hAP) hsize' henergy'
  have hQS : Q ⊆ A.image (fun p => rowPoint 0 ((p 1-a)/(4*Δ))) := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp (hQA hq)
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_image.mpr ⟨p,hp,?_⟩
    unfold lineParameterProjection F localPacketPoint
    simp only [zero_mul,zero_add,rowPoint_one]
    congr 1
    ring
  obtain ⟨R,hR,hRQ,hRsep,hRreg,hrep⟩ := projected_packet_row hΔ A Q hQ hQS
    (fun p hp => (hcell p (hAP hp)).1) hsep hreg
  refine ⟨R,hR,?_,hRsep,hRreg,
    finite_ball_bound_card_lower hΔ hΔ1 hR hRreg,hrep⟩
  rwa [hRQ]

end Falconer

end OAI
