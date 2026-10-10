import OAI.MeasureTheory.Falconer.Estimates.LocalPacketRows

namespace OAI

/-! Center a genuine coarse line packet by an affine shear. Translation in
line-parameter space preserves all pencil counts and ball bounds exactly;
the point-line residual is unchanged. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def packetCenterPoint (c b : ℝ) (p : Space 2) : Space 2 :=
  rowPoint (p 0) (p 1+c*p 0-b)

noncomputable def packetCenterLine (c b : ℝ) (l : Space 2) : Space 2 :=
  rowPoint (l 0+c) (l 1-b)

theorem packetCenterPoint_inverse (c b : ℝ) (p : Space 2) :
    packetCenterPoint (-c) (-b) (packetCenterPoint c b p) = p := by
  ext i
  fin_cases i
  · rfl
  · change p 1+c*p 0-b+(-c)*p 0-(-b) = p 1
    ring

theorem packetCenterPoint_injective (c b : ℝ) :
    Function.Injective (packetCenterPoint c b) :=
  Function.LeftInverse.injective (packetCenterPoint_inverse c b)

theorem packetCenterLine_inverse (c b : ℝ) (l : Space 2) :
    packetCenterLine (-c) (-b) (packetCenterLine c b l) = l := by
  ext i
  fin_cases i
  · change l 0+c+(-c) = l 0
    ring
  · change l 1-b-(-b) = l 1
    ring

theorem packetCenterLine_injective (c b : ℝ) :
    Function.Injective (packetCenterLine c b) :=
  Function.LeftInverse.injective (packetCenterLine_inverse c b)

theorem packetCenterLine_dist (c b : ℝ) (l m : Space 2) :
    dist (packetCenterLine c b l) (packetCenterLine c b m) = dist l m := by
  have he (l : Space 2) : packetCenterLine c b l = l+rowPoint c (-b) := by
    ext i
    fin_cases i
    · rfl
    · change l 1-b = l 1+(-b)
      ring
  rw [he l,he m,dist_add_right]

theorem packetCenterLine_card (c b : ℝ) (T : Finset (Space 2)) :
    (T.image (packetCenterLine c b)).card = T.card :=
  Finset.card_image_of_injective _ (packetCenterLine_injective c b)

theorem packetCenterLine_separated {δ c b : ℝ} (T : Finset (Space 2))
    (hT : FiniteSeparatedAt δ T) : FiniteSeparatedAt δ (T.image (packetCenterLine c b)) := by
  intro l hl m hm hne
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hm
  rw [packetCenterLine_dist]
  exact hT p hp q hq (fun h => hne (congrArg _ h))

theorem packetCenterLine_regular {δ s K c b : ℝ} (T : Finset (Space 2))
    (hT : NormalizedFiniteBallBound δ s K T) :
    NormalizedFiniteBallBound δ s K (T.image (packetCenterLine c b)) := by
  intro z r hr hr1
  let w := packetCenterLine (-c) (-b) z
  have hw : packetCenterLine c b w = z := by
    simpa only [neg_neg] using packetCenterLine_inverse (-c) (-b) z
  have hsub : (T.image (packetCenterLine c b)).filter (fun l => dist l z ≤ r) ⊆
      (T.filter (fun l => dist l w ≤ r)).image (packetCenterLine c b) := by
    intro l hl
    obtain ⟨hl,hlr⟩ := Finset.mem_filter.mp hl
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hl
    refine Finset.mem_image.mpr ⟨m,Finset.mem_filter.mpr ⟨hm,?_⟩,rfl⟩
    rwa [← hw,packetCenterLine_dist] at hlr
  rw [packetCenterLine_card]
  exact (Nat.cast_le.mpr ((Finset.card_le_card hsub).trans Finset.card_image_le)).trans
    (hT w r hr hr1)

theorem packetCenter_residual (c b : ℝ) (p l : Space 2) :
    packetCenterPoint c b p 1-packetCenterLine c b l 0*packetCenterPoint c b p 0-
      packetCenterLine c b l 1 = p 1-l 0*p 0-l 1 := by
  change p 1+c*p 0-b-(l 0+c)*p 0-(l 1-b) = _
  ring

theorem packetCenter_residual_le {δ c b : ℝ} (hδ : 0 ≤ δ)
    (p l : Space 2) (hslope : |l 0| ≤ 1) (hi : TubeIncident δ p l) :
    |packetCenterPoint c b p 1-packetCenterLine c b l 0*packetCenterPoint c b p 0-
      packetCenterLine c b l 1| ≤ 2*δ := by
  rw [packetCenter_residual]
  exact tube_residual_le hδ hslope hi

theorem local_centered_projection {Δ : ℝ} (hΔ : 0 < Δ)
    (c b y a : ℝ) (p : Space 2) :
    lineParameterProjection 0
      (localPacketPoint Δ y (a+c*y-b) (packetCenterPoint c b p)) =
      lineParameterProjection c (localPacketPoint Δ y a p) := by
  simp only [lineParameterProjection,localPacketPoint,packetCenterPoint,rowPoint_zero,
    rowPoint_one,zero_mul,zero_add]
  field_simp
  ring

end Falconer

end OAI
