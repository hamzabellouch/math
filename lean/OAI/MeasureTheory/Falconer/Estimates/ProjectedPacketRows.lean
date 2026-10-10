import OAI.MeasureTheory.Falconer.Geometry.RobustProjectionSets

namespace OAI

/-! Undo the harmless quarter scaling used in the projection sampler.
These are actual common-row points, with witnesses in the original packet. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def rowUnquarter (y a : ℝ) (p : Space 2) : Space 2 :=
  rowPoint y (a+4*p 1)

theorem rowUnquarter_injOn (y a : ℝ) (Q : Finset (Space 2))
    (hrow : ∀ p ∈ Q, p 0 = 0) : Set.InjOn (rowUnquarter y a) Q := by
  intro p hp q hq he
  have h1 := congrArg (fun z : Space 2 => z 1) he
  change a+4*p 1 = a+4*q 1 at h1
  ext i
  fin_cases i
  · exact (hrow p hp).trans (hrow q hq).symm
  · change p 1 = q 1
    linarith only [h1]

theorem rowUnquarter_card (y a : ℝ) (Q : Finset (Space 2))
    (hrow : ∀ p ∈ Q, p 0 = 0) : (Q.image (rowUnquarter y a)).card = Q.card :=
  Finset.card_image_iff.mpr (rowUnquarter_injOn y a Q hrow)

theorem rowUnquarter_dist (y a : ℝ) {p q : Space 2}
    (hp : p 0 = 0) (hq : q 0 = 0) :
    dist (rowUnquarter y a p) (rowUnquarter y a q) = 4*dist p q := by
  have hp' : p = rowPoint 0 (p 1) := by ext i; fin_cases i; exact hp; rfl
  have hq' : q = rowPoint 0 (q 1) := by ext i; fin_cases i; exact hq; rfl
  conv_rhs => rw [hp',hq',rowPoint_dist]
  rw [rowUnquarter,rowUnquarter,rowPoint_dist]
  rw [show a+4*p 1-(a+4*q 1) = 4*(p 1-q 1) by ring,abs_mul]
  norm_num

theorem rowUnquarter_separated {δ y a : ℝ} (Q : Finset (Space 2))
    (hrow : ∀ p ∈ Q, p 0 = 0) (hsep : FiniteSeparatedAt δ Q) :
    FiniteSeparatedAt (4*δ) (Q.image (rowUnquarter y a)) := by
  intro p hp q hq hpq
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
  rw [rowUnquarter_dist y a (hrow u hu) (hrow v hv)]
  exact mul_le_mul_of_nonneg_left (hsep u hu v hv (fun h => hpq (congrArg _ h)))
    (by norm_num)

theorem rowUnquarter_regular {δ y a s K : ℝ} (hδ : 0 ≤ δ) (Q : Finset (Space 2))
    (hrow : ∀ p ∈ Q, p 0 = 0) (hreg : NormalizedFiniteBallBound δ s K Q) :
    NormalizedFiniteBallBound (4*δ) s (K/(4:ℝ)^s) (Q.image (rowUnquarter y a)) := by
  intro z r hr hr1
  let w := rowPoint 0 ((z 1-a)/4)
  have hsub : (Q.image (rowUnquarter y a)).filter (fun p => dist p z ≤ r) ⊆
      (Q.filter (fun p => dist p w ≤ r/4)).image (rowUnquarter y a) := by
    intro p hp
    obtain ⟨hp,hpz⟩ := Finset.mem_filter.mp hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,?_⟩,rfl⟩
    have hc := (PiLp.dist_apply_le (rowUnquarter y a q) z 1).trans hpz
    change |a+4*q 1-z 1| ≤ r at hc
    rw [row_dist_projection (hrow q hq)]
    change |q 1-(z 1-a)/4| ≤ r/4
    have he : q 1-(z 1-a)/4 = (a+4*q 1-z 1)/4 := by ring
    rw [he,abs_div]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 4)]
    exact div_le_div_of_nonneg_right hc (by norm_num)
  rw [rowUnquarter_card y a Q hrow]
  calc
    _ ≤ ((Q.filter fun p => dist p w ≤ r/4).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
    _ ≤ K*(r/4)^s*(Q.card:ℝ) := hreg w (r/4) (by linarith only [hr])
      (by linarith only [hr1])
    _ = _ := by rw [Real.div_rpow (by linarith only [hδ,hr]) (by norm_num)]; ring

theorem projected_packet_row {Δ y a s K : ℝ} (hΔ : 0 < Δ)
    (S Q : Finset (Space 2)) (hQ : Q.Nonempty)
    (hQS : Q ⊆ S.image (fun p => rowPoint 0 ((p 1-a)/(4*Δ))))
    (hnear : ∀ p ∈ S, |p 0-y| ≤ Δ)
    (hsep : FiniteSeparatedAt (Δ/4) Q)
    (hreg : NormalizedFiniteBallBound (Δ/4) s K Q) :
    ∃ R : Finset (Space 2), R.Nonempty ∧ R.card = Q.card ∧
      FiniteSeparatedAt Δ R ∧ NormalizedFiniteBallBound Δ s (K/(4:ℝ)^s) R ∧
      ∀ x ∈ R, x 0 = y ∧ ∃ p ∈ S, p 1 = Δ*x 1 ∧ |p 0-x 0| ≤ Δ := by
  have hrow : ∀ q ∈ Q, q 0 = 0 := by
    intro q hq
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp (hQS hq)
    rfl
  let R := Q.image (rowUnquarter y (a/Δ))
  have hscale : 4*(Δ/4) = Δ := by ring
  refine ⟨R,hQ.image _,rowUnquarter_card _ _ Q hrow,?_,?_,?_⟩
  · simpa only [hscale] using rowUnquarter_separated (y := y) (a := a/Δ) Q hrow hsep
  · simpa only [hscale] using rowUnquarter_regular (y := y) (a := a/Δ)
      (by positivity : 0 ≤ Δ/4) Q hrow hreg
  · intro x hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (hQS hq)
    refine ⟨rfl,p,hp,?_,?_⟩
    · change p 1 = Δ*(a/Δ+4*((p 1-a)/(4*Δ)))
      field_simp
      ring
    · exact hnear p hp

end Falconer

end OAI
