import OAI.MeasureTheory.Falconer.Incidence.LeafIncidenceGain
import OAI.MeasureTheory.Falconer.Incidence.LeafPencilTransport
import OAI.MeasureTheory.Falconer.Incidence.LeafPrefixPower

namespace OAI

/-! Original points and pencils enter the profile theorem through their
actual leaf assignment. The conclusion counts original line parameters. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem uniform_centered_planar_incidence {κ s t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100)
    (hs : κ ≤ s) (hs1 : s ≤ 1-8*κ) (ht : s+8*κ ≤ t) :
    ∃ B : ℕ, 0 < B ∧ Even B ∧ ∃ lam ζ : ℝ, 0 < lam ∧ 0 < ζ ∧
    ∃ M : ℕ, 0 < M ∧ ∀ m : ℕ, M ≤ m →
    ∀ Q : DyadicCube 2, Q.side = 1 → Q.center = 0 →
    ∀ δ K a b : ℝ, 0 < δ → 1 ≤ K → 0 < a →
      16*δ ≤ 1/(2:ℝ)^(m*B) →
      K*2^t ≤ (2:ℝ)^((lam/4)*(m*B:ℕ)) →
      K*4^s ≤ (2:ℝ)^(lam*(m*B:ℕ)) → b ≤ (2:ℝ)^(lam*(m*B:ℕ))*a →
    ∀ P : Finset (Space 2), P.Nonempty → (∀ x ∈ P, x ∈ Q.carrier) →
      FiniteSeparatedAt (2/(2:ℝ)^(m*B)) P → NormalizedFiniteBallBound δ t K P →
    ∀ V : Space 2 → Finset (Space 2),
      (∀ x ∈ P, a ≤ ((V x).card:ℝ) ∧ ((V x).card:ℝ) ≤ b ∧
        InBoundedLineChart (V x) ∧ FiniteSeparatedAt (1/(2:ℝ)^(m*B)) (V x) ∧
        NormalizedFiniteBallBound δ s K (V x) ∧
        ∀ u ∈ V x, |u 0| ≤ 1/2 ∧ TubeIncident δ x u) →
      (2:ℝ)^((s+ζ)*(m*B:ℕ)) ≤ ((P.biUnion V).card:ℝ)/a := by
  obtain ⟨B,hB,hBeven,lam,ζ,hlam,hζ,M,hM,hgain⟩ := uniform_leaf_incidence_gain hκ hκ1 hs hs1 ht
  refine ⟨B,hB,hBeven,lam,ζ,hlam,hζ,M,hM,?_⟩
  intro m hm Q hQ hcenter δ K a b hδ hK ha hsmall hpointbudget hpencilbudget hsize P hP hcarry hsep hball V hV
  have ht0 : 0 ≤ t := by linarith
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hsmall' : Real.sqrt 2*(Q.side/(2:ℝ)^(m*B)) < 2/(2:ℝ)^(m*B) := by
    rw [hQ]
    have hh : Real.sqrt 2 < 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)]
    have hp := mul_lt_mul_of_pos_right hh (show 0 < 1/(2:ℝ)^(m*B) by positivity)
    convert hp using 1
    ring
  obtain ⟨l,hleaf,hinj⟩ := exists_planar_leaf_injection hsep Q hQpos hcarry (m*B) hsmall'
  let L := P.image l
  have hL : L ⊆ cubePaths 2 (m*B) := by
    intro r hr
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hr
    exact (hleaf x hx).1
  have hpref := leaf_image_prefix_power_bound hδ ht0 hK hball Q hQ l hinj hleaf
    (show δ ≤ 1/(2:ℝ)^(m*B) by linarith)
  have hpref' : ∀ k ≤ m*B, ∀ q : CellPath 2,
      ((prefixFiber L k q).card:ℝ) ≤ (2:ℝ)^((lam/4)*(m*B:ℕ))*
        (2:ℝ)^(-t*(k:ℝ))*(L.card:ℝ) := by
    intro k hk q
    exact (hpref k hk q).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpointbudget (by positivity)) (Nat.cast_nonneg _))
  obtain ⟨p,_,_,_,hCG⟩ := hgain m hm L hL (hP.image l) hpref' Q hQ
  let C := classLeaves L (blockLabel L (m*B) B (fun _ => []) (m+1))
    (blockLabel L (m*B) B (fun _ => []) (m+1) p)
  have hCP : C ⊆ P.image l := Finset.filter_subset _ _
  obtain ⟨T,hT,hunion⟩ := transport_pencils_to_leaf_centers Q hQ hcenter P l hleaf hCP
    hδ hs0 hK hsmall hsize hpencilbudget V hV
  exact (hCG a ha T hT).trans (div_le_div_of_nonneg_right hunion ha.le)

end Falconer

end OAI
