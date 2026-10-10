import OAI.Analysis.LipschitzHilbert.Phase.PacketAngularModel
import OAI.Analysis.LipschitzHilbert.Estimates.IntegerSlopeMultiplicity

namespace OAI

/-! Choose the fixed enlargement used by the manuscript's angular
cells. Enlarging the auxiliary angular width rescales the annulus and
selector constants together and preserves their separation. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem exists_angular_normalization (cStar cEta cb radius : ℝ)
    (_hcEta : 0<cEta) (hcb : 0<cb) (hcbQuarter : cb≤1/4)
    (hsmall : cStar/cEta<cb/4) :
    ∃ n : ℕ, let H : ℝ := 2^n
      1≤H ∧ 0<cb/H ∧ cb/H≤1/4 ∧
      cStar/(H*cEta)<(cb/H)/4 ∧
      6*max (radius/H) (cStar/(H*cEta)+cb/H)<1 := by
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (max 1 (6*max radius (cStar/cEta+cb)))
    (by norm_num : (1:ℝ)<2)
  let H : ℝ := 2^n
  have hH : 1≤H := (le_max_left _ _).trans hn.le
  have hHp : 0<H := zero_lt_one.trans_le hH
  have hmax : 6*max radius (cStar/cEta+cb)<H := (le_max_right _ _).trans_lt hn
  have hratio : cStar/(H*cEta)=(cStar/cEta)/H := by ring
  refine ⟨n,hH,div_pos hcb hHp,?_,?_,?_⟩
  · exact (div_le_self hcb.le hH).trans hcbQuarter
  · rw [hratio,show (cb/H)/4=(cb/4)/H by ring]
    exact div_lt_div_of_pos_right hsmall hHp
  · change 6*max (radius/H) (cStar/(H*cEta)+cb/H)<1
    rw [hratio,←add_div,max_div_div_right hHp.le]
    have h := (div_lt_one hHp).mpr hmax
    convert h using 1
    ring

theorem rescaled_vertical_annulus (H w eta cEta CEta : ℝ) (hH : 0≤H)
    (hlo : cEta≤w*eta) (hhi : w*eta≤CEta) :
    H*cEta≤(H*w)*eta ∧ (H*w)*eta≤H*CEta := by
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlo hH
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hhi hH

theorem exists_uniform_lattice_multiplicity (H spacing : ℝ) (hspacing : 0<spacing) :
    ∃ K : ℕ, ∀ (labels : Finset ℤ) (offset delta : ℝ), 0<delta → 0≤H →
      SourceSlopeLabels.LocalMultiplicity (Finset.univ : Finset labels)
        (fun n => offset+(spacing*delta)*(n.val:ℝ)) (H*delta) (2*K+1) := by
  obtain ⟨K,hK⟩ := exists_nat_gt (H/(2*spacing))
  refine ⟨K,?_⟩
  intro labels offset delta hd hH
  apply SourceSlopeLabels.integer_label_multiplicity labels offset (spacing*delta) (H*delta)
    (mul_pos hspacing hd) (mul_nonneg hH hd.le) K
  have h := (div_lt_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hspacing)).mp hK
  nlinarith [mul_le_mul_of_nonneg_right h.le hd.le]

end LipschitzHilbert.PacketRepresentation

end

end OAI
