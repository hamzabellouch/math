import OAI.Analysis.LipschitzHilbert.Packets.AnnularPacketGeometry

namespace OAI

/-! A concrete choice of the narrow frequency plateau and slope spacing
for every fixed positive annular support. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem exists_diagonal_geometry (B c C a M : ℝ) (hB : 0<B)
    (hc : 0<c) (hC : 0<C) (ha : 0<a) (hM : 0<M) :
    ∃ A delta : ℝ, ∃ _p : AnnularPacketGeometry A B c C a M,
      0<A ∧ 0<delta ∧ delta*C≤A/2 := by
  let A := min (a/8) (3*a*c/(128*C))
  have hA : 0<A := lt_min (by positivity) (by positivity)
  have hnarrow : A≤a/4 := (min_le_left _ _).trans (by linarith)
  have hAc : A/c≤3*a/(128*C) := by
    apply (div_le_iff₀ hc).mpr
    convert min_le_right (a/8) (3*a*c/(128*C)) using 1
    ring
  have hsep : A/c<(3*a/(4*C)/2)/4 := by
    have hp : 0<3*a/(128*C) := by positivity
    have heq : (3*a/(4*C)/2)/4=4*(3*a/(128*C)) := by ring
    rw [heq]
    linarith
  obtain ⟨p⟩ := exists_annular_packet_geometry A B c C a M hA.le hB.le hc hC ha hM hnarrow hsep
  let delta := A/(4*C)
  have hd : 0<delta := by dsimp [delta]; positivity
  have hdelta : delta*C≤A/2 := by
    have heq : delta*C=A/4 := by dsimp [delta]; field_simp
    rw [heq]
    linarith
  exact ⟨A,delta,p,hA,hd,hdelta⟩

theorem center_frequency_bounds (B c C w W center : ℝ)
    (hB : 0≤B) (hc : 0<c) (hw : 0<w) (hW : 0<W)
    (hlo : c+B*(w/W)≤w*center) (hhi : w*center+B*(w/W)≤C) :
    (2*Real.pi*c)/w≤|2*Real.pi*center| ∧ |2*Real.pi*center|≤(2*Real.pi*C)/w := by
  have hp : 0≤B*(w/W) := by positivity
  have hcenter : 0<center := by nlinarith
  rw [abs_of_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hcenter)]
  constructor
  · apply (div_le_iff₀ hw).mpr
    nlinarith [Real.pi_pos]
  · apply (le_div_iff₀ hw).mpr
    nlinarith [Real.pi_pos]

end LipschitzHilbert.PacketRepresentation

end

end OAI
