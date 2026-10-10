import OAI.Analysis.LipschitzHilbert.Trees.SlopePartitionGrid

namespace OAI

/-! The finite partition can be confined to a fixed slope range after
removing a fixed number of scales at the band width. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem finiteSlopeCenter_abs_le (K : ℕ) (delta d : ℝ) (hd : 0≤delta*d)
    (n : finiteSlopeLabels K) : |finiteSlopeCenter K delta d n.val|≤delta*d*K := by
  have hn : n.val≤2*K := Nat.lt_succ_iff.mp (Finset.mem_range.mp n.property)
  have hn' : (n.val:ℝ)≤2*K := by exact_mod_cast hn
  have hnonneg : (0:ℝ)≤n.val := Nat.cast_nonneg _
  unfold finiteSlopeCenter
  apply abs_le.mpr
  constructor <;> nlinarith

theorem finiteSlopeCenter_unit_range (H delta c M U d : ℝ)
    (hd : 0<d) (hdelta : 0<delta) (hc : 0<c) (hM : 0≤M) (hU : 0≤U)
    (hshort : U+(H+M/c+delta)*d≤1)
    (n : finiteSlopeLabels ⌈U/(delta*d)+M/(delta*c)⌉₊) :
    |finiteSlopeCenter ⌈U/(delta*d)+M/(delta*c)⌉₊ delta d n.val|+H*d≤1 := by
  have hden : 0<delta*d := mul_pos hdelta hd
  have hx : 0≤U/(delta*d)+M/(delta*c) := by positivity
  have hceil := (Nat.ceil_lt_add_one hx).le
  have hK := mul_le_mul_of_nonneg_left hceil hden.le
  have heq : delta*d*(U/(delta*d)+M/(delta*c)+1)=U+(M/c+delta)*d := by
    field_simp
    ring
  rw [heq] at hK
  have hn := finiteSlopeCenter_abs_le _ delta d hden.le n
  linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
