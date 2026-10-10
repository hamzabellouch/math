import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedBoxSeparation
import OAI.Analysis.LipschitzHilbert.Estimates.TileLatticeEnvelope

namespace OAI

/-! The number of actual spatial lattice boxes through a point is bounded
at one scale and label, uniformly in the comparison direction. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert

private theorem envelope_lower_near (a x r K : ℝ) (hr : 0<r)
    (hx : |x-a|≤K*r) : 1≤(1+K^2)*lineEnvelope a r 1 x := by
  have ht : |(x-a)/r|≤K := by
    rw [abs_div,abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr hx
  have hs := pow_le_pow_left₀ (abs_nonneg _) ht 2
  rw [sq_abs] at hs
  simp only [lineEnvelope,pow_one]
  rw [←div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity)).mpr (by linarith)

namespace PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem direction_lattice_count (j : Fin N) (l : P.labels j)
    (S : Finset (Item j l)) (t K D : ℝ) (hK : 0≤K)
    (hangle : |t-P.rowSlope j l| * P.length j≤D*P.width)
    (z : ℝ×ℝ)
    (hbox : ∀ u∈S, z∈densitySpatialBox (P.directionBox t ⟨j,⟨l,u⟩⟩) K) :
    (S.card:ℝ)≤((1+K^2)*(1+(K*(1+D))^2))*(4*Real.pi)^2 := by
  classical
  let theta := P.rowSlope j l
  let y := z.2-theta*z.1
  let b := P.originZ j l-theta*P.originX j l
  let Ex := fun u => lineEnvelope (P.actualX j l u) (P.length j) 1 z.1
  let Ey := fun u => lineEnvelope (b+P.width*(P.site j l u).2) P.width 1 y
  let A := (1+K^2)*(1+(K*(1+D))^2)
  have hA : 0≤A := mul_nonneg (by positivity) (by positivity)
  have hy (u : Item j l) (hu : u∈S) :
      |y-(b+P.width*(P.site j l u).2)|≤(K*(1+D))*P.width := by
    have hz := hbox u hu
    have hx : |z.1-P.actualX j l u|≤K*P.length j := hz.1
    have he : y-(b+P.width*(P.site j l u).2)=
        ((z.2-P.actualZ j l u)-t*(z.1-P.actualX j l u))+
        (t-theta)*(z.1-P.actualX j l u) := by
      dsimp [y,b,theta,actualX,actualZ]
      ring
    rw [he]
    calc
      _ ≤ |(z.2-P.actualZ j l u)-t*(z.1-P.actualX j l u)|+
          |(t-theta)*(z.1-P.actualX j l u)| := abs_add_le _ _
      _ ≤ K*P.width+|t-theta| * (K*P.length j) :=
        add_le_add hz.2 (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg _))
      _ = K*P.width+K*(|t-theta| * P.length j) := by ring
      _ ≤ K*P.width+K*(D*P.width) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hangle hK)
      _ = _ := by ring
  have hpoint (u : Item j l) (hu : u∈S) : 1≤A*(Ex u*Ey u) := by
    have hx := envelope_lower_near (P.actualX j l u) z.1 (P.length j) K
      (P.length_pos j) (hbox u hu).1
    have ht := envelope_lower_near (b+P.width*(P.site j l u).2) y P.width (K*(1+D))
      P.width_pos (hy u hu)
    have hh := mul_le_mul hx ht (by norm_num : (0:ℝ)≤1) (le_trans (by norm_num) hx)
    calc
      (1:ℝ) = 1*1 := by norm_num
      _ ≤ ((1+K^2)*Ex u)*((1+(K*(1+D))^2)*Ey u) := hh
      _ = A*(Ex u*Ey u) := by dsimp only [A]; ring
  have hsum : (∑ u∈S, Ex u*Ey u)≤(4*Real.pi)^2 := by
    have hh := finite_scaled_plane_lattice_overlap (P.originX j l) b (P.length j) P.width z.1 y
      (P.length_pos j).ne' P.width_pos.ne' (S.image (P.site j l))
      (by decide : 1≤1) (by decide : 1≤1)
    rw [Finset.sum_image (fun _ _ _ _ he => P.site_injective j l he)] at hh
    exact hh
  calc
    _ = ∑ _u∈S, (1:ℝ) := by simp
    _ ≤ ∑ u∈S, A*(Ex u*Ey u) := Finset.sum_le_sum hpoint
    _ = A*∑ u∈S, Ex u*Ey u := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hA

end PacketLatticeData
end LipschitzHilbert

end

end OAI
