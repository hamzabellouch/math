import OAI.MeasureTheory.Falconer.Graphs.GraphBallCover
import OAI.MeasureTheory.Falconer.Geometry.ScalarSmallSumCover

namespace OAI

/-! Small mixed projections and retained graph degrees control the
concentration of the actual reference factor. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_graph_density_bound {δ R z c M K Kreg t ρ : ℝ}
    (hδ : 0 < δ) (hR : δ ≤ R) (hc : c ≠ 0) (hM : |c⁻¹| ≤ M)
    (ht : 0 ≤ t) (hKreg : 1 ≤ Kreg)
    (F Y : Finset ℝ) (hF : F.Nonempty) (e : ℝ → ℝ → Prop)
    (G : Finset (Space 2)) (hreg : NormalizedFiniteBallBound δ t Kreg G)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → δ ≤ |x-y|)
    (hlocal : ∀ x ∈ F, |x-z| ≤ R)
    (hdegree : ∀ x ∈ F, ρ*(Y.card:ℝ) ≤ ((Y.filter fun y => e x y).card:ℝ))
    (hgraph : ∀ x ∈ F, ∀ y ∈ Y, e x y → rowPoint x y ∈ G)
    (hsum : ((scalarCells δ (F+Y.image (fun y => c*y))).card:ℝ) ≤ K*(F.card:ℝ)) :
    ρ*(F.card:ℝ)*(Y.card:ℝ) ≤
      2*K*Kreg*((1+4*M)*R)^t*(G.card:ℝ) := by
  obtain ⟨Q,hQ,hcover⟩ := scalar_small_sum_cover hδ hR hc hM F Y hF hsep hlocal hsum
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  have hR0 : 0 ≤ R := hδ.le.trans hR
  have hδ' : δ ≤ R+4*M*R := by nlinarith
  have hb := scalar_graph_ball_cover F Y Q e G hR0 (by positivity : 0 ≤ 4*M*R)
    hδ' ht hKreg hreg hlocal hcover hgraph
  calc
    _ = ∑ _x ∈ F, ρ*(Y.card:ℝ) := by simp; ring
    _ ≤ ∑ x ∈ F, ((Y.filter fun y => e x y).card:ℝ) := Finset.sum_le_sum hdegree
    _ ≤ (Q.card:ℝ)*Kreg*(R+4*M*R)^t*(G.card:ℝ) := hb
    _ = (Q.card:ℝ)*(Kreg*(R+4*M*R)^t*(G.card:ℝ)) := by ring
    _ ≤ (2*K)*(Kreg*(R+4*M*R)^t*(G.card:ℝ)) :=
      mul_le_mul_of_nonneg_right hQ (by positivity)
    _ = _ := by rw [show R+4*M*R = (1+4*M)*R by ring]; ring

 theorem scalar_graph_density_relative {δ R z c M K Kreg t ρ N L : ℝ}
    (hδ : 0 < δ) (hR : δ ≤ R) (hc : c ≠ 0) (hM : |c⁻¹| ≤ M)
    (ht : 0 ≤ t) (hKreg : 1 ≤ Kreg) (hK : 0 ≤ K) (hN : 0 < N) (hρ : 0 < ρ)
    (F Y : Finset ℝ) (hF : F.Nonempty) (hY : Y.Nonempty) (e : ℝ → ℝ → Prop)
    (G : Finset (Space 2)) (hreg : NormalizedFiniteBallBound δ t Kreg G)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → δ ≤ |x-y|)
    (hlocal : ∀ x ∈ F, |x-z| ≤ R)
    (hdegree : ∀ x ∈ F, ρ*(Y.card:ℝ) ≤ ((Y.filter fun y => e x y).card:ℝ))
    (hgraph : ∀ x ∈ F, ∀ y ∈ Y, e x y → rowPoint x y ∈ G)
    (hsize : (G.card:ℝ) ≤ L*N*(Y.card:ℝ))
    (hsum : ((scalarCells δ (F+Y.image (fun y => c*y))).card:ℝ) ≤ K*N) :
    ((F.card:ℝ)/N)^2 ≤ (2*K*Kreg*L/ρ)*((1+4*M)*R)^t := by
  have hFpos : 0 < (F.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hF)
  have hYpos : 0 < (Y.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hY)
  have hs : ((scalarCells δ (F+Y.image (fun y => c*y))).card:ℝ) ≤
      (K*N/(F.card:ℝ))*(F.card:ℝ) := by rwa [div_mul_cancel₀ _ hFpos.ne']
  have hb := scalar_graph_density_bound hδ hR hc hM ht hKreg F Y hF e G hreg
    hsep hlocal hdegree hgraph hs
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  have hKreg0 : 0 ≤ Kreg := zero_le_one.trans hKreg
  have hR0 : 0 ≤ R := hδ.le.trans hR
  have hrad : 0 ≤ ((1+4*M)*R)^t := Real.rpow_nonneg (by positivity) _
  have hm := mul_le_mul_of_nonneg_left hsize
    (show 0 ≤ 2*(K*N/(F.card:ℝ))*Kreg*((1+4*M)*R)^t by positivity)
  have hb' := mul_le_mul_of_nonneg_right (hb.trans hm) hFpos.le
  have heq : (2*(K*N/(F.card:ℝ))*Kreg*((1+4*M)*R)^t*(L*N*(Y.card:ℝ)))*(F.card:ℝ) =
      (2*K*Kreg*L*((1+4*M)*R)^t*N^2)*(Y.card:ℝ) := by field_simp
  rw [heq] at hb'
  have hcore : ρ*(F.card:ℝ)^2 ≤ 2*K*Kreg*L*((1+4*M)*R)^t*N^2 := by
    apply (mul_le_mul_iff_right₀ hYpos).1
    convert hb' using 1 <;> ring
  apply (mul_le_mul_iff_left₀ hρ).1
  have hh : (ρ*(F.card:ℝ)^2)/N^2 ≤ 2*K*Kreg*L*((1+4*M)*R)^t :=
    (div_le_iff₀ (sq_pos_of_pos hN)).2 hcore
  have heL : ρ*((F.card:ℝ)/N)^2 = (ρ*(F.card:ℝ)^2)/N^2 := by ring
  have heR : ρ*((2*K*Kreg*L/ρ)*((1+4*M)*R)^t) =
      2*K*Kreg*L*((1+4*M)*R)^t := by field_simp
  calc
    _ = (ρ*(F.card:ℝ)^2)/N^2 := by rw [mul_comm _ ρ,heL]
    _ ≤ 2*K*Kreg*L*((1+4*M)*R)^t := hh
    _ = _ := by rw [mul_comm _ ρ,heR]

end Falconer

end OAI
