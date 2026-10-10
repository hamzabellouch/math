import OAI.MeasureTheory.Falconer.Estimates.PacketGoodRegularFiber
import OAI.MeasureTheory.Falconer.Geometry.RegularCoordinateRows

namespace OAI

/-! Original coarse-cell rows on a tube with good local projection energies. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem good_coarse_rows (N : ℕ) {s t K KP m M L R τ : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hτ1 : τ ≤ 1) (hτ : τ ≤ t-s)
    (hK : 1 ≤ K) (hKP : 1 ≤ KP) (hm : 0 < m) (hL : 0 < L) (hR : 1 ≤ R)
    (C : Finset (Space 2)) (T Q : Space 2 → Finset (Space 2)) (hC : C.Nonempty)
    (hCchart : InBoundedLineChart C)
    (hCsep : FiniteSeparatedAt (1/(2:ℝ)^(N+3)) C)
    (hCball : NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) t K C)
    (hT : ∀ x ∈ C, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ FiniteSeparatedAt (1/(2:ℝ)^(N+3)) (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^(N+3)) x l)
    (hQ : ∀ x ∈ C, (Q x).Nonempty ∧ InBoundedLineChart (Q x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) t KP (Q x))
    (hunion : ((C.biUnion T).card:ℝ) ≤ L)
    (hbudget : 4*pencilEnergyCutoff (N+3) s t (50*K) M (m/50) C*
      (4*L/((m/50)*(C.card:ℝ)))^2*(2:ℝ)^(t-s) ≤ R) :
    ∃ l ∈ C.biUnion T, ∃ Y : Finset ℝ, Y.Nonempty ∧
      m*(C.card:ℝ)/(10000*L) ≤ (Y.card:ℝ) ∧
      (∀ u r : ℝ, 1/(2:ℝ)^(N+3) ≤ r → r ≤ 1 →
        scalarBallMass Y u r ≤ (100*R)*r^τ*(Y.card:ℝ)) ∧
      ∃ c : ℝ → Space 2, ∀ y ∈ Y,
        c y ∈ C ∧ c y 0 = y ∧ |y| ≤ 1 ∧ l ∈ T (c y) ∧
        planarProjectionEnergy N s (-l 0) (Q (c y)) ≤
          2*projectionEnergyBudget N s t (25*K*(4:ℝ)^s) KP*((Q (c y)).card:ℝ)^2 := by
  obtain ⟨l,hl,S,hSC,hS,hsize,hreg,hgood⟩ := packet_good_regular_fiber N hs hst hK hKP
    hm hL C T Q hC hCchart hCball hT hQ hunion
  have hregR : NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) (t-s) R S := by
    intro z r hr hr1
    exact (hreg z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg ((by positivity : 0 ≤ 1/(2:ℝ)^(N+3)).trans hr) _))
      (Nat.cast_nonneg _))
  let v := min (t-s) 1
  have hv : 0 ≤ v := le_min (sub_nonneg.mpr hst.le) zero_le_one
  have hτv : τ ≤ v := le_min hτ hτ1
  have hregU : NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) v R S := by
    intro z r hr hr1
    have hr0 : 0 < r := (by positivity : 0 < 1/(2:ℝ)^(N+3)).trans_le hr
    exact (hregR z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hr0 hr1
        (min_le_left _ _)) (zero_le_one.trans hR)) (Nat.cast_nonneg _))
  obtain ⟨x,hx,hlx⟩ := Finset.mem_biUnion.mp hl
  have hl0 : |l 0| ≤ 1 := ((hT x hx).2.2.1 l hlx).1
  obtain ⟨hY,hcard,hYball,c,hc⟩ := regular_coordinate_rows
    (by positivity : 0 < 1/(2:ℝ)^(N+3)) hv hR l hl0 S hS
    (fun x hx => hCchart x (hSC hx)) (finiteSeparatedAt_subset hSC hCsep)
    (fun x hx => (hT x (hSC hx)).2.2.2.2.2 l (hgood x hx).1) hregU
  refine ⟨l,hl,S.image (fun p => p 0),hY,?_,?_,c,?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < 10000*L)).2
    have hh := (div_le_iff₀ (by positivity : 0 < 400*L)).1 hsize
    have hh' := mul_le_mul_of_nonneg_right hcard (show 0 ≤ 400*L by positivity)
    nlinarith only [hh,hh']
  · intro u r hr hr1
    have hr0 : 0 < r := (by positivity : 0 < 1/(2:ℝ)^(N+3)).trans_le hr
    have h4 : (4:ℝ)^v ≤ 4 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1:ℝ) ≤ 4) (min_le_right (t-s) (1:ℝ))
    have hp : r^v ≤ r^τ := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hτv
    calc
      _ ≤ (25*R*(4:ℝ)^v)*r^v*((S.image fun p => p 0).card:ℝ) := hYball u r hr hr1
      _ ≤ (25*R*4)*r^τ*((S.image fun p => p 0).card:ℝ) := by gcongr
      _ = _ := by ring
  · intro y hy
    have hh := hc y hy
    exact ⟨hSC hh.1,hh.2.1,hh.2.2,(hgood (c y) hh.1).1,(hgood (c y) hh.1).2⟩

end Falconer

end OAI
