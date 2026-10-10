import OAI.NumberTheory.JointDickman.Counting.ShortAffineDyadic
import OAI.NumberTheory.JointDickman.Analysis.MellinShortLimit

namespace OAI

/-! # Iterated short averages from a uniform affine spectral budget -/
namespace JointDickman
open Finset Filter MeasureTheory PublishedInputs
open scoped Topology

theorem shortAverage_iterated_affine
    (f : ℕ → ℝ → ArithmeticFunction ℂ) (hf : ∀ B x n, ‖f B x n‖≤1)
    (A H a b : ℕ → ℝ) (hA : ∀ B, 0<A B) (hH : Tendsto H atTop atTop)
    (hpos : ∀ᶠ B in atTop, 0≤a B ∧ 0≤b B)
    (hbudget : Tendsto (fun B => a B+b B/H B) atTop (𝓝 0))
    (hspec : ∀ᶠ B in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ, (A B/2)*x≤N → (N:ℝ)≤(2*A B)*x → ∀ T : ℝ, 1≤T →
        (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) (f B x) t‖^2) ≤
          a B+b B*T/N) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ B in atTop, ∀ᶠ x : ℝ in atTop,
      (1/(A B*x))*(∫ z in (A B*x)..2*(A B*x), ‖complexShortAverage (f B x) (H B) z‖^2)<ε := by
  intro ε hε
  obtain ⟨η,hη,hηhalf,m,hm,hsmall⟩ := exists_mellin_smoothing_parameters (half_pos hε)
  obtain ⟨C,hC,hshort⟩ := shortAverage_of_dyadic_affine η hη hηhalf m hm
  have hi := tendsto_inv_atTop_zero.comp hH
  have hcost : Tendsto (fun B => C*(16*(a B+b B/H B)+6/H B)+
      2*(3/(m:ℝ)+13/H B+16*η)^2) atTop
      (𝓝 (2*(3/(m:ℝ)+16*η)^2)) := by
    have hb := ((hbudget.const_mul 16).add (hi.const_mul 6)).const_mul C
    have he := ((((hi.const_mul 13).const_add (3/(m:ℝ))).add_const (16*η)).pow 2).const_mul 2
    convert hb.add he using 1 <;> simp [Function.comp_apply,div_eq_mul_inv]
  have hnum := hcost.eventually (gt_mem_nhds (hsmall.trans (half_lt_self hε)))
  filter_upwards [hspec,hpos,hnum,hH.eventually_ge_atTop 1] with B hspec hpos hnum hHB
  have hX : Tendsto (fun x : ℝ => A B*x) atTop atTop := tendsto_id.const_mul_atTop (hA B)
  filter_upwards [hspec,hX.eventually_ge_atTop 2,hX.eventually_ge_atTop ((H B)^2)]
    with x hspec hX2 hXH
  have hfl : A B*x/2 ≤ (⌊A B*x⌋₊:ℝ) := by
    have hh := Nat.lt_floor_add_one (A B*x)
    linarith
  have hfu : (⌊A B*x⌋₊:ℝ)≤A B*x := Nat.floor_le (by linarith)
  have hs := hshort (f B x) (hf B x) (A B*x) (H B) (a B) (b B)
    hX2 hHB hXH hpos.1 hpos.2 (by
      intro N hN T hT
      apply hspec N _ _ T hT
      · rcases hN with rfl | rfl <;> push_cast <;> nlinarith only [hfl]
      · rcases hN with rfl | rfl <;> push_cast <;> nlinarith only [hfu,hX2])
  apply hs.trans_lt
  apply lt_of_le_of_lt _ hnum
  have hb : 8*a B+16*b B/H B+6/H B≤16*(a B+b B/H B)+6/H B := by
    have ha := hpos.1
    linear_combination 8*ha
  exact add_le_add (mul_le_mul_of_nonneg_left hb hC.le) le_rfl

end JointDickman

end OAI
