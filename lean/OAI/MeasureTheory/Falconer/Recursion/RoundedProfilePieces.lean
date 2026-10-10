import OAI.MeasureTheory.Falconer.Geometry.RelativeGridError
import OAI.MeasureTheory.Falconer.Recursion.ProfileCellFamily

namespace OAI

/-! The structured profile decomposition on the actual finite grid, with
explicit slope slack and preserved linear or superlinear control. -/
namespace Falconer
open Set

theorem rounded_structured_profile_pieces {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {n : ℕ} (hn : 0 < n) {τ ε s : ℝ} (hτ : 0 < τ) (hε : 0 ≤ ε)
    (hmesh : 2/(n : ℝ) ≤ τ/2) (herror : 4/(n : ℝ) ≤ ε*(τ/2))
    {S : List (ℝ × ℝ)} (hS : StructuredProfilePieces f τ ε s 1 S) :
    (S.map (innerProfileCell n)).Pairwise (fun c d => c.1+c.2 ≤ d.1) ∧
    ∀ c ∈ S.map (innerProfileCell n),
      0 ≤ c.1 ∧ c.1+c.2 ≤ 1 ∧ τ/2 ≤ c.2 ∧
      s-16/((n : ℝ)*τ) ≤ intervalSecantSlope f c.1 c.2 ∧
      ((∀ x ∈ Icc c.1 (c.1+c.2), |intervalSecantError f c.1 c.2 x| ≤ (3*ε)*c.2) ∨
       (intervalSecantSlope f c.1 c.2 ≤ s+16/((n : ℝ)*τ) ∧
        ∀ x ∈ Icc c.1 (c.1+c.2), -(3*ε)*c.2 ≤ intervalSecantError f c.1 c.2 x)) := by
  refine ⟨innerProfileCells_ordered hn hS.ordered,?_⟩
  intro c hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  have hb := hS.bounds d hd
  have hrel := innerProfileCell_relative_bounds hn hτ hε hmesh herror d hb.2.2
  have hslope := abs_le.mp (rounded_profile_uniform_slope hf hn hτ hmesh d hb.2.2)
  refine ⟨hb.1.trans (profileGridLeft_bounds hn d.1).1,?_,hrel.1,?_,?_⟩
  · rw [innerProfileCell_end]
    exact (profileGridRight_bounds hn (d.1+d.2)).2.trans hb.2.1
  · rcases hS.alternatives d hd with hlin | hsup
    · linarith [hlin.1]
    · rw [hsup.1] at hslope
      linarith
  · rcases hS.alternatives d hd with hlin | hsup
    · exact Or.inl (rounded_profile_relative_linear hf hn hτ hε hmesh herror d hb.2.2 hlin.2)
    · refine Or.inr ⟨?_,rounded_profile_relative_superlinear hf hn hτ hε hmesh herror d hb.2.2 hsup.2⟩
      rw [hsup.1] at hslope
      linarith

theorem innerProfileCell_integer_endpoints {n : ℕ} (hn : 0 < n) (c : ℝ × ℝ)
    (ha : 0 ≤ c.1) (hb : c.1+c.2 ≤ 1) (hd : 0 < (innerProfileCell n c).2) :
    ∃ i j : ℤ, 0 ≤ i ∧ i < j ∧ j ≤ (n : ℤ) ∧
      (innerProfileCell n c).1 = (i : ℝ)/(n : ℝ) ∧
      (innerProfileCell n c).1+(innerProfileCell n c).2 = (j : ℝ)/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let i : ℤ := ⌈(n : ℝ)*c.1⌉
  let j : ℤ := ⌊(n : ℝ)*(c.1+c.2)⌋
  have hi : (n : ℝ)*(innerProfileCell n c).1 = (i : ℝ) := by
    change (n : ℝ)*((i : ℝ)/(n : ℝ)) = i
    exact mul_div_cancel₀ _ hnR.ne'
  have hj : (n : ℝ)*((innerProfileCell n c).1+(innerProfileCell n c).2) = (j : ℝ) := by
    rw [innerProfileCell_end]
    change (n : ℝ)*((j : ℝ)/(n : ℝ)) = j
    exact mul_div_cancel₀ _ hnR.ne'
  have ha' : 0 ≤ (innerProfileCell n c).1 := ha.trans (profileGridLeft_bounds hn c.1).1
  have hb' : (innerProfileCell n c).1+(innerProfileCell n c).2 ≤ 1 := by
    rw [innerProfileCell_end]
    exact (profileGridRight_bounds hn (c.1+c.2)).2.trans hb
  have hi0 : (0 : ℝ) ≤ i := by rw [← hi]; positivity
  have hij : (i : ℝ) < j := by rw [← hi,← hj]; nlinarith [mul_pos hnR hd]
  have hjn : (j : ℝ) ≤ n := by
    rw [← hj]
    nlinarith [mul_le_mul_of_nonneg_left hb' hnR.le]
  refine ⟨i,j,by exact_mod_cast hi0,by exact_mod_cast hij,by exact_mod_cast hjn,rfl,?_⟩
  rw [innerProfileCell_end]
  rfl

end Falconer

end OAI
