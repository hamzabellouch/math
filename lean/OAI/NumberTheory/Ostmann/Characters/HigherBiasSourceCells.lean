import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceCellsFinite
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceCellsPartition

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open scoped BigOperators
open Construction

theorem exists_many_good_prime_cells (c₀ δ : ℝ) (hc₀ : 0 < c₀) (hδ : 0 < δ) :
    ∃ c b₀ : ℝ, 0 < c ∧ 2 ≤ b₀ ∧ ∀ (E : Finset ℕ) (f : ℕ → ℂ) (b : ℝ),
      b₀ ≤ b → (∀ p∈E,p.Prime) →
      (∀ p∈E,b ≤ Real.log p ∧ Real.log p ≤ Real.exp 1*b) →
      c₀ ≤ harmonicPrimeMass E → (∀ p∈E,‖f p‖ ≤ 1) →
      (δ/2)*harmonicPrimeMass E  ≤  ∑ p∈E,((1:ℝ)/p)*(f p).re →
      ∃ I : Finset ℤ, c*b ≤ (I.card:ℝ) ∧ ∀ h∈I,
        b ≤ (h:ℝ) ∧ (h:ℝ) ≤ Real.exp 1*b ∧
        c/b ≤ harmonicPrimeMass (rawLogCell E h) ∧ δ/4 ≤ rawCellMeanReal E f h := by
  classical
  let D : ℝ := Real.exp 1+2
  have hD : 0 < D := by dsimp [D]; positivity
  let t : ℝ := δ*c₀/(16*D)
  have ht : 0 < t := div_pos (mul_pos hδ hc₀) (by positivity)
  let q : ℝ := δ*c₀/8
  have hq : 0 < q := by dsimp [q]; positivity
  let c : ℝ := min t (q/primeLogCellConstant)
  have hc : 0 < c := lt_min ht (div_pos hq primeLogCellConstant_pos)
  let b₀ : ℝ := max 2 (32*primeLogCellConstant/(δ*c₀))
  refine ⟨c,b₀,hc,le_max_left _ _,?_⟩
  intro E f b hlarge hE hband hmass hf hmean
  have hb : 2 ≤ b := (le_max_left _ _).trans hlarge
  have hbp : 0 < b := by linarith
  have hboundary : 2*primeLogCellConstant/b  ≤  δ*c₀/16 := by
    have hsize : 32*primeLogCellConstant/(δ*c₀)  ≤  b := (le_max_right _ _).trans hlarge
    have hh := (div_le_iff₀ (mul_pos hδ hc₀)).mp hsize
    apply (div_le_iff₀ hbp).mpr
    nlinarith
  let S := rawCellIndices b
  let m : ℤ → ℝ := fun h => harmonicPrimeMass (rawLogCell E h)
  let y : ℤ → ℝ := rawCellRealSum E f
  let I := S.filter (fun h : ℤ => b ≤ (h:ℝ) ∧ (δ/4)*m h ≤ y h ∧ t/b ≤ m h)
  have hm (h : ℤ) : 0 ≤ m h := Finset.sum_nonneg (fun p _ => by positivity)
  have hy (h : ℤ) : y h ≤ m h := by
    apply Finset.sum_le_sum
    intro p hp
    have hre : (f p).re ≤ 1 := (Complex.re_le_norm (f p)).trans (hf p (Finset.mem_filter.mp hp).1)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hre (show 0 ≤ (1:ℝ)/p by positivity)
  have hM : (∑ h∈S,m h)=harmonicPrimeMass E :=
    sum_rawLogCells E hE b (fun p hp => (hband p hp).2) (fun p => (1:ℝ)/p)
  have hY : (∑ h∈S,y h)=∑ p∈E,((1:ℝ)/p)*(f p).re :=
    sum_rawLogCells E hE b (fun p hp => (hband p hp).2) (fun p => ((1:ℝ)/p)*(f p).re)
  have hbad : (∑ h∈S.filter (fun h : ℤ => ¬b ≤ (h:ℝ)),m h) ≤ δ*c₀/16 := by
    simpa only [not_le] using (rawLogCell_boundary_mass_le E hE b hb hband).trans hboundary
  have hthin : (S.card:ℝ)*(t/b) ≤ δ*c₀/16 := by
    have hcS : (S.card:ℝ) ≤ D*b := rawCellIndices_card_le b (by linarith)
    have hh := mul_le_mul_of_nonneg_right hcS (div_nonneg ht.le hbp.le)
    have hid : D*b*(t/b)=δ*c₀/16 := by dsimp [t]; field_simp
    rw [hid] at hh
    exact hh
  have hgood : q ≤ ∑ h∈I,m h := by
    have hh := good_cells_mass_lower S m y (fun h : ℤ => b ≤ (h:ℝ)) (δ/2) (δ/4) (t/b)
      (by positivity) (by positivity) (fun h _ => hm h) (fun h _ => hy h)
      (by rw [hM,hY]; exact hmean)
    change (δ/2-δ/4)*(∑ h∈S,m h)-
      (∑ h∈S.filter (fun h : ℤ => ¬b ≤ (h:ℝ)),m h)-S.card*(t/b) ≤ ∑ h∈I,m h at hh
    rw [hM] at hh
    have hhM := mul_le_mul_of_nonneg_left hmass hδ.le
    dsimp [q]
    nlinarith
  have hI (h : ℤ) (hh : h∈I) :
      b ≤ (h:ℝ) ∧ (δ/4)*m h ≤ y h ∧ t/b ≤ m h := (Finset.mem_filter.mp hh).2
  have hcap (h : ℤ) (hh : h∈I) : m h ≤ primeLogCellConstant/b := by
    apply (rawLogCell_mass_le E hE h (lt_of_lt_of_le hbp (hI h hh).1)).trans
    exact div_le_div_of_nonneg_left primeLogCellConstant_pos.le hbp (hI h hh).1
  refine ⟨I,?_,?_⟩
  · have hh := card_lower_of_cell_mass I m b primeLogCellConstant q hbp primeLogCellConstant_pos hcap hgood
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hbp.le).trans hh
  · intro h hh
    obtain ⟨hlo,havg,hmasscell⟩ := hI h hh
    have hmpos : 0 < m h := (div_pos ht hbp).trans_le hmasscell
    have hne : (rawLogCell E h).Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      simp only [m,harmonicPrimeMass,he,Finset.sum_empty,lt_self_iff_false] at hmpos
    obtain ⟨p,hp⟩ := hne
    have hhi : (h:ℝ) ≤ Real.exp 1*b :=
      (Finset.mem_filter.mp hp).2.1.trans (hband p (Finset.mem_filter.mp hp).1).2
    refine ⟨hlo,hhi,?_,?_⟩
    · exact (div_le_div_of_nonneg_right (min_le_left _ _) hbp.le).trans hmasscell
    · exact (le_div_iff₀ hmpos).mpr havg

end Ostmann.Characters.HigherBiasSource

end

end OAI
