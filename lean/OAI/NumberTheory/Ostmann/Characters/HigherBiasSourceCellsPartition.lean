import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceCellsMass

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open scoped BigOperators
open Construction

def rawLogCell (E : Finset ℕ) (h : ℤ) : Finset ℕ :=
  E.filter (fun p : ℕ => (h:ℝ) ≤ Real.log p ∧ Real.log p < (h:ℝ)+1)

def rawCellIndices (b : ℝ) : Finset ℤ := Finset.Icc 0 ⌈Real.exp 1*b⌉

def rawCellRealSum (E : Finset ℕ) (f : ℕ → ℂ) (h : ℤ) : ℝ :=
  ∑ p∈rawLogCell E h, ((1:ℝ)/p)*(f p).re

def rawCellMeanReal (E : Finset ℕ) (f : ℕ → ℂ) (h : ℤ) : ℝ :=
  rawCellRealSum E f h / harmonicPrimeMass (rawLogCell E h)

theorem rawLogCell_eq_fiber (E : Finset ℕ) (h : ℤ) :
    rawLogCell E h=E.filter (fun p : ℕ => ⌊Real.log (p:ℝ)⌋=h) := by
  ext p
  simp only [rawLogCell,Finset.mem_filter,Int.floor_eq_iff]

theorem floor_mem_rawCellIndices (E : Finset ℕ) (hE : ∀ p∈E,p.Prime)
    (b : ℝ) (hband : ∀ p∈E,Real.log p ≤ Real.exp 1*b) (p : ℕ) (hp : p∈E) :
    ⌊Real.log (p:ℝ)⌋ ∈ rawCellIndices b := by
  apply Finset.mem_Icc.mpr
  constructor
  · exact Int.floor_nonneg.mpr (Real.log_nonneg (by exact_mod_cast (hE p hp).one_le))
  · apply Int.cast_le.mp (show (⌊Real.log (p:ℝ)⌋:ℝ) ≤ (⌈Real.exp 1*b⌉:ℤ) from
      (Int.floor_le _).trans ((hband p hp).trans (Int.le_ceil _)))

theorem sum_rawLogCells (E : Finset ℕ) (hE : ∀ p∈E,p.Prime)
    (b : ℝ) (hband : ∀ p∈E,Real.log p ≤ Real.exp 1*b) (g : ℕ → ℝ) :
    (∑ h∈rawCellIndices b,∑ p∈rawLogCell E h,g p)=∑ p∈E,g p := by
  simp_rw [rawLogCell_eq_fiber]
  exact Finset.sum_fiberwise_of_maps_to (floor_mem_rawCellIndices E hE b hband) g

theorem rawCellIndices_card_le (b : ℝ) (hb : 1 ≤ b) :
    ((rawCellIndices b).card:ℝ) ≤ (Real.exp 1+2)*b := by
  have he : 0 ≤ Real.exp 1*b := mul_nonneg (Real.exp_pos _).le (by linarith)
  have hc0 : (0:ℤ) ≤ ⌈Real.exp 1*b⌉ := Int.ceil_nonneg he
  have hc : ((rawCellIndices b).card:ℤ)=⌈Real.exp 1*b⌉+1 := by
    simpa only [rawCellIndices,sub_zero] using
      (Int.card_Icc_of_le (a:=0) (b:=⌈Real.exp 1*b⌉) (by omega))
  have hcr : ((rawCellIndices b).card:ℝ)=(⌈Real.exp 1*b⌉:ℤ)+1 := by exact_mod_cast hc
  rw [hcr]
  have hh := Int.ceil_lt_add_one (Real.exp 1*b)
  nlinarith

theorem rawLogCell_mass_le (E : Finset ℕ) (hE : ∀ p∈E,p.Prime)
    (h : ℤ) (hh : (0:ℝ)<h) :
    harmonicPrimeMass (rawLogCell E h) ≤ primeLogCellConstant/(h:ℝ) := by
  apply harmonicPrimeMass_le_logCell _
    (fun p hp => hE p (Finset.mem_filter.mp hp).1) h hh
  intro p hp
  exact ⟨(Finset.mem_filter.mp hp).2.1,(Finset.mem_filter.mp hp).2.2.le⟩

theorem rawLogCell_boundary_mass_le (E : Finset ℕ) (hE : ∀ p∈E,p.Prime)
    (b : ℝ) (hb : 2 ≤ b) (hband : ∀ p∈E,b ≤ Real.log p ∧ Real.log p ≤ Real.exp 1*b) :
    (∑ h∈(rawCellIndices b).filter (fun h : ℤ => (h:ℝ)<b),
      harmonicPrimeMass (rawLogCell E h)) ≤ 2*primeLogCellConstant/b := by
  have hrewrite :
      (∑ h∈(rawCellIndices b).filter (fun h : ℤ => (h:ℝ)<b),
        harmonicPrimeMass (rawLogCell E h)) =
      harmonicPrimeMass (E.filter (fun p : ℕ => (⌊Real.log (p:ℝ)⌋:ℝ)<b)) := by
    simp only [harmonicPrimeMass,rawLogCell_eq_fiber]
    rw [Finset.sum_fiberwise_eq_sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp,_,hh⟩
      exact ⟨hp,hh⟩
    · rintro ⟨hp,hh⟩
      exact ⟨hp,floor_mem_rawCellIndices E hE b (fun p hp => (hband p hp).2) p hp,hh⟩
  rw [hrewrite]
  have hs : E.filter (fun p : ℕ => (⌊Real.log (p:ℝ)⌋:ℝ)<b) ⊆ rawLogCell E ⌊b⌋ := by
    intro p hp
    obtain ⟨hp,hh⟩ := Finset.mem_filter.mp hp
    have hf : ⌊Real.log (p:ℝ)⌋=⌊b⌋ := le_antisymm
      (Int.le_floor.mpr hh.le) (Int.floor_mono (hband p hp).1)
    rw [rawLogCell_eq_fiber]
    exact Finset.mem_filter.mpr ⟨hp,hf⟩
  have hfloor : b/2 ≤ (⌊b⌋:ℝ) := by
    have hh := Int.lt_floor_add_one b
    linarith
  have hfloorpos : (0:ℝ)<⌊b⌋ := by linarith
  calc
    _ ≤ harmonicPrimeMass (rawLogCell E ⌊b⌋) :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun p _ _ => by positivity)
    _ ≤ primeLogCellConstant/(⌊b⌋:ℝ) := rawLogCell_mass_le E hE _ hfloorpos
    _ ≤ 2*primeLogCellConstant/b := by
      apply (div_le_div_iff₀ hfloorpos (show 0<b by linarith)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hfloor primeLogCellConstant_pos.le]

end Ostmann.Characters.HigherBiasSource

end

end OAI
