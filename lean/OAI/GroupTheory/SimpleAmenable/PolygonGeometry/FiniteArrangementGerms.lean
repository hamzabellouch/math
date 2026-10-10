import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveGeometricGeneration

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteArrangementGerms

theorem exists_interval_avoiding_countable (l r : ℝ) (hlr : l < r)
    (S : Set ℝ) (hS : S.Countable) : ∃ x ∈ Set.Ioo l r, x ∉ S := by
  apply Set.not_subset.mp
  intro h
  have := Cardinal.Real.Ioo_countable_iff.mp (hS.mono h)
  linarith

theorem avoidsCuts_rectangle (a : ℕ) (l₁ r₁ l₂ r₂ : ℝ)
    (h₁ : l₁ < r₁) (h₂ : l₂ < r₂) :
    ∃ p : ℝ × ℝ, p.1 ∈ Set.Ioo l₁ r₁ ∧ p.2 ∈ Set.Ioo l₂ r₂ ∧ AvoidsCuts a p := by
  obtain ⟨x, hx, hx'⟩ := exists_interval_avoiding_countable l₁ r₁ h₁
    (Set.range ordinary) (Set.countable_range ordinary)
  let t := Real.goldenRatio ^ a
  have ht : t ≠ 0 := ne_of_gt (pow_pos Real.goldenRatio_pos a)
  let S := Set.range ordinary ∪ Set.range (fun z : CutRing => ordinary z + t*x) ∪
    Set.range (fun z : CutRing => (x - ordinary z)/t)
  have hS : S.Countable := ((Set.countable_range ordinary).union
    (Set.countable_range _)).union (Set.countable_range _)
  obtain ⟨y, hy, hy'⟩ := exists_interval_avoiding_countable l₂ r₂ h₂ S hS
  have hav : AvoidsCuts a (x,y) := by
    intro j z hz
    fin_cases j
    · exact hx' ⟨z, by simpa [cutForm] using hz.symm⟩
    · apply hy'
      exact Or.inl (Or.inl ⟨z, by simpa [cutForm] using hz.symm⟩)
    · apply hy'
      apply Or.inl ∘ Or.inr
      refine ⟨z, ?_⟩
      change ordinary z + t*x = y
      change y - t*x = ordinary z at hz
      linarith
    · apply hy'
      apply Or.inr
      refine ⟨z, ?_⟩
      apply (div_eq_iff ht).mpr
      change x - t*y = ordinary z at hz
      linarith
  exact ⟨(x,y),hx,hy,hav⟩

theorem avoidsCuts_dense (a : ℕ) : Dense {p : ℝ × ℝ | AvoidsCuts a p} := by
  apply dense_iff_inter_open.mpr
  intro U hU ⟨z,hz⟩
  obtain ⟨l,h,hl,hsub⟩ := exists_box_in_open hU z hz
  obtain ⟨p,hp₁,hp₂,hp⟩ := avoidsCuts_rectangle a
    (ordinary l.1) (ordinary h.1) (ordinary l.2) (ordinary h.2)
    (hl.1.1.trans hl.1.2) (hl.2.1.trans hl.2.2)
  exact ⟨p,hsub ⟨hp₁,hp₂⟩,hp⟩

theorem cutForm_smul (a : ℕ) (j : Fin 4) (t : ℝ) (p : ℝ × ℝ) :
    cutForm a j (t • p) = t * cutForm a j p := by
  fin_cases j <;> simp [cutForm] <;> ring

def strictLineCell {ι : Type*} (a : ℕ) (j : ι → Fin 4) (c : ι → ℝ)
    (σ : ι → Bool) : Set (ℝ × ℝ) :=
  {p | ∀ i, if σ i then cutForm a (j i) p < c i else c i < cutForm a (j i) p}

theorem strictLineCell_open {ι : Type*} [Finite ι] (a : ℕ)
    (j : ι → Fin 4) (c : ι → ℝ) (σ : ι → Bool) :
    IsOpen (strictLineCell a j c σ) := by
  classical
  have he : strictLineCell a j c σ = ⋂ i, {p | if σ i then cutForm a (j i) p < c i else c i < cutForm a (j i) p} := by
    ext p; simp only [strictLineCell,Set.mem_ofPred_eq,Set.mem_iInter]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  cases σ i
  · exact isOpen_lt continuous_const (cutForm_continuous a (j i))
  · exact isOpen_lt (cutForm_continuous a (j i)) continuous_const

theorem finite_arrangement_germ {ι : Type*} [Finite ι] (a : ℕ)
    (j : ι → Fin 4) (c : ι → ℝ) (z y : ℝ × ℝ) (σ : ι → Bool)
    (hactive : ∀ i, cutForm a (j i) z=c i →
      if σ i then cutForm a (j i) y < c i else c i < cutForm a (j i) y)
    (hinactive : ∀ i, cutForm a (j i) z≠c i →
      if σ i then cutForm a (j i) z < c i else c i < cutForm a (j i) z)
    (N : Set (ℝ × ℝ)) (hN : IsOpen N) (hz : z ∈ N) :
    ∃ p ∈ N, p ∈ strictLineCell a j c σ ∧ AvoidsCuts a p := by
  classical
  let U : Set (ℝ × ℝ) := N ∩ ⋂ i, if cutForm a (j i) z=c i then Set.univ
    else {p | if σ i then cutForm a (j i) p < c i else c i < cutForm a (j i) p}
  have hU : IsOpen U := by
    apply hN.inter
    apply isOpen_iInter_of_finite
    intro i
    by_cases hi : cutForm a (j i) z=c i
    · rw [ite_eq_left hi]; exact isOpen_univ
    · rw [ite_eq_right hi]
      cases σ i
      · exact isOpen_lt continuous_const (cutForm_continuous a (j i))
      · exact isOpen_lt (cutForm_continuous a (j i)) continuous_const
  have hzU : z ∈ U := by
    refine ⟨hz,Set.mem_iInter.mpr fun i => ?_⟩
    by_cases hi : cutForm a (j i) z=c i
    · rw [ite_eq_left hi]; trivial
    · rw [ite_eq_right hi]; exact hinactive i hi
  let ray : ℝ → ℝ × ℝ := fun t => z+t • (y-z)
  have hray : Continuous ray := continuous_const.add (continuous_id.smul continuous_const)
  have he : ray ⁻¹' U ∈ nhds (0:ℝ) := by
    apply hray.continuousAt.preimage_mem_nhds
    simpa [ray] using hU.mem_nhds hzU
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp he
  let t := ε/2
  have ht : 0<t := by dsimp [t]; positivity
  have htU : ray t ∈ U := hεU (by
    change dist t 0 < ε
    rw [Real.dist_eq,sub_zero,abs_of_pos ht]
    dsimp [t]; linarith)
  have hcell : ray t ∈ strictLineCell a j c σ := by
    intro i
    by_cases hi : cutForm a (j i) z=c i
    · have ha := hactive i hi
      have heq : cutForm a (j i) (ray t)=c i+t*(cutForm a (j i) y-c i) := by
        simp only [ray,cutForm_add,cutForm_smul,cutForm_sub,hi]
      cases hσ : σ i <;> simp only [hσ,Bool.false_eq_true,↓reduceIte] at ha ⊢
      · rw [heq]; nlinarith
      · rw [heq]; nlinarith
    · have hh := Set.mem_iInter.mp htU.2 i
      simpa only [ite_eq_right hi,Set.mem_ofPred_eq] using hh
  obtain ⟨p,hp,hpg⟩ := (avoidsCuts_dense a).inter_open_nonempty
    (N ∩ strictLineCell a j c σ) (hN.inter (strictLineCell_open a j c σ))
    ⟨ray t,htU.1,hcell⟩
  exact ⟨p,hp.1,hp.2,hpg⟩

end FiniteArrangementGerms

end SimpleAmenable
end
end

end OAI
