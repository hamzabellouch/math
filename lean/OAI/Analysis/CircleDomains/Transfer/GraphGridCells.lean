import OAI.Analysis.CircleDomains.Topology.EqualScaleCellSeparation

namespace OAI

/-! Equal-scale three-dimensional cells, colored by sixteen residues
in each coordinate. Enlarged balls in one color are disjoint. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

abbrev GraphGridColor := (Fin 16 × Fin 16) × Fin 16
abbrev GraphGridIndex := (ℤ × ℤ) × ℤ
abbrev GraphSpace := (ℝ × ℝ) × ℝ

def graphGridInterval (r : Fin 16) (k : ℤ) (s : ℝ) : Set ℝ :=
  Icc ((16*(k:ℝ)+(r:ℕ))*s) ((16*(k:ℝ)+(r:ℕ)+1)*s)

def graphGridCell (r : GraphGridColor) (k : GraphGridIndex) (s : ℝ) : Set GraphSpace :=
  (graphGridInterval r.1.1 k.1.1 s ×ˢ graphGridInterval r.1.2 k.1.2 s) ×ˢ
    graphGridInterval r.2 k.2 s

lemma graphGridCell_dist_gt {s : ℝ} (hs : 0 < s) (r : GraphGridColor)
    {k l : GraphGridIndex} (hkl : k ≠ l) {x y : GraphSpace}
    (hx : x ∈ graphGridCell r k s) (hy : y ∈ graphGridCell r l s) :
    8*s < dist x y := by
  by_cases h₀ : k.1.1 = l.1.1
  · by_cases h₁ : k.1.2 = l.1.2
    · have h₂ : k.2 ≠ l.2 := by
        intro h
        exact hkl (Prod.ext (Prod.ext h₀ h₁) h)
      have hh := equal_scale_cell_separation hs h₂ (r.2:ℕ) hx.2 hy.2
      exact hh.trans_le (by
        rw [Prod.dist_eq,Real.dist_eq]
        exact le_max_right _ _)
    · have hh := equal_scale_cell_separation hs h₁ (r.1.2:ℕ) hx.1.2 hy.1.2
      exact hh.trans_le (by
        rw [Prod.dist_eq,Prod.dist_eq,Real.dist_eq]
        exact (le_max_right _ _).trans (le_max_left _ _))
  · have hh := equal_scale_cell_separation hs h₀ (r.1.1:ℕ) hx.1.1 hy.1.1
    exact hh.trans_le (by
      rw [Prod.dist_eq,Prod.dist_eq,Real.dist_eq]
      exact (le_max_left _ _).trans (le_max_left _ _))

lemma graphGridCell_enlarged_disjoint {s : ℝ} (hs : 0 < s) (r : GraphGridColor)
    {k l : GraphGridIndex} (hkl : k ≠ l) {x y : GraphSpace}
    (hx : x ∈ graphGridCell r k s) (hy : y ∈ graphGridCell r l s) :
    Disjoint (closedBall x (4*s)) (closedBall y (4*s)) := by
  apply Set.disjoint_left.mpr
  intro z hzx hzy
  have ht := dist_triangle x z y
  rw [dist_comm x z] at ht
  have hle : dist x y ≤ 8*s := by
    linarith [mem_closedBall.mp hzx, mem_closedBall.mp hzy]
  exact (not_lt_of_ge hle) (graphGridCell_dist_gt hs r hkl hx hy)

lemma exists_graphGridInterval {s : ℝ} (hs : 0 < s) (x : ℝ) :
    ∃ (r : Fin 16) (k : ℤ), x ∈ graphGridInterval r k s := by
  let n : ℤ := Int.floor (x/s)
  have hn0 : 0 ≤ n % 16 := Int.emod_nonneg _ (by norm_num)
  have hn16 : n % 16 < 16 := Int.emod_lt_of_pos _ (by norm_num)
  let r : Fin 16 := ⟨(n%16).toNat,by omega⟩
  refine ⟨r,n/16,?_⟩
  have he : (16:ℝ)*(n/16:ℤ)+(r:ℕ) = (n:ℝ) := by
    have hr : ((r:ℕ):ℝ) = ((n%16:ℤ):ℝ) := by
      dsimp only [r]
      exact_mod_cast (Int.natCast_toNat_eq_self.mpr hn0)
    rw [hr]
    have hh : (16:ℤ)*(n/16)+n%16 = n := by simpa only [add_comm] using Int.emod_add_mul_ediv n 16
    exact_mod_cast hh
  change (16*(n/16:ℤ)+(r:ℕ))*s ≤ x ∧ x ≤ (16*(n/16:ℤ)+(r:ℕ)+1)*s
  rw [he]
  have hlo := (le_div_iff₀ hs).mp (Int.floor_le (x/s))
  have hhi := (div_lt_iff₀ hs).mp (Int.lt_floor_add_one (x/s))
  exact ⟨hlo,hhi.le⟩

lemma exists_graphGridCell {s : ℝ} (hs : 0 < s) (x : GraphSpace) :
    ∃ (r : GraphGridColor) (k : GraphGridIndex), x ∈ graphGridCell r k s := by
  obtain ⟨r₀,k₀,h₀⟩ := exists_graphGridInterval hs x.1.1
  obtain ⟨r₁,k₁,h₁⟩ := exists_graphGridInterval hs x.1.2
  obtain ⟨r₂,k₂,h₂⟩ := exists_graphGridInterval hs x.2
  exact ⟨((r₀,r₁),r₂),((k₀,k₁),k₂),⟨⟨h₀,h₁⟩,h₂⟩⟩

lemma graphGridCell_dist_le {s : ℝ} (r : GraphGridColor) (k : GraphGridIndex)
    {x y : GraphSpace} (hx : x ∈ graphGridCell r k s) (hy : y ∈ graphGridCell r k s) :
    dist x y ≤ s := by
  have hcoord {a x y : ℝ} (hx : x ∈ Icc a (a+s)) (hy : y ∈ Icc a (a+s)) :
      |x-y| ≤ s := abs_le.mpr ⟨by linarith [hx.1,hy.2],by linarith [hx.2,hy.1]⟩
  have h₀ := hcoord (a := (16*(k.1.1:ℝ)+(r.1.1:ℕ))*s)
    (by simpa only [graphGridInterval,add_mul,one_mul] using hx.1.1)
    (by simpa only [graphGridInterval,add_mul,one_mul] using hy.1.1)
  have h₁ := hcoord (a := (16*(k.1.2:ℝ)+(r.1.2:ℕ))*s)
    (by simpa only [graphGridInterval,add_mul,one_mul] using hx.1.2)
    (by simpa only [graphGridInterval,add_mul,one_mul] using hy.1.2)
  have h₂ := hcoord (a := (16*(k.2:ℝ)+(r.2:ℕ))*s)
    (by simpa only [graphGridInterval,add_mul,one_mul] using hx.2)
    (by simpa only [graphGridInterval,add_mul,one_mul] using hy.2)
  simpa only [Prod.dist_eq,Real.dist_eq,max_le_iff] using And.intro (And.intro h₀ h₁) h₂

end CircleDomainRigidity

end

end OAI
