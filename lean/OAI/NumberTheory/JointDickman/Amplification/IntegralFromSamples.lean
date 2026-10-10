import OAI.NumberTheory.JointDickman.Amplification.SeparatedCellIntegral

namespace OAI

/-! # An integral bound from all separated finite frequency samples -/
namespace JointDickman
open Finset MeasureTheory Function
open scoped Classical

lemma unit_grid_cover {a : ℝ} {M : ℕ} {S : Set ℝ}
    (hS : S ⊆ Set.Ico a (a+M)) :
    S = ⋃ j ∈ range M, S ∩ Set.Ico (a+j) (a+(j+1:ℕ)) := by
  ext t
  constructor
  · intro ht
    have hs := hS ht
    let j := ⌊t-a⌋₊
    have hta : 0 ≤ t-a := by linarith [hs.1]
    have hj : j < M := (Nat.floor_lt hta).mpr (by linarith [hs.2])
    have hlo := Nat.floor_le hta
    have hhi := Nat.lt_floor_add_one (t-a)
    refine Set.mem_iUnion₂.mpr ⟨j,mem_range.mpr hj,ht,?_,?_⟩
    · dsimp [j]
      linarith
    · change t < a+(j+1:ℕ)
      push_cast
      dsimp [j]
      linarith
  · intro ht
    obtain ⟨j,_,ht⟩ := Set.mem_iUnion₂.mp ht
    exact ht.1

lemma unit_grid_same_parity_separated (a : ℝ) {i j : ℕ}
    (hp : i%2=j%2) (hne : i≠j) {x y : ℝ}
    (hx : x ∈ Set.Ico (a+i) (a+(i+1:ℕ)))
    (hy : y ∈ Set.Ico (a+j) (a+(j+1:ℕ))) : 1 ≤ |x-y| := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hgap : i+2 ≤ j := by omega
    have hgr : (i:ℝ)+2 ≤ j := by exact_mod_cast hgap
    have hxi : x < a+(i:ℝ)+1 := by simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using hx.2
    have hyl : a+(j:ℝ) ≤ y := hy.1
    have hh : 1 ≤ y-x := by linarith
    exact hh.trans (by simpa only [abs_sub_comm] using le_abs_self (y-x))
  · have hgap : j+2 ≤ i := by omega
    have hgr : (j:ℝ)+2 ≤ i := by exact_mod_cast hgap
    have hyj : y < a+(j:ℝ)+1 := by simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using hy.2
    have hxl : a+(i:ℝ) ≤ x := hx.1
    exact (show 1 ≤ x-y by linarith).trans (le_abs_self _)

/-- A unit grid splits into two separated classes. No regularity of the
frequency set beyond measurability is required. -/
theorem integral_le_twice_separated_samples (S : Set ℝ) (hSm : MeasurableSet S)
    (F : ℝ → ℝ) (hF0 : ∀ x ∈ S, 0 ≤ F x) (a : ℝ) (M : ℕ)
    (hS : S ⊆ Set.Ico a (a+M)) (hF : IntegrableOn F (Set.Ico a (a+M))) (B : ℝ)
    (hsample : ∀ U : Finset ℝ, (∀ x ∈ U, x ∈ S) →
      (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) → (∑ x ∈ U, F x) ≤ B) :
    (∫ x in S, F x) ≤ 2*B := by
  let E := fun j : ℕ => S ∩ Set.Ico (a+j) (a+(j+1:ℕ))
  have hEi : ∀ j ∈ range M, IntegrableOn F (E j) :=
    fun j _ => hF.mono_set (fun x hx => hS hx.1)
  have hEm : ∀ j ∈ range M, MeasurableSet (E j) := fun _ _ => hSm.inter measurableSet_Ico
  have hEf : ∀ j ∈ range M, volume (E j) ≠ ⊤ := by
    intro j _
    exact ne_top_of_le_ne_top (measure_Ico_lt_top (μ := volume)).ne
      (measure_mono Set.inter_subset_right)
  have hE1 : ∀ j ∈ range M, volume.real (E j) ≤ 1 := by
    intro j _
    have hh := measureReal_mono (μ := volume)
      (show E j ⊆ Set.Ico (a+j) (a+(j+1:ℕ)) from Set.inter_subset_right)
      (measure_Ico_lt_top (μ := volume)).ne
    rw [Real.volume_real_Ico] at hh
    have he : a+((j+1:ℕ):ℝ)-(a+(j:ℝ))=1 := by push_cast; ring
    simpa only [he,max_eq_left (by norm_num : (0:ℝ)≤1)] using hh
  have hdis : Set.Pairwise (↑(range M)) (Disjoint on E) := by
    intro i hi j hj hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hxL := hx.2.1
    have hxU := hx.2.2
    have hyL := hy.2.1
    have hyU := hy.2.2
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hh : (i:ℝ)+1 ≤ j := by exact_mod_cast hij
      push_cast at hxU
      linarith
    · have hh : (j:ℝ)+1 ≤ i := by exact_mod_cast hji
      push_cast at hyU
      linarith
  have hI : (∫ x in S, F x) = ∑ j ∈ range M, ∫ x in E j, F x := by
    calc
      _ = ∫ x in ⋃ j ∈ range M, E j, F x := by
        rw [← unit_grid_cover hS]
      _ = _ := integral_biUnion_finset (range M) hEm hdis hEi
  let I₀ := (range M).filter (fun j => j%2=0)
  let I₁ := (range M).filter (fun j => ¬j%2=0)
  have hclass (I : Finset ℕ) (hI : I ⊆ range M)
      (hp : ∀ i ∈ I, ∀ j ∈ I, i%2=j%2) : (∑ j ∈ I, ∫ x in E j, F x) ≤ B := by
    apply separated_cell_integral_bound I E S F B (fun j hj => hEi j (hI hj)) hF0
      (fun _ _ => Set.inter_subset_left) (fun j hj => hEf j (hI hj))
      (fun j hj => hE1 j (hI hj)) _ hsample
    intro i hi j hj hne x hx y hy
    exact unit_grid_same_parity_separated a (hp i hi j hj) hne hx.2 hy.2
  have h₀ := hclass I₀ (filter_subset _ _) (by
    intro i hi j hj
    exact (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)
  have h₁ := hclass I₁ (filter_subset _ _) (by
    intro i hi j hj
    have hi := (mem_filter.mp hi).2
    have hj := (mem_filter.mp hj).2
    omega)
  rw [hI,← sum_filter_add_sum_filter_not (range M) (fun j => j%2=0)]
  change (∑ j ∈ I₀, ∫ x in E j, F x)+(∑ j ∈ I₁, ∫ x in E j, F x) ≤ 2*B
  linarith

/-- The bounded-frequency form used for Mellin polynomials. -/
theorem bounded_integral_le_twice_samples (S : Set ℝ) (hSm : MeasurableSet S)
    (F : ℝ → ℝ) (hF : Continuous F) (hF0 : ∀ x ∈ S, 0 ≤ F x)
    {T : ℝ} (_hT : 0 ≤ T) (hS : S ⊆ Set.Ioc (-T) T) (B : ℝ)
    (hsample : ∀ U : Finset ℝ, (∀ x ∈ U, x ∈ S) →
      (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) → (∑ x ∈ U, F x) ≤ B) :
    (∫ x in S, F x) ≤ 2*B := by
  let a := -T-1
  let M := ⌈2*T+2⌉₊
  have hcover : S ⊆ Set.Ico a (a+M) := by
    intro x hx
    obtain ⟨hslo,hshi⟩ := hS hx
    have hc := Nat.le_ceil (2*T+2)
    dsimp [a,M]
    constructor <;> linarith
  exact integral_le_twice_separated_samples S hSm F hF0 a M hcover
    (hF.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self) B hsample

end JointDickman

end OAI
