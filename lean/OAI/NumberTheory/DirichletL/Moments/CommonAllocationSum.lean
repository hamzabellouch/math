import OAI.NumberTheory.DirichletL.Moments.CommonAllocationBox

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonAllocationSum
open CenteredMomentCommonAllocation CenteredMomentCommonAllocationBox CenteredMomentSupport
open IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def allocationLabels (S : ι → Finset (Ideal O)) (C : Ideal O) : Finset (ι → Ideal O) :=
  (Fintype.piFinset S).image (fun v i => supportExtract (v i) (primeSupport C))

def actualAllocations (S : ι → Finset (Ideal O)) (C : Ideal O) : Finset (ι → Ideal O) :=
  (allocationLabels S C).filter (fun B => ∏ i,B i=C)

theorem allocation_data (S : ι → Finset (Ideal O)) (C : Ideal O)
    (B : ι → Ideal O) (hB : B∈allocationLabels S C) :
    (∀ i,B i≠0) ∧ (∀ i,primeSupport (B i)⊆primeSupport C) := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hB
  refine ⟨fun i => supportExtract_ne_zero _ _,?_⟩
  intro i
  rw [supportExtract_support]
  exact Finset.inter_subset_right

 theorem sum_source_fibers (S : ι → Finset (Ideal O)) (C : Ideal O)
    (F : (ι → Ideal O) → ℂ) :
    (∑ v∈Fintype.piFinset S,F v)=∑ B∈allocationLabels S C,∑ v∈sourceFiber S C B,F v := by
  have hh := Finset.sum_fiberwise_of_maps_to (s:=Fintype.piFinset S) (t:=allocationLabels S C)
    (g:=fun v i => supportExtract (v i) (primeSupport C))
    (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) F
  symm
  convert hh using 1
  apply Finset.sum_congr rfl
  intro B hB
  congr 1
  ext v
  simp only [sourceFiber,Finset.mem_filter,funext_iff]

theorem sum_actual_allocations (S : ι → Finset (Ideal O))
    (C a : Ideal O) (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a)
    (F : (ι → Ideal O) → ℂ) :
    (∑ v∈Fintype.piFinset S,if (∏ i,v i)=C*a then F v else 0)=
      ∑ B∈actualAllocations S C,
        ∑ v∈sourceFiber S C B,if (∏ i,v i)=C*a then F v else 0 := by
  rw [sum_source_fibers S C]
  symm
  apply Finset.sum_filter_of_ne
  intro B hB hn
  obtain ⟨v,hv,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hp : (∏ i,v i)=C*a := by
    by_contra hh
    exact hne (ite_eq_right hh)
  have he := (tuple_products v C a hC ha hCa hp).1
  have hb := (Finset.mem_filter.mp hv).2
  simpa only [hb] using he

theorem original_coefficient_allocated (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C a : Ideal O) (hC : C≠0) (ha : a≠0)
    (hCa : IsCoprime C a) (F : (ι → Ideal O) → ℂ) :
    (∑ v∈Fintype.piFinset S,if (∏ i,v i)=C*a then F v else 0)=
      ∑ B : actualAllocations S C,
        ∑ u∈residualBoxes S C B
          (allocation_data S C B (Finset.mem_filter.mp B.property).1).1,
          if (∏ i,u i)=a then F (fun i => B.val i*u i) else 0 := by
  rw [sum_actual_allocations S C a hC ha hCa F]
  rw [← Finset.sum_coe_sort (actualAllocations S C)
    (fun B => ∑ v∈sourceFiber S C B,if (∏ i,v i)=C*a then F v else 0)]
  apply Finset.sum_congr rfl
  intro B hB
  exact sourceFiber_product_sum S hS C hC B
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).2
    (Finset.mem_filter.mp B.property).2 a F

theorem actualAllocations_card (S : ι → Finset (Ideal O)) (C : Ideal O) (hC : C≠0) :
    (actualAllocations S C).card≤(idealDivisors C).card^(Fintype.card ι) := by
  let f (B : actualAllocations S C) : ι → idealDivisors C := fun i => ⟨B.val i,by
    apply (mem_idealDivisors hC).mpr
    have hh := Finset.dvd_prod_of_mem B.val (Finset.mem_univ i)
    rw [(Finset.mem_filter.mp B.property).2] at hh
    exact hh⟩
  have hf : Function.Injective f := by
    intro B D he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  simpa only [Fintype.card_coe,Fintype.card_fun] using Fintype.card_le_of_injective f hf

theorem actualAllocations_small_power [Nonempty ι] (ε : ℝ) (hε : 0<ε) :
    ∃ D : ℝ,0<D ∧ ∀ (S : ι → Finset (Ideal O)) (C : Ideal O),C≠0 →
      ((actualAllocations S C).card:ℝ)≤D*(Ideal.absNorm C:ℝ)^ε := by
  have hr : (0:ℝ)<Fintype.card ι := by exact_mod_cast Fintype.card_pos
  let δ := ε/(Fintype.card ι:ℝ)
  have hδ : 0<δ := div_pos hε hr
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨D^(Fintype.card ι),pow_pos hD _,?_⟩
  intro S C hC
  have hd : δ*(Fintype.card ι:ℝ)=ε := by dsimp only [δ];field_simp
  calc
    _ ≤ ((idealDivisors C).card:ℝ)^(Fintype.card ι) := by exact_mod_cast actualAllocations_card S C hC
    _ ≤ (D*(Ideal.absNorm C:ℝ)^δ)^(Fintype.card ι) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv C hC) _
    _ = _ := by rw [mul_pow,← Real.rpow_mul_natCast (Nat.cast_nonneg _),hd]

end SevenEighths.CenteredMomentCommonAllocationSum

end

end OAI
