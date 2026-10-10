import OAI.NumberTheory.DirichletL.Descent.WholeRetainedSource
import OAI.NumberTheory.DirichletL.Descent.SecondDeletedMovingMass

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.InverseSecondSourceBlocks
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseMoment
open InverseSecondFibers InversePrioritySecondSource
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]

abbrev BlockIndex := Fin 4 → ℕ

def outerNorms (p : ι → O) {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : Fin 4 → ℝ :=
  ![primeProductNorm p x.second.sourceCommon, primeProductNorm p x.second.divisor,
    primeProductNorm p x.second.overlap, ‖eisEmbedding x.second.frequency‖^2]

theorem outerNorms_eq_actual (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (Ψ : O →* ℂ) (m : O)
    (ray : SecondRayIndex) (N M : Finset ι) (i : Fin 4) :
    outerNorms p x i = secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i) := by
  fin_cases i <;> simp [outerNorms,secondActualNorms,secondInheritedProfile,
    actualMarkedSecondProfileData,expansionProfileData,primeSubsetGenerator_norm_eq_productNorm]

omit [DecidableEq ι] in
theorem outerNorms_ge_one (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (hk : x.second.frequency ≠ 0) :
    ∀ i,1 ≤ outerNorms p x i := by
  intro i
  fin_cases i
  · exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _
  · exact element_norm_ge_one _ hk

theorem frequency_ne_zero_of_gate (a : O) (R : ℝ) {k : O}
    (hk : k ∈ nonzeroChildFrequencyBall a R) : k ≠ 0 :=
  (Finset.mem_erase.mp hk).1

theorem retained_frequency_ne_zero (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo : ℕ} (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo → Finset ι → Finset ι → ℝ)
    (label : SecondParentSource ι Jo → Finset ι → SecondExpansionData ι → κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι Jo 0)
    (hx : x ∈ retainedPool p pool parents R label residual j) : x.second.frequency ≠ 0 :=
  frequency_ne_zero_of_gate _ _ (retainedPool_original_support p pool parents R label residual j x hx).2.2.2

def dyadIndex (r : ℝ) : ℕ := ⌊Real.logb 2 r⌋₊
def dyadScale (n : ℕ) : ℝ := 2^n

theorem dyadScale_pos (n : ℕ) : 0 < dyadScale n := by unfold dyadScale; positivity

theorem dyadIndex_bounds (r : ℝ) (hr : 1 ≤ r) :
    dyadScale (dyadIndex r) ≤ r ∧ r < 2*dyadScale (dyadIndex r) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hlog : 0 ≤ Real.logb 2 r := Real.logb_nonneg (by norm_num) hr
  constructor
  · have h := (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) hr0).mp (Nat.floor_le hlog)
    simpa only [dyadScale,dyadIndex,Real.rpow_natCast] using h
  · have h := (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ)<2) hr0).mp
      (Nat.lt_floor_add_one (Real.logb 2 r))
    have ht : r < (2:ℝ)^(dyadIndex r+1) := by
      rw [←Real.rpow_natCast]
      simpa only [Nat.cast_add,Nat.cast_one,dyadIndex] using h
    simpa only [dyadScale,pow_succ,mul_comm] using ht

def index (p : ι → O) {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : BlockIndex :=
  fun i => dyadIndex (outerNorms p x i)

def keys (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) : Finset BlockIndex :=
  source.image (index p)

def cell (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : Finset (MarkedSecondSource ι Jo Jn) := source.filter (fun x => index p x = d)

omit [DecidableEq ι] in
@[simp] theorem mem_cell (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) :
    x ∈ cell p source d ↔ x ∈ source ∧ index p x = d := Finset.mem_filter

omit [DecidableEq ι] in
theorem cell_subset (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : cell p source d ⊆ source := Finset.filter_subset _ _

omit [DecidableEq ι] in
theorem cell_inherits (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) (P : MarkedSecondSource ι Jo Jn → Prop) (hP : ∀ x∈source,P x) :
    ∀ x∈cell p source d,P x := fun x hx => hP x (cell_subset p source d hx)

theorem cell_conditions (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (d : BlockIndex) :
    ActualSecondSourceConditions p (cell p source d) := ActualSecondSourceConditions.mono p hs (cell_subset p source d)

omit [DecidableEq ι] in
theorem mem_keys_iff (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : d ∈ keys p source ↔ (cell p source d).Nonempty := by
  simp only [keys,Finset.mem_image,Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨x,hx,he⟩
    exact Finset.nonempty_iff_ne_empty.mp ⟨x,(mem_cell p source d x).mpr ⟨hx,he⟩⟩
  · intro h
    obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr h
    exact ⟨x,(mem_cell p source d x).mp hx⟩

omit [DecidableEq ι] in
theorem cells_disjoint (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    {d e : BlockIndex} (h : d ≠ e) : Disjoint (cell p source d) (cell p source e) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact h (((mem_cell p source d x).mp hx).2.symm.trans ((mem_cell p source e x).mp hy).2)

omit [DecidableEq ι] in
theorem cell_ratios (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) (i : Fin 4) :
    1 ≤ outerNorms p x i / dyadScale (d i) ∧ outerNorms p x i / dyadScale (d i) < 2 := by
  obtain ⟨hxs,he⟩ := (mem_cell p source d x).mp hx
  have hb := dyadIndex_bounds _ (outerNorms_ge_one p hp x (hk x hxs) i)
  have hi : dyadIndex (outerNorms p x i) = d i := congrFun he i
  rw [hi] at hb
  exact ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hb.1),
    (div_lt_iff₀ (dyadScale_pos _)).mpr hb.2⟩

omit [DecidableEq ι] in
theorem sum_cells (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    {β : Type*} [AddCommMonoid β] (f : MarkedSecondSource ι Jo Jn → β) :
    (∑ x∈source,f x) = ∑ d∈keys p source,∑ x∈cell p source d,f x := by
  exact (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem (index p) hx) f).symm

def scales (d : BlockIndex) : Fin 4 → ℝ := fun i => dyadScale (d i)

theorem actual_cell_ratios (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex) (N M : Finset ι) (i : Fin 4) :
    1 ≤ secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i) / scales d i ∧
    secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i) / scales d i < 2 := by
  rw [←outerNorms_eq_actual p x Ψ m ray N M i]
  exact cell_ratios p hp source hk d x hx i

theorem physical_source_partition
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0 → Finset ι)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X : ℝ) :
    (Y:ℂ)*secondRayCoefficient ray *
      (∑ x∈source,(w x * actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x) *
        actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
          slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x)
          a₁ a₂ W₁ W₂ Φ Y X) =
    ∑ d∈keys p source,(Y:ℂ)*secondRayCoefficient ray *
      (∑ x∈cell p source d,(w x * actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x) *
        actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
          slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x)
          a₁ a₂ W₁ W₂ Φ Y X) := by
  rw [sum_cells p source]
  exact Finset.mul_sum _ _ _

def capBox (A : Fin 4 → ℝ) (Z : ℝ) : Finset BlockIndex :=
  Fintype.piFinset (fun i => Finset.range (dyadIndex (Z^(A i))+1))

omit [DecidableEq ι] in
theorem keys_subset_capBox (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (A : Fin 4 → ℝ) (Z : ℝ) (hcaps : ∀ x∈source,∀ i,outerNorms p x i ≤ Z^(A i)) :
    keys p source ⊆ capBox A Z := by
  intro d hd
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hd
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  exact Nat.floor_mono (Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (lt_of_lt_of_le zero_lt_one (outerNorms_ge_one p hp x (hk x hx) i)) (hcaps x hx i))

omit [DecidableEq ι] in
theorem keys_card_le_product (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (A : Fin 4 → ℝ) (Z : ℝ) (hcaps : ∀ x∈source,∀ i,outerNorms p x i ≤ Z^(A i)) :
    (keys p source).card ≤ ∏ i : Fin 4,(dyadIndex (Z^(A i))+1) := by
  have h := Finset.card_le_card (keys_subset_capBox p hp source hk A Z hcaps)
  simpa [capBox,Fintype.card_piFinset] using h

def capConstant (A : Fin 4 → ℝ) : ℝ := (∑ i,A i)/Real.log 2

theorem capConstant_nonneg (A : Fin 4 → ℝ) (hA : ∀ i,0 ≤ A i) :
    0 ≤ capConstant A := by
  unfold capConstant
  exact div_nonneg (Finset.sum_nonneg (fun i _ => hA i)) (Real.log_pos (by norm_num)).le

theorem cap_bin_bound (A : Fin 4 → ℝ) (hA : ∀ i,0 ≤ A i) (Z : ℝ) (hZ : 2 ≤ Z)
    (i : Fin 4) : (dyadIndex (Z^(A i)) : ℝ)+1 ≤ 1+capConstant A*Real.log Z := by
  have hZ0 : 0 < Z := by linarith
  have hZi : 1 ≤ Z^(A i) := Real.one_le_rpow (by linarith) (hA i)
  have hf := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hZi)
  have hAi : A i ≤ ∑ j,A j := Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)
  have hc := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hAi
    (Real.log_pos (by norm_num : (1:ℝ)<2)).le) (Real.log_nonneg (by linarith : 1 ≤ Z))
  dsimp [dyadIndex,capConstant]
  calc
    _ ≤ 1+Real.logb 2 (Z^(A i)) := by linarith
    _ = 1+(A i/Real.log 2)*Real.log Z := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos hZ0,Real.logb]
      ring
    _ ≤ _ := by linarith

omit [DecidableEq ι] in
theorem keys_card_polynomial (A : Fin 4 → ℝ) (hA : ∀ i,0 ≤ A i) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → O) (_hp : ∀ i,p i ≠ 0)
      [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
      (source : Finset (MarkedSecondSource ι Jo Jn)) (Z : ℝ), 2 ≤ Z →
      (∀ x∈source,x.second.frequency ≠ 0) →
      (∀ x∈source,∀ i,outerNorms p x i ≤ Z^(A i)) →
      ((keys p source).card : ℝ) ≤ (1+C*Real.log Z)^4 := by
  refine ⟨capConstant A,capConstant_nonneg A hA,?_⟩
  intro p hp _ Jo Jn source Z hZ hk hcaps
  have h := keys_card_le_product p hp source hk A Z hcaps
  have hr : ((keys p source).card:ℝ) ≤ ∏ i : Fin 4,((dyadIndex (Z^(A i)):ℝ)+1) := by
    exact_mod_cast h
  apply hr.trans
  calc
    _ ≤ ∏ _i : Fin 4,(1+capConstant A*Real.log Z) :=
      Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => cap_bin_bound A hA Z hZ i)
    _ = (1+capConstant A*Real.log Z)^4 := by simp

omit [DecidableEq ι] in
@[simp] theorem keys_empty (p : ι → O) (Jo Jn : ℕ) :
    keys p (∅ : Finset (MarkedSecondSource ι Jo Jn)) = ∅ := by simp [keys]

omit [DecidableEq ι] in
@[simp] theorem cell_empty (p : ι → O) (Jo Jn : ℕ) (d : BlockIndex) :
    cell p (∅ : Finset (MarkedSecondSource ι Jo Jn)) d = ∅ := by simp [cell]

omit [DecidableEq ι] in
theorem cell_empty_of_not_mem (p : ι → O) {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (d : BlockIndex) (hd : d ∉ keys p source) :
    cell p source d = ∅ := by
  exact Finset.not_nonempty_iff_eq_empty.mp (fun h => hd ((mem_keys_iff p source d).mpr h))

theorem retained_cell_ratios (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo : ℕ}
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo → Finset ι → Finset ι → ℝ)
    (label : SecondParentSource ι Jo → Finset ι → SecondExpansionData ι → κ)
    (residual : Finset ι) (j : κ) (d : BlockIndex) (x : MarkedSecondSource ι Jo 0)
    (hx : x∈cell p (retainedPool p pool parents R label residual j) d)
    (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex) (N M : Finset ι) (i : Fin 4) :
    1 ≤ secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i)/scales d i ∧
    secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i)/scales d i < 2 :=
  actual_cell_ratios p hp _ (retained_frequency_ne_zero p pool parents R label residual j)
    d x hx Ψ m ray N M i

theorem retained_keys_card_polynomial (A : Fin 4 → ℝ) (hA : ∀ i,0 ≤ A i) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → O) (_hp : ∀ i,p i ≠ 0)
      [∀ i,(Ideal.span {p i}).IsMaximal] {Jo : ℕ}
      (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
      (R : SecondParentSource ι Jo → Finset ι → Finset ι → ℝ)
      (label : SecondParentSource ι Jo → Finset ι → SecondExpansionData ι → κ)
      (residual : Finset ι) (j : κ) (Z : ℝ), 2 ≤ Z →
      (∀ x∈retainedPool p pool parents R label residual j,∀ i,outerNorms p x i ≤ Z^(A i)) →
      ((keys p (retainedPool p pool parents R label residual j)).card:ℝ) ≤
        (1+C*Real.log Z)^4 := by
  obtain ⟨C,hC,h⟩ := keys_card_polynomial (ι:=ι) A hA
  refine ⟨C,hC,?_⟩
  intro p hp _ Jo pool parents R label residual j Z hZ hcaps
  exact h p hp _ Z hZ (retained_frequency_ne_zero p pool parents R label residual j) hcaps

end SevenEighths.InverseSecondSourceBlocks

end

end OAI
