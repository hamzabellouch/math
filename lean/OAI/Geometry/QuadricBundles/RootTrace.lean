import OAI.Geometry.QuadricBundles.Removability

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14

namespace QuadricCounterexample
open Complex Topology BigOperators

noncomputable section
variable (m : ℕ) [NeZero m]
local instance : Fintype (rootsOfUnity m ℂ) := Fintype.ofFinite _

noncomputable def chosenRoot (x : ℂ) : ℂ :=
  Classical.choose ((Complex.isOpenQuotientMap_pow m).surjective x)

lemma chosenRoot_pow (x : ℂ) : chosenRoot m x ^ m = x :=
  Classical.choose_spec ((Complex.isOpenQuotientMap_pow m).surjective x)

lemma same_power_orbit {x y : ℂ} (h : x^m=y^m) :
    ∃ ζ : rootsOfUnity m ℂ, x = (ζ.val : ℂ)*y := by
  by_cases hy : y=0
  · have hx : x=0 := (pow_eq_zero_iff (NeZero.ne m)).mp (by simpa [hy, zero_pow (NeZero.ne m)] using h)
    exact ⟨1, by simp [hx,hy]⟩
  · have hp : (x/y)^m=1 := by rw [div_pow,h,div_self (pow_ne_zero m hy)]
    exact ⟨rootsOfUnity.mkOfPowEq (x/y) hp, by simp [div_mul_cancel₀ _ hy]⟩

def rootOrbitAverage {V : Type u1} (F : ℂ × V → ℝ) (p : ℂ × V) : ℝ :=
  (m : ℝ)⁻¹ * ∑ ζ : rootsOfUnity m ℂ, F ((ζ.val : ℂ)*p.1,p.2)

def rootTrace {V : Type u2} (F : ℂ × V → ℝ) (p : ℂ × V) : ℝ :=
  rootOrbitAverage m F (chosenRoot m p.1,p.2)

lemma rootOrbitAverage_orbit {V : Type u3} (F : ℂ × V → ℝ) (x : ℂ) (v : V)
    (η : rootsOfUnity m ℂ) :
    rootOrbitAverage m F ((η.val : ℂ)*x,v) = rootOrbitAverage m F (x,v) := by
  unfold rootOrbitAverage
  congr 1
  have he := Equiv.sum_comp (Equiv.mulRight η)
    (fun ζ : rootsOfUnity m ℂ ↦ F ((ζ.val : ℂ)*x,v))
  change (∑ ζ : rootsOfUnity m ℂ, F ((((ζ * η).val : ℂ))*x,v)) = _ at he
  simpa only [Subgroup.coe_mul, Units.val_mul, mul_assoc] using he

lemma rootTrace_pow {V : Type u4} (F : ℂ × V → ℝ) (x : ℂ) (v : V) :
    rootTrace m F (x^m,v) = rootOrbitAverage m F (x,v) := by
  obtain ⟨ζ,hζ⟩ := same_power_orbit m (chosenRoot_pow m (x^m))
  change rootOrbitAverage m F (chosenRoot m (x^m),v) = _
  rw [hζ,rootOrbitAverage_orbit]

lemma continuous_rootOrbitAverage {V : Type u5} [TopologicalSpace V]
    {F : ℂ × V → ℝ} (hF : Continuous F) : Continuous (rootOrbitAverage m F) := by
  unfold rootOrbitAverage
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro ζ _
  exact hF.comp (by fun_prop)

theorem continuous_rootTrace {V : Type u6} [TopologicalSpace V]
    {F : ℂ × V → ℝ} (hF : Continuous F) : Continuous (rootTrace m F) := by
  have hquot := ((Complex.isOpenQuotientMap_pow m).prodMap
    (IsOpenQuotientMap.id (X := V))).isQuotientMap
  apply hquot.continuous_iff.mpr
  convert continuous_rootOrbitAverage m hF using 1
  ext p
  exact rootTrace_pow m F p.1 p.2

lemma rootTrace_zero {V : Type u7} (F : ℂ × V → ℝ) (v : V) :
    rootTrace m F (0,v) = F (0,v) := by
  have hc : Fintype.card (rootsOfUnity m ℂ) = m := by
    rw [← Nat.card_eq_fintype_card, Complex.card_rootsOfUnity]
  have hz : (0 : ℂ)^m=0 := zero_pow (NeZero.ne m)
  conv_lhs => rw [← hz]
  rw [rootTrace_pow]
  simp only [rootOrbitAverage, mul_zero, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hc]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne m)), one_mul]

lemma rootTrace_nonneg {V : Type u8} {F : ℂ × V → ℝ}
    (hF : ∀ p, 0 ≤ F p) (p : ℂ × V) : 0 ≤ rootTrace m F p := by
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m))
  exact Finset.sum_nonneg fun ζ _ ↦ hF _

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric Complex BigOperators
noncomputable section

lemma DiskPshOn.sum {E : Type u9} {ι : Type u10} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (s : Finset ι) (q : ι → E → ℝ) (hq : ∀ i ∈ s, DiskPshOn U (q i)) :
    DiskPshOn U (fun x ↦ ∑ i ∈ s, q i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using diskPshOn_const U 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hq i (Finset.mem_insert_self i s)).add
      (ih (fun j hj ↦ hq j (Finset.mem_insert_of_mem hj)))

variable (m : ℕ) [NeZero m]
local instance : Fintype (rootsOfUnity m ℂ) := Fintype.ofFinite _

lemma rootTrace_eq_of_pow {W : Type u11} (F : ℂ × W → ℝ) {z x : ℂ} (hz : z^m=x)
    (v : W) : rootTrace m F (x,v) = rootOrbitAverage m F (z,v) := by
  rw [← hz, rootTrace_pow]

theorem continuousOn_rootTrace {W : Type u12} [TopologicalSpace W]
    {U : Set (ℂ × W)} {F : ℂ × W → ℝ} (hU : IsOpen U)
    (hF : ContinuousOn F ((fun p : ℂ × W ↦ (p.1^m,p.2)) ⁻¹' U)) :
    ContinuousOn (rootTrace m F) U := by
  let π : ℂ × W → ℂ × W := fun p ↦ (p.1^m,p.2)
  have hav : ContinuousOn (rootOrbitAverage m F) (π ⁻¹' U) := by
    apply ContinuousOn.const_mul
    apply continuousOn_finsetSum
    intro ζ _
    apply hF.comp (by fun_prop : ContinuousOn
      (fun p : ℂ × W ↦ ((ζ.val : ℂ)*p.1,p.2)) (π ⁻¹' U))
    intro p hp
    change (((ζ.val : ℂ)*p.1)^m,p.2) ∈ U
    rw [mul_pow, (mem_rootsOfUnity' m ζ.val).mp ζ.property, one_mul]
    exact hp
  have hπ := ((Complex.isOpenQuotientMap_pow m).prodMap
    (IsOpenQuotientMap.id (X := W)))
  apply (hπ.isQuotientMap.continuousOn_isOpen_iff hU).mpr
  apply hav.congr
  intro p _
  exact rootTrace_pow m F p.1 p.2

def centeredRoot (x : ℂ) (z : ℂ) : ℂ :=
  chosenRoot m x * (z/x) ^ ((m : ℂ)⁻¹)

lemma centeredRoot_pow {x : ℂ} (hx : x ≠ 0) (z : ℂ) : centeredRoot m x z ^ m = z := by
  rw [centeredRoot, mul_pow, chosenRoot_pow,
    Complex.cpow_nat_inv_pow _ (NeZero.ne m)]
  exact mul_div_cancel₀ z hx

lemma centeredRoot_differentiableOn {x : ℂ} :
    DifferentiableOn ℂ (centeredRoot m x) {z | z/x ∈ Complex.slitPlane} := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  exact ((analyticAt_const.mul ((analyticAt_id.div_const (c := x)).cpow analyticAt_const hz)).differentiableAt)

variable {V : Type u13} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [LocallyCompactSpace V]

omit [LocallyCompactSpace V] in

theorem rootTrace_psh_off_zero {U : Set (ℂ × V)} (hU : IsOpen U)
    {F : ℂ × V → ℝ}
    (hF : ContinuousOn F ((fun p : ℂ × V ↦ (p.1^m,p.2)) ⁻¹' U))
    (hp : DiskPshOn ((fun p : ℂ × V ↦ (p.1^m,p.2)) ⁻¹' U) F) :
    DiskPshOn (U ∩ {p | p.1 ≠ 0}) (rootTrace m F) := by
  let π : ℂ × V → ℂ × V := fun p ↦ (p.1^m,p.2)
  have hc := continuousOn_rootTrace m hU hF
  apply DiskPshOn.of_locally (hc.mono inter_subset_left)
  intro x hx
  let W : Set (ℂ × V) := U ∩ {p | p.1/x.1 ∈ Complex.slitPlane}
  have hW : IsOpen W := hU.inter (Complex.isOpen_slitPlane.preimage (by fun_prop))
  have hxW : x ∈ W := by
    refine ⟨hx.1, ?_⟩
    change x.1 / x.1 ∈ Complex.slitPlane
    simpa only [div_self hx.2] using Complex.one_mem_slitPlane
  refine ⟨W, hW, hxW, ?_⟩
  let R : rootsOfUnity m ℂ → (ℂ × V) → (ℂ × V) :=
    fun ζ p ↦ ((ζ.val : ℂ) * centeredRoot m x.1 p.1,p.2)
  have hRd (ζ : rootsOfUnity m ℂ) : DifferentiableOn ℂ (R ζ) W := by
    apply DifferentiableOn.prodMk
    · apply DifferentiableOn.const_mul
      exact (centeredRoot_differentiableOn m).comp differentiableOn_fst (fun p hp ↦ hp.2)
    · exact differentiableOn_snd
  have hRm (ζ : rootsOfUnity m ℂ) : MapsTo (R ζ) W (π ⁻¹' U) := by
    intro p hp
    change (((ζ.val : ℂ) * centeredRoot m x.1 p.1)^m,p.2) ∈ U
    rw [mul_pow, (mem_rootsOfUnity' m ζ.val).mp ζ.property, one_mul,
      centeredRoot_pow m hx.2]
    exact hp.1
  have hsum := DiskPshOn.sum (Finset.univ : Finset (rootsOfUnity m ℂ))
    (fun ζ p ↦ F (R ζ p)) (fun ζ _ ↦ hp.comp (hRd ζ) (hRm ζ))
  have hsumc : ContinuousOn (fun p ↦ ∑ ζ : rootsOfUnity m ℂ, F (R ζ p)) W := by
    apply continuousOn_finsetSum
    intro ζ _
    exact hF.comp (hRd ζ).continuousOn (hRm ζ)
  have hs := hsum.const_mul_of_continuous hsumc (inv_nonneg.mpr (Nat.cast_nonneg m))
  apply hs.congr
  intro p _
  exact (rootTrace_eq_of_pow m F (centeredRoot_pow m hx.2 p.1) p.2).symm

theorem rootTrace_psh {U : Set (ℂ × V)} (hU : IsOpen U)
    {F : ℂ × V → ℝ}
    (hF : ContinuousOn F ((fun p : ℂ × V ↦ (p.1^m,p.2)) ⁻¹' U))
    (hF0 : ∀ p, (p.1^m,p.2) ∈ U → 0 ≤ F p)
    (hp : DiskPshOn ((fun p : ℂ × V ↦ (p.1^m,p.2)) ⁻¹' U) F) :
    DiskPshOn U (rootTrace m F) := by
  apply first_hyperplane_removable hU (continuousOn_rootTrace m hU hF)
  · intro p hpU
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m))
    apply Finset.sum_nonneg
    intro ζ _
    apply hF0
    rw [mul_pow, (mem_rootsOfUnity' m ζ.val).mp ζ.property, one_mul, chosenRoot_pow]
    exact hpU
  · exact rootTrace_psh_off_zero m hU hF hp

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric Complex BigOperators
noncomputable section
variable {W : Type u14} [NormedAddCommGroup W] [NormedSpace ℂ W]

def swapBase (p : ℂ × (ℂ × W)) : ℂ × (ℂ × W) := (p.2.1,(p.1,p.2.2))

omit [NormedAddCommGroup W] [NormedSpace ℂ W] in
@[simp] lemma swapBase_swapBase (p : ℂ × (ℂ × W)) : swapBase (swapBase p) = p := rfl

lemma differentiable_swapBase : Differentiable ℂ (swapBase (W := W)) := by
  exact (differentiable_snd.fst).prodMk
    (differentiable_fst.prodMk (differentiable_snd.snd))

variable (m : ℕ) [NeZero m]
local instance : Fintype (rootsOfUnity m ℂ) := Fintype.ofFinite _

def secondRootTrace (F : ℂ × (ℂ × W) → ℝ) (p : ℂ × (ℂ × W)) : ℝ :=
  rootTrace m (F ∘ swapBase) (swapBase p)

lemma continuousOn_secondRootTrace {U : Set (ℂ × (ℂ × W))} (hU : IsOpen U)
    {F : ℂ × (ℂ × W) → ℝ}
    (hF : ContinuousOn F ((fun p : ℂ × (ℂ × W) ↦ (p.1,(p.2.1^m,p.2.2))) ⁻¹' U)) :
    ContinuousOn (secondRootTrace m F) U := by
  have hT := differentiable_swapBase (W := W)
  have hc : ContinuousOn (F ∘ swapBase)
      ((fun p : ℂ × (ℂ × W) ↦ (p.1^m,p.2)) ⁻¹' (swapBase ⁻¹' U)) :=
    hF.comp hT.continuous.continuousOn (fun _ h ↦ h)
  exact (continuousOn_rootTrace m (hU.preimage hT.continuous) hc).comp
    hT.continuous.continuousOn (fun _ h ↦ h)

variable [LocallyCompactSpace W]

lemma secondRootTrace_psh {U : Set (ℂ × (ℂ × W))} (hU : IsOpen U)
    {F : ℂ × (ℂ × W) → ℝ}
    (hF : ContinuousOn F ((fun p : ℂ × (ℂ × W) ↦ (p.1,(p.2.1^m,p.2.2))) ⁻¹' U))
    (hF0 : ∀ p, (p.1,(p.2.1^m,p.2.2)) ∈ U → 0 ≤ F p)
    (hp : DiskPshOn ((fun p : ℂ × (ℂ × W) ↦ (p.1,(p.2.1^m,p.2.2))) ⁻¹' U) F) :
    DiskPshOn U (secondRootTrace m F) := by
  have hT := differentiable_swapBase (W := W)
  have hc : ContinuousOn (F ∘ swapBase)
      ((fun p : ℂ × (ℂ × W) ↦ (p.1^m,p.2)) ⁻¹' (swapBase ⁻¹' U)) :=
    hF.comp hT.continuous.continuousOn (fun _ h ↦ h)
  have hq : DiskPshOn
      ((fun p : ℂ × (ℂ × W) ↦ (p.1^m,p.2)) ⁻¹' (swapBase ⁻¹' U)) (F ∘ swapBase) :=
    hp.comp hT.differentiableOn (fun _ h ↦ h)
  exact (rootTrace_psh m (hU.preimage hT.continuous) hc
    (fun p h ↦ hF0 (swapBase p) h) hq).comp hT.differentiableOn (fun _ h ↦ h)

def doubleRootTrace (F : ℂ × (ℂ × W) → ℝ) : ℂ × (ℂ × W) → ℝ :=
  rootTrace m (secondRootTrace m F)

omit [LocallyCompactSpace W] [NormedAddCommGroup W] [NormedSpace ℂ W] in
lemma doubleRootTrace_formula (F : ℂ × (ℂ × W) → ℝ) (p : ℂ × (ℂ × W)) :
    doubleRootTrace m F p = (m : ℝ)⁻¹ ^ 2 *
      ∑ ζ : rootsOfUnity m ℂ, ∑ η : rootsOfUnity m ℂ,
        F ((ζ.val : ℂ) * chosenRoot m p.1,
          ((η.val : ℂ) * chosenRoot m p.2.1,p.2.2)) := by
  simp only [doubleRootTrace, secondRootTrace, rootTrace, rootOrbitAverage,
    Function.comp_apply, swapBase]
  rw [← Finset.mul_sum, ← mul_assoc, pow_two]

omit [LocallyCompactSpace W] in
lemma continuousOn_doubleRootTrace {U : Set (ℂ × (ℂ × W))} (hU : IsOpen U)
    {F : ℂ × (ℂ × W) → ℝ}
    (hF : ContinuousOn F ((fun p : ℂ × (ℂ × W) ↦ (p.1^m,(p.2.1^m,p.2.2))) ⁻¹' U)) :
    ContinuousOn (doubleRootTrace m F) U := by
  apply continuousOn_rootTrace m hU
  apply continuousOn_secondRootTrace m (hU.preimage (by fun_prop))
  exact hF

theorem doubleRootTrace_psh {U : Set (ℂ × (ℂ × W))} (hU : IsOpen U)
    {F : ℂ × (ℂ × W) → ℝ}
    (hF : ContinuousOn F ((fun p : ℂ × (ℂ × W) ↦ (p.1^m,(p.2.1^m,p.2.2))) ⁻¹' U))
    (hF0 : ∀ p, (p.1^m,(p.2.1^m,p.2.2)) ∈ U → 0 ≤ F p)
    (hp : DiskPshOn ((fun p : ℂ × (ℂ × W) ↦ (p.1^m,(p.2.1^m,p.2.2))) ⁻¹' U) F) :
    DiskPshOn U (doubleRootTrace m F) := by
  apply rootTrace_psh m hU
  · exact continuousOn_secondRootTrace m (hU.preimage (by fun_prop)) hF
  · intro p hpU
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m))
    apply Finset.sum_nonneg
    intro η _
    apply hF0
    change (p.1 ^ m, (((η.val : ℂ) * chosenRoot m p.2.1)^m,p.2.2)) ∈ U
    rw [mul_pow, (mem_rootsOfUnity' m η.val).mp η.property, one_mul, chosenRoot_pow]
    exact hpU
  · exact secondRootTrace_psh m (hU.preimage (by fun_prop)) hF hF0 hp

end
end QuadricCounterexample

end OAI
