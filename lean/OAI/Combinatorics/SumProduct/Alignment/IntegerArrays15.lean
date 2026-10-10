import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays14
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
end

 

 

 

noncomputable section
open scoped BigOperators BoundedContinuousFunction Topology NNReal ENNReal
namespace SourceIntegerArrays.GlobalJoint.SourceFrozenFamily
open ProductExposureLabels ProductExposureLaw SourceExposureSlots SourceResidueAlignment
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.AlignmentScales
open ConstructedWordPlan.RationalPivotPlan
open ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic
open RawHarmonicProbability
attribute [local instance] Classical.propDecidable
variable {a : ℕ} (D : Pivot a)

 

lemma residue_abs_le (L t q : ℤ) (hL : 0 < L) :
    |SourceResidueAlignment.residue L t q| ≤ L := by
  by_cases hc : IsCoprime t L
  · have h := SourceResidueAlignment.residue_spec L t q hL hc
    rw [abs_of_nonneg h.1]
    exact h.2.1.le
  · simp only [SourceResidueAlignment.residue, hc, and_false, ↓reduceDIte, abs_zero]
    exact hL.le

lemma actual_slot_bound (L : ℤ) (hL : 0 < L) (C : Fin D.pairs → ℤ)
    (u : Fin a → ℤ) (v : Slots D) :
    |slotValue D L C u v| ≤ (∑ e, |v e|) * L := by
  calc
    |slotValue D L C u v| ≤ ∑ e, |v e * rValue D L C u e| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, |v e| * L := by
      apply Finset.sum_le_sum
      intro e he
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (residue_abs_le L _ _ hL) (abs_nonneg _)
    _ = (∑ e, |v e|) * L := by rw [Finset.sum_mul]

lemma source_heightCoeff_bound (q₀ : ℕ) (hq₀ : 0 < q₀)
    (ht : ℕ → Fin a → ℤ) (N M : ℕ) (hpos : ∀ j, 0 < ht N j)
    (hheight : ∀ e, height (ht N) (D.added e) ≤ M) (e : Fin D.pairs) :
    |heightCoeff D q₀ ht N e| ≤ M := by
  have hA : 0 ≤ height (ht N) (D.added e) :=
    (Finset.prod_pos (fun j _ => hpos j)).le
  have hB : 0 ≤ (q₀ : ℤ) * height (ht N) (block D.index D.tail (D.owner e)) := by
    exact mul_nonneg (by omega) (Finset.prod_pos (fun j _ => hpos j)).le
  unfold heightCoeff
  rw [abs_of_nonneg (Int.ediv_nonneg hA hB)]
  exact (Int.ediv_le_self _ hA).trans (hheight e)

lemma perm_inside (t : Fin D.targets) (j : Fin (m D t)) :
    perm D t (j.castAdd (h D t)) ∈ D.tail t := by
  unfold perm
  rw [Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.trans_apply]
  exact ((Fintype.equivFin {j : Fin a // j ∈ D.tail t}).symm j).property

 

lemma reconstruct_outside_bound (t : Fin D.targets) (X : Fin a → ℕ) (W : ℕ)
    (y : Fin (h D t) → ℕ)
    (hy : y ∈ outsideDomain (fun j => X (perm D t (j.natAdd (m D t)))) W)
    (b : Label (m D t)) (j : Fin a) (hj : j ∉ D.tail t) :
    |reconstruct D t y b j| ≤ (X j : ℤ)^2 := by
  obtain ⟨k, rfl⟩ := (perm D t).surjective j
  revert hj
  refine Fin.addCases ?_ ?_ k
  · intro i hi
    exact False.elim (hi (perm_inside D t i))
  · intro i hi
    have h := Fintype.mem_piFinset.mp hy i
    have hh := (Finset.mem_Ico.mp (Finset.mem_filter.mp h).1).2.le
    simpa [reconstruct, abs_of_nonneg (Int.natCast_nonneg _)] using
      (show (y i : ℤ) ≤ (X (perm D t (i.natAdd (m D t))) : ℤ)^2 by exact_mod_cast hh)

 

lemma source_qValue_bound (q₀ : ℕ) (hq₀ : 0 < q₀)
    (ht : ℕ → Fin a → ℤ) (N M : ℕ) (hpos : ∀ j, 0 < ht N j)
    (hheight : ∀ e, height (ht N) (D.added e) ≤ M)
    (hd : ∀ e, Disjoint (D.added e) (D.tail (D.owner e)))
    (X : Fin a → ℕ) (hX : ∀ j, 1 ≤ X j) (W : ℕ)
    (t : Fin D.targets) (y : Fin (h D t) → ℕ)
    (hy : y ∈ outsideDomain (fun j => X (perm D t (j.natAdd (m D t)))) W)
    (b : Label (m D t)) (k : Fin (qdim D t)) :
    |qValue D (heightCoeff D q₀ ht N) (reconstruct D t y b) (ownPair D t k).val| ≤
      (M : ℤ) * (∏ j ∈ Finset.univ.filter (fun j : Fin a => j < D.index), (X j : ℤ))^2 := by
  let e := (ownPair D t k).val
  have he : D.owner e = t := (ownPair D t k).property
  have hpoint (j : Fin a) (hj : j ∈ D.added e) :
      |reconstruct D t y b j| ≤ (X j : ℤ)^2 := by
    apply reconstruct_outside_bound D t X W y hy b j
    intro ht
    exact Finset.disjoint_left.mp (hd e) hj (by simpa [he] using ht)
  have hprod : |∏ j ∈ D.added e, reconstruct D t y b j| ≤
      (∏ j ∈ Finset.univ.filter (fun j : Fin a => j < D.index), (X j : ℤ))^2 := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ j ∈ D.added e, (X j : ℤ)^2 :=
        Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j hj => hpoint j hj)
      _ ≤ ∏ j ∈ Finset.univ.filter (fun j : Fin a => j < D.index), (X j : ℤ)^2 := by
        apply Finset.prod_le_prod_of_subset_of_one_le₀
          (by intro j hj; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, D.added_lt e j hj⟩)
          (fun j _ => sq_nonneg _)
        intro j _ _
        have hx : (1 : ℤ) ≤ X j := by exact_mod_cast hX j
        nlinarith
      _ = (∏ j ∈ Finset.univ.filter (fun j : Fin a => j < D.index), (X j : ℤ))^2 := by
        rw [Finset.prod_pow]
  unfold qValue
  rw [abs_mul]
  exact mul_le_mul (source_heightCoeff_bound D q₀ hq₀ ht N M hpos hheight e)
    hprod (abs_nonneg _) (by omega)

 
def previousProduct (X : Fin a → ℕ) : ℕ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin a => j < D.index), X j

lemma previousProduct_pos (X : Fin a → ℕ) (hX : ∀ j, 1 ≤ X j) :
    0 < previousProduct D X :=
  Finset.prod_pos (fun j _ => lt_of_lt_of_le Nat.zero_lt_one (hX j))

lemma le_previousProduct (X : Fin a → ℕ) (hX : ∀ j, 1 ≤ X j)
    (j : Fin a) (hj : j < D.index) : X j ≤ previousProduct D X :=
  Finset.single_le_prod (fun j _ => hX j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)

lemma tail_product_le_previous (X : Fin a → ℕ) (hX : ∀ j, 1 ≤ X j)
    (t : Fin D.targets) :
    (∏ j : Fin (m D t), X (perm D t (j.castAdd (h D t)))) ≤ previousProduct D X := by
  let e : Fin (m D t) ↪ Fin a :=
    ⟨fun j => perm D t (j.castAdd (h D t)), by
      intro j k he
      apply Fin.ext
      exact congrArg (fun z : Fin (m D t + h D t) => z.val) ((perm D t).injective he)⟩
  have hsub : Finset.univ.map e ⊆ Finset.univ.filter (fun j : Fin a => j < D.index) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, D.tail_lt t _ (perm_inside D t k)⟩
  calc
    _ = ∏ j ∈ Finset.univ.map e, X j := (Finset.prod_map _ _ _).symm
    _ ≤ previousProduct D X := Finset.prod_le_prod_of_subset_of_one_le₀ hsub
      (fun j _ => Nat.zero_le _) (fun j _ _ => hX j)

variable (s r : ℕ) (hs : 1 ≤ s) (Fs : Finset (Scale a)) (q₀ : ℕ) (b₀ : Scale a)
local notation "I" => FiniteModelSlots.Index D s r hs Fs q₀ b₀

 

def modelBudget : ℝ :=
  (∑ av ∈ FiniteModelSlots.required D s r hs Fs q₀ b₀,
    ∑ e, |(av.2 e : ℝ)|) +
  ∑ p ∈ pivotOptions s r hs D Fs, ∑ i : Comparison D Fs r,
    ∑ e, |(ownInput D (qdim D) (coord D) i.2.1.1
      (terminalShift D q₀ (scaleRun D 0 p b₀ * i.1.val) i.2.1.2.val).toAdd e : ℝ)|

lemma modelBudget_nonneg : 0 ≤ modelBudget D s r hs Fs q₀ b₀ := by
  unfold modelBudget
  positivity

lemma modelBudget_slot (i : I) :
    (∑ e, |(i.1.val.2 e : ℝ)|) ≤ modelBudget D s r hs Fs q₀ b₀ := by
  unfold modelBudget
  apply le_trans ?_ (le_add_of_nonneg_right (by positivity))
  exact Finset.single_le_sum (f := fun av : ℚ × Slots D => ∑ e, |(av.2 e : ℝ)|)
    (fun av _ => Finset.sum_nonneg (fun e _ => abs_nonneg _)) i.1.property

lemma modelBudget_input (p : Path D) (hp : p ∈ pivotOptions s r hs D Fs)
    (i : Comparison D Fs r) :
    (∑ e, |(ownInput D (qdim D) (coord D) i.2.1.1
      (terminalShift D q₀ (scaleRun D 0 p b₀ * i.1.val) i.2.1.2.val).toAdd e : ℝ)|) ≤
      modelBudget D s r hs Fs q₀ b₀ := by
  apply le_trans ?_ (le_add_of_nonneg_left (by positivity))
  apply le_trans (Finset.single_le_sum
    (fun i _ => Finset.sum_nonneg (fun e _ => abs_nonneg _)) (Finset.mem_univ i))
  apply Finset.single_le_sum _ hp
  intro p hp
  positivity

open Filter MeasureTheory RationalLattice MalcevCharacters
open MicrocellScale AdmissibleMicrocellBoundary RoughScales IntegerAlignment
open RoughSamplingWeights SourceMacroSelection

section Harmonic
variable (G₀ : Fin D.targets → ℚ → Fin r → Type)
variable [∀ t v c, Group (G₀ t v c)] [∀ t v c, TopologicalSpace (G₀ t v c)]
variable [∀ t v c, IsTopologicalGroup (G₀ t v c)]
variable (Γ₀ : ∀ t v c, Subgroup (G₀ t v c))
variable (n₀ : Fin D.targets → ℚ → Fin r → ℕ)
variable (c₀ : ∀ t v c, RealCoordinates (G₀ t v c) (n₀ t v c))
variable (hsk : ∀ t v c, SecondKind (c₀ t v c))
variable (A₀ : ∀ t v c, CubeFaces.Filtration (G₀ t v c))
variable (weight : ∀ t v c, Fin (n₀ t v c) → ℕ)
variable (hA : ∀ t v c k (g : G₀ t v c), g ∈ (A₀ t v c).level k ↔
  ∀ j, weight t v c j < k → (c₀ t v c).coord g j = 0)
variable (hw : ∀ t v c j, 0 < weight t v c j)
include hsk hA hw

 

theorem source_actual_harmonic
    (hΓ : ∀ t v c g, g ∈ Γ₀ t v c ↔ ∀ j, ∃ z : ℤ, (c₀ t v c).coord g j = z)
    (hmono : ∀ t v c, Monotone (weight t v c))
    (h0 : ∀ t v c, (A₀ t v c).level 0 = ⊤)
    (h1 : ∀ t v c, (A₀ t v c).level 1 = ⊤)
    (hstep : ∀ t v c, (A₀ t v c).level (s+1) = ⊥)
    (M J R H : ℕ → ℕ) (L : ℕ → ℤ) (ht : ℕ → Fin a → ℤ)
    (g₀ x₀ : ∀ t, ℕ → (Fin (h D t) → ℕ) → ∀ v c, ℤ → ℤ → G₀ t v c)
    (obs₀ : ∀ t, ℕ → (Fin (h D t) → ℕ) → ∀ v c, ℤ → ℤ → ((G₀ t v c) ⧸ Γ₀ t v c) →ᵇ ℝ)
    (w0 Xp : ℕ → ℕ) (X : ℕ → Fin a → ℕ)
    (hw0 : Tendsto w0 atTop atTop)
    (hX : ∀ N j, 4*primorial (w0 N) ≤ X N j)
    (hXp : ∀ N, 4*primorial (w0 N) ≤ Xp N)
    (hXt : ∀ j, Tendsto (fun N => X N j) atTop atTop)
    (hXpt : Tendsto Xp atTop atTop)
    (hWM : ∀ N, (primorial (w0 N) : ℤ) ∣ (M N : ℤ))
    (hM : ∀ N, 0 < M N) (hMs : ∀ N, RoughScales.Smooth (w0 N) (M N : ℤ))
    (hJ : ∀ N, 0 < J N) (hRJ : ∀ N, R N = M N*J N)
    (hL : ∀ N, 0 < L N) (hsm : ∀ N, RoughScales.Smooth (w0 N) (L N))
    (hWL : ∀ N, (primorial (w0 N) : ℤ) ∣ L N) (hML : ∀ N, (M N : ℤ) ∣ L N)
    (hLexact : ∀ N, L N = (M N : ℤ)*(primorial (w0 N) : ℤ)^(w0 N))
    (hXL : ∀ t (j : Fin (m D t)), Tendsto (fun N =>
      (X N (perm D t (j.castAdd (h D t))) : ℝ)/(L N : ℝ)) atTop atTop)
    (hH : ∀ N, 0 < H N) (hRrad : ∀ N, R N = radius (M N) (H N))
    (hdom : Dominates (fun N => (H N : ℝ)) (earlierScale M (fun N => previousProduct D (X N))))
    (hxdom : Dominates (fun N => Real.log (Xp N : ℝ)) (fun N => (H N : ℝ)))
    (hLsize : ∀ᶠ N in atTop, (L N : ℝ) ≤ (M N : ℝ)^2)
    (hq₀ : 0 < q₀) (hht : ∀ N j, 0 < ht N j)
    (hheight : ∀ N e, height (ht N) (D.added e) ≤ M N)
    (hd : ∀ e, Disjoint (D.added e) (D.tail (D.owner e)))
    (metric : ∀ t v c, MetricSpace ((G₀ t v c) ⧸ Γ₀ t v c))
    (hmetric : ∀ t v c, QuotientGroup.instTopologicalSpace (Γ₀ t v c) =
      (metric t v c).toUniformSpace.toTopologicalSpace) :
    letI : ∀ t v c, MetricSpace ((G₀ t v c) ⧸ Γ₀ t v c) :=
      fun t v c => (metric t v c).replaceTopology (hmetric t v c)
    ∀ (Kobs : ℝ≥0) (Bobs : ℝ),
      (∀ t N y v c b r', LipschitzWith Kobs (obs₀ t N y v c b r')) →
      (∀ t N y v c b r' z, |obs₀ t N y v c b r' z| ≤ Bobs) →
      ∀ (Bs : Finset (Scale a)), b₀ ∈ Bs →
      pivotModulus s r hs D Fs Bs ∣ q₀ → ∀ (τ : ℝ), 0 < τ →
    let d := family D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L (heightCoeff D q₀ ht) g₀ x₀ obs₀
    Tendsto (fun N => (jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _) (hX N) (hXp N))
      {z | cellRatio (Xp N) (primorial (w0 N)) (M N) (J N) z.2 (primorial_pos _) (hXp N)
        {k | ((d.atTime N).localModel z).modelSuccess (coord D) (k : ℤ) s r hs
          (FiniteModelSlots.formula D s r hs Fs q₀ b₀) Fs q₀ b₀ τ} ≤
            ((pivotOptions s r hs D Fs).card : ℝ)⁻¹/3}) atTop (𝓝 0) := by
  let : ∀ t v c, MetricSpace ((G₀ t v c) ⧸ Γ₀ t v c) :=
    fun t v c => (metric t v c).replaceTopology (hmetric t v c)
  intro Kobs Bobs hLip hBound Bs hb hq τ hτ
  let d := family D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L (heightCoeff D q₀ ht) g₀ x₀ obs₀
  let P := fun N => previousProduct D (X N)
  let Q := fun N => (M N : ℝ)*(P N : ℝ)^2
  have hx1 (N j) : 1 ≤ X N j := by
    have hW := primorial_pos (w0 N)
    have hh := hX N j
    omega
  have hP (N) : 0 < P N := previousProduct_pos D (X N) (hx1 N)
  have hprod : ∀ t, ∀ᶠ N in atTop,
      (∀ j : Fin (m D t), X N (perm D t (j.castAdd (h D t))) ≤ P N) ∧
      (∏ j : Fin (m D t), (X N (perm D t (j.castAdd (h D t))) : ℝ)^2) ≤ (P N : ℝ)^2 := by
    intro t
    apply Filter.Eventually.of_forall
    intro N
    constructor
    · intro j
      exact le_previousProduct D (X N) (hx1 N) _ (D.tail_lt t _ (perm_inside D t j))
    · rw [Finset.prod_pow]
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast tail_product_le_previous D (X N) (hx1 N) t
  have hslot : ∀ t N y,
      y ∈ outsideDomain (fun j : Fin (h D t) => X N (perm D t (j.natAdd (m D t)))) (primorial (w0 N)) →
      ∀ (b : Label (m D t)) (i : I), |(d.slot t N y b i : ℝ)| ≤ modelBudget D s r hs Fs q₀ b₀*(L N : ℝ) := by
    intro t N y hy b i
    have hn : (0 : ℝ) ≤ L N := by exact_mod_cast (hL N).le
    apply le_trans _ (mul_le_mul_of_nonneg_right (modelBudget_slot D s r hs Fs q₀ b₀ i) hn)
    exact_mod_cast actual_slot_bound D (L N) (hL N) (heightCoeff D q₀ ht N) (reconstruct D t y b) i.1.val.2
  have hQ : ∀ t N y,
      y ∈ outsideDomain (fun j : Fin (h D t) => X N (perm D t (j.natAdd (m D t)))) (primorial (w0 N)) →
      ∀ (b : Label (m D t)) k, |(d.qval t N y b k : ℝ)| ≤ Q N := by
    intro t N y hy b k
    have hb := source_qValue_bound D q₀ hq₀ ht N (M N) (hht N) (hheight N) hd
      (X N) (hx1 N) (primorial (w0 N)) t y hy b k
    dsimp only [Q, P, previousProduct]
    exact_mod_cast hb
  exact source_model_harmonic D (fun t (i : I) => G₀ t i.1.val.1 i.2)
    (fun t i => n₀ t i.1.val.1 i.2) (qdim D)
    (fun t i => c₀ t i.1.val.1 i.2) (fun t i => hsk t i.1.val.1 i.2)
    (fun t i => A₀ t i.1.val.1 i.2) (fun t i => weight t i.1.val.1 i.2)
    (fun t i => hA t i.1.val.1 i.2) (fun t i => hw t i.1.val.1 i.2)
    (fun t i => Γ₀ t i.1.val.1 i.2) (coord D)
    (fun t i => hΓ t i.1.val.1 i.2) (fun t i => hmono t i.1.val.1 i.2) s
    (fun t i => h0 t i.1.val.1 i.2) (fun t i => h1 t i.1.val.1 i.2)
    (fun t i => hstep t i.1.val.1 i.2) a d w0 Xp P X Q hw0 hX hXp hXt hXpt
    hWM hM hMs hJ hRJ hL hsm hWL hML hLexact hXL hH hP hRrad hdom hxdom hprod
    (fun _ => by dsimp [Q]; positivity) (Eventually.of_forall (fun _ => le_rfl)) hLsize
    (modelBudget D s r hs Fs q₀ b₀) (modelBudget_nonneg D s r hs Fs q₀ b₀)
    (fun t N y hy b _ i => hslot t N y hy b i)
    (fun t N y hy b _ k => hQ t N y hy b k)
    (fun t i => metric t i.1.val.1 i.2) (fun t i => hmetric t i.1.val.1 i.2)
    Kobs Bobs (fun t N y i => hLip t N y i.1.val.1 i.2)
    (fun t N y i => hBound t N y i.1.val.1 i.2)
    r hs (FiniteModelSlots.formula D s r hs Fs q₀ b₀) Fs Bs q₀ hq b₀ hb τ hτ
    (modelBudget_input D s r hs Fs q₀ b₀)

end Harmonic

end SourceIntegerArrays.GlobalJoint.SourceFrozenFamily

end
end

end OAI
