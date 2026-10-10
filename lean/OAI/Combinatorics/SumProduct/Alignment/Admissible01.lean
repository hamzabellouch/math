import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.Blocks01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Topology
noncomputable section
open scoped BigOperators Topology BoundedContinuousFunction
noncomputable section
open scoped BigOperators
open MeasureTheory Filter Function
noncomputable section
open scoped BigOperators
noncomputable section
open Filter MeasureTheory
open scoped Topology BoundedContinuousFunction NNReal
noncomputable section
open scoped Topology BigOperators
noncomputable section
open scoped Topology BigOperators commutatorElement
noncomputable section
open scoped Topology BoundedContinuousFunction NNReal
noncomputable section
open scoped BigOperators
noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction NNReal
noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators
namespace SourceAdmissible
open SourceBlocks SourceChartedAlignment MicrocellScale AdmissibleMicrocellBoundary
open ConstructedWordPlan.GlobalWordPlan
open ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic
open SourceIntegerArrays.GlobalJoint.SourceFrozenFamily
attribute [local instance] Classical.propDecidable

 
def previous {a : ℕ} (X : Fin a → ℕ) (i : Fin a) : ℕ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin a => j < i), X j

 

structure Parameters (a : ℕ) where
  M : ℕ → ℕ
  ht : ℕ → Fin a → ℤ
  H : ℕ → Fin a → ℕ
  X : ℕ → Fin a → ℕ
  Mpos : ∀ N, 0 < M N
  htpos : ∀ N i, 0 < ht N i
  Hpos : ∀ N i, 0 < H N i
  Xpow : ∀ N i, ∃ k : ℕ, X N i = 2^k
  Msmooth : ∀ N, RoughScales.Smooth (N+1) (M N : ℤ)
  htsmooth : ∀ N i, RoughScales.Smooth (N+1) (ht N i)
  Mdiv : ∀ N, primorial (N+1) ^ (N+1) ∣ M N
  htdiv : ∀ N i, (primorial (N+1) : ℤ) ^ (N+1) ∣ ht N i
  singleton_bound : ∀ N i, ht N i ≤ M N
  block_bound : ∀ N (B : Block a), height (ht N) B.set ≤ M N
  ratio : ∀ N (B : Block a) A, Added B.1 B.2.val A →
    ∃ d : ℤ, height (ht N) A = height (ht N) B.set *
      ((primorial (N+1) : ℤ) ^ (N+1) * d)
  Hdiv : ∀ N i, M N ∣ H N i
  Hdom : ∀ i, Dominates (fun N => (H N i : ℝ))
    (earlierScale M (fun N => previous (X N) i))
  Xdom : ∀ i, Dominates (fun N => Real.log (X N i : ℝ)) (fun N => (H N i : ℝ))

variable {a : ℕ} (A : Parameters a)

def Parameters.L (N : ℕ) : ℤ := (A.M N : ℤ) * (primorial (N+1) : ℤ)^(N+1)

lemma Parameters.Xpos (N : ℕ) (i : Fin a) : 0 < A.X N i := by
  obtain ⟨k,hk⟩ := A.Xpow N i
  rw [hk]
  positivity

lemma Parameters.Wdiv (N : ℕ) : primorial (N+1) ∣ A.M N :=
  (dvd_pow_self _ (by omega : N+1 ≠ 0)).trans (A.Mdiv N)

lemma Parameters.Wle (N : ℕ) : primorial (N+1) ≤ A.M N :=
  Nat.le_of_dvd (A.Mpos N) (A.Wdiv N)

lemma Parameters.Lpos (N : ℕ) : 0 < A.L N :=
  (SourceHierarchyRates.source_modulus_size _ _ _ (A.Mpos N) (primorial_pos _) (A.Mdiv N)).1

lemma Parameters.Lbound (N : ℕ) : (A.L N : ℝ) ≤ (A.M N : ℝ)^2 :=
  by simpa [Parameters.L] using
    (SourceHierarchyRates.source_modulus_size _ _ _ (A.Mpos N) (primorial_pos _) (A.Mdiv N)).2

lemma Parameters.Lsmooth (N : ℕ) : RoughScales.Smooth (N+1) (A.L N) := by
  apply RoughRationalBlock.smooth_mul (A.Msmooth N)
  intro p hp hd
  have hp' : Prime (p:ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  exact IntegerAlignment.primorial_smooth (N+1) p hp (hp'.dvd_of_dvd_pow hd)

lemma Parameters.Xtendsto (i : Fin a) : Tendsto (fun N => A.X N i) atTop atTop :=
  SourceHierarchyRates.raw_interval_tendsto (fun N => A.Hpos N i)
    (fun N => A.Xpos N i) (A.Xdom i)

lemma Parameters.XoverL (i : Fin a) :
    Tendsto (fun N => (A.X N i : ℝ)/(A.L N : ℝ)) atTop atTop :=
  SourceHierarchyRates.raw_over_modulus_tendsto (fun N => A.Hpos N i)
    (fun N => A.Xpos N i) A.L A.Lpos A.Lbound (A.Hdom i) (A.Xdom i)

lemma Parameters.eventual_X (i : Fin a) :
    ∀ᶠ N in atTop, 4*primorial (N+1) ≤ A.X N i :=
  SourceHierarchyRates.eventually_interval_four_modulus A.Mpos (fun N => A.Hpos N i)
    (fun N => A.Xpos N i) A.Wle (A.Hdom i) (A.Xdom i)

lemma Parameters.eventual_J (i : Fin a) :
    ∀ᶠ N in atTop, 0 < MicrocellScale.length (A.M N) (A.H N i) :=
  (MicrocellEarlierScale.length_tendsto (Eventually.of_forall A.Mpos)
    (A.Hdom i)).eventually_gt_atTop 0

 
lemma Parameters.exists_tail : ∃ K : ℕ, ∀ N i,
    4*primorial (N+K+1) ≤ A.X (N+K) i ∧
    0 < MicrocellScale.length (A.M (N+K)) (A.H (N+K) i) := by
  have he : ∀ᶠ N in atTop, ∀ i,
      4*primorial (N+1) ≤ A.X N i ∧
      0 < MicrocellScale.length (A.M N) (A.H N i) := by
    apply eventually_all.mpr
    intro i
    exact (A.eventual_X i).and (A.eventual_J i)
  obtain ⟨K,hK⟩ := eventually_atTop.mp he
  exact ⟨K, fun N i => hK (N+K) (by omega) i⟩

 

structure TailBound (K : ℕ) : Prop where
  hX : ∀ N i, 4*primorial (N+K+1) ≤ A.X (N+K) i
  hJ : ∀ N i, 0 < MicrocellScale.length (A.M (N+K)) (A.H (N+K) i)

lemma Parameters.exists_tailBound : ∃ K, TailBound A K := by
  obtain ⟨K,hK⟩ := A.exists_tail
  exact ⟨K,⟨fun N i => (hK N i).1, fun N i => (hK N i).2⟩⟩

variable (K : ℕ) (hK : TailBound A K)

 
def normalized : CommonScales a where
  w N := N+K+1
  M N := A.M (N+K)
  X N := A.X (N+K)
  ht N := A.ht (N+K)
  L N := A.L (N+K)
  hw := (tendsto_add_atTop_nat 1).comp (tendsto_add_atTop_nat K)
  hX := hK.hX
  hXt j := (A.Xtendsto j).comp (tendsto_add_atTop_nat K)
  hWM N := by exact_mod_cast A.Wdiv (N+K)
  hM N := A.Mpos (N+K)
  hMs N := A.Msmooth (N+K)
  hL N := A.Lpos (N+K)
  hLs N := A.Lsmooth (N+K)
  hWL N := dvd_mul_of_dvd_left (by exact_mod_cast A.Wdiv (N+K)) _
  hML N := dvd_mul_right _ _
  hLexact N := rfl
  hpowWM N := A.Mdiv (N+K)
  hht N := A.htpos (N+K)
  hXL j := (A.XoverL j).comp (tendsto_add_atTop_nat K)

 
lemma added_is_block {i : Fin a} {T S : Finset (Fin a)} (hT : T.Nonempty)
    (h : Added i T S) : ∃ B : Block a, B.set = S := by
  obtain ⟨P,j,hP,hPT,hTj,hji,rfl⟩ := h
  obtain ⟨t,ht⟩ := hT
  exact ⟨⟨j,⟨P,hP, fun p hp => (hPT p hp t ht).trans (hTj t ht)⟩⟩,rfl⟩

 

def pivotScales (i : Fin a) : PivotScales (normalized A K hK) (pivot i) where
  H N := A.H (N+K) i
  J N := MicrocellScale.length (A.M (N+K)) (A.H (N+K) i)
  R N := radius (A.M (N+K)) (A.H (N+K) i)
  hJ N := hK.hJ N i
  hRJ N := (Nat.mul_div_cancel' (MicrocellScale.modulus_dvd _ _)).symm
  hH N := A.Hpos (N+K) i
  hRrad N := rfl
  hdom C hC := (A.Hdom i C hC).comp (tendsto_add_atTop_nat K)
  hxdom C hC := (A.Xdom i C hC).comp (tendsto_add_atTop_nat K)
  hheight N e := by
    obtain ⟨B,hB⟩ := added_is_block
      (tailEnum i (pairEnum i e).val.1).property.1 (pairEnum i e).property
    have hb := A.block_bound (N+K) B
    change height (A.ht (N+K)) (pairEnum i e).val.2 ≤ (A.M (N+K) : ℤ)
    simpa only [hB] using hb
  hdisj := pivot_disjoint i
  hratio N e := by
    let B : Block a := ⟨i,tailEnum i (pairEnum i e).val.1⟩
    exact A.ratio (N+K) B _ (pairEnum i e).property

end SourceAdmissible

 

 

 

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction NNReal
namespace SourceAdmissible
open SourceBlocks SourceChartedAlignment MicrocellScale AdmissibleMicrocellBoundary
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.AlignmentScales
open SourceIntegerArrays.GlobalJoint.SourceFrozenFamily
open SourceIntegerArrays.GlobalJoint.SourceExposureSlots ProductExposureLaw
open SourcePivotPaths
variable {a s r : ℕ}

 

def shiftModel {D : Pivot a} (F : ChartedModels s r D) (K : ℕ) : ChartedModels s r D :=
  { F with
    g := fun t N => F.g t (N+K)
    x := fun t N => F.x t (N+K)
    obs := fun t N => F.obs t (N+K)
    lip := fun t N => F.lip t (N+K)
    bound := fun t N => F.bound t (N+K) }

 
def Parameters.models (A : Parameters a) {D : Pivot a} (F : ChartedModels s r D)
    (N : ℕ) : ScalarModels D r :=
  scalarModels D r F.G F.Γ A.M (fun N => A.H N D.index) F.g F.x F.obs N

lemma shift_models (A : Parameters a) (K : ℕ) (hK : TailBound A K)
    (i : Fin a) (F : ChartedModels s r (pivot i)) (N : ℕ) :
    (shiftModel F K).scalar (normalized A K hK) (pivotScales A K hK i) N =
      A.models F (N+K) := rfl

 

def Parameters.law (A : Parameters a) (N : ℕ)
    (hX : ∀ i, 4*primorial (N+1) ≤ A.X N i) : Measure (Fin a → ℕ) :=
  outsideLaw (A.X N) (primorial (N+1)) (primorial_pos _) hX

 

theorem admissible_charted_alignment (s r : ℕ) (hs : 1 ≤ s) :
    0 < delta s r hs (pivots a) ∧
    (∀ b ∈ multipliers (sourcePlan s r hs (pivots a)), ∀ j, 0 < b j) ∧
    ∀ (A : Parameters a) (Ss : ℕ → (D : Pivot a) → ScalarModels D r),
      (∀ D ∈ pivots a, ∃ F : ChartedModels s r D, ∀ N, Ss N D = A.models F N) →
      ∀ τ : ℝ, 0 < τ → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N in atTop, ∃ hX : ∀ i, 4*primorial (N+1) ≤ A.X N i,
        delta s r hs (pivots a) ≤ (A.law N hX).real
          {u | ∃ b ∈ multipliers (sourcePlan s r hs (pivots a)),
            ∀ D ∈ pivots a, comparison D r (Ss N D) (A.ht N) b u (u D.index) τ} + ε := by
  refine ⟨delta_pos s r hs _, source_multipliers_pos s r hs _, ?_⟩
  intro A Ss hSs τ hτ ε hε
  obtain ⟨K,hK⟩ := A.exists_tailBound
  have hR : ∀ D ∈ pivots a,
      Realizes s r (normalized A K hK) D (fun N => Ss (N+K) D) := by
    intro D hD
    apply Classical.choice
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hD
    obtain ⟨F,hF⟩ := hSs (pivot i) (mem_pivots i)
    exact ⟨⟨pivotScales A K hK i, shiftModel F K,
      fun N => (hF (N+K)).trans (shift_models A K hK i F N).symm⟩⟩
  have he := (charted_alignment s r hs (pivots a) pivots_ordered).2.2
    (normalized A K hK) (fun N => Ss (N+K)) hR τ hτ ε hε
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp he
  apply eventually_atTop.mpr
  refine ⟨N₀+K,?_⟩
  intro N hN
  have hNK : N-K+K=N := Nat.sub_add_cancel (by omega)
  have hx : ∀ i, 4*primorial (N+1) ≤ A.X N i := by
    simpa only [hNK] using hK.hX (N-K)
  refine ⟨hx,?_⟩
  have h := hN₀ (N-K) (by omega)
  change delta s r hs (pivots a) ≤
    (A.law (N-K+K) (hK.hX (N-K))).real
      {u | ∃ b ∈ multipliers (sourcePlan s r hs (pivots a)),
        ∀ D ∈ pivots a, comparison D r (Ss (N-K+K) D) (A.ht (N-K+K)) b u (u D.index) τ} + ε at h
  simpa only [hNK] using h

end SourceAdmissible

 

 

 

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
