import OAI.MathematicalPhysics.NavierStokes.Material.Curls

namespace OAI

namespace Alternating
open scoped Topology BigOperators
open MeasureTheory Filter

noncomputable section

theorem spatialD_iterate_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Space → E} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 3) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) ((spatialD i)^[n] g) := by
  induction n with
  | zero => exact hg
  | succ n ih => simpa only [Function.iterate_succ_apply'] using spatialD_smooth ih i

theorem spatialPartial_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Space → E} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (α : MultiIndex) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialPartial α g) :=
  spatialD_iterate_smooth (spatialD_iterate_smooth (spatialD_iterate_smooth hg 0 (α 0)) 1 (α 1)) 2 (α 2)

theorem spatialD_finiteCombination {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    {W : ι → Space → Space} (hW : ∀ n ∈ s, ContDiff ℝ (⊤ : ℕ∞) (W n)) (i : Fin 3) :
    spatialD i (fun x => ∑ n ∈ s, c n • W n x) = fun x => ∑ n ∈ s, c n • spatialD i (W n) x := by
  funext x
  have hd : ∀ n ∈ s, Differentiable ℝ (fun y => c n • W n y) := by
    intro n hn
    exact ((hW n hn).differentiable (by simp)).fun_const_smul (c n)
  simp only [spatialD, fderiv_fun_sum (fun n hn => hd n hn x), sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  rw [fderiv_fun_const_smul ((hW n hn).differentiable (by simp) x), smul_apply]

theorem spatialD_iterate_finiteCombination {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    {W : ι → Space → Space} (hW : ∀ n ∈ s, ContDiff ℝ (⊤ : ℕ∞) (W n)) (i : Fin 3) (r : ℕ) :
    (spatialD i)^[r] (fun x => ∑ n ∈ s, c n • W n x) =
      fun x => ∑ n ∈ s, c n • (spatialD i)^[r] (W n) x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih,
      spatialD_finiteCombination s c (fun n hn => spatialD_iterate_smooth (hW n hn) i r) i]
    simp only [Function.iterate_succ_apply']

theorem spatialPartial_finiteCombination {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    {W : ι → Space → Space} (hW : ∀ n ∈ s, ContDiff ℝ (⊤ : ℕ∞) (W n)) (α : MultiIndex) :
    spatialPartial α (fun x => ∑ n ∈ s, c n • W n x) =
      fun x => ∑ n ∈ s, c n • spatialPartial α (W n) x := by
  unfold spatialPartial
  rw [spatialD_iterate_finiteCombination s c hW 0 (α 0),
    spatialD_iterate_finiteCombination s c (fun n hn => spatialD_iterate_smooth (hW n hn) 0 (α 0)) 1 (α 1),
    spatialD_iterate_finiteCombination s c
      (fun n hn => spatialD_iterate_smooth (spatialD_iterate_smooth (hW n hn) 0 (α 0)) 1 (α 1)) 2 (α 2)]

theorem tsupport_spatialD_iterate_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Space → E) (i : Fin 3) (n : ℕ) : tsupport ((spatialD i)^[n] g) ⊆ tsupport g := by
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (tsupport_fderiv_apply_subset ℝ (basisVector i)).trans ih

theorem spatialPartial_hasCompactSupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Space → E} (hg : HasCompactSupport g) (α : MultiIndex) : HasCompactSupport (spatialPartial α g) := by
  apply hg.of_isClosed_subset (isClosed_tsupport _)
  exact (tsupport_spatialD_iterate_subset _ 2 (α 2)).trans
    ((tsupport_spatialD_iterate_subset _ 1 (α 1)).trans (tsupport_spatialD_iterate_subset _ 0 (α 0)))

namespace SlotL2

variable (W : ℕ → Space → Space) (hW : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (W n))
    (hc : ∀ n, HasCompactSupport (W n))

include hW hc in

theorem mem (α : MultiIndex) (n : ℕ) : MemLp (spatialPartial α (W n)) 2 volume :=
  (spatialPartial_smooth (hW n) α).continuous.memLp_of_hasCompactSupport
    (spatialPartial_hasCompactSupport (hc n) α)

def component (α : MultiIndex) (n : ℕ) : SpatialL2 Space := (mem W hW hc α n).toLp _

def finiteLift (a : ℝ → ℝ) (α : MultiIndex) (N : ℕ) (t : ℝ) : SpatialL2 Space :=
  ∑ n ∈ Finset.range N, a (t - n) • component W hW hc α n

theorem finiteLift_continuous {a : ℝ → ℝ} (ha : Continuous a) (α : MultiIndex) (N : ℕ) :
    Continuous (finiteLift W hW hc a α N) := by
  apply continuous_finsetSum
  intro n hn
  exact (ha.comp (continuous_id.sub continuous_const)).smul continuous_const

theorem finiteLift_ae (a : ℝ → ℝ) (α : MultiIndex) (N : ℕ) (t : ℝ) :
    (fun x : Space => (finiteLift W hW hc a α N t) x) =ᵐ[volume]
      fun x => ∑ n ∈ Finset.range N, a (t - n) • spatialPartial α (W n) x := by
  unfold finiteLift
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    exact (Lp.coeFn_add _ _).trans
      (ih.add ((Lp.coeFn_smul _ _).trans ((mem W hW hc α N).coeFn_toLp.const_smul _)))

theorem finiteLift_hasDerivAt {a : ℝ → ℝ} (ha : Differentiable ℝ a)
    (α : MultiIndex) (N : ℕ) (t : ℝ) :
    HasDerivAt (finiteLift W hW hc a α N)
      (finiteLift W hW hc (deriv a) α N t) t := by
  apply HasDerivAt.fun_sum
  intro n hn
  have hh := (ha (t - n)).hasDerivAt.comp t ((hasDerivAt_id t).sub_const (n : ℝ))
  simpa using hh.smul_const (component W hW hc α n)

end SlotL2

end
end Alternating

end OAI
