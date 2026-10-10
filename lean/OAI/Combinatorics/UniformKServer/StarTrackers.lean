import Mathlib
import OAI.Combinatorics.UniformKServer.EpochSide
import OAI.Combinatorics.UniformKServer.AlphaFiniteInput
import OAI.Combinatorics.UniformKServer.SideFiniteInput

namespace OAI

                                   
section

/-! The recursive minimizers instantiated with the finite hidden-count law and
its literal held parameters, rather than an assumed allocator interface. -/
noncomputable section
namespace UniformKServer.StarTrackers
open Finset StarRanks StarSchedules
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def alphaParam (d : Data Ω ι k) (δ ct C : ℝ) (t : ℕ) (ω : Ω) : AlphaEmpty.Config ι :=
  EpochAlphaSchedule.schedule (fun s => held d s ω) (fun s => parentRefresh d δ s ω) k ct C t

theorem alphaParam_measurable (d : Data Ω ι k) (δ ct C : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : alphaParam d δ ct C t ω=alphaParam d δ ct C t v :=
  CausalSchedules.alpha_congr k ct C t (fun s hs => held_measurable d s (refining d hs h))
    (fun s hs => refresh_measurable d δ s (refining d (by omega) h))

theorem alphaParam_active (d : Data Ω ι k) (δ ct C : ℝ) (t : ℕ) (ω : Ω) :
    AlphaEmpty.active (alphaParam d δ ct C t ω)=EpochParameters.active (held d t ω) :=
  EpochAlphaSchedule.schedule_active (fun s i => held_nonneg d s ω i) _ _ _ _ _

def alphaData (d : Data Ω ι k) (δ : ℝ) {ct C : ℝ} (hc : 0 < ct) (hct : ct*50000 ≤ 1)
    (hC : 1000 < C*ct) : AlphaFiniteInput.Data Ω ι (Fin k) where
  weight := d.weight
  nonneg := fun ω => (d.positive ω).le
  filtration := d.filtration
  refines := d.refines
  hidden := fun t ω ir => ConditionalRank.indicator (d.count t ω ir.1) ir.2
  hidden_range := fun t ω ir => ConditionalRank.indicator_range _ _
  param := alphaParam d δ ct C
  param_valid := fun t ω => EpochAlphaSchedule.schedule_valid
    (fun s i => held_nonneg d s ω i) _ k hc hct hC
    (fun s => held_sum d s ω) (fun s i => held_min d s ω i) t
  param_measurable := fun t ω v h => alphaParam_measurable d δ ct C t h
  flag := flags d
  flag_measurable := fun t ω v h => flag_measurable d t h
  supported := by
    intro t ω i hi j
    rw [alphaParam_active] at hi
    apply zero_flags d t ω i _ j
    exact le_antisymm (le_of_not_gt (by simpa only [EpochParameters.mem_active] using hi))
      (held_nonneg d t ω i)

theorem alpha_post (d : Data Ω ι k) (δ : ℝ) {ct C : ℝ} (hc : 0 < ct) (hct : ct*50000 ≤ 1)
    (hC : 1000 < C*ct) (t : ℕ) (ω : Ω) (i : ι) (j : Fin k) :
    AlphaFiniteInput.post (alphaData d δ hc hct hC) t ω i j=(input d i j).posterior t ω := rfl

theorem alpha_input (d : Data Ω ι k) (δ : ℝ) {ct C : ℝ} (hc : 0 < ct) (hct : ct*50000 ≤ 1)
    (hC : 1000 < C*ct) (t : ℕ) (ω : Ω) :
    AlphaFiniteInput.input (alphaData d δ hc hct hC) t ω=coreInput d t ω := rfl

def sideParam (d : Data Ω ι k) (δ cw : ℝ) (t : ℕ) (ω : Ω) : AdaptiveSide.Config ι :=
  EpochSide.config (held d t ω) (epoch d δ t ω) (EpochAlpha.ell k) cw (upper d δ t ω)

theorem sideParam_measurable (d : Data Ω ι k) (δ cw : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : sideParam d δ cw t ω=sideParam d δ cw t v := by
  unfold sideParam
  rw [held_measurable d t h,epoch_measurable d δ t h,upper_measurable d δ t h]

def sideFlags (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) (i : ι) (j : Fin k) : Bool :=
  if i ∈ EpochSide.active (held d t ω) (epoch d δ t ω) then flags d t ω i j else false

theorem sideFlags_measurable (d : Data Ω ι k) (δ : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : sideFlags d δ t ω=sideFlags d δ t v := by
  funext i j
  unfold sideFlags
  rw [held_measurable d t h,epoch_measurable d δ t h,flag_measurable d t h]

theorem side_core_le (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) (i : ι) :
    SyntheticCore.input (fun j => (input d i j).posterior t ω) (sideFlags d δ t ω i) ≤
      coreInput d t ω i := by
  unfold sideFlags coreInput
  by_cases hi : i ∈ EpochSide.active (held d t ω) (epoch d δ t ω)
  · simp only [hi,↓reduceIte,le_refl]
  · simp only [hi,↓reduceIte]
    rw [SyntheticCore.no_flags _ (fun _ => rfl)]
    exact SyntheticCore.input_nonneg (fun j => ((input d i j).posterior_range t ω).1) _

def sideData (d : Data Ω ι k) (hk : 1 ≤ k) {δ cw : ℝ} (hδ : 0 < δ)
    (hcw : 0 < cw) (hc : cw*50000 ≤ 1) : SideFiniteInput.Data Ω ι (Fin k) where
  weight := d.weight
  nonneg := fun ω => (d.positive ω).le
  filtration := d.filtration
  refines := d.refines
  hidden := fun t ω ir => ConditionalRank.indicator (d.count t ω ir.1) ir.2
  hidden_range := fun t ω ir => ConditionalRank.indicator_range _ _
  param := sideParam d δ cw
  param_valid := by
    intro t ω
    apply EpochSide.schedule_valid (fun s i => held_nonneg d s ω i) _ k hcw hc
      (fun s => upper d δ s ω) _ (fun s => held_sum d s ω) (fun s i => held_min d s ω i) t
    intro s
    have hb := upper_allowed d hδ hk s ω
    norm_num [RankFunctions.allowed] at hb
    constructor <;> linarith [hb.1,hb.2]
  param_measurable := fun t ω v h => sideParam_measurable d δ cw t h
  flag := sideFlags d δ
  flag_measurable := fun t ω v h => sideFlags_measurable d δ t h
  supported := by
    intro t ω i hi j
    exact ite_eq_right hi
  deficit := deficit d δ
  deficit_nonneg := deficit_nonneg d δ
  deficit_measurable := fun t ω v h => deficit_measurable d δ t h
  mass := fun t ω => ∑ i, coreInput d t ω i
  mass_measurable := by
    intro t ω v h
    rw [core_measurable d t h]
  mass_bound := fun t ω => sum_le_sum fun i _ => side_core_le d δ t ω i

theorem side_post (d : Data Ω ι k) (hk : 1 ≤ k) {δ cw : ℝ} (hδ : 0 < δ)
    (hcw : 0 < cw) (hc : cw*50000 ≤ 1) (t : ℕ) (ω : Ω) (i : ι) (j : Fin k) :
    SideFiniteInput.post (sideData d hk hδ hcw hc) t ω i j=(input d i j).posterior t ω := rfl

end UniformKServer.StarTrackers

end


end

end OAI
