import OAI.Analysis.SeparableQuotients.BranchReduction

namespace OAI

noncomputable section

namespace SeparableQuotient.Singular
open Set
lemma exists_unit {𝕜 Y : Type*} [RCLike 𝕜] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (hI : ¬ FiniteDimensional 𝕜 Y) : ∃ x : Y, ‖x‖ = 1 := by
  let : Nontrivial Y := not_subsingleton_iff_nontrivial.mp (by
    intro hs
    let : Subsingleton Y := hs
    exact hI inferInstance)
  obtain ⟨x,hx⟩ := exists_ne (0 : Y)
  refine ⟨(↑‖x‖ : 𝕜)⁻¹ • x,?_⟩
  simp only [norm_smul,norm_inv,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg x),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
end SeparableQuotient.Singular

namespace SeparableQuotient.ActualSpace
open Norming Singular Set
open scoped Classical Topology

lemma familyP_initial (γ : Cut) (f : Family) (x : E) :
    initialP γ (familyP γ f x) = familyP γ f x := by
  cases f with
  | mixed => exact initialP_initialP le_rfl x
  | pure k =>
    change initialP γ (colorP k (initialP γ x)) = colorP k (initialP γ x)
    rw [initialP_colorP,initialP_initialP le_rfl]

lemma familyP_color (γ : Cut) (k : ℕ) (x : E) :
    colorP k (familyP γ (.pure k) x) = familyP γ (.pure k) x :=
  colorP_colorP k _

variable {F : Submodule ℝ E} (R : BranchReduction F)

lemma BranchReduction.initial_fixed (x : R.H) : initialP R.cut (x : E) = x := by
  simpa only [R.lift] using familyP_initial R.cut R.family (R.U x)

lemma BranchReduction.color_fixed (k : ℕ) (hk : R.family = .pure k) (x : R.H) :
    colorP k (x : E) = x := by
  have hl : familyP R.cut (.pure k) (R.U x) = x := by simpa only [hk] using R.lift x
  simpa only [hl] using familyP_color R.cut k (R.U x)

lemma BranchReduction.coordinate_zero_of_cut (x : R.H) (a : Γ) (ha : ¬ (a : Cut) < R.cut) :
    coordinate a (x : E) = 0 := by
  have h := congrArg (coordinate a) (R.initial_fixed x)
  simpa only [coordinate_initialP,ha,ite_false,eq_comm] using h

lemma BranchReduction.coordinate_zero_of_color (k : ℕ) (hk : R.family = .pure k)
    (x : R.H) (a : Γ) (ha : Colors.color a ≠ k) : coordinate a (x : E) = 0 := by
  have h := congrArg (coordinate a) (R.color_fixed k hk x)
  simpa only [coordinate_colorP,ha,ite_false,eq_comm] using h

lemma BranchReduction.cut_nonempty : ∃ a : Γ, (a : Cut) < R.cut := by
  obtain ⟨x,hx⟩ := Singular.exists_unit R.infinite
  have hn : (x : E) ≠ 0 := by
    intro hh
    have hh0 : ‖x‖ = 0 := by
      change ‖(x : E)‖ = 0
      rw [hh,norm_zero]
    linarith
  have he : ∃ a : Γ, coordinate a (x : E) ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hn
    exact norming.coordinate_ext (fun a => (hh a).trans (map_zero _).symm)
  obtain ⟨a,ha⟩ := he
  exact ⟨a,by by_contra hh; exact ha (R.coordinate_zero_of_cut x a hh)⟩

lemma BranchReduction.beyond_finite (s : Finset Γ) (hs : ∀ a ∈ s, (a : Cut) < R.cut) :
    ∃ β : Γ, (β : Cut) < R.cut ∧ ∀ a ∈ s, a < β := by
  by_cases hn : s.Nonempty
  · obtain ⟨β,hβ,hβc⟩ := R.noLast (s.max' hn) (hs _ (s.max'_mem hn))
    exact ⟨β,hβc,fun a ha => (s.le_max' a ha).trans_lt hβ⟩
  · obtain ⟨a,ha⟩ := R.cut_nonempty
    exact ⟨a,ha,by simp only [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.notMem_empty,false_implies,implies_true]⟩

def blockCrop (γ : Cut) (f : Family) (β : Γ) (l : ℕ) : Crop where
  ordinal := initialSet γ ∩ Set.Ici β
  ordinal_convex := (initialSet_connected γ).inter Set.ordConnected_Ici
  colors := match f with | .pure k => {k} | .mixed => Set.Ici l
  colors_convex := by cases f <;> first | exact Set.ordConnected_singleton | exact Set.ordConnected_Ici

lemma blockCrop_mem (γ : Cut) (f : Family) (β a : Γ) (l : ℕ) :
    a ∈ (blockCrop γ f β l).set .mixed ↔ (a : Cut) < γ ∧ β ≤ a ∧
      (match f with | .pure k => Colors.color a = k | .mixed => l ≤ Colors.color a) := by
  cases f <;> simp only [blockCrop,Crop.set,Set.mem_inter_iff,initialSet,Set.mem_ofPred_eq,
    Set.mem_Ici,Set.mem_preimage,Set.mem_singleton_iff,and_assoc]

lemma BranchReduction.crop_difference_pure (k : ℕ) (hk : R.family = .pure k)
    (β : Γ) (l : ℕ) (x : R.H) :
    (x : E)-projection (blockCrop R.cut R.family β l) x = initialP (β : Cut) x := by
  apply norming.coordinate_ext
  intro a
  by_cases hg : (a : Cut) < R.cut
  · by_cases hb : β ≤ a
    · by_cases hc : Colors.color a = k
      · simp only [map_sub,coordinate_projection,blockCrop_mem,hg,hb,hk,hc,and_self,
          ite_true,sub_self,coordinate_initialP,WithTop.coe_lt_coe,not_lt_of_ge hb,ite_false]
      · have hz := R.coordinate_zero_of_color k hk x a hc
        simp only [map_sub,coordinate_projection,blockCrop_mem,hg,hb,hk,hc,and_false,
          sub_zero,coordinate_initialP,hz,ite_self]
    · have hab : a < β := lt_of_not_ge hb
      simp only [map_sub,coordinate_projection,blockCrop_mem,hb,and_false,false_and,
        ite_false,sub_zero,coordinate_initialP,WithTop.coe_lt_coe,hab,ite_true]
  · have hz := R.coordinate_zero_of_cut x a hg
    simp only [map_sub,coordinate_projection,blockCrop_mem,hg,false_and,sub_zero,
      coordinate_initialP,hz,ite_self]

lemma BranchReduction.crop_difference_mixed (hm : R.family = .mixed)
    (β : Γ) (l : ℕ) (x : R.H) :
    (x : E)-projection (blockCrop R.cut R.family β l) x = initialP (β : Cut) x +
      intervalProjection (Set.Ici β) Set.ordConnected_Ici (projection (Crop.colorsBelow l) x) := by
  apply norming.coordinate_ext
  intro a
  have hz : ¬ (a : Cut) < R.cut → coordinate a (x : E) = 0 := R.coordinate_zero_of_cut x a
  simp only [map_sub,map_add,coordinate_projection,blockCrop_mem,hm,coordinate_initialP,
    intervalProjection,Crop.ordinalSet_set,Crop.colorsBelow_set,Set.mem_ofPred_eq,Set.mem_Ici,
    WithTop.coe_lt_coe]
  by_cases hg : (a : Cut) < R.cut <;> by_cases hb : β ≤ a <;> by_cases hc : l ≤ Colors.color a
  all_goals simp only [hg,hb,hc,lt_iff_not_ge,not_true_eq_false,not_false_eq_true,
    and_self,and_true,and_false,ite_true,ite_false]
  all_goals try abel_nf
  all_goals exact hz hg

lemma exists_crop_approx (A : Crop) (x : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : Γ →₀ ℝ, (∀ a ∈ v.support, a ∈ A.set .mixed) ∧
      ‖projection A x-norming.includeFinite v‖ < ε := by
  obtain ⟨w,hw⟩ := norming.denseRange_includeFinite.exists_dist_lt x hε
  refine ⟨w.filter (· ∈ A.set .mixed),?_,?_⟩
  · intro a ha
    exact (Finsupp.mem_support_iff.mp ha |> fun h => of_not_not (fun hn => h (by simp [hn])))
  · have he : norming.includeFinite (w.filter (· ∈ A.set .mixed)) = projection A (norming.includeFinite w) :=
      (norming.projection_includeFinite (A.set .mixed) (cropStable A) w).symm
    rw [he,← map_sub]
    exact (norm_projection_le A _).trans_lt (by simpa only [dist_eq_norm] using hw)

lemma BranchReduction.exists_tail_small (β : Γ) (hβ : (β : Cut) < R.cut)
    (l : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ x : R.H, ‖x‖ = 1 ∧ ‖initialP (β : Cut) (x : E)‖ ≤ δ ∧
      (R.family = .mixed → ∑ k ∈ Finset.range l, ‖colorP k (x : E)‖ ≤ (l : ℝ)*δ) := by
  let D : Finset (R.H →L[ℝ] E) := insert ((initialP (β : Cut)).comp R.H.subtypeL)
    (if R.family = .mixed then (Finset.range l).image (fun k => (colorP k).comp R.H.subtypeL) else ∅)
  have hD : ∀ T ∈ D, StrictlySingular T := by
    intro T hT
    rcases Finset.mem_insert.mp hT with rfl | hT
    · exact R.earlier _ hβ
    · by_cases hm : R.family = .mixed
      · rw [ite_eq_left hm] at hT
        obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hT
        exact R.mixed hm k
      · simp only [ite_eq_right hm,Finset.notMem_empty] at hT
  obtain ⟨N,_,hNc,hNi,hN⟩ := exists_small_restriction_finite D hD ⊤ isClosed_univ
    (Singular.top_infinite R.infinite) δ hδ
  obtain ⟨u,hu⟩ := Singular.exists_unit hNi
  let x : R.H := u
  have hxn : ‖x‖ = 1 := hu
  have hi : ‖initialP (β : Cut) (x : E)‖ ≤ δ := by
    have h := hN _ (Finset.mem_insert_self _ _) x u.property
    change ‖initialP (β : Cut) (x : E)‖ ≤ δ*‖x‖ at h
    rwa [hxn,mul_one] at h
  have hcolor (hm : R.family = .mixed) : ∑ k ∈ Finset.range l, ‖colorP k (x : E)‖ ≤ (l : ℝ)*δ := by
    calc
      _ ≤ ∑ _k ∈ Finset.range l, δ := by
        apply Finset.sum_le_sum
        intro k hk
        have hmem : (colorP k).comp R.H.subtypeL ∈ D := Finset.mem_insert_of_mem (by
          rw [ite_eq_left hm]; exact Finset.mem_image.mpr ⟨k,hk,rfl⟩)
        have h := hN _ hmem x u.property
        change ‖colorP k (x : E)‖ ≤ δ*‖x‖ at h
        rwa [hxn,mul_one] at h
      _ = _ := by simp
  exact ⟨x,hxn,hi,hcolor⟩

lemma BranchReduction.crop_error_bound (β : Γ) (l : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (x : R.H) (hi : ‖initialP (β : Cut) (x : E)‖ ≤ δ)
    (hc : R.family = .mixed → ∑ k ∈ Finset.range l, ‖colorP k (x : E)‖ ≤ (l : ℝ)*δ) :
    ‖(x : E)-projection (blockCrop R.cut R.family β l) x‖ ≤ (1+(l : ℝ))*δ := by
  cases hf : R.family with
  | pure k =>
    rw [← hf,R.crop_difference_pure k hf]
    exact hi.trans (by nlinarith [(Nat.cast_nonneg l : (0:ℝ) ≤ l)])
  | mixed =>
    rw [← hf,R.crop_difference_mixed hf]
    calc
      _ ≤ ‖initialP (β : Cut) (x : E)‖ +
          ‖intervalProjection (Set.Ici β) Set.ordConnected_Ici (projection (Crop.colorsBelow l) x)‖ := norm_add_le _ _
      _ ≤ δ + ‖projection (Crop.colorsBelow l) x‖ := add_le_add hi (norm_projection_le _ _)
      _ ≤ δ + (l : ℝ)*δ := by
        apply add_le_add_right
        rw [projection_colorsBelow_sum]
        exact (norm_sum_le _ _).trans (hc hf)
      _ = _ := by ring

/-- A unit vector in the reduced subspace can be approximated in any prescribed ordinal and color tail. -/
lemma BranchReduction.exists_next_block (β : Γ) (hβ : (β : Cut) < R.cut)
    (l : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ (x : R.H) (v : Γ →₀ ℝ), ‖x‖ = 1 ∧ v ≠ 0 ∧
      (∀ a ∈ v.support, a ∈ (blockCrop R.cut R.family β l).set .mixed) ∧
      ‖(x : E)-norming.includeFinite v‖ < ε := by
  let δ := ε/(6*((l : ℝ)+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨x,hxn,hi,hc⟩ := R.exists_tail_small β hβ l δ hδ
  have hδb : (1+(l : ℝ))*δ ≤ ε/3 := by
    dsimp only [δ]
    field_simp
    nlinarith [hε]
  have herr := (R.crop_error_bound β l δ hδ.le x hi hc).trans hδb
  obtain ⟨v,hv,herr'⟩ := exists_crop_approx (blockCrop R.cut R.family β l) x (ε/3) (by positivity)
  have he : ‖(x : E)-norming.includeFinite v‖ < ε := by
    have ht := norm_sub_le_norm_sub_add_norm_sub ((x : E)) (projection (blockCrop R.cut R.family β l) x) (norming.includeFinite v)
    linarith
  refine ⟨x,v,hxn,?_,hv,he⟩
  intro hv0
  have hh : ‖(x : E)-norming.includeFinite v‖ = 1 := by rw [hv0,map_zero,sub_zero]; exact hxn
  rw [hh] at he
  linarith

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming Singular Set
open scoped Classical
variable {F : Submodule ℝ E} (R : BranchReduction F)
namespace BlockApprox

def error (n : ℕ) : ℝ := (1/64000)*(1/2)^n
lemma error_pos (n : ℕ) : 0 < error n := by unfold error; positivity
lemma error_le (n : ℕ) : error n ≤ 1/2 := by
  have h : (1/2 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold error
  nlinarith
lemma error_sum (s : Finset ℕ) : ∑ n ∈ s, error n ≤ 1/32000 := by
  have h : (∑ n ∈ s, (1/2 : ℝ)^n) ≤ 2 := by
    simpa only [tsum_geometric_two] using summable_geometric_two.sum_le_tsum s (fun n _ => by positivity)
  simp only [error,← Finset.mul_sum]
  linarith

structure State where
  ordinal : Γ
  below : (ordinal : Cut) < R.cut
  color : ℕ

structure Step (s : State R) (n : ℕ) where
  x : R.H
  vector : Γ →₀ ℝ
  unit : ‖x‖ = 1
  nonzero : vector ≠ 0
  support : ∀ a ∈ vector.support, a ∈ (blockCrop R.cut R.family s.ordinal s.color).set .mixed
  approx : ‖(x : E)-norming.includeFinite vector‖ < error n
  next : Γ
  next_below : (next : Cut) < R.cut
  before_next : ∀ a ∈ vector.support, a < next

lemma exists_step (s : State R) (n : ℕ) : Nonempty (Step R s n) := by
  obtain ⟨x,v,hx,hv,hvs,he⟩ := R.exists_next_block s.ordinal s.below s.color (error n) (error_pos n) (error_le n)
  have hs : ∀ a ∈ v.support, (a : Cut) < R.cut := fun a ha => ((blockCrop_mem _ _ _ _ _).mp (hvs a ha)).1
  obtain ⟨β,hβ,hβv⟩ := R.beyond_finite v.support hs
  exact ⟨⟨x,v,hx,hv,hvs,he,β,hβ,hβv⟩⟩

def step (s : State R) (n : ℕ) : Step R s n := (exists_step R s n).some

def nextState (s : State R) (n : ℕ) : State R where
  ordinal := (step R s n).next
  below := (step R s n).next_below
  color := max s.color ((step R s n).vector.support.sup Colors.color + 1)

def state : ℕ → State R
  | 0 => ⟨R.cut_nonempty.choose,R.cut_nonempty.choose_spec,0⟩
  | n+1 => nextState R (state n) n

def node (n : ℕ) := step R (state R n) n

lemma state_ordinal_strict : StrictMono (fun n => (state R n).ordinal) := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨a,ha⟩ := Finsupp.support_nonempty_iff.mpr (node R n).nonzero
  have hs := ((blockCrop_mem _ _ _ _ _).mp ((node R n).support a ha)).2.1
  exact hs.trans_lt ((node R n).before_next a ha)

lemma state_color_mono : Monotone (fun n => (state R n).color) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

lemma support_after {n : ℕ} {a : Γ} (ha : a ∈ (node R n).vector.support) :
    (state R n).ordinal ≤ a ∧ (a : Cut) < R.cut ∧
      (R.family = .mixed → (state R n).color ≤ Colors.color a) := by
  have h := (blockCrop_mem _ _ _ _ _).mp ((node R n).support a ha)
  refine ⟨h.2.1,h.1,?_⟩
  intro hf
  simpa only [hf] using h.2.2

lemma support_color_next {n : ℕ} {a : Γ} (ha : a ∈ (node R n).vector.support) :
    Colors.color a < (state R (n+1)).color := by
  have h := Finset.le_sup (f := Colors.color) ha
  exact (Nat.lt_succ_of_le h).trans_le (le_max_right _ _)

/-- A block sequence approximating unit vectors in the reduced closed subspace, in the selected pure or mixed family. -/
def blocks : BlockSequence R.family where
  vector n := (node R n).vector
  nonzero n := (node R n).nonzero
  successive i j hij a ha b hb := by
    have hβ : a < (state R (i+1)).ordinal := (node R i).before_next a ha
    have hj := support_after R hb
    refine ⟨hβ.trans_le (((state_ordinal_strict R).monotone (Nat.succ_le_iff.mpr hij)).trans hj.1),?_⟩
    intro hm
    exact (support_color_next R ha).trans_le
      ((state_color_mono R (Nat.succ_le_iff.mpr hij)).trans (hj.2.2 hm))
  pure_color k hk n a ha := by
    have h := ((blockCrop_mem _ _ _ _ _).mp ((node R n).support a ha)).2.2
    simpa only [hk] using h

lemma blocks_norm (n : ℕ) : (1/2:ℝ) ≤ ‖(blocks R).embed n‖ := by
  have he := (node R n).approx
  have hu := (node R n).unit
  have h := norm_sub_norm_le ((node R n).x : E) ((blocks R).embed n)
  change ‖(node R n).x‖ - ‖(blocks R).embed n‖ ≤ _ at h
  rw [hu] at h
  have hε := error_le n
  change ‖((node R n).x : E)-((blocks R).embed n)‖ < error n at he
  linarith

lemma blocks_below (n : ℕ) (a : Γ) (ha : a ∈ ((blocks R).vector n).support) :
    (a : Cut) < R.cut := (support_after R ha).2.1

end BlockApprox
end SeparableQuotient.ActualSpace

end

end OAI
