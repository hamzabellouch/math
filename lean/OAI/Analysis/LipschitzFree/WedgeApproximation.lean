import OAI.Analysis.LipschitzFree.Functor
import OAI.Analysis.LipschitzFree.CompactApproximation
import OAI.Analysis.LipschitzFree.RetainedWedge

namespace OAI

/-!
# Compact-uniform approximation on wedges and contractive BAP inheritance
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped Classical BigOperators

section OperatorTools
variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem contraction_norm (T : E →L[ℝ] F) (hT : ‖T‖ ≤ 1) (u : E) : ‖T u‖ ≤ ‖u‖ := by
  exact (T.le_opNorm u).trans (by simpa using mul_le_mul_of_nonneg_right hT (norm_nonneg u))

theorem finiteRank_sandwich (I : G →L[ℝ] H) (T : F →L[ℝ] G) (P : E →L[ℝ] F)
    (hT : Module.Finite ℝ (LinearMap.range T.toLinearMap)) :
    Module.Finite ℝ (LinearMap.range ((I.comp T).comp P).toLinearMap) := by
  have hfg := ((Submodule.fg_iff_finiteDimensional _).mpr hT).map I.toLinearMap
  apply (Submodule.fg_iff_finiteDimensional _).mp
  apply hfg.of_le
  rintro v ⟨u,rfl⟩
  exact ⟨T (P u),⟨P u,rfl⟩,rfl⟩

theorem hasBAP_of_contractive_retract (I : E →L[ℝ] F) (P : F →L[ℝ] E)
    (hI : ‖I‖ ≤ 1) (hP : ‖P‖ ≤ 1) (hPI : P.comp I = ContinuousLinearMap.id ℝ E)
    (Λ : ℝ) (h : HasBAP F Λ) : HasBAP E Λ := by
  intro C hC ε hε
  obtain ⟨U,hU,hn,η,hη,he⟩ := h (I '' C) (hC.image I.continuous) ε hε
  let T := (P.comp U).comp I
  refine ⟨T,finiteRank_sandwich P U I hU,?_,η,hη,?_⟩
  · apply le_trans _ hn
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg U)
    intro u
    calc
      ‖T u‖ ≤ ‖U (I u)‖ := contraction_norm P hP _
      _ ≤ ‖U‖ * ‖I u‖ := U.le_opNorm _
      _ ≤ ‖U‖ * ‖u‖ := mul_le_mul_of_nonneg_left (contraction_norm I hI u) (norm_nonneg U)
  · intro u hu
    have hpu : P (I u) = u := congrArg (fun A : E →L[ℝ] E => A u) hPI
    calc
      ‖T u-u‖ = ‖P (U (I u)-I u)‖ := by dsimp [T]; rw [map_sub,hpu]
      _ ≤ ‖U (I u)-I u‖ := contraction_norm P hP _
      _ ≤ η := he _ ⟨u,hu,rfl⟩
end OperatorTools

namespace MetricWedge
universe u
variable (M : ℕ → Type u) [∀ n, MetricSpace (M n)] (o : ∀ n, M n)

def inclusionL (n : ℕ) : FreeSpace (o n) →L[ℝ] FreeSpace (base M o) :=
  freeMap (o n) (base M o) (inclusion M o n) (inclusion_base M o n)
    (inclusion_isometry M o n).lipschitzWith

def retractionL (n : ℕ) : FreeSpace (base M o) →L[ℝ] FreeSpace (o n) :=
  freeMap (base M o) (o n) (retraction M o n) (retraction_base M o n)
    (retraction_lipschitz M o n)

@[simp] theorem retractionL_inclusionL (n : ℕ) :
    (retractionL M o n).comp (inclusionL M o n) = ContinuousLinearMap.id ℝ (FreeSpace (o n)) := by
  apply freeMap_ext (o n)
  intro x
  simp [inclusionL,retractionL]

theorem inclusionL_bound (n : ℕ) : ‖inclusionL M o n‖ ≤ 1 := freeMap_bound ..
theorem retractionL_bound (n : ℕ) : ‖retractionL M o n‖ ≤ 1 := freeMap_bound ..

def retainL (F : Finset ℕ) : FreeSpace (base M o) →L[ℝ] FreeSpace (base M o) :=
  freeMap (base M o) (base M o) (retain M o F) (retain_base M o F) (retain_lipschitz M o F)

theorem retainL_bound (F : Finset ℕ) : ‖retainL M o F‖ ≤ 1 := freeMap_bound ..

theorem retain_span_fixed {u : FreeSpace (base M o)}
    (hu : u ∈ Submodule.span ℝ (Set.range (delta (base M o)))) :
    ∃ F : Finset ℕ, ∀ G : Finset ℕ, F ⊆ G → retainL M o G u = u := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x,rfl⟩ := hu
    rcases x with _ | ⟨n,x⟩
    · refine ⟨∅,fun G _ => ?_⟩
      change retainL M o G (delta (base M o) (base M o)) = delta (base M o) (base M o)
      rw [delta_base,map_zero]
    · refine ⟨{n},fun G hG => ?_⟩
      have hn : n ∈ G := hG (Finset.mem_singleton_self _)
      change delta (base M o) (retain M o G (some ⟨n,x⟩ : Point M o)) =
        delta (base M o) (some ⟨n,x⟩ : Point M o)
      congr 1
      simp [retain,hn]; rfl
  | zero => exact ⟨∅,fun _ _ => map_zero _⟩
  | add u v hu hv ihu ihv =>
    obtain ⟨F,hF⟩ := ihu
    obtain ⟨G,hG⟩ := ihv
    exact ⟨F∪G,fun K hK => by rw [map_add,hF K (Finset.subset_union_left.trans hK),hG K (Finset.subset_union_right.trans hK)]⟩
  | smul c u hu ih =>
    obtain ⟨F,hF⟩ := ih
    exact ⟨F,fun G hG => by rw [map_smul,hF G hG]⟩

theorem retain_error_bound (F : Finset ℕ) (u : FreeSpace (base M o)) :
    ‖retainL M o F u-u‖ ≤ 2*‖u‖ := by
  calc
    _ ≤ ‖retainL M o F u‖ + ‖u‖ := norm_sub_le _ _
    _ ≤ ‖u‖ + ‖u‖ := add_le_add (contraction_norm _ (retainL_bound M o F) u) le_rfl
    _ = _ := by ring

theorem retain_pointwise (u : FreeSpace (base M o)) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset ℕ, ∀ G : Finset ℕ, F ⊆ G → ‖retainL M o G u-u‖ < ε := by
  obtain ⟨v,hv,huv⟩ := Metric.mem_closure_iff.mp (evaluation_span_dense (base M o) u) (ε/2) (by positivity)
  obtain ⟨F,hF⟩ := retain_span_fixed M o hv
  refine ⟨F,fun G hG => ?_⟩
  calc
    ‖retainL M o G u-u‖ = ‖retainL M o G (u-v)-(u-v)‖ := by rw [map_sub,hF G hG]; congr 1; abel
    _ ≤ 2*‖u-v‖ := retain_error_bound M o G (u-v)
    _ < ε := by rw [dist_eq_norm] at huv; linarith

theorem retain_compact (C : Set (FreeSpace (base M o))) (hC : IsCompact C) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset ℕ, ∀ G : Finset ℕ, F ⊆ G → ∀ u ∈ C, ‖retainL M o G u-u‖ < ε := by
  obtain ⟨t,_,ht,hcover⟩ := hC.finite_cover_balls (e := ε/4) (by positivity)
  choose F hF using (fun z : FreeSpace (base M o) => retain_pointwise M o z (ε/2) (by positivity))
  refine ⟨ht.toFinset.biUnion F,fun G hG u hu => ?_⟩
  obtain ⟨z,hz,huz⟩ := Set.mem_iUnion₂.mp (hcover hu)
  have hze := hF z G ((Finset.subset_biUnion_of_mem F (ht.mem_toFinset.mpr hz)).trans hG)
  have huz' : ‖u-z‖ < ε/4 := by simpa only [Metric.mem_ball,dist_eq_norm] using huz
  calc
    ‖retainL M o G u-u‖ = ‖(retainL M o G (u-z)-(u-z))+(retainL M o G z-z)‖ := by
      rw [map_sub]; congr 1; abel
    _ ≤ ‖retainL M o G (u-z)-(u-z)‖ + ‖retainL M o G z-z‖ := norm_add_le _ _
    _ ≤ 2*‖u-z‖ + ‖retainL M o G z-z‖ := add_le_add (retain_error_bound M o G (u-z)) le_rfl
    _ < ε := by linarith

def collapseL (F : Finset ℕ) : FreeSpace (base M o) →L[ℝ] FreeSpace (retainedBase M o F) :=
  freeMap _ _ (collapse M o F) (collapse_base M o F) (collapse_lipschitz M o F)

def embedL (F : Finset ℕ) : FreeSpace (retainedBase M o F) →L[ℝ] FreeSpace (base M o) :=
  freeMap _ _ (embed M o F) (embed_base M o F) (embed_isometry M o F).lipschitzWith

theorem embedL_bound (F : Finset ℕ) : ‖embedL M o F‖ ≤ 1 := freeMap_bound ..

@[simp] theorem embedL_collapseL (F : Finset ℕ) :
    (embedL M o F).comp (collapseL M o F) = retainL M o F := by
  apply freeMap_ext (base M o)
  intro x
  rfl

theorem hasAP (sep : ∀ n (x y : M n), x ≠ y → 1 ≤ dist x y)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) (hb : ∀ n (x : M n), dist x (o n) ≤ B n) :
    HasAP (FreeSpace (base M o)) := by
  intro C hC ε hε
  obtain ⟨F,hF⟩ := retain_compact M o C hC (ε/4) (by positivity)
  let P := collapseL M o F
  let I := embedL M o F
  have hAP := bounded_separated_hasBAP (retainedBase M o F) (retained_separated M o F sep)
    (∑ n ∈ F, B n) (Finset.sum_nonneg (fun n _ => hB n)) (retained_radius M o F B hB hb)
  obtain ⟨U,hU,_,η,hη,he⟩ := hAP (P '' C) (hC.image P.continuous) (ε/4) (by positivity)
  let T := (I.comp U).comp P
  refine ⟨T,finiteRank_sandwich I U P hU,ε/2,by linarith,?_⟩
  intro u hu
  have hretain : I (P u) = retainL M o F u := congrArg (fun A : FreeSpace (base M o) →L[ℝ] FreeSpace (base M o) => A u) (embedL_collapseL M o F)
  have he' := he (P u) ⟨u,hu,rfl⟩
  have htail := hF F le_rfl u hu
  calc
    ‖T u-u‖ = ‖I (U (P u)-P u)+(retainL M o F u-u)‖ := by
      rw [map_sub,← hretain]; dsimp [T]; congr 1; abel
    _ ≤ ‖I (U (P u)-P u)‖ + ‖retainL M o F u-u‖ := norm_add_le _ _
    _ ≤ ‖U (P u)-P u‖ + ‖retainL M o F u-u‖ := add_le_add (contraction_norm I (embedL_bound M o F) _) le_rfl
    _ ≤ ε/2 := by linarith

end MetricWedge
end DiscreteFree
end

end

end OAI
