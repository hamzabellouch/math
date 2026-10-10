import Mathlib
import OAI.Geometry.WeakMTW.Domains.Definitions
import OAI.Geometry.WeakMTW.Geodesics.CompactGeodesic

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

 theorem shifted_local_intrinsic {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hl : ∀ y : M, ∀ v : TangentSpace 𝓘(ℝ, E) y, ‖v‖ ≤ C →
      ∃ γ : ℝ → M, curveState (E := E) γ 0 = ⟨y, v⟩ ∧
        IsIntrinsicGeodesicOn (E := E) γ ‖v‖ (Ioo (-ε) ε))
    {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hγ : IsIntrinsicGeodesicOn (E := E) γ C U) {t : ℝ} (ht : t ∈ U) :
    ∃ η : ℝ → M, curveState (E := E) η t = curveState (E := E) γ t ∧
      IsIntrinsicGeodesicOn (E := E) η C (Ioo (t-ε) (t+ε)) := by
  have hn := intrinsic_state_norm hU hC hγ ht
  obtain ⟨η, hη₀, hη⟩ := hl (γ t) (curveState (E := E) γ t).2 hn.le
  let η' : ℝ → M := fun s => η (s-t)
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have he : (fun s : ℝ => s-t) ⁻¹' Ioo (-ε) ε = Ioo (t-ε) (t+ε) := by
    ext s
    simp only [mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  refine ⟨η', ?_, ?_⟩
  · have hs := curveState_comp_sub (γ := η) (t := t) (a := t) (by
      simpa only [sub_self] using (((hη.1 0 h0).contMDiffAt
        (isOpen_Ioo.mem_nhds h0)).mdifferentiableAt (by simp)))
    change curveState (E := E) (fun s => η (s-t)) t = _
    rw [hs, sub_self, hη₀]
    rfl
  · have hs := hη.comp_sub (a := t)
    rw [he] at hs
    exact (congrArg (fun speed : ℝ =>
      IsIntrinsicGeodesicOn (E := E) η' speed (Ioo (t-ε) (t+ε))) hn).mp hs

 theorem intrinsic_extend_interval {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hl : ∀ y : M, ∀ v : TangentSpace 𝓘(ℝ, E) y, ‖v‖ ≤ C →
      ∃ γ : ℝ → M, curveState (E := E) γ 0 = ⟨y, v⟩ ∧
        IsIntrinsicGeodesicOn (E := E) γ ‖v‖ (Ioo (-ε) ε))
    {a b : ℝ} (hab : a + ε < b) {γ : ℝ → M}
    (hγ : IsIntrinsicGeodesicOn (E := E) γ C (Ioo a b)) :
    ∃ η : ℝ → M, IsIntrinsicGeodesicOn (E := E) η C (Ioo (a-ε/2) (b+ε/2)) ∧
      EqOn η γ (Ioo a b) := by
  classical
  let t := b-ε/2
  have ht : t ∈ Ioo a b := ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩
  obtain ⟨η, hs, hη⟩ := shifted_local_intrinsic hC hε hl isOpen_Ioo hγ ht
  let δ : ℝ → M := (Ioo a b).piecewise γ η
  have hδ : IsIntrinsicGeodesicOn (E := E) δ C (Ioo a (b+ε/2)) := by
    have hh := intrinsic_piecewise hC isOpen_Ioo isOpen_Ioo
      ((convex_Ioo a b).inter (convex_Ioo (t-ε) (t+ε))).isPreconnected hγ hη
      (show t ∈ Ioo a b ∩ Ioo (t-ε) (t+ε) from ⟨ht, by constructor <;> linarith⟩)
      hs.symm
    have hh' : IsIntrinsicGeodesicOn (E := E) δ C (Ioo a b ∪ Ioo (t-ε) (t+ε)) := by
      convert hh using 1
      funext parameter
      by_cases hparameter : parameter ∈ Ioo a b <;> simp [δ, hparameter]
    apply hh'.mono
    intro s hs
    by_cases hsb : s < b
    · exact Or.inl ⟨hs.1, hsb⟩
    · right
      dsimp [t]
      constructor <;> linarith [hs.2]
  have hδγ : EqOn δ γ (Ioo a b) := fun s hs => piecewise_eq_of_mem _ _ _ hs
  let r := a+ε/2
  have hr : r ∈ Ioo a (b+ε/2) := ⟨by dsimp [r]; linarith, by dsimp [r]; linarith⟩
  obtain ⟨ζ, hrs, hζ⟩ := shifted_local_intrinsic hC hε hl isOpen_Ioo hδ hr
  let β : ℝ → M := (Ioo a (b+ε/2)).piecewise δ ζ
  refine ⟨β, ?_, ?_⟩
  · have hh := intrinsic_piecewise hC isOpen_Ioo isOpen_Ioo
      ((convex_Ioo a (b+ε/2)).inter (convex_Ioo (r-ε) (r+ε))).isPreconnected hδ hζ
      (show r ∈ Ioo a (b+ε/2) ∩ Ioo (r-ε) (r+ε) from ⟨hr, by constructor <;> linarith⟩)
      hrs.symm
    have hh' : IsIntrinsicGeodesicOn (E := E) β C (Ioo a (b+ε/2) ∪ Ioo (r-ε) (r+ε)) := by
      convert hh using 1
      funext parameter
      by_cases hparameter : parameter ∈ Ioo a (b+ε/2) <;> simp [β, hparameter]
    apply hh'.mono
    intro s hs
    by_cases has : a < s
    · exact Or.inl ⟨has, hs.2⟩
    · right
      dsimp [r]
      constructor <;> linarith [hs.1]
  · intro s hs
    rw [show β s = δ s from piecewise_eq_of_mem _ _ _ ⟨hs.1, by linarith [hs.2]⟩]
    exact hδγ hs

 theorem intrinsic_arbitrarily_long [CompactSpace M] (p : TangentBundle 𝓘(ℝ, E) M) :
    ∀ R : ℝ, ∃ γ : ℝ → M, curveState (E := E) γ 0 = p ∧
      IsIntrinsicGeodesicOn (E := E) γ ‖p.2‖ (Ioo (-R) R) := by
  obtain ⟨ε, hε, hl⟩ := compact_uniform_intrinsic (E := E) (M := M) (norm_nonneg p.2)
  have he : ∀ n : ℕ, ∃ γ : ℝ → M, curveState (E := E) γ 0 = p ∧
      IsIntrinsicGeodesicOn (E := E) γ ‖p.2‖
        (Ioo (-(ε + n * (ε/2))) (ε + n * (ε/2))) := by
    intro n
    induction n with
    | zero => simpa using hl p.1 p.2 le_rfl
    | succ n ih =>
      obtain ⟨γ, hγ₀, hγ⟩ := ih
      have hn : 0 ≤ (n : ℝ) * (ε/2) := mul_nonneg (Nat.cast_nonneg _) (by positivity)
      obtain ⟨η, hη, heq⟩ := intrinsic_extend_interval (norm_nonneg p.2) hε hl
        (by linarith : -(ε + n * (ε/2)) + ε < ε + n * (ε/2)) hγ
      refine ⟨η, ?_, ?_⟩
      · rw [← hγ₀]
        apply curveState_congr
        filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-(ε+n*(ε/2))) (ε+n*(ε/2))
          from ⟨by linarith, by linarith⟩)] with s hs
        exact heq hs
      · convert hη using 1
        push_cast
        congr 1 <;> ring
  intro R
  obtain ⟨n, hn⟩ := exists_nat_gt ((R - ε) / (ε/2))
  have hr : R < ε + n * (ε/2) := by
    have hh := (div_lt_iff₀ (show 0 < ε/2 by positivity)).mp hn
    linarith
  obtain ⟨γ, hγ₀, hγ⟩ := he n
  exact ⟨γ, hγ₀, hγ.mono (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩)⟩

 theorem intrinsic_complete_exists [CompactSpace M] (p : TangentBundle 𝓘(ℝ, E) M) :
    ∃ γ : ℝ → M, curveState (E := E) γ 0 = p ∧
      IsIntrinsicGeodesicOn (E := E) γ ‖p.2‖ univ := by
  classical
  choose η hη₀ hη using intrinsic_arbitrarily_long p
  let γ : ℝ → M := fun t => η (|t|+1) t
  have heq : ∀ R : ℝ, 0 < R → EqOn γ (η R) (Ioo (-R) R) := by
    intro R hR t ht
    have hp : 0 < |t|+1 := by positivity
    have hu : IsOpen (Ioo (-R) R ∩ Ioo (-(|t|+1)) (|t|+1)) := isOpen_Ioo.inter isOpen_Ioo
    have hc := ((convex_Ioo (-R) R).inter (convex_Ioo (-(|t|+1)) (|t|+1))).isPreconnected
    have hz : (0 : ℝ) ∈ Ioo (-R) R ∩ Ioo (-(|t|+1)) (|t|+1) :=
      ⟨⟨by linarith, hR⟩, ⟨by linarith, hp⟩⟩
    have hh := intrinsic_unique_on hu hc (norm_nonneg p.2) (norm_nonneg p.2)
      ((hη (|t|+1)).mono inter_subset_right) ((hη R).mono inter_subset_left) hz
      ((hη₀ (|t|+1)).trans (hη₀ R).symm)
    exact hh ⟨ht, ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩⟩
  have hgerm : ∀ t : ℝ, γ =ᶠ[𝓝 t] η (|t|+1) := by
    intro t
    filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Ioo (-(|t|+1)) (|t|+1)
      from ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩)] with s hs
    exact heq (|t|+1) (by positivity) hs
  refine ⟨γ, ?_, ?_⟩
  · exact (curveState_congr (hgerm 0)).trans (hη₀ _)
  · apply intrinsicOn_of_at
    intro t _
    exact ((hη (|t|+1)).at isOpen_Ioo
      ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩).congr (hgerm t)

end
end RiemannianLocal

namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

 theorem completeGeodesic_exists [CompactSpace M] (x : M) (v : TangentSpace (model n) x) :
    ∃ γ : ℝ → M, CompleteGeodesicWithInitialData x v γ := by
  obtain ⟨γ, hs, hγ⟩ := intrinsic_complete_exists (E := Model n) (⟨x,v⟩ : TangentBundle (model n) M)
  have hpair := TotalSpace.ext_iff.mp hs
  refine ⟨γ, contMDiffOn_univ.mp hγ.1, hpair.1, ?_, fun t => hγ.2 t (mem_univ t)⟩
  exact eq_of_heq (eqRec_heq_iff.mpr hpair.2)

 theorem geodesicExistenceUniqueness [CompactSpace M] : GeodesicExistenceUniqueness (n := n) (M := M) := by
  intro x v
  obtain ⟨γ, hγ⟩ := completeGeodesic_exists x v
  exact ⟨γ, hγ, fun η hη => completeGeodesic_unique hη hγ⟩

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
